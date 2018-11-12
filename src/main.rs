

fn var(name: &str) -> Term {
    Term::Var(Variable::new(name, 0))
}

fn main() {
    let db = vec![
        // sibling(X,Y) :- child(X,Z), child(Y,Z).
        Assertion::new(
            Atom::new("sibling".into(), vec![var("X"), var("Y")]),
            Clause::new(vec![
                Atom::new("child".into(), vec![var("X"), var("Z")]),
                Atom::new("child".into(), vec![var("Y"), var("Z")])
            ])
        ),
        // child("luke", "vader")
        Assertion::new(
            Atom::new("child".into(), vec![var("luke"), var("vader")]),
            Clause::empty()
        ),
        // child("leia", "vader")
        Assertion::new(
            Atom::new("child".into(), vec![var("leia"), var("vader")]),
            Clause::empty()
        )
    ];
    // ?- sibling(X, Y).
    let clause = Clause::new(vec![Atom::new("sibling".into(), vec![var("X"), var("Y")])]);
    solve_top_level(clause, db).unwrap();
}

// String starting with a lower case letter
type Constant = String;

// A string starting with an upper case letter,
// followeed by a number which indicates an
// instance of the variable.
// When the proof search depth is n, all variables
// that we need to use are renamed from (x, 0) to
// (x, n)
#[derive(Debug, Clone, PartialEq, Eq)]
struct Variable {
    name: String,
    depth: i32
}

impl Variable {
    fn new(name: impl Into<String>, depth: i32) -> Variable {
        Variable { name: name.into(), depth: depth }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum Term {
    Var(Variable),
    Const(Constant),
    App(Constant, Vec<Term>)
}

// Atomic proposition. p(t1, .., tn)
#[derive(Debug, Clone, PartialEq, Eq)]
struct Atom {
    sym: Constant,
    terms: Vec<Term>
}

impl Atom {
    fn new(sym: Constant, terms: Vec<Term>) -> Atom {
        Atom { sym, terms }
    }
}

// A conjunction of atomic propositions
#[derive(Debug, Clone, PartialEq, Eq)]
struct Clause { conjuncts: Vec<Atom> }

impl Clause {
    fn new(conjuncts: Vec<Atom>) -> Clause {
        Clause { conjuncts }
    }

    fn empty() -> Clause {
        Clause { conjuncts: vec![] }
    }

    fn is_empty(&self) -> bool {
        self.conjuncts.len() == 0
    }
}

// (a, b1, .., bn) is a Horn formula
// (b1 & .. bn) => a
#[derive(Debug, Clone, PartialEq, Eq)]
struct Assertion {
    head: Atom,
    body: Clause
}

impl Assertion {
    fn new(head: Atom, body: Clause) -> Assertion {
        Assertion { head, body }
    }
}

// The current values of variables
type Environment = Vec<(Variable, Term)>;

// The current program
type Database = Vec<Assertion>;

#[derive(Debug, Clone, PartialEq, Eq)]
enum TopLevelCommand {
    Assert(Assertion),
    Goal(Clause)
}

// Returns the value of x in env, or Var(x) if the variable
// is not contained in the environment
fn lookup(env: Environment, x: Variable) -> Term {
    env.iter()
        .find(|vt| vt.0 == x)
        .map_or(Term::Var(x), |vt| vt.1.clone())
}

#[test]
fn test_lookup_found() {
    let env = vec![
        (Variable::new("X", 0), Term::Const("value".into()))
    ];
    let x = Variable::new("X", 0);
    assert_eq!(lookup(env, x), Term::Const("value".into()));
}

#[test]
fn test_lookup_not_found() {
    let env = vec![
        (Variable::new("X", 0), Term::Const("value".into()))
    ];
    let y = Variable::new("Y", 0);
    assert_eq!(lookup(env, y.clone()), Term::Var(y.clone()));
}

// subst_term(sub, t) subsitutes variables in term t for values
// specified by sub. It substitutes repeatedly until the terms
// stop changing, as needed during unification
fn subst_term(env: &Environment, t: &Term) -> Term {
    println!("SUBST_TERM");
    println!("  env: {:?}", env);
    println!("  t: {:?}", t);

    match t {
        Term::Var(x) => {
            let e = lookup(env.clone(), x.clone());
            if e == Term::Var(x.clone()) { 
                e
            } else {
                subst_term(env, &e)
            }
        },
        e@Term::Const(_) => e.clone(),
        Term::App(c, ts) => Term::App(
            c.clone(),
            ts.iter()
                .map(|l| subst_term(env, l))
                .collect()
            )
    }
}

// Converts a term t to its string representation
fn string_of_term(t: &Term) -> String {
    match t {
        Term::Var(Variable { name: v, depth: 0 }) => v.clone(),
        Term::Var(Variable { name: v, depth: n })  => format!("{}{}", v, n),
        Term::Const(c) => c.clone(),
        Term::App(f, ts) => {
            let args: Vec<String> = ts.iter().map(string_of_term).collect();
            format!("{}({})", f, args.join(", "))
        }
    }
}

// Converts an environment to it its string representation,
// only keeping variables at level 0
fn string_of_env(env: &Environment) -> String {
    let env = env.clone().into_iter().filter(|(Variable { name: _, depth: n }, _)| *n == 0).collect::<Vec<_>>();
    if env.len() == 0 {
        String::from("Yes")
    } else {
        env.iter()
            .rev()
            .map(|(Variable { name: x, depth: _ }, t)| format!(
                "{} = {}",
                x,
                string_of_term(&subst_term(&env, t)
                )
            ))
            .collect::<Vec<_>>()
            .join("\n")
    }
}

// Whether a variable occurs in a term
fn occurs(x: &Variable, t: &Term) -> bool {
    match t {
        Term::Var(y) => x == y,
        Term::Const(_) => false,
        Term::App(_, ts) => ts.iter().any(|l| occurs(x, l))
    }
}

#[derive(Debug)]
struct NoUnify;

// Unifies terms t1 and t2 in the current environment.
// On success it returns the environment extended with the result of 
// unification. On failure it returns None.
fn unify_terms(env: &Environment, t1: &Term, t2: &Term) -> Result<Environment, NoUnify> {
    println!("UNIFY_TERMS");
    println!("  env: {:?}", env);
    println!("  t1: {:?}", t1);
    println!("  t2: {:?}", t2);

    let s1 = subst_term(env, t1);
    let s2 = subst_term(env, t2);

    if s1 == *t1 && s2 == *t2 {
        return Ok(env.clone());
    }

    match (&s1, &s2) {
        (Term::Var(y), t) | (t, Term::Var(y)) => {
            if occurs(y, t) { Err(NoUnify) } else {
                let mut r = env.clone();
                r.insert(0, (y.clone(), t.clone()));
                Ok(r)
            }
        },
        (Term::Const(_), _) => Err(NoUnify),
        (Term::App(c1, ts1), Term::App(c2, ts2)) if c1 == c2 => {
            unify_lists(env, ts1.clone(), ts2.clone())
        },
        (Term::App(_, _), _) => Err(NoUnify)
    }
}

// Unifies two lists in current environment and returns a new environment on success.
// Returns Err on failure to unify or if the lists are not of equal length.
fn unify_lists(env: &Environment, lst1: Vec<Term>, lst2: Vec<Term>) -> Result<Environment, NoUnify> {
    if lst1.len() != lst2.len() {
        return Err(NoUnify);
    }
    let mut acc = env.clone();
    for i in 0..lst1.len() {
        acc = unify_terms(&acc, &lst1[i], &lst2[i])?;
    }
    Ok(acc)
}

// Unifies atomic propositions in current environment
fn unify_atoms(env: &Environment, a1: &Atom, a2: &Atom) -> Result<Environment, NoUnify> {
    let Atom { sym: c1, terms: ts1 } = a1;
    let Atom { sym: c2, terms: ts2 } = a2;

    if c1 == c2 {
        unify_lists(env, ts1.clone(), ts2.clone())
    } else {
        Err(NoUnify)
    }
}

// A choice point in the proof search at which we may continue searching
// for another solution for a clause. Final item is the search depth
type Choice = (Database, Environment, Clause, i32);

#[derive(Debug)]
struct NoSolution;

// Renumbers all variable instances occurring in a term so that they have level n
fn renumber_term(n: i32, t: &Term) -> Term {
    match t {
        Term::Var(Variable { name: x, depth: _ }) => Term::Var(Variable::new(x.clone(), n)),
        Term::Const(x) => Term::Const(x.clone()),
        Term::App(c, ts) => Term::App(c.clone(), ts.iter().map(|u| renumber_term(n, u)).collect())
    }
}

// Renumbers all variable instances occurring in an atom so that they have level n
fn renumber_atom(n: i32, a: &Atom) -> Atom {
    let Atom { sym: c, terms: ts } = a;
    Atom::new(c.clone(), ts.iter().map(|t| renumber_term(n, t)).collect())
}

// Displays the solution of a goal encoded by env. Gives the user the option to search
// for other solutions, as described by the list of choice points ch, to to abort the
// current proof search
fn display_solution(ch: &[Choice], env: &Environment) -> Result<(), NoSolution> {
    println!("ENV IS: {:?}", env);

    let env_str = string_of_env(env);
    if env_str == "Yes" {
        println!("Yes");
        return Ok(());
    }
    if ch.len() == 0 {
        println!("{}", env_str);
        return Ok(());
    }
    // TODO: support searching for more solutions
    let answer = "n";
    match answer {
        "y" => continue_search(ch),
        _ => Err(NoSolution)
    }
}

// Looks for other answers. Continues the search at the first choice in the list
fn continue_search(ch: &[Choice]) -> Result<(), NoSolution> {
    if ch.len() == 0 {
        Err(NoSolution)
    } else {
        let (d, e, c, n) = &ch[0];
        solve(&ch[1..], d.clone(), e.clone(), c.clone(), *n)
    }
}

// Reduces atom a to subgoals by using the first assertion in the db whose
// conclusion matches a. It returns None if the atom cannot be reduced, or the
// remaining assertions, new environment and list of subgoals if it can.
fn reduce_atom(a: Atom, env: Environment, db: Database, n: i32) -> Option<(Database, Environment, Clause)> {
    println!("REDUCE_ATOM");
    println!("  a: {:?}", a);
    println!("  env: {:?}", env);
    println!("  db: {:?}", db);
    println!("  n: {}", n);

    if db.len() == 0 {
            None
    } else {
        let Assertion { head: b, body: lst } = &db[0];
        let rest = db.clone().into_iter().skip(1).collect::<Vec<_>>();
        let maybe_new_env = unify_atoms(&env, &a, &renumber_atom(n, b));
        match maybe_new_env {
            Ok(new_env) => Some((rest, new_env, Clause::new(lst.conjuncts.iter().map(|l| renumber_atom(n, l)).collect::<Vec<_>>()))),
            Err(_) => reduce_atom(a, env, rest, n)
        }
    }
}

// Searches for a proof of clause c.
fn solve(ch: &[Choice], db: Database, env: Environment, c: Clause, n: i32) -> Result<(), NoSolution> {
    println!("C LENGTH = {}. n = {}", c.conjuncts.len(), n);

    if c.is_empty() {
        // All atoms are solved, we found a solution
        return display_solution(ch, &env);
    }

    let a = c.conjuncts[0].clone();
    let cp = c.clone().conjuncts.into_iter().skip(1).collect::<Vec<_>>();

    // Reduce the first atom in the clause
    match reduce_atom(a, env.clone(), db.clone(), n) {
        None => {
            // This clause cannot be solved, look for other solutions.
            continue_search(ch)
        },
        Some((new_db, new_env, mut d)) => {
            // The atom was reduced to subgoals d. Continue search with
            // the subgoals added to the list of goals.
            let mut new_ch = ch.iter().map(|x| x.clone()).collect::<Vec<_>>();
            new_ch.insert(0, (new_db, env.clone(), c, n));
            d.conjuncts.extend(cp);
            solve(&new_ch, db.clone(), new_env, d, n + 1)
        }
    }
}

// Searches for the proof of clause c using the provided global database
fn solve_top_level(c: Clause, db: Database) -> Result<(), NoSolution> {
    solve(&vec![], db, vec![], c, 1)
}