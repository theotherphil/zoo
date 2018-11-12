fn main() {
    let t = Term::App(
        String::from("foo"),
        vec![
            Term::Var((String::from("X"), 0)),
            Term::Var((String::from("Y"), 1))
        ]);

    println!("{}", string_of_term(&t));
}

// String starting with a lower case letter
type Constant = String;

// A string starting with an upper case letter,
// followeed by a number which indicates an
// instance of the variable.
// When the proof search depth is n, all variables
// that we need to use are renamed from (x, 0) to
// (x, n)
type Variable = (String, i32);

#[derive(Debug, Clone, PartialEq, Eq)]
enum Term {
    Var(Variable),
    Const(Constant),
    App(Constant, Vec<Term>)
}

// Atomic proposition. p(t1, .., tn)
type Atom = (Constant, Vec<Term>);

// A conjunction of atomic propositions
type Clause = Vec<Atom>;

// (a, b1, .., bn) is a Horn formula
// (b1 & .. bn) => a
type Assertion = (Variable, Term);

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

// subst_term(sub, t) subsitutes variables in term t for values
// specified by sub. It substitutes repeatedly until the terms
// stop changing, as needed during unification
fn subst_term(env: Environment, t: Term) -> Term {
    match &t {
        Term::Var(x) => {
            let e = lookup(env.clone(), x.clone());
            if e == Term::Var(x.clone()) { 
                e
            } else {
                subst_term(env.clone(), e.clone())
            }
        },
        e@Term::Const(_) => e.clone(),
        Term::App(c, ts) => Term::App(
            c.clone(),
            ts.iter()
                .map(|l| subst_term(env.clone(), l.clone()))
                .collect()
            )
    }
}

// Converts a term t to its string representation
fn string_of_term(t: &Term) -> String {
    match t {
        Term::Var((v, 0)) => v.clone(),
        Term::Var((v, n)) => format!("{}{}", v, n),
        Term::Const(c) => c.clone(),
        Term::App(f, ts) => {
            let args: Vec<String> = ts.iter().map(string_of_term).collect();
            format!("{}({})", f, args.join(", "))
        }
    }
}

// Converts an environment to it its string representation,
// only keeping variables at level 0
fn string_of_env(env: Environment) -> String {
    let env = env.clone().into_iter().filter(|((_, n), _)| *n == 0).collect::<Vec<_>>();
    if env.len() == 0 {
        String::from("Yes")
    } else {
        env.iter()
            .rev()
            .map(|((x, _), t)| format!(
                "{} = {}",
                x,
                string_of_term(&subst_term(env.clone(), t.clone())
                )
            ))
            .collect::<Vec<_>>()
            .join("\n")
    }
}

fn occurs(x: &Variable, t: &Term) -> bool {
    match t {
        Term::Var(y) => x == y,
        Term::Const(_) => false,
        Term::App(_, ts) => ts.iter().any(|l| occurs(x, l))
    }
}
