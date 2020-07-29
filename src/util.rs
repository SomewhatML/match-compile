use super::*;
use std::cell::Cell;

thread_local! {
    pub static COUNTER: Cell<usize> = Cell::new(0);
}

/// Generate a unique variable name
pub fn fresh() -> String {
    let c = COUNTER.with(|c| {
        let n = c.get();
        c.set(n + 1);
        n
    });
    format!("$x{}", c)
}

/// Return whether a data constructor takes an argument
pub fn simulate_db(constructor: &str) -> bool {
    match constructor {
        "nil" => false,
        "cons" => true,
        "t" => false,
        "f" => false,
        _ => panic!("something has gone horribly wrong"),
    }
}

impl From<APat> for Pat {
    fn from(other: APat) -> Self {
        match other {
            APat::Wild | APat::Var(_) => Pat::Wild,
            APat::Record(fields) => {
                Pat::Record(fields.into_iter().map(|(s, p)| (s, p.into())).collect())
            }
            APat::App(s, c) => Pat::App(s, c.map(|p| Box::new(Pat::from(*p)))),
        }
    }
}

impl From<Pat> for APat {
    fn from(other: Pat) -> Self {
        match other {
            Pat::Wild => APat::Wild,
            Pat::Record(fields) => {
                APat::Record(fields.into_iter().map(|(s, p)| (s, p.into())).collect())
            }
            Pat::App(s, c) => APat::App(s, c.map(|p| Box::new(APat::from(*p)))),
        }
    }
}

/// fun merge [] y = 1
///   | merge x [] = 1
///   | merge (x::xs) y = 2
pub fn example() -> Expr {
    Expr::Case(
        Box::new(Expr::Var("args".into())),
        vec![
            (
                APat::Record(vec![
                    ("0".into(), APat::App("nil".into(), None)),
                    ("1".into(), APat::Var("y".into())),
                ]),
                Expr::Int(1),
            ),
            (
                APat::Record(vec![
                    ("0".into(), APat::Var("x".into())),
                    ("1".into(), APat::App("nil".into(), None)),
                ]),
                Expr::Int(2),
            ),
            (
                APat::Record(vec![
                    (
                        "0".into(),
                        APat::App(
                            "cons".into(),
                            Some(Box::new(APat::Record(vec![
                                ("0".into(), APat::Var("x".into())),
                                ("1".into(), APat::Var("xs".into())),
                            ]))),
                        ),
                    ),
                    (
                        "1".into(),
                        APat::App(
                            "cons".into(),
                            Some(Box::new(APat::Record(vec![
                                ("0".into(), APat::Var("y".into())),
                                ("1".into(), APat::Var("ys".into())),
                            ]))),
                        ),
                    ),
                ]),
                Expr::Int(3),
            ),
        ],
    )
}
/// example2
/// match x, y, z with
///     | _, F, T => 1
///     | F, T, _ => 2
///     | _, _, F => 3
///     | _, _, T => 4
pub fn example2() -> Expr {
    Expr::Case(
        Box::new(Expr::Var("args".into())),
        vec![
            (
                APat::Record(vec![
                    ("0".into(), APat::Wild),
                    ("1".into(), APat::App("f".into(), None)),
                    ("2".into(), APat::App("t".into(), None)),
                ]),
                Expr::Int(1),
            ),
            (
                APat::Record(vec![
                    ("0".into(), APat::App("f".into(), None)),
                    ("1".into(), APat::App("t".into(), None)),
                    ("2".into(), APat::Wild),
                ]),
                Expr::Int(2),
            ),
            (
                APat::Record(vec![
                    ("0".into(), APat::Wild),
                    ("1".into(), APat::Wild),
                    ("2".into(), APat::App("f".into(), None)),
                ]),
                Expr::Int(3),
            ),
            (
                APat::Record(vec![
                    ("0".into(), APat::Wild),
                    ("1".into(), APat::Wild),
                    ("2".into(), APat::App("t".into(), None)),
                ]),
                Expr::Int(4),
            ),
        ],
    )
}

impl fmt::Debug for Matrix {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "matrix {:?}\n", self.vars)?;
        for (pats, exprs) in self.pats.iter().zip(self.exprs.iter()) {
            writeln!(
                f,
                "{} => {}",
                pats.iter()
                    .map(|pat| format!("{}", APat::from(pat.clone())))
                    .collect::<Vec<String>>()
                    .join(","),
                exprs
            )?;
        }
        // write!(f, "")
        Ok(())
    }
}

impl fmt::Display for APat {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            APat::Wild => write!(f, "_"),
            APat::Var(s) => write!(f, "{}", s),
            APat::App(c, Some(p)) => write!(f, "{} {}", c, p),
            APat::App(c, None) => write!(f, "{}", c),
            APat::Record(fields) => write!(
                f,
                "{{{}}}",
                fields
                    .iter()
                    .map(|(s, p)| format!("{}: {}", s, p))
                    .collect::<Vec<String>>()
                    .join(",")
            ),
        }
    }
}

impl fmt::Display for Expr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Expr::Fail => write!(f, "raise Match"),
            Expr::Int(i) => write!(f, "{}", i),
            Expr::Var(s) => write!(f, "{}", s),
            Expr::Let(s, bind, body) => write!(f, "let {} = {} in {} end", s, bind, body),
            Expr::Case(e, fields) => write!(
                f,
                "case {} of\n{} end",
                e,
                fields
                    .iter()
                    .map(|(s, p)| format!("\t| {} => {}", s, p))
                    .collect::<Vec<String>>()
                    .join("\n")
            ),
            Expr::Record(fields) => write!(
                f,
                "{{{}}}",
                fields
                    .iter()
                    .map(|(s, p)| format!("{}: {}", s, p))
                    .collect::<Vec<String>>()
                    .join(",")
            ),
        }
    }
}
