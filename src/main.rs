use std::cell::Cell;
use std::collections::{HashMap, HashSet};
use std::fmt;

thread_local! {
    pub static COUNTER: Cell<usize> = Cell::new(0);
}

fn fresh() -> String {
    let c = COUNTER.with(|c| {
        let n = c.get();
        c.set(n + 1);
        n
    });
    format!("$x{}", c)
}

fn simulate_db(constructor: &str) -> bool {
    match constructor {
        "nil" => false,
        "cons" => true,
        _ => panic!("something has gone horribly wrong"),
    }
}

#[derive(Clone, Debug, PartialEq)]
pub enum APat {
    Wild,
    Var(String),
    Record(Vec<(String, APat)>),
    App(String, Option<Box<APat>>),
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Pat {
    Wild,
    Record(Vec<(String, Pat)>),
    App(String, Option<Box<Pat>>),
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

#[derive(Clone, Debug, PartialEq)]
pub enum Expr {
    Case(Box<Expr>, Vec<(APat, Expr)>),
    Record(Vec<(String, Expr)>),
    Let(APat, Box<Expr>, Box<Expr>),
    Var(String),
    Int(i64),
    Fail,
}

/// fun merge [] x = 1
///   | merge x [] = 1
///   | merge (x::xs) y = 2
fn example() -> Expr {
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

#[derive(Default)]
pub struct Matrix {
    pats: Vec<Vec<Pat>>,
    exprs: Vec<Expr>,

    vars: Vec<String>,
}

impl Matrix {
    pub fn build(arg: String, rules: Vec<(APat, Expr)>) -> Matrix {
        let mut mat = Matrix::default();
        mat.vars = vec![arg];
        for (pat, expr) in rules {
            mat.pats.push(vec![Pat::from(pat)]);
            mat.exprs.push(expr);
        }
        mat
    }

    pub fn variable_rule(&self) -> Expr {
        self.exprs[0].clone()
    }

    pub fn record_rule(&self, fields: &[(String, Pat)]) -> Expr {
        // let val {x, y, z} = a in case (x, y, z) of ... end
        let mut vars = self.vars.clone();
        let base = vars.remove(0);
        let pat = APat::Record(
            fields
                .iter()
                .enumerate()
                .map(|(idx, (s, _))| {
                    let f = fresh();
                    vars.insert(idx, f.clone());
                    (s.clone(), APat::Var(f))
                })
                .collect(),
        );

        let mut mat = Matrix::default();
        for (idx, row) in self.pats.iter().enumerate() {
            let mut new_row: Vec<Pat> = row.iter().skip(1).cloned().collect();
            if let Pat::Record(fields) = &row[0] {
                for (idx, (_, pat)) in fields.iter().enumerate() {
                    new_row.insert(idx, pat.clone());
                }
            } else {
                for idx in 0..fields.len() {
                    new_row.insert(idx, Pat::Wild);
                }
            }

            mat.exprs.push(self.exprs[idx].clone());
            mat.pats.push(new_row);
        }
        mat.vars = vars;

        // dbg!(&mat);
        Expr::Let(pat, Box::new(Expr::Var(base)), Box::new(mat.compile()))
    }

    pub fn specialize(&self, head: &str, arity: bool) -> Expr {
        let mut mat = Matrix::default();
        for (idx, row) in self.pats.iter().enumerate() {
            let mut new_row: Vec<Pat> = row.iter().skip(1).cloned().collect();
            match &row[0] {
                Pat::App(con, Some(arg)) if con == head => {
                    new_row.insert(0, *arg.clone());
                }
                Pat::App(con, None) if con == head => {}
                Pat::Wild => {
                    if arity {
                        new_row.insert(0, Pat::Wild);
                    }
                }
                _ => continue,
            }

            mat.exprs.push(self.exprs[idx].clone());
            mat.pats.push(new_row);
        }
        mat.vars = self.vars.clone();
        if !arity {
            mat.vars.remove(0);
        }
        println!("specialize rule {} {:?}\n{:?}", head, self, mat);

        mat.compile()
    }

    pub fn sum_rule(&self) -> Expr {
        let mut set = HashSet::new();
        let mut wild = false;
        for row in &self.pats {
            match &row[0] {
                Pat::App(con, _) => {
                    set.insert(con);
                }
                Pat::Wild => {
                    wild = true;
                }
                _ => unreachable!(),
            }
        }
        let exhaustive = wild || set.len() == 2;
        // println!("sum rule {:?}", self);
        let mut rules = Vec::new();
        for con in set {
            let arity = simulate_db(con);
            let branch = self.specialize(con, arity);
            if arity {
                rules.push((APat::App(con.into(), Some(Box::new(APat::Wild))), branch));
            } else {
                rules.push((APat::App(con.into(), None), branch));
            }
            // println!("branch {} = {:?}", con, branch);
        }
        if !exhaustive {
            rules.push((APat::Wild, self.default_matrix()));
        }
        Expr::Case(Box::new(Expr::Var(self.vars[0].clone())), rules)
        // todo!()
    }

    fn default_matrix(&self) -> Expr {
        let mut mat = Matrix::default();
        mat.vars = self.vars.clone();
        mat.vars.remove(0);

        for (idx, row) in self.pats.iter().enumerate() {
            if let Some(Pat::Wild) = row.first() {
                mat.pats.push(row.iter().skip(1).cloned().collect());
                mat.exprs.push(self.exprs[idx].clone());
            }
        }
        mat.compile()
    }

    pub fn compile(&self) -> Expr {
        // dbg!(&self);
        if self.pats.is_empty() {
            Expr::Fail
        } else if self.pats[0].iter().all(|p| p == &Pat::Wild) {
            self.variable_rule()
        } else {
            // There is at least one non-wild pattern in the first row
            for row in &self.pats {
                match &row[0] {
                    Pat::Record(fields) => return self.record_rule(fields),
                    Pat::App(_, _) => return self.sum_rule(),
                    _ => continue,
                }
            }
            self.default_matrix()
        }
    }
}

fn main() {
    println!("Hello, world!");
    let ex = example();
    println!("init {}", ex);
    let e = if let Expr::Case(e, rules) = ex {
        let mat = Matrix::build("x".into(), rules);
        Expr::Let(APat::Var("x".into()), e, Box::new(mat.compile()))
    } else {
        panic!()
    };
    println!("final {}", e);
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
        write!(f, "")
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
