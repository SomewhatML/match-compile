//! A simplified source-to-source pattern match compiler, derived from
//! Luc Maranget's "Compiling Pattern Matching to Good Decision Trees"

use std::collections::HashSet;
use std::fmt;
mod util;

/// A pattern as represented in the AST
#[derive(Clone, Debug, PartialEq)]
pub enum APat {
    Wild,
    Var(String),
    Record(Vec<(String, APat)>),
    App(String, Option<Box<APat>>),
}

/// Simplified pattern, without variable bindings
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Pat {
    Wild,
    Record(Vec<(String, Pat)>),
    App(String, Option<Box<Pat>>),
}

/// An expression from the AST
#[derive(Clone, Debug, PartialEq)]
pub enum Expr {
    /// `case expr of | apat => expr, ...`
    Case(Box<Expr>, Vec<(APat, Expr)>),
    /// Record or tuple
    Record(Vec<(String, Expr)>),
    /// `let val APat = Expr in Expr end`
    Let(APat, Box<Expr>, Box<Expr>),
    Var(String),
    Int(i64),
    /// `raise Match`
    Fail,
}

#[derive(Default)]
pub struct Matrix {
    pats: Vec<Vec<Pat>>,
    exprs: Vec<Expr>,

    vars: Vec<String>,
}

impl Matrix {
    /// Build a new pattern matrix.
    ///
    /// # Invariants:
    ///
    /// * Type safety - the case expression that is being transformed
    ///     should have been previously verified to be well typed
    /// * Following #1, all patterns should have the same width, etc
    /// * `arg` should be a fresh variable of the same type of the
    ///     match rules
    pub fn build(arg: String, rules: Vec<(APat, Expr)>) -> Matrix {
        let mut mat = Matrix::default();
        mat.vars = vec![arg];
        for (pat, expr) in rules {
            mat.pats.push(vec![Pat::from(pat)]);
            mat.exprs.push(expr);
        }
        mat
    }

    /// Deconstruct a record or tuple pattern, binding each field to a fresh
    /// variable, and flattening all of the record patterns in the first column
    /// [{a, b, c}, ...] --> [a, b, c, ...]
    fn record_rule(&self, fields: &[(String, Pat)]) -> Expr {
        // This part is a little tricky. We need to generate a fresh variable
        // for every field in the pattern
        let mut vars = self.vars.clone();
        let base = vars.remove(0);
        let pat = APat::Record(
            fields
                .iter()
                .enumerate()
                .map(|(idx, (s, _))| {
                    let f = util::fresh();
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
                // If we have a wildcard pattern, generate enough wildcards to
                // subsume every field in the record
                for idx in 0..fields.len() {
                    new_row.insert(idx, Pat::Wild);
                }
            }

            mat.exprs.push(self.exprs[idx].clone());
            mat.pats.push(new_row);
        }
        mat.vars = vars;
        // We now have `let val ($x0, $x1... fresh vars) = x in case [$x0, $x1...]
        Expr::Let(pat, Box::new(Expr::Var(base)), Box::new(mat.compile()))
    }

    /// This is basically the same thing as the record rule, but for data
    /// constructors. We want to select all of the rows in the first column
    /// that will match the constructor `head` (e.g. `head` itself, and wildcard)
    fn specialize(&self, head: &str, arity: bool) -> Expr {
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
        // do we need to mess with mat.vars more?
        mat.compile()
    }

    /// Generate a case expression for the data constructors in the first column
    fn sum_rule(&self) -> Expr {
        // Generate the set of constructors appearing in the column
        let mut set = HashSet::new();
        for row in &self.pats {
            if let Pat::App(con, _) = &row[0] {
                set.insert(con);
            }
        }

        // We only use `true` and `false` or `cons` and `nil`, so we know
        // there are only 2 constructors in each datatype. Otherwise we
        // would need to query a context to determine this
        let exhaustive = set.len() == 2;

        let mut rules = Vec::new();
        for con in set {
            // In a real system, we would have some context to pull the number
            // of data constructors for a datatype, and the arity of each
            // data constructor. We just mock it instead
            let arity = util::simulate_db(con);
            let branch = self.specialize(con, arity);

            let arg = match arity {
                true => Some(Box::new(APat::Wild)),
                false => None,
            };
            rules.push((APat::App(con.into(), arg), branch));
        }

        // If we don't have an exhaustive match, generate a default matrix
        if !exhaustive {
            rules.push((APat::Wild, self.default_matrix()));
        }
        Expr::Case(Box::new(Expr::Var(self.vars[0].clone())), rules)
    }

    /// Compute the "default" matrix
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

    /// Compile a [`Matrix`] into a source-level expression
    pub fn compile(&mut self) -> Expr {
        if self.pats.is_empty() {
            // We have an in-exhaustive case expression
            Expr::Fail
        } else if self.pats[0].iter().all(|p| p == &Pat::Wild) {
            // Every pattern in the first row is a variable or wildcard,
            // so the it matches. return the body of the match rule
            self.exprs[0].clone()
        } else {
            // There is at least one non-wild pattern in the matrix somewhere
            for row in &self.pats {
                match &row[0] {
                    Pat::Record(fields) => return self.record_rule(fields),
                    Pat::App(_, _) => return self.sum_rule(),
                    _ => continue,
                }
            }

            // The first column contains only wildcard patterns. Search the
            // matrix until we find a column that has a non-wildcard pattern,
            // and swap columns with column 0
            let sz = self.pats[0].len();
            let mut col = 1;
            'outer: while col < sz {
                for row in &self.pats {
                    match row.get(col) {
                        Some(Pat::Wild) => continue,
                        _ => break 'outer,
                    }
                }
                col += 1;
            }

            if col < sz {
                for row in self.pats.iter_mut() {
                    row.swap(0, col);
                }
                self.compile()
            } else {
                self.default_matrix()
            }
        }
    }
}

fn main() {
    let ex = util::example2();
    println!("init {}", ex);
    let e = if let Expr::Case(ex, rules) = ex {
        let mut mat = Matrix::build("x".into(), rules);
        mat.compile()
    } else {
        panic!()
    };
    println!("final {}", e);
}
