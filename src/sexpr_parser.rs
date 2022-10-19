use std::fmt::{self, Display, Formatter};

#[derive(Debug, PartialEq)]
pub enum SExpr<'a> {
    Symbol(&'a [u8]),
    Expr(Vec<SExpr<'a>>),
}

impl<'a> SExpr<'a> {
    pub fn as_symbol(&self) -> &[u8] {
        if let SExpr::Symbol(s) = self {
            s
        } else {
            panic!("Expected symbol.");
        }
    }
    pub fn as_subexpr(&self) -> &Vec<SExpr<'a>> {
        if let SExpr::Expr(items) = self {
            items
        } else {
            panic!("Expected subexpression.");
        }
    }
}

pub fn parse_sexpr(input: &[u8]) -> SExpr {
    let (result, rest) = parse_sexpr_slice(input, 0);
    assert!(rest >= input.len());
    result
}

pub fn parse_sexpr_slice(input: &[u8], mut p: usize) -> (SExpr, usize) {
    while matches!(input[p], b' ' | b'\r' | b'\n') {
        p += 1
    }
    if input[p] == b'(' {
        let mut sub = Vec::new();
        p += 1;
        loop {
            while matches!(input[p], b' ' | b'\r' | b'\n') {
                p += 1
            }
            if input[p] == b')' {
                break;
            }
            let next;
            (next, p) = parse_sexpr_slice(input, p);
            sub.push(next);
        }
        (SExpr::Expr(sub), p + 1)
    } else {
        let start = p;
        loop {
            if p >= input.len() {
                break;
            }
            let c = input[p];
            if c == b'(' || c == b')' || c == b' ' {
                break;
            }
            p += 1;
        }
        (SExpr::Symbol(&input[start..p]), p)
    }
}

impl<'a> Display for SExpr<'a> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            SExpr::Symbol(s) => write!(f, "{}", std::str::from_utf8(*s).unwrap()),
            SExpr::Expr(sub_expr) => write!(
                f,
                "({})",
                sub_expr
                    .iter()
                    // TODO should properly write to f instead of using to_string.
                    .map(|e| e.to_string())
                    .collect::<Vec<_>>()
                    .join(" ")
            ),
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn parse() {
        let x = "()".to_string();
        assert_eq!(parse_sexpr(b"()"), SExpr::Expr(vec![]));
        assert_eq!(parse_sexpr(&x.as_bytes()), SExpr::Expr(vec![]));
        assert_eq!(parse_sexpr(b"x"), SExpr::Symbol("x".as_bytes()));
        assert_eq!(
            parse_sexpr(b"(x)"),
            SExpr::Expr(vec![SExpr::Symbol("x".as_bytes())])
        );
        assert_eq!(
            parse_sexpr(b"(x y)"),
            SExpr::Expr(vec![
                SExpr::Symbol("x".as_bytes()),
                SExpr::Symbol("y".as_bytes())
            ])
        );
        assert_eq!(
            parse_sexpr(b"(x (y t) (r))"),
            SExpr::Expr(vec![
                SExpr::Symbol("x".as_bytes()),
                SExpr::Expr(vec![
                    SExpr::Symbol("y".as_bytes()),
                    SExpr::Symbol("t".as_bytes()),
                ]),
                SExpr::Expr(vec![SExpr::Symbol("r".as_bytes()),])
            ])
        );
    }

    #[test]
    fn parse_sexpr_spaces() {
        assert_eq!(parse_sexpr(b"()"), parse_sexpr(b"(  )"));
        assert_eq!(parse_sexpr(b"(  x (y )  )"), parse_sexpr(b"(x(y))"));
        assert_eq!(
            parse_sexpr(b"(  x () (y ) ( t t) )"),
            parse_sexpr(b"(x()(y)(t t))")
        );
    }

    #[test]
    fn display() {
        assert_eq!(
            format!("{}", parse_sexpr(b"(  x () (y ) ( t t) )")),
            "(x () (y) (t t))"
        );
    }
}
