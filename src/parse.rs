

#[derive(Parser)]
#[grammar = "./rule.pest"]
/// FCParser = Factory Config Parser
pub struct FCParser;

use pest::{iterators::*, pratt_parser::PrattParser};

lazy_static::lazy_static! {
    pub static ref PRATT_PARSER: PrattParser<Rule> = {
        use pest::pratt_parser::{Assoc::*, Op};
        use Rule::*;

        PrattParser::new()
            .op(Op::infix(equ, Left) 
              | Op::infix(neq, Left)
              | Op::infix(gt, Left)
              | Op::infix(lt, Left)
              | Op::infix(ge, Left)
              | Op::infix(le, Left))
            .op(Op::infix(add, Left) | Op::infix(sub, Left))
            .op(Op::infix(mul, Left) | Op::infix(div, Left) | Op::infix(idv, Left))
            .op(Op::infix(pow, Left))
            .op(Op::prefix(neg))
    };
}


#[derive(Debug, Clone)]
pub enum Expr{
    Equ(Box<(Expr, Expr)>),
    Neq(Box<(Expr, Expr)>),
    Gt(Box<(Expr, Expr)>),
    Lt(Box<(Expr, Expr)>),
    Ge(Box<(Expr, Expr)>),
    Le(Box<(Expr, Expr)>),
    Add(Box<(Expr, Expr)>),
    Sub(Box<(Expr, Expr)>),
    Mul(Box<(Expr, Expr)>),
    Div(Box<(Expr, Expr)>),
    Idv(Box<(Expr, Expr)>),
    Pow(Box<(Expr, Expr)>),
    Neg(Box<Expr>),
    Pathident(String),
    Call(String, Vec<Expr>),
    Int(i64),
    Float(f64),
    Bool(bool),
    Nil,
}



pub fn parse_expr(pairs: Pairs<Rule>) -> Expr {
    use Rule as R;
    use Expr::*;
    PRATT_PARSER
        .map_primary(|primary| match primary.as_rule() {
            R::float => {
                Float(primary.as_str().parse().unwrap())
            },
            R::uint => {
                Int(primary.as_str().parse().unwrap())
            },
            R::int => {
                Int(primary.as_str().parse().unwrap())
            },
            R::bool => {
                Bool(primary.as_str().parse().unwrap())
            },
            R::char => {
                unimplemented!()
            },
            R::nil => {
                Nil
            },
            R::call => {
                let mut i = primary.into_inner();
                Call(
                    i.next().unwrap().as_str().to_string(), 
                    i.map(|x|parse_expr(x.into_inner())).collect()
                )
            },
            R::pathident => {
                Pathident(primary.as_str().to_string())
            },
            R::expr => {
                parse_expr(primary.into_inner())
            },
            _ => unreachable!()
        })
        .map_prefix(|op, rhs| match op.as_rule() {
            R::neg => {Neg(Box::new(rhs))}
            _ => unreachable!()
        })
        // .map_postfix(|lhs, op| match op.as_rule() {
        //     _          => unreachable!(),
        // })
        .map_infix(|lhs, op, rhs| match op.as_rule() {
            R::equ => Equ(Box::new((lhs,rhs))),
            R::neq => Neq(Box::new((lhs,rhs))),
            R::gt =>  Gt(Box::new((lhs,rhs))),
            R::lt =>  Lt(Box::new((lhs,rhs))),
            R::ge =>  Ge(Box::new((lhs,rhs))),
            R::le =>  Le(Box::new((lhs,rhs))),
            R::add => Add(Box::new((lhs,rhs))),
            R::sub => Sub(Box::new((lhs,rhs))),
            R::mul => Mul(Box::new((lhs,rhs))),
            R::div => Div(Box::new((lhs,rhs))),
            R::idv => Idv(Box::new((lhs,rhs))),
            R::pow => Pow(Box::new((lhs,rhs))),
            _          => unreachable!(),
        })
        .parse(pairs)
}

enum AST{
    EmptyStatement,
    Ident(String),

    Int(i64),
    Real(f64),
    Bool(bool),
    Primitive(String),
    Pointer(Box<AST>),
    ConstTypeField(String, Box<AST>, Box<AST>),
    TypeField(Vec<String>,Box<AST>),
    Kamus(Vec<(Vec<String>,String)>),
    Assignment(String,Box<AST>),
    Konstanta(Vec<(Vec<String>,String)>),
    UserType(String),
    Expr(Box<AST>),
    Add(Vec<AST>),
    Mul(Vec<AST>),
    Sub(Box<(AST,AST)>),
    Div(Box<(AST,AST)>),
    Idv(Box<(AST,AST)>),
    Neq(Box<(AST,AST)>),
    Equ(Box<(AST,AST)>),
    Pow(Box<(AST,AST)>),
    Le(Box<(AST,AST)>),
    Ge(Box<(AST,AST)>),
    Lt(Box<(AST,AST)>),
    Gt(Box<(AST,AST)>),
    Neg(Box<AST>),
    Fac(Box<AST>),
    ParamIO(bool,bool),
    Parameter(bool,bool,Vec<String>,Box<AST>),
    Algoritma(Vec<AST>),
    ProcDef(
        String,
        Vec<(bool,bool,Vec<String>,Box<AST>)>,
        Box<(AST,AST,AST)>, // konstant, kamus, algoritma
    ),
    FuncDef(
        String,
        Vec<(bool,bool,Vec<String>,Box<AST>)>,
        String,
        Box<(AST,AST,AST)>, // konstant, kamus, algoritma
    ),
    TypeDef(
        String,
        Vec<(Vec<String>,String)>,
    ),
    TypeAlias(Vec<String>, Box<AST>),
    RetStmt(Box<AST>),
    IfStmt(
        Vec<(AST,AST)>,//if x then y + else if x then y
        Option<Box<AST>>, //else y
    ),
    WhlStmt(
        Box<AST>,//while expr
        Vec<AST>,//do stmt*
    ),
    MainProg(
        String,
        Box<(AST,AST,AST)>, // konstant, kamus, algoritma
    )
}

impl Into<AST> for Pair<'_, Rule>{
    fn into(self) -> AST {
        use Rule::*;
        use AST::*;
        let s = self.as_str().to_string();
        let mut i = self.clone().into_inner();
        match self.as_rule() {
            ident => Ident(s),
            uint|int => Int(s.parse().unwrap()),
            float => Real(s.parse().unwrap()),
            bool => Bool(s.parse().unwrap()),
            primitives => Primitive(s),
            pointer_type => Pointer(Box::new(i.next().unwrap().into())),
            type_field => TypeField(
                i.clone().fold(vec![], |mut v,p|{
                    if p.as_rule()==ident{
                        v.push(p.as_str().to_string());
                    }
                    return v;
                }),
                Box::new(i.last().unwrap().into())
            ),
            const_type_field => ConstTypeField(
                i.next().unwrap().as_str().to_string(),
                Box::new({ 
                    let j = i.next().unwrap();
                    match j.as_rule(){
                        primitives => Primitive(j.as_str().to_string()),
                        pointer_type => j.into(),
                        user_type => UserType(j.as_str().to_string()),
                        _ => unreachable!(),
                    }
                }),
                Box::new({ 
                    let j = i.next().unwrap();
                    let jstr = j.as_str();
                    match j.as_rule(){
                        float=>Real(jstr.parse().unwrap()),
                        uint|int=>Int(jstr.parse().unwrap()),
                        bool=>Bool(jstr.parse().unwrap()),
                        char=>unimplemented!(),
                        _ => unreachable!(),
                    }
                }),
            ),
            type_def => TypeDef(
                i.next().unwrap().to_string(), 
                i.fold(vec![], |mut v,x|{
                    let xi = x.into_inner();
                    v.push((
                        xi.clone().fold(vec![], |mut vi, p|{
                            if p.as_rule()==ident{
                                vi.push(p.as_str().to_string());
                            }
                            return vi;
                        }),
                        xi.last().unwrap().as_str().to_string()
                    ));
                    v
                })
            ),
            kamus => Kamus(
                i.fold(vec![], |mut v,x|{
                    let xi = x.into_inner();
                    v.push((
                        xi.clone().fold(vec![], |mut vi, p|{
                            if p.as_rule()==ident{
                                vi.push(p.as_str().to_string());
                            }
                            return vi;
                        }),
                        xi.last().unwrap().as_str().to_string()
                    ));
                    v
                })
            ),
            asgnstmt => Assignment(
                i.clone().fold((String::new(),false), |(mut s, mut b), x|{
                    if x.as_rule()==ident{
                        if b{
                            s+=".";
                        }
                        b=true;
                        s+=x.as_str();
                    }
                    (s, b)
                }).0, 
                Box::new(i.next().unwrap().into())
            ),
            konstanta => Konstanta(
                i.fold(vec![], |mut v,x|{
                    let xi = x.into_inner();
                    v.push((
                        xi.clone().fold(vec![], |mut vi, p|{
                            if p.as_rule()==ident{
                                vi.push(p.as_str().to_string());
                            }
                            return vi;
                        }),
                        xi.last().unwrap().as_str().to_string()
                    ));
                    v
                })
            ),
            param_io => ParamIO(s.starts_with("in"), s.ends_with("out")),
            parameter => {

                let last = i.clone().last().unwrap();
                let idents = last.clone().into_inner().filter_map(|x|{
                    if x.as_rule()!=ident{
                        return None;
                    }
                    Some(x.as_str().to_string())
                }).collect();
                
                let outtype = Box::new(last.into_inner().last().unwrap().into());
                let j = i.next().unwrap();
                let js = j.as_str().to_string();
                if j.as_rule()==param_io{
                    return Parameter(
                        js.starts_with("in"),
                        js.ends_with("out"),
                        idents,
                        outtype
                    )

                }
                return Parameter(
                    false,
                    false,
                    idents,
                    outtype
                )
            },
            expr => todo!(),
            // infix => todo!(),
            // add => todo!(),
            // sub => todo!(),
            // mul => todo!(),
            // div => todo!(),
            // idv => todo!(),
            // neq => todo!(),
            // equ => todo!(),
            // pow => todo!(),
            // lt => todo!(),
            // le => todo!(),
            // gt => todo!(),
            // ge => todo!(),
            // prefix => todo!(),
            // neg => todo!(),
            // postfix => todo!(),
            // fac => todo!(),
            // primary => todo!(),
            algoritma => Algoritma(
                i.map(|x|x.into()).collect()
            ),
            procedure_def => ProcDef(
                i.next().unwrap().as_str().to_string(), 
                i.clone().filter_map(|p|{
                    if p.as_rule()==parameter{
                        if let Parameter(a , b , c , d )=p.into(){
                            return Some((a,b,c,d))
                        }
                    }
                    None
                }).collect(), 
                {
                    let alg = i.clone().last().unwrap().into();
                    let kon = i.find(|x|x.as_rule()==konstanta)
                        .map(|x|x.into())
                        .unwrap_or(EmptyStatement);
                    let kam = i.find(|x|x.as_rule()==kamus)
                        .map(|x|x.into())
                        .unwrap_or(EmptyStatement);
                    Box::new((kon,kam,alg))
                }
            ),
            function_def => FuncDef(
                i.next().unwrap().as_str().to_string(), 
                i.clone().filter_map(|p|{
                    if p.as_rule()==parameter{
                        if let Parameter(a , b , c , d )=p.into(){
                            return Some((a,b,c,d))
                        }
                    }
                    None
                }).collect(), 
                i.clone().find(|x|{
                    match x.as_rule(){
                        primitives|pointer_type|user_type=>{
                            true
                        }
                        _ => false
                    }
                }).map(|x|x.as_str().to_string()).unwrap_or("ERROR_NAME".to_string()), 
                {
                    let alg = i.clone().last().unwrap().into();
                    let kon = i.find(|x|x.as_rule()==konstanta)
                        .map(|x|x.into())
                        .unwrap_or(EmptyStatement);
                    let kam = i.find(|x|x.as_rule()==kamus)
                        .map(|x|x.into())
                        .unwrap_or(EmptyStatement);
                    Box::new((kon,kam,alg))
                }
            ),
            typealias => {
                if let TypeField(a , b ) = i.last().unwrap().into(){
                    return TypeAlias(a, b)
                }
                unreachable!()
            },
            retstmt => RetStmt(Box::new(i.last().unwrap().into())),
            ifstmt => {
                 
                let last_stmt: Option<Box<AST>> = if i.clone().count()%2!=0{Some(Box::new(i.clone().last().unwrap().into()))}else{
                    None
                };
                use itertools::Itertools;
                let ifthens: Vec<(AST,AST)> = (&i.chunks(2)).into_iter().fold(Vec::<(AST,AST)>::new(), |mut v,mut x|{
                    let if_expr:AST = x.next().unwrap().into();
                    let maybe_then_stmt: Option<AST> =x.next().map(|x|x.into());
                    if let Some(then_stmt) = maybe_then_stmt{
                        v.push((if_expr,then_stmt));
                    }
                    v
                });
                IfStmt(ifthens, last_stmt)
            },
            whlstmt => todo!(),
            mainprogram => todo!(),
            program => todo!(),
            user_type => todo!(),
            _ => unreachable!(),
        }
    }
}

