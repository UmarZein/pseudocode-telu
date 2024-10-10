

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
            .op(Op::infix(mul, Left) | Op::infix(div, Left) | Op::infix(idv, Left) | Op::infix(mdl, Left))
            .op(Op::infix(pow, Left))
            .op(Op::infix(lor, Left))
            .op(Op::infix(land, Left))
            .op(Op::prefix(neg))
            .op(Op::prefix(not))
    };
}


#[derive(Debug, Clone)]
pub enum Expr{
    Equ(Box<(Expr, Expr)>),
    Neq(Box<(Expr, Expr)>),
    Land(Box<(Expr, Expr)>),
    Lor(Box<(Expr, Expr)>),
    Gt(Box<(Expr, Expr)>),
    Lt(Box<(Expr, Expr)>),
    Ge(Box<(Expr, Expr)>),
    Le(Box<(Expr, Expr)>),
    Add(Box<(Expr, Expr)>),
    Sub(Box<(Expr, Expr)>),
    Mul(Box<(Expr, Expr)>),
    Div(Box<(Expr, Expr)>),
    Idv(Box<(Expr, Expr)>),
    Mod(Box<(Expr, Expr)>),
    Pow(Box<(Expr, Expr)>),
    Neg(Box<Expr>),
    Not(Box<Expr>),
    Ident(String),
    /// `{expr}.member`
    Pathident(Box<Expr>, String), // {expr}.member
    //PathidentPtr(String, Box<Expr>), // 
    /// `this(thing)`
    /// Round Args may be interpreted as function call (i.e., funcName(args)) or gep (i.e., ptrInstance->member)
    RoundArgs(Box<Expr>, Vec<Expr>), // {expr}({expr, }*)
    /// `this[thing]`
    /// `ptr[index]`
    SquareArgs(Box<Expr>, Vec<Expr>), // {expr}[{expr, }*]
    Int(i64),
    Float(f64),
    Bool(bool),
    Char(u8),
    Str(Vec<u8>),
    Nil,
}

pub fn simple_expr_str(e: &Expr) -> String{
    use Expr as E;
    match e{
        E::Equ(_) => format!("Equ"),
        E::Neq(_) => format!("Neq"),
        E::Gt(_) => format!("Gt"),
        E::Lt(_) => format!("Lt"),
        E::Ge(_) => format!("Ge"),
        E::Le(_) => format!("Le"),
        E::Add(_) => format!("Add"),
        E::Sub(_) => format!("Sub"),
        E::Mul(_) => format!("Mul"),
        E::Div(_) => format!("Div"),
        E::Idv(_) => format!("Idv"),
        E::Mod(_) => format!("Mod"),
        E::Pow(_) => format!("Pow"),
        E::Neg(_) => format!("Neg"),
        E::Not(_) => format!("Not"),
        E::Pathident(_, s) => format!("Pathident .{s}"),
        E::RoundArgs(_, v) => format!("Call with {} args",v.len()),
        E::SquareArgs(_, v) => format!("Call with {} args",v.len()),
        E::Int(a) => format!("Int: {a}"),
        E::Float(a) => format!("Float: {a}"),
        E::Bool(a) => format!("Bool: {a}"),
        E::Char(a) => format!("Char: {}",*a as u8),
        E::Str(a) => format!("Str: {}",String::from_utf8(a.clone()).unwrap()),
        E::Nil => format!("Nil"),
        E::Land(_) => format!("Band"),
        E::Lor(_) =>  format!("Bor"),
        E::Ident(v) => format!("{v}"),
        //E::PathidentPtr(s, _) => format!("{s}"),
    }
}

impl Expr{
    pub fn is_nil(&self)->bool{
        match self{
            Self::Nil => true,
            _ => false
        }
    }
}


pub fn parse_literal(pair: Pair<Rule>) -> Expr {
    use Rule as R;
    use Expr as E;
    match pair.as_rule(){
        R::float => {
            E::Float(pair.as_str().parse().unwrap())
        },
        R::uint => {
            E::Int(pair.as_str().parse().unwrap())
        },
        R::int => {
            E::Int(pair.as_str().parse().unwrap())
        },
        R::bool => {
            E::Bool(pair.as_str().parse().unwrap())
        },
        R::char => {
            E::Char(pair.as_str().chars().next().unwrap() as u8)
        },
        R::string => {
            E::Str(pair.as_str().chars().map(|x|x as u8).collect())
        },
        R::nil => {
            E::Nil
        },
        other => unreachable!("{other} is not `literal`, or it is not implemented.")
    }
}

pub fn parse_expr(pairs: Pairs<Rule>) -> Expr {
    use Rule as R;
    use Expr as E;
    PRATT_PARSER
        .map_primary(|primary| match primary.as_rule() {
            R::float => {
                E::Float(primary.as_str().parse().unwrap())
            },
            R::uint => {
                E::Int(primary.as_str().parse().unwrap())
            },
            R::int => {
                E::Int(primary.as_str().parse().unwrap())
            },
            R::bool => {
                E::Bool(primary.as_str().parse().unwrap())
            },
            R::char => {
                E::Char(primary.as_str().chars().next().unwrap() as u8)
            },
            R::string => {
                E::Str(primary.as_str().chars().map(|x|x as u8).collect())
            },
            R::nil => {
                E::Nil
            },
            R::ident => {
                E::Ident(primary.as_str().to_string())
            }
            R::linear_expr => {
                let mut i = primary.into_inner();
                let first = i.next().unwrap();
                let mut expr = match first.as_rule(){
                    R::expr => parse_expr(first.into_inner()),
                    R::ident => E::Ident(first.as_str().to_string()),

                    // TODO: this, the statement hereunder, is not enforced correctly...
                    // at this point, 'other' should ONLY be literal
                    other => {
                        parse_literal(first)
                    }
                }; 
                while let Some(pair) = i.next(){
                    expr = match pair.as_rule(){
                        R::dot_arg => E::Pathident(Box::new(expr), pair.into_inner().next().unwrap().as_str().to_string()),
                        R::square_brackets_args => todo!("square bracket args (e.g.: this[thing]) is not yet implemented"),
                        R::round_brackets_args => {
                            let j = pair.into_inner();
                            E::RoundArgs(Box::new(expr), j.map(|x|parse_expr(x.into_inner())).collect())
                        },

                        other => unimplemented!("{other} is incorrect in this stage: parsing linear expression after the first element")
                    }
                }
                return expr;
                
            }
            R::expr => {
                parse_expr(primary.into_inner())
            },
            case => unreachable!("case is {case}")
        })
        .map_prefix(|op, rhs| match op.as_rule() {
            R::neg => {E::Neg(Box::new(rhs))}
            R::not => {E::Not(Box::new(rhs))}
            _ => unreachable!()
        })
        // .map_postfix(|lhs, op| match op.as_rule() {
        //     _          => unreachable!(),
        // })
        .map_infix(|lhs, op, rhs| match op.as_rule() {
            R::equ => E::Equ(Box::new((lhs,rhs))),
            R::neq => E::Neq(Box::new((lhs,rhs))),
            R::gt =>  E::Gt(Box::new((lhs,rhs))),
            R::lt =>  E::Lt(Box::new((lhs,rhs))),
            R::ge =>  E::Ge(Box::new((lhs,rhs))),
            R::le =>  E::Le(Box::new((lhs,rhs))),
            R::add => E::Add(Box::new((lhs,rhs))),
            R::sub => E::Sub(Box::new((lhs,rhs))),
            R::mul => E::Mul(Box::new((lhs,rhs))),
            R::div => E::Div(Box::new((lhs,rhs))),
            R::idv => E::Idv(Box::new((lhs,rhs))),
            R::mdl => E::Mod(Box::new((lhs,rhs))),
            R::pow => E::Pow(Box::new((lhs,rhs))),
            R::lor => E::Lor(Box::new((lhs,rhs))),
            R::land => E::Land(Box::new((lhs,rhs))),
            _          => unreachable!(),
        })
        .parse(pairs)
}

// enum AST{
//     EmptyStatement,
//     Ident(String),
// 
//     Int(i64),
//     Real(f64),
//     Bool(bool),
//     Primitive(String),
//     Pointer(Box<AST>),
//     ConstTypeField(String, Box<AST>, Box<AST>),
//     TypeField(Vec<String>,Box<AST>),
//     Kamus(Vec<(Vec<String>,String)>),
//     Assignment(String,Box<AST>),
//     Konstanta(Vec<(Vec<String>,String)>),
//     UserType(String),
//     Expr(Box<AST>),
//     Add(Vec<AST>),
//     Mul(Vec<AST>),
//     Sub(Box<(AST,AST)>),
//     Div(Box<(AST,AST)>),
//     Idv(Box<(AST,AST)>),
//     Neq(Box<(AST,AST)>),
//     Equ(Box<(AST,AST)>),
//     Pow(Box<(AST,AST)>),
//     Le(Box<(AST,AST)>),
//     Ge(Box<(AST,AST)>),
//     Lt(Box<(AST,AST)>),
//     Gt(Box<(AST,AST)>),
//     Neg(Box<AST>),
//     Fac(Box<AST>),
//     ParamIO(bool,bool),
//     Parameter(bool,bool,Vec<String>,Box<AST>),
//     Algoritma(Vec<AST>),
//     ProcDef(
//         String,
//         Vec<(bool,bool,Vec<String>,Box<AST>)>,
//         Box<(AST,AST,AST)>, // konstant, kamus, algoritma
//     ),
//     FuncDef(
//         String,
//         Vec<(bool,bool,Vec<String>,Box<AST>)>,
//         String,
//         Box<(AST,AST,AST)>, // konstant, kamus, algoritma
//     ),
//     TypeDef(
//         String,
//         Vec<(Vec<String>,String)>,
//     ),
//     TypeAlias(Vec<String>, Box<AST>),
//     RetStmt(Box<AST>),
//     IfStmt(
//         Vec<(AST,AST)>,//if x then y + else if x then y
//         Option<Box<AST>>, //else y
//     ),
//     WhlStmt(
//         Box<AST>,//while expr
//         Vec<AST>,//do stmt*
//     ),
//     MainProg(
//         String,
//         Box<(AST,AST,AST)>, // konstant, kamus, algoritma
//     )
// }
// 
// impl Into<AST> for Pair<'_, Rule>{
//     fn into(self) -> AST {
//         use Rule::*;
//         use AST::*;
//         let s = self.as_str().to_string();
//         let mut i = self.clone().into_inner();
//         match self.as_rule() {
//             ident => Ident(s),
//             uint|int => Int(s.parse().unwrap()),
//             float => Real(s.parse().unwrap()),
//             bool => Bool(s.parse().unwrap()),
//             primitives => Primitive(s),
//             pointer_type => Pointer(Box::new(i.next().unwrap().into())),
//             type_field => TypeField(
//                 i.clone().fold(vec![], |mut v,p|{
//                     if p.as_rule()==ident{
//                         v.push(p.as_str().to_string());
//                     }
//                     return v;
//                 }),
//                 Box::new(i.last().unwrap().into())
//             ),
//             const_type_field => ConstTypeField(
//                 i.next().unwrap().as_str().to_string(),
//                 Box::new({ 
//                     let j = i.next().unwrap();
//                     match j.as_rule(){
//                         primitives => Primitive(j.as_str().to_string()),
//                         pointer_type => j.into(),
//                         user_type => UserType(j.as_str().to_string()),
//                         _ => unreachable!(),
//                     }
//                 }),
//                 Box::new({ 
//                     let j = i.next().unwrap();
//                     let jstr = j.as_str();
//                     match j.as_rule(){
//                         float=>Real(jstr.parse().unwrap()),
//                         uint|int=>Int(jstr.parse().unwrap()),
//                         bool=>Bool(jstr.parse().unwrap()),
//                         char=>unimplemented!(),
//                         _ => unreachable!(),
//                     }
//                 }),
//             ),
//             type_def => TypeDef(
//                 i.next().unwrap().to_string(), 
//                 i.fold(vec![], |mut v,x|{
//                     let xi = x.into_inner();
//                     v.push((
//                         xi.clone().fold(vec![], |mut vi, p|{
//                             if p.as_rule()==ident{
//                                 vi.push(p.as_str().to_string());
//                             }
//                             return vi;
//                         }),
//                         xi.last().unwrap().as_str().to_string()
//                     ));
//                     v
//                 })
//             ),
//             kamus => Kamus(
//                 i.fold(vec![], |mut v,x|{
//                     let xi = x.into_inner();
//                     v.push((
//                         xi.clone().fold(vec![], |mut vi, p|{
//                             if p.as_rule()==ident{
//                                 vi.push(p.as_str().to_string());
//                             }
//                             return vi;
//                         }),
//                         xi.last().unwrap().as_str().to_string()
//                     ));
//                     v
//                 })
//             ),
//             asgnstmt => Assignment(
//                 i.clone().fold((String::new(),false), |(mut s, mut b), x|{
//                     if x.as_rule()==ident{
//                         if b{
//                             s+=".";
//                         }
//                         b=true;
//                         s+=x.as_str();
//                     }
//                     (s, b)
//                 }).0, 
//                 Box::new(i.next().unwrap().into())
//             ),
//             konstanta => Konstanta(
//                 i.fold(vec![], |mut v,x|{
//                     let xi = x.into_inner();
//                     v.push((
//                         xi.clone().fold(vec![], |mut vi, p|{
//                             if p.as_rule()==ident{
//                                 vi.push(p.as_str().to_string());
//                             }
//                             return vi;
//                         }),
//                         xi.last().unwrap().as_str().to_string()
//                     ));
//                     v
//                 })
//             ),
//             param_io => ParamIO(s.starts_with("in"), s.ends_with("out")),
//             parameter => {
// 
//                 let last = i.clone().last().unwrap();
//                 let idents = last.clone().into_inner().filter_map(|x|{
//                     if x.as_rule()!=ident{
//                         return None;
//                     }
//                     Some(x.as_str().to_string())
//                 }).collect();
//                 
//                 let outtype = Box::new(last.into_inner().last().unwrap().into());
//                 let j = i.next().unwrap();
//                 let js = j.as_str().to_string();
//                 if j.as_rule()==param_io{
//                     return Parameter(
//                         js.starts_with("in"),
//                         js.ends_with("out"),
//                         idents,
//                         outtype
//                     )
// 
//                 }
//                 return Parameter(
//                     false,
//                     false,
//                     idents,
//                     outtype
//                 )
//             },
//             expr => todo!(),
//             algoritma => Algoritma(
//                 i.map(|x|x.into()).collect()
//             ),
//             procedure_def => ProcDef(
//                 i.next().unwrap().as_str().to_string(), 
//                 i.clone().filter_map(|p|{
//                     if p.as_rule()==parameter{
//                         if let Parameter(a , b , c , d )=p.into(){
//                             return Some((a,b,c,d))
//                         }
//                     }
//                     None
//                 }).collect(), 
//                 {
//                     let alg = i.clone().last().unwrap().into();
//                     let kon = i.find(|x|x.as_rule()==konstanta)
//                         .map(|x|x.into())
//                         .unwrap_or(EmptyStatement);
//                     let kam = i.find(|x|x.as_rule()==kamus)
//                         .map(|x|x.into())
//                         .unwrap_or(EmptyStatement);
//                     Box::new((kon,kam,alg))
//                 }
//             ),
//             function_def => FuncDef(
//                 i.next().unwrap().as_str().to_string(), 
//                 i.clone().filter_map(|p|{
//                     if p.as_rule()==parameter{
//                         if let Parameter(a , b , c , d )=p.into(){
//                             return Some((a,b,c,d))
//                         }
//                     }
//                     None
//                 }).collect(), 
//                 i.clone().find(|x|{
//                     match x.as_rule(){
//                         primitives|pointer_type|user_type=>{
//                             true
//                         }
//                         _ => false
//                     }
//                 }).map(|x|x.as_str().to_string()).unwrap_or("ERROR_NAME".to_string()), 
//                 {
//                     let alg = i.clone().last().unwrap().into();
//                     let kon = i.find(|x|x.as_rule()==konstanta)
//                         .map(|x|x.into())
//                         .unwrap_or(EmptyStatement);
//                     let kam = i.find(|x|x.as_rule()==kamus)
//                         .map(|x|x.into())
//                         .unwrap_or(EmptyStatement);
//                     Box::new((kon,kam,alg))
//                 }
//             ),
//             typealias => {
//                 if let TypeField(a , b ) = i.last().unwrap().into(){
//                     return TypeAlias(a, b)
//                 }
//                 unreachable!()
//             },
//             retstmt => RetStmt(Box::new(i.last().unwrap().into())),
//             ifstmt => {
//                  
//                 let last_stmt: Option<Box<AST>> = if i.clone().count()%2!=0{Some(Box::new(i.clone().last().unwrap().into()))}else{
//                     None
//                 };
//                 use itertools::Itertools;
//                 let ifthens: Vec<(AST,AST)> = (&i.chunks(2)).into_iter().fold(Vec::<(AST,AST)>::new(), |mut v,mut x|{
//                     let if_expr:AST = x.next().unwrap().into();
//                     let maybe_then_stmt: Option<AST> =x.next().map(|x|x.into());
//                     if let Some(then_stmt) = maybe_then_stmt{
//                         v.push((if_expr,then_stmt));
//                     }
//                     v
//                 });
//                 IfStmt(ifthens, last_stmt)
//             },
//             whlstmt => todo!(),
//             mainprogram => todo!(),
//             program => todo!(),
//             user_type => todo!(),
//             _ => unreachable!(),
//         }
//     }
// }
// 
