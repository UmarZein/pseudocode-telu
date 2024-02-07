use inkwell::context::Context;
use inkwell::module::{Module, Linkage};
use inkwell::passes::PassManager;
use inkwell::{OptimizationLevel, AddressSpace};
use inkwell::{
    passes::PassBuilderOptions,
    targets::{CodeModel, InitializationConfig, RelocMode, Target, TargetMachine},
};

use inkwell::builder::Builder;
use inkwell::types::{BasicMetadataTypeEnum, FunctionType, BasicTypeEnum, BasicType};
use inkwell::values::{BasicMetadataValueEnum, BasicValueEnum, FloatValue, FunctionValue, PointerValue, BasicValue};
use inkwell::FloatPredicate;

use pest::Parser;
use pest::iterators::{Pairs, Pair};
use itertools::Itertools;

use std::collections::HashMap;
use std::hint::unreachable_unchecked;

use crate::parse::{PRATT_PARSER, FCParser, Rule};

#[derive(Debug,Clone)]
pub struct Codegen<'a, 'ctx> {
    pub context: &'ctx Context,
    pub module: &'a Module<'ctx>,
    pub builder: &'a Builder<'ctx>,
    // pub functions: &'a mut HashMap<&'a str, FunctionValue<'ctx>>,
    // pub variables: &'a mut HashMap<&'a str, PointerValue<'ctx>>,
    pub program_name: String,
}

impl<'a, 'ctx> Codegen<'a, 'ctx> {
    fn add_function(&mut self, name: &'ctx str, ftype: FunctionType<'ctx>, linkage: Option<Linkage>)->FunctionValue<'ctx>{
        let f = self.module.add_function(name, ftype, linkage);
        //self.functions.insert(name, f);    
        return f;

    }
    fn pair_to_type(&self, pair: Pair<Rule>) -> BasicTypeEnum{
        match pair.as_rule(){
            Rule::integer_type => self.context.i64_type().into(),
            Rule::real_type => self.context.f64_type().into(),
            Rule::bool_type => self.context.bool_type().into(),
            Rule::pointer_type => self.pair_to_type(pair.into_inner().next().unwrap()).ptr_type(AddressSpace::default()).into(),
            _ => unreachable!()
        }
    }
    fn pair_to_value(&self, pair:Pair<Rule>) -> BasicValueEnum{
        match pair.as_rule(){
            Rule::float => self.context.f64_type().const_float(pair.into_inner().next().unwrap().as_str().parse().unwrap()).into(),
            Rule::int => self.context.i64_type().const_int(
                pair.into_inner().next().unwrap().as_str().parse::<i64>().unwrap() as u64, false).into(),
            Rule::bool => self.context.bool_type().const_int(
                pair.into_inner().next().unwrap().as_str().parse::<bool>().unwrap() as u64, false).into(),
            _ => unreachable!(),
        }
    }
    pub fn compile_program(&mut self, source_filename: &str){
        self.add_printf();
        let code = std::fs::read_to_string(source_filename).unwrap();
        let parsed = FCParser::parse(Rule::program, &code).unwrap();
        let _ = parsed.map(|p|self.compile_pest_output(p)).collect::<Vec<()>>();
        todo!()
    }
    
    fn process_parameter(&self, pair:Pair<Rule>)->(bool,bool,Vec<String>,BasicTypeEnum){
        if pair.as_rule()!=Rule::parameter{
            unreachable!()
        }
        let mut i = pair.into_inner();
        let mut invar = false;
        let mut outvar = false;
        let mut vars: Vec<_> = vec![];
        let mut partype = self.context.i8_type().as_basic_type_enum();
        while let Some(x) = i.next(){
            match x.as_rule(){
                Rule::param_io => {
                    let s = x.as_str();
                    invar=s.starts_with("in");
                    outvar=s.ends_with("out");
                },
                Rule::type_field => {
                    for type_decl in x.into_inner(){
                        let mut k = type_decl.into_inner().rev();
                        partype = self.pair_to_type(k.next().unwrap());
                        let var_ptrs: Vec<_> = k.map(|x|x.as_str().to_string()).collect();
                        vars.extend(var_ptrs);
                    }
                },
                _ => unreachable!()
            }
        }
        return (invar,outvar,vars,partype)
    }
    fn compile_pest_output(&mut self, pair: Pair<Rule>){
        use Rule as R;
        match pair.as_rule(){
            R::COMMENT => (),
            R::WHITESPACE => (),
            R::procedure_def => todo!(),
            R::function_def => {
                let mut i = pair.into_inner();
                let name = i.next().unwrap().as_str();//
                let mut intype_blueprint: Vec<(bool,bool,String,BasicTypeEnum)> = vec![];
                let mut intypes: Vec<BasicMetadataTypeEnum> = vec![];
                let mut outtype = self.context.i8_type().as_basic_type_enum();
                let parameters: Vec<_> = i.clone().filter(|x|x.as_rule()==R::parameter)
                    .map(|x|self.process_parameter(x)).collect();
                for (inv,outv, vars, typ) in parameters{
                    for var in vars{
                        intype_blueprint.push((inv,outv,var.clone(),typ));
                        intypes.push(typ.into());
                    }
                }
                let outtyp = self.pair_to_type(i.clone().find(|x|x.as_rule()==R::typename).unwrap());
                let functype = outtyp.fn_type(&intypes, false);
                let func = self.module.add_function(name, functype, None);
                self.context.append_basic_block(func, "entry");
                while let Some(x) = i.next(){
                    self.compile_pest_output(x);
                }

            },
            R::typealias => todo!(),
            R::mainprogram => {
                let main_type = self.context.i32_type().fn_type(&[], false);
                let main_fn = self.add_function("main", main_type, None);
                let mainf_entry = self.context.append_basic_block(main_fn, "mainf_entry");
                self.builder.position_at_end(mainf_entry);
                let mut i = pair.into_inner(); 
                self.program_name = i.next().unwrap().as_str().to_string();
                let _ = i.map(|p|self.compile_pest_output(p)).collect::<Vec<()>>();
            },
            R::konstanta => {
                let j = pair.into_inner();
                //ctf = const type field
                for ctf in j{
                    let mut k = ctf.into_inner();
                    let ident = k.next().unwrap().as_str();
                    let ty = self.pair_to_type(k.next().unwrap());
                    let var_ptr = self.builder.build_alloca(ty, ident).unwrap();
                    let val = k.next().unwrap();
                    
                    self.builder.build_store(var_ptr.into(), self.pair_to_value(val)).unwrap();
                }
            },
            R::kamus => {
                let j = pair.into_inner();
                for type_decl in j{
                    let mut k = type_decl.into_inner().rev();
                    let ty = self.pair_to_type(k.next().unwrap());
                    let var_ptrs: Vec<_> = k.map(|x|self.builder.build_alloca(ty, x.as_str()).unwrap()).collect();
                }

            },
            R::algoritma => {
               let _ = pair.into_inner().map(|p|self.compile_pest_output(p)).collect::<Vec<()>>();
            }
            _ => unreachable!()
        }
    }
    pub fn add_printf(&mut self){
        let int32 = self.context.i32_type();
        let int8ptr = self.context.i8_type().ptr_type(AddressSpace::default());
        let printf_types = int32.fn_type(&[int8ptr.into()], true);
        self.add_function("printf", printf_types, Some(Linkage::External));
    }
}
