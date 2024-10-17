use log::{debug, error, info, log_enabled, warn, Level};

use inkwell::context::Context;
use inkwell::intrinsics::Intrinsic;
use inkwell::llvm_sys::prelude::LLVMValueRef;
use inkwell::module::{Module, Linkage};
use inkwell::passes::PassManager;
use inkwell::{OptimizationLevel, AddressSpace};
use inkwell::{
    passes::PassBuilderOptions,
    targets::{CodeModel, InitializationConfig, RelocMode, Target, TargetMachine},
};

use inkwell::builder::Builder;
use inkwell::types::{BasicMetadataTypeEnum, FunctionType, BasicTypeEnum, BasicType, PointerType, StructType};
use inkwell::values::{BasicMetadataValueEnum, BasicValueEnum, FloatValue, FunctionValue, StructValue, PointerValue, BasicValue, InstructionOpcode, AsValueRef, InstructionValue};
use inkwell::FloatPredicate;

use pest::Parser;
use pest::iterators::{Pairs, Pair};
use itertools::Itertools;

use std::collections::{HashMap, VecDeque};
use std::hint::unreachable_unchecked;

use crate::parse::{PRATT_PARSER, FCParser, Rule, parse_expr, Expr, simple_expr_str};
use crate::{print_pair, print_pairs};
use super::{Type, Codegen};


impl<'a, 'ctx> Codegen<'a, 'ctx> where 'ctx:'a{
    fn add_function(&self, name: &'ctx str, ftype: FunctionType<'ctx>, linkage: Option<Linkage>)->FunctionValue<'ctx>{
        let f = self.module.add_function(name, ftype, linkage);
        //self.functions.insert(name, f);    
        return f;
    }
    
    pub(crate) fn find_function(&self, name: &str, linkage: Option<Linkage>, itype: &[Type]) -> (FunctionValue<'ctx>,Type,Vec<(bool,bool,String,Type)>){
        info!("trying to find function {name} with {} argtypes",itype.len());
        info!("argtypes: {itype:#?}");
        let mut funcs = self.functions.get(name).unwrap_or_else(||panic!("{name} not found!")).clone();
        funcs.sort_by(|a, b|{
            b.0.get_params().len().cmp(&a.0.get_params().len())
        });
        if name=="input"{
            info!("printing funcs...");
            info!("{funcs:#?}");
        }
        let func = funcs.iter().find(|&e|{
            let fargtypes: Vec<_> = e.2.iter().map(|(a,b,c,d)|d.clone()).collect();
            if fargtypes.len()>itype.len(){ return false }
            if (!e.0.get_type().is_var_arg()) && fargtypes.len()!=itype.len(){ return false }
            
            // match all types f(int,int)==f(int,int)
            // but also, we want voidptr polymorphism...
            // such that f(*void)==f(*float)
            return fargtypes.iter().zip(&itype[..fargtypes.len()])
                .all(|(candidate,key)|{
                    info!("checking {candidate:?} and {key:?}");
                    match candidate.clone(){
                        Type::VoidPtr => {
                            match key{
                                Type::Ptr(_) => true,
                                _ => candidate==key,
                            }
                        },
                        _ => candidate==key,
                    }
                });
        }).expect(&format!("could not find function named {name} with {} arguments",itype.len()));
        func.clone()
    }
    #[inline]
    pub(crate) fn pair_to_type(context: &'ctx Context, struct_defs: &HashMap<String, (StructType<'ctx>, Vec<(String,Type)>)>,
        aliases: &HashMap<String, Type>,
        pair: Pair<Rule>) -> Type{
        match pair.as_rule(){
            Rule::integer_type => Type::Int,
            Rule::real_type => Type::Float,
            Rule::bool_type => Type::Bool,
            Rule::char_type => Type::Char,
            Rule::string_type => Type::String,
            Rule::void_type => Type::Void,
            Rule::array_type => {
                let mut i = pair.into_inner();
                let mut array_dim = i.next().unwrap().into_inner();
                let one_indexed = array_dim.next().unwrap().as_str()=="1";
                let size = array_dim.next().unwrap().as_str().parse().unwrap();
                let inner_type = Self::pair_to_type(context, struct_defs, aliases, i.next().unwrap());
                Type::Array(one_indexed, size, Box::new(inner_type))
            },
            Rule::pointer_type => Type::Ptr(Box::new(Self::pair_to_type(context, struct_defs, aliases, pair.into_inner().next().unwrap()))),
            Rule::user_type => {
                let struct_name = pair.as_str().to_string();
                if let Some((stype, fields)) = struct_defs.get(&struct_name){
                    Type::StructType(struct_name, fields.clone())
                } else if let Some(typ) = aliases.get(&struct_name) {
                    typ.clone().translate_opaque(struct_defs, aliases) 
                } else {
                    info!("struct_defs:\n{struct_defs:#?}");
                    panic!("{struct_name} not found in struct_defs");
                }
            },
            
            _ => unreachable!("pair = {pair:#?}")
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
        let code = std::fs::read_to_string(source_filename).unwrap_or_else(|e|panic!("stdio error: {e}\nfilename = {source_filename}"));
        let parsed = FCParser::parse(Rule::program, &code).unwrap();
        info!("done parsing {source_filename}");
        println!("printing pairs...");
        print_pairs(parsed.clone(), 0);
        println!("done printing pairs...");
        info!("done printing pairs");
        let main_fn = self.register_func_unnamed_params("main", Type::Int, vec![]);
        self.context.append_basic_block(main_fn, "mainf_entry");
        //TODO uncomment this: self.add_alloc();
        self.add_printf();
        self.add_scanf();
        self.add_output();
        self.add_time();
        self.add_rand();
        // self.add_powi();
        // self.add_powf();
        
        println!("declaring aliases");
        let _ = parsed.clone().map(|p|self.declare_aliases(p)).collect::<Vec<()>>();
        println!("declaring structs");
        let _ = parsed.clone().map(|p|self.declare_structs(p)).collect::<Vec<()>>();
        println!("declaring funcs");
        let _ = parsed.clone().map(|p|self.declare_funcs(p)).collect::<Vec<()>>();
        info!("done declaring functions");
        debug!("after debugging, locals[{}]={:#?}",self.locals.len(),self.locals);
        println!("compiling pest output");
        let _ = parsed.map(|p|self.compile_pest_output(p)).collect::<Vec<()>>();
    }
    
    fn process_parameter(context: &'ctx Context, struct_defs: &HashMap<String, (StructType<'ctx>, Vec<(String,Type)>)>,
        aliases: &HashMap<String, Type>,
        pair:Pair<Rule>)->(bool,bool,Vec<String>,Type){
        if pair.as_rule()!=Rule::parameter{
            unreachable!()
        }
        let mut i = pair.into_inner();
        let mut invar = false;
        let mut outvar = false;
        let mut vars: Vec<_> = vec![];
        let mut partype = Type::Int; // WARNING: Int as default type...good idea?
        while let Some(x) = i.next(){
            match x.as_rule(){
                Rule::param_io => {
                    let s = x.as_str();
                    invar=s.starts_with("in");
                    outvar=s.ends_with("out");
                },
                Rule::type_field => {
                    let mut k = x.into_inner().rev();
                    partype = Self::pair_to_type(&context, struct_defs, aliases, k.next().unwrap());
                    let var_ptrs: Vec<_> = k.map(|j|j.as_str().to_string()).collect();
                    vars.extend(var_ptrs);
                },
                _ => unreachable!()
            }
        }
        return (invar,outvar,vars,partype)
    }
    fn declare_funcs(&mut self, pair: Pair<Rule>){
        //println!("declare_funcs({pair:?})");
        use Rule as R;
        match pair.as_rule(){
            R::typealias => return,
            R::procedure_def => {
                let mut i = pair.into_inner();
                let name = i.next().unwrap().as_str();//
                let mut intype_blueprint: Vec<(bool,bool,String,Type)> = vec![];
                let mut outtype = Type::Int;
                let parameters: Vec<_> = i.clone().filter(|x|x.as_rule()==R::parameter)
                    .map(|x|Self::process_parameter(&self.context,self.struct_defs, self.aliases,x)).collect();
                for (inv,outv, vars, typ) in &parameters{
                    for var in vars{
                        intype_blueprint.push((*inv,*outv,var.clone(),typ.clone()));
                    }
                }
                let func = self.register_proc(name, outtype, intype_blueprint);
                let funcblock = self.context.append_basic_block(func, "entry");
                self.builder.position_at_end(funcblock);

                let mut parami = 0;
                for (inv, outv, vars, typ) in &parameters{
                    if *outv{
                        for var in vars.iter().rev(){
                            let p = func.get_nth_param(parami).unwrap();
                            self.locals.insert((func,var.clone()), (p.into_pointer_value(),typ.clone()));
                        }
                    }
                    else{
                        for var in vars.iter().rev(){
                            let p = func.get_nth_param(parami).unwrap();
                            let ptr = self.builder.build_alloca(typ.into_bte(self.context, self.aliases, self.struct_defs), &var).unwrap();
                            self.locals.insert((func,var.clone()), (ptr,typ.clone()));
                            let load_instr = self.builder.build_store(ptr, p).unwrap();
                            //load_instr.set_alignment(typ.correct_alignment()).unwrap();
                        }
                    }
                    parami+=1;
                }


                while let Some(x) = i.next(){
                    match x.as_rule(){
                        R::konstanta | R::kamus => self.declare_funcs(x),
                        _ => continue
                    }
                }
            },
            R::function_def => {
                let mut i = pair.into_inner();
                let name = i.next().unwrap().as_str();//
                assert!(name!="main");
                let mut intype_blueprint: Vec<(String,Type)> = vec![];
                let mut intypes: Vec<Type> = vec![];
                let mut outtype = self.context.i8_type().as_basic_type_enum();
                let parameters: Vec<_> = i.clone().filter(|x|x.as_rule()==R::parameter)
                    .map(|x|Self::process_parameter(&self.context,self.struct_defs, self.aliases,x)).collect();
                for (inv,outv, vars, typ) in parameters.clone(){
                    for var in vars{
                        intype_blueprint.push((var.clone(),typ.clone()));
                        intypes.push(typ.clone().into());
                    }
                }


                let typename = i.clone().find(|x|{
                    match x.as_rule(){
                        R::integer_type|R::real_type|R::bool_type|R::string_type
                        |R::pointer_type|R::char_type|R::user_type|R::void_type|R::array_type => true,
                        _ => false
                    }
                }).unwrap();
                let outtyp = Self::pair_to_type(self.context,self.struct_defs, self.aliases, typename);
                let func = self.register_func(name, outtyp, intype_blueprint);
                //
                let funcblock = self.context.append_basic_block(func, "entry");
                self.builder.position_at_end(funcblock);
                let mut parami = 0;
                for (inv,outv, vars, typ) in parameters.iter(){
                    for var in vars.iter().rev(){
                        let p = func.get_nth_param(parami).unwrap();
                        let ptr = self.builder.build_alloca(typ.into_bte(self.context, self.aliases, self.struct_defs), &var).unwrap();
                        self.locals.insert((func,var.clone()), (ptr,typ.clone()));
                        let load_instr = self.builder.build_store(ptr, p).unwrap();
                        //load_instr.set_alignment(typ.correct_alignment()).unwrap();
                        parami+=1;
                    }
                }

                while let Some(x) = i.next(){
                    match x.as_rule(){
                        R::konstanta | R::kamus => self.declare_funcs(x),
                        _ => continue
                    }
                }

            },
            R::mainprogram => {
                let main_fn = self.module.get_function("main").unwrap();
                let entry =main_fn.get_first_basic_block().unwrap();
                self.builder.position_at_end(entry);
                let mut i = pair.into_inner(); 
                let _ = i.map(|p|self.declare_funcs(p)).collect::<Vec<()>>();
            },
            R::konstanta => {
                let j = pair.into_inner();
                //ctf = const type field
                for ctf in j{
                    let mut k = ctf.into_inner();
                    let ident = k.next().unwrap().as_str();
                    let module = self.module;
                    let context = self.context;
                    let ty = Self::pair_to_type(&context, self.struct_defs, self.aliases, k.next().unwrap());
                    //let ftype = ty.fn_type(&[], false);
                    //let func = module.add_function("name", ftype, None);
                    let var_ptr = self.builder.build_alloca(ty.into_bte(self.context, self.aliases, self.struct_defs), ident).unwrap();
                    let func = self.builder.get_insert_block().unwrap().get_parent().unwrap();
                    let val = k.next().unwrap();
                    self.locals.insert((func,ident.clone().to_string()), (var_ptr.clone(),ty.clone()));
                    let load_instr = self.builder.build_store(var_ptr.into(), self.pair_to_value(val)).unwrap();
                    //load_instr.set_alignment(ty.correct_alignment()).unwrap();
                }
            },
            R::kamus => {
                let j = pair.into_inner();
                let func = self.builder.get_insert_block().unwrap().get_parent().unwrap();
                for type_decl in j{
                    let mut k = type_decl.into_inner().rev();
                    let context = self.context;
                    let ty = Self::pair_to_type(&context, self.struct_defs, self.aliases, k.next().unwrap());
                    let var_ptrs: Vec<_> = k.map(|x|{
                        let name = x.as_str();
                        println!("kamus for {name}");
                        let var_ptr = self.builder.build_alloca(ty.into_bte(self.context, self.aliases, self.struct_defs), x.as_str()).unwrap();
                        self.locals.insert((func,name.clone().to_string()), (var_ptr.clone(),ty.clone()));
                    }).collect();
                }

            },
            R::type_def => {
                let mut j = pair.into_inner();  
                let struct_name = j.next().unwrap().as_str().to_string();
                let mut v: Vec<(String, Type)> = vec![];
                for type_field in j.rev(){
                    let mut k = type_field.into_inner().rev();
                    let context = self.context;
                    let ty = Self::pair_to_type(&context, self.struct_defs, self.aliases, k.next().unwrap());
                    let var_ptrs: Vec<_> = k.map(|x|{
                        let name = x.as_str();
                        v.push((name.to_string(), ty.clone()));
                    }).collect();
                }
                v.reverse();
                let st_typ=self.context.struct_type(&v.iter().map(|(name,typ)|typ.into_bte(self.context, self.aliases, self.struct_defs)).collect::<Vec<_>>(), false);
                self.struct_defs.insert(struct_name, (st_typ, v.clone()));
            }
            _ => return // to many cases just catch em all
        }

    }

    pub fn register_proc(&mut self, name: &str, otype: Type, itype: Vec<(bool, bool, String,Type)>) -> FunctionValue<'ctx>{
        self._register_function(name, otype, itype, false, None)
    }
    pub fn register_func_unnamed_params(&mut self, name: &str, otype: Type, itype: Vec<(Type)>) -> FunctionValue<'ctx>{
        self._register_function(name, otype, 
            itype.iter().map(|t|(false,false,String::new(),t.clone())).collect(), 
            false, None)
    }
    pub fn register_func(&mut self, name: &str, otype: Type, itype: Vec<(String,Type)>) -> FunctionValue<'ctx>{
        self._register_function(name, otype, 
            itype.iter().map(|(s,t)|(false,false,s.clone(),t.clone())).collect(), 
            false, None)
    }
    pub fn register_extern_func_variadic(&mut self, name: &str, otype: Type, itype: Vec<Type>) -> FunctionValue<'ctx>{
        self._register_function(name, otype, 
            itype.iter().map(|t|(false,false,String::new(),t.clone())).collect(), 
            true, Some(Linkage::External))
    }
    pub fn register_variadic_extern_func(&mut self, name: &str, otype: Type, itype: Vec<Type>) -> FunctionValue<'ctx>{
        self._register_function(name, otype, 
            itype.iter().map(|t|(false,false,String::new(),t.clone())).collect(), 
            true, Some(Linkage::External))
    }
    pub fn register_extern_func(&mut self, name: &str, otype: Type, itype: Vec<Type>) -> FunctionValue<'ctx>{
        self._register_function(name, otype, 
            itype.iter().map(|t|(false,false,String::new(),t.clone())).collect(), 
            false, Some(Linkage::External))
    }
    pub fn _register_function(
        &mut self, 
        name: &str, 
        otype: Type, 
        itype:Vec<(bool,bool,String,Type)>, 
        is_var_args: bool,
        linkage: Option<Linkage>,
    ) -> FunctionValue<'ctx> {
        let func = self.module.add_function(
            &name, 
            otype.clone()
                .fn_type(
                    linkage,
                    name,
                    &itype
                    //.iter()
                    //.map(|(inv,outv,name,typ)|{
                    //    if !outv {typ.clone().into_bmte(self.context, self.struct_defs)}
                    //    else {Type::Ptr(Box::new(typ.clone())).into_bmte(self.context, self.struct_defs)}
                    //})
                    //.collect::<Vec<_>>()
                    ,
                ).compile(self.context, self.aliases, self.struct_defs).into_function_type(), 
            linkage,
        );
        match self.functions.get_mut(name){
            None => {self.functions.insert(name.to_string(), vec![(func.clone(),otype,itype)]);},
            Some(x) => x.push((func.clone(),otype.clone(),itype))
        };
        func
    }
    pub fn add_alloc(&mut self){
        // malloc
        self.register_extern_func("malloc", Type::VoidPtr, vec![Type::Int]);
    }
    pub fn add_time(&mut self){
        self.register_extern_func("time", Type::Int, vec![Type::Int]);
    }
    pub fn add_precise_time(&mut self){
        if cfg!(windows){
            // FILETIME struct
            let s_ty1 = self.context.i32_type().into();
            let s_ty2 = self.context.i32_type().into();
            let s = self.context.struct_type(&[s_ty1, s_ty2], false);
            
        } else if cfg!(unix) || cfg!(darwin){
            let out_ty = self.context.i32_type();
            let in_ty1 = self.context.i32_type().into();
            let in_ty2 = self.context.i8_type().ptr_type(AddressSpace::default()).into();
            let fn_ty = out_ty.fn_type(&[in_ty1, in_ty2], false);
            self.module.add_function("clock_gettime", fn_ty, Some(Linkage::External));
        } else {unimplemented!("Platform/OS not supported for precise time")}
    }
    pub fn add_rand(&mut self){
        self.register_extern_func("srand", Type::Void, vec![Type::Int]);
        self.register_extern_func("rand", Type::Int, vec![]);
    }
    pub fn add_printf(&mut self){
        self.register_variadic_extern_func("printf", Type::Int, vec![Type::String]);
    }
    pub fn add_scanf(&mut self){
        self.register_variadic_extern_func("scanf", Type::Int, vec![Type::VoidPtr]);
    }
    pub fn add_output(&mut self){
        let main_fn = self.module.get_function("main").unwrap();
        let entry =main_fn.get_first_basic_block().unwrap();
        self.builder.position_at_end(entry);

        let space = self.builder.build_global_string_ptr(" ", "space").unwrap();
        //space.set_alignment(4);
        

        let newline_fstr = self.builder.build_global_string_ptr("\n", "newline").unwrap();
        // newline_fstr.set_alignment(4);
        let char_fstr = self.builder.build_global_string_ptr("%c", "char_fstr").unwrap();
        // char_fstr.set_alignment(4);
        let string_fstr = self.builder.build_global_string_ptr("%s", "string_fstr").unwrap();
        // string_fstr.set_alignment(4);
        // ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^--> ChatGPT said .set_alignment(x) is actually optional

        // story time: it took my at least 6 hours of the night to figure out that %lld is the
        // correct i64 format specifier rather than %ld
        let i64_fstr = self.builder.build_global_string_ptr("%lld", "long_fstr").unwrap();
        //i64_fstr.set_alignment(4);
        let f64_fstr = self.builder.build_global_string_ptr("%f", "double_fstr").unwrap();
        //f64_fstr.set_alignment(4);
        let bool_fstr = self.builder.build_global_string_ptr("%hhd", "bool_fstr").unwrap();
        //bool_fstr.set_alignment(4);
        let printf = self.module.get_function("printf").unwrap();
        let scanf = self.module.get_function("scanf").unwrap();

        let func = self.register_func_unnamed_params("output_space", Type::Void, vec![]);
        let fblock = self.context.append_basic_block(func, "outputspace");
        self.builder.position_at_end(fblock);
        let pcall = self.builder.build_direct_call(
            printf, 
            &[
                space.as_pointer_value().into(), 
            ], 
            "printspace").unwrap();
        self.builder.build_return(None);

        let func = self.register_func_unnamed_params("output", Type::Void, vec![]);
        let fblock = self.context.append_basic_block(func, "outputentryempty");
        self.builder.position_at_end(fblock);
        let pcall = self.builder.build_direct_call(
            printf, 
            &[
                newline_fstr.as_pointer_value().into(), 
            ], 
            "printnewline").unwrap();
        self.builder.build_return(None);

        let func = self.register_func_unnamed_params("output", Type::Void, vec![Type::Int]);
        let fblock = self.context.append_basic_block(func, "outputentryi64");
        self.builder.position_at_end(fblock);
        let param= func.get_first_param().unwrap();
        let pcall = self.builder.build_direct_call(
            printf, 
            &[
                i64_fstr.as_pointer_value().into(), 
                param.into()
            ], 
            "printi64").unwrap();
        self.builder.build_return(None);

        let func = self.register_func_unnamed_params("output", Type::Void, vec![Type::Float]);
        let fblock = self.context.append_basic_block(func, "outputentryf64");
        self.builder.position_at_end(fblock);
        let param= func.get_first_param().unwrap();
        let pcall = self.builder.build_direct_call(
            printf, 
            &[
                f64_fstr.as_pointer_value().into(), 
                param.into()
            ], 
            "printf64").unwrap();
        self.builder.build_return(None);

        let func = self.register_func_unnamed_params("output", Type::Void, vec![Type::Bool]);
        let fblock = self.context.append_basic_block(func, "outputentrybool");
        self.builder.position_at_end(fblock);
        let param= func.get_first_param().unwrap();
        let pcall = self.builder.build_direct_call(
            printf, 
            &[
                bool_fstr.as_pointer_value().into(), 
                param.into()
            ], 
            "printfbool").unwrap();
        self.builder.build_return(None);

        let func = self.register_func_unnamed_params("output", Type::Void, vec![Type::Char]);
        let fblock = self.context.append_basic_block(func, "outputentrychar");
        self.builder.position_at_end(fblock);
        let param= func.get_first_param().unwrap();
        let pcall = self.builder.build_direct_call(
            printf, 
            &[
                char_fstr.as_pointer_value().into(), 
                param.into()
            ], 
            "printfchar").unwrap();
        self.builder.build_return(None);

        let func = self.register_func_unnamed_params("output", Type::Void, vec![Type::String]);
        let fblock = self.context.append_basic_block(func, "outputentrystring");
        self.builder.position_at_end(fblock);
        let param= func.get_first_param().unwrap();
        let pcall = self.builder.build_direct_call(
            printf, 
            &[
                string_fstr.as_pointer_value().into(), 
                param.into()
            ], 
            "printfstring").unwrap();
        self.builder.build_return(None);

        ////// 

        // let func = self.register_func_unnamed_params("input", Type::Void, vec![]);
        // let fblock = self.context.append_basic_block(func, "inputentryempty");
        // self.builder.position_at_end(fblock);
        // self.builder.build_return(None);

        let func = self.register_func_unnamed_params("input", Type::Void, vec![Type::Ptr(Box::new(Type::Int))]);
        let fblock = self.context.append_basic_block(func, "inputentryi64");
        self.builder.position_at_end(fblock);
        let param= func.get_first_param().unwrap();
        let pcall = self.builder.build_direct_call(
            scanf, 
            &[
                i64_fstr.as_pointer_value().into(), 
                param.into()
            ], 
            "scani64").unwrap();
        self.builder.build_return(None);

        let func = self.register_func_unnamed_params("input", Type::Void, vec![Type::Float]);
        let fblock = self.context.append_basic_block(func, "inputentryf64");
        self.builder.position_at_end(fblock);
        let param= func.get_first_param().unwrap();
        let pcall = self.builder.build_direct_call(
            scanf, 
            &[
                f64_fstr.as_pointer_value().into(), 
                param.into()
            ], 
            "scanf64").unwrap();
        self.builder.build_return(None);

        // let func = self.register_func_unnamed_params("input", Type::Void, vec![Type::Bool]);
        // let fblock = self.context.append_basic_block(func, "inputentrybool");
        // self.builder.position_at_end(fblock);
        // let param= func.get_first_param().unwrap();
        // let pcall = self.builder.build_direct_call(
        //     scanf, 
        //     &[
        //         bool_fstr.as_pointer_value().into(), 
        //         param.into()
        //     ], 
        //     "scanfbool").unwrap();
        // self.builder.build_return(None);

        let func = self.register_func_unnamed_params("input", Type::Void, vec![Type::Char]);
        let fblock = self.context.append_basic_block(func, "inputentrychar");
        self.builder.position_at_end(fblock);
        let param= func.get_first_param().unwrap();
        let pcall = self.builder.build_direct_call(
            scanf, 
            &[
                char_fstr.as_pointer_value().into(), 
                param.into()
            ], 
            "scanfchar").unwrap();
        self.builder.build_return(None);

        let func = self.register_func_unnamed_params("input", Type::Void, vec![Type::String]);
        let fblock = self.context.append_basic_block(func, "inputentrystring");
        self.builder.position_at_end(fblock);
        let param= func.get_first_param().unwrap();
        let pcall = self.builder.build_direct_call(
            scanf, 
            &[
                string_fstr.as_pointer_value().into(), 
                param.into()
            ], 
            "scanfstring").unwrap();
        self.builder.build_return(None);


    }
    // pub fn add_powi(&self){
    //     let f32t = self.context.f32_type().into();
    //     let i32t = self.context.i32_type().into();
    //     let f32tout = self.context.f32_type();
    //     let ftype = f32tout.fn_type(&[f32t,i32t], false);
    //     self.module.add_function("powi", ftype, None);
    // }
    // pub fn add_powf(&self){
    //     let f64t = self.context.f64_type().into();
    //     let f64tout = self.context.f64_type();
    //     let ftype = f64tout.fn_type(&[f64t,f64t], false);
    //     self.module.add_function("powf", ftype, None);
    // }
    pub fn fpowf(&self) -> FunctionValue<'ctx>{
        let powf = Intrinsic::find("llvm.pow.f64").expect("couldnt find powf64");
        powf.get_declaration(
            &self.module, 
            &[
                self.context.f64_type().as_basic_type_enum(),
                self.context.f64_type().as_basic_type_enum()
            ]
        ).unwrap()
    }
    pub fn fpowi(&self) -> FunctionValue<'ctx>{
        let powi = Intrinsic::find("llvm.powi.f32.i32").unwrap();
        powi.get_declaration(
            &self.module, 
            &[
                self.context.f32_type().as_basic_type_enum(),
                self.context.i32_type().as_basic_type_enum()
            ]
        ).unwrap()
    }
}
