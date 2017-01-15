structure tigerseman :> tigerseman =
struct

open tigerabs
open tigersres

type expty = {exp: unit, ty: Tipo}

type venv = (string, EnvEntry) tigertab.Tabla
type tenv = (string, Tipo) tigertab.Tabla

val tab_tipos : (string, Tipo) Tabla = tabInserList(
	tabNueva(),
	[("int", TInt), ("string", TString)])

val tab_vars : (string, EnvEntry) Tabla = tabInserList(
	tabNueva(),
	[("print", Func{level=mainLevel, label="print",
		formals=[TString], result=TUnit, extern=true}),
	("flush", Func{level=mainLevel, label="flush",
		formals=[], result=TUnit, extern=true}),
	("getchar", Func{level=mainLevel, label="getstr",
		formals=[], result=TString, extern=true}),
	("ord", Func{level=mainLevel, label="ord",
		formals=[TString], result=TInt, extern=true}),
	("chr", Func{level=mainLevel, label="chr",
		formals=[TInt], result=TString, extern=true}),
	("size", Func{level=mainLevel, label="size",
		formals=[TString], result=TInt, extern=true}),
	("substring", Func{level=mainLevel, label="substring",
		formals=[TString, TInt, TInt], result=TString, extern=true}),
	("concat", Func{level=mainLevel, label="concat",
		formals=[TString, TString], result=TString, extern=true}),
	("not", Func{level=mainLevel, label="not",
		formals=[TInt], result=TInt, extern=true}),
	("exit", Func{level=mainLevel, label="exit",
		formals=[TInt], result=TUnit, extern=true})
	])

fun tipoReal (TTipo s, (env : tenv)) : Tipo = 
    (case tabBusca(s , env) of 
         NONE => raise Fail "tipoReal Ttipo"
       | SOME t => t)
  | tipoReal (t, _) = t

fun tiposIguales (TRecord _) TNil = true
  | tiposIguales TNil (TRecord _) = true 
  | tiposIguales (TRecord (_, u1)) (TRecord (_, u2 )) = (u1=u2)
  | tiposIguales (TArray (_, u1)) (TArray (_, u2)) = (u1=u2)
  | tiposIguales (TTipo _) b =
		(* let *)
		(* 	val a = case !r of *)
		(* 		SOME t => t *)
		(* 		| NONE => raise Fail "No debería pasar! (1)" *)
		(* in *)
		(* 	tiposIguales a b *)
		(* end *)raise Fail "No debería pasar! (1)"
  | tiposIguales a (TTipo _) =
		(* let *)
		(* 	val b = case !r of *)
		(* 		SOME t => t *)
		(* 		| NONE => raise Fail "No debería pasar! (2)" *)
		(* in *)
		(* 	tiposIguales a b *)
		(* end *)raise Fail "No debería pasar! (2)"
  | tiposIguales a b = (a=b)

fun transExp(venv, tenv) =
	let fun error(s, p) = raise Fail ("Error -- línea "^Int.toString(p)^": "^s^"\n")
		fun trexp(VarExp v) = trvar(v)
		| trexp(UnitExp _) = {exp=(), ty=TUnit}
		| trexp(NilExp _)= {exp=(), ty=TNil}
		| trexp(IntExp(i, _)) = {exp=(), ty=TInt}
		| trexp(StringExp(s, _)) = {exp=(), ty=TString}
		| trexp(CallExp({func=f, args=a}, nl)) =
            (case tabBusca(f, venv) of
              SOME(Func({level=l, label=labl, formals=formals, result=r, extern=e})) =>
				let val argsTypes = map (fn (arg_exp) => (#ty (trexp(arg_exp)))) a
                    fun join(t1, t2, b) = b andalso (tiposIguales t1 t2)
                    open ListPair
                    val areArgsTypesEqual = (ListPair.foldlEq join true (argsTypes, formals))
                    handle UnequalLengths => error("Number of formal arguments does not match number of actual arguments", nl)
                in 
                    if areArgsTypesEqual then {exp=(), ty=r} else error("Los tipos de los argumentos no coinciden con los definidos para la funcion " ^ f, nl)
                end
              | _ => error("Funcion no definida " ^ f, nl))
		| trexp(OpExp({left, oper=EqOp, right}, nl)) =
			let
				val {exp=_, ty=tyl} = trexp left
				val {exp=_, ty=tyr} = trexp right
			in
				if tiposIguales tyl tyr andalso not (tyl=TNil andalso tyr=TNil) andalso tyl<>TUnit then {exp=(), ty=TInt}
					else error("Tipos no comparables", nl)
			end
		| trexp(OpExp({left, oper=NeqOp, right}, nl)) = 
			let
				val {exp=_, ty=tyl} = trexp left
				val {exp=_, ty=tyr} = trexp right
			in
				if tiposIguales tyl tyr andalso not (tyl=TNil andalso tyr=TNil) andalso tyl<>TUnit then {exp=(), ty=TInt}
					else error("Tipos no comparables", nl)
			end
		| trexp(OpExp({left, oper, right}, nl)) = 
			let
				val {exp=_, ty=tyl} = trexp left
				val {exp=_, ty=tyr} = trexp right
			in
				if tiposIguales tyl tyr then
					case oper of
						PlusOp => if tipoReal(tyl, tenv)=TInt then {exp=(),ty=TInt} else error("Error de tipos", nl)
						| MinusOp => if tipoReal(tyl,tenv)=TInt then {exp=(),ty=TInt} else error("Error de tipos", nl)
						| TimesOp => if tipoReal(tyl,tenv)=TInt then {exp=(),ty=TInt} else error("Error de tipos", nl)
						| DivideOp => if tipoReal(tyl,tenv)=TInt then {exp=(),ty=TInt} else error("Error de tipos", nl)
						| LtOp => if tipoReal(tyl,tenv)=TInt orelse tipoReal(tyl,tenv)=TString then {exp=(),ty=TInt} else error("Error de tipos", nl)
						| LeOp => if tipoReal(tyl,tenv)=TInt orelse tipoReal(tyl,tenv)=TString then {exp=(),ty=TInt} else error("Error de tipos", nl)
						| GtOp => if tipoReal(tyl,tenv)=TInt orelse tipoReal(tyl,tenv)=TString then {exp=(),ty=TInt} else error("Error de tipos", nl)
						| GeOp => if tipoReal(tyl,tenv)=TInt orelse tipoReal(tyl,tenv)=TString then {exp=(),ty=TInt} else error("Error de tipos", nl)
						| _ => raise Fail "No debería pasar! (3)"
				else error("Error de tipos", nl)
			end
		| trexp(RecordExp({fields, typ}, nl)) =
			let
				(* Traducir cada expresión de fields *)
				val tfields = map (fn (sy,ex) => (sy, trexp ex)) fields

				(* Buscar el tipo *)
				val (tyr, cs) = case tabBusca(typ, tenv) of
					SOME t => (case tipoReal(t,tenv) of
						TRecord (cs, u) => (TRecord (cs, u), cs)
						| _ => error(typ^" no es de tipo record", nl))
					| NONE => error("Tipo inexistente ("^typ^")", nl)
				
				(* Verificar que cada campo esté en orden y tenga una expresión del tipo que corresponde *)
				fun verificar [] [] = ()
				  | verificar (c::cs) [] = error("Faltan campos", nl)
				  | verificar [] (c::cs) = error("Sobran campos", nl)
				  | verificar ((s,t,_)::cs) ((sy,{exp,ty})::ds) =
						if s<>sy then error("Error de campo", nl)
						else if tiposIguales ty (!t) then verificar cs ds
							 else error("Error de tipo del campo "^s, nl)
				val _ = verificar cs tfields
			in
				{exp=(), ty=tyr}
			end
		| trexp(SeqExp(s, nl)) =
			let	val lexti = map trexp s
				val exprs = map (fn{exp, ty} => exp) lexti
				val {exp, ty=tipo} = hd(rev lexti)
			in	{ exp=(), ty=tipo } end
		| trexp(AssignExp({var=SimpleVar s, exp}, nl)) =
            let val _ = case tabBusca(s, venv)
                         of SOME(VIntro) => 
                            error("Error: asignación a entero de sólo lectura "^s, nl)
                          | _ => ()
                val typ_exp = tipoReal((#ty (trexp exp)), tenv)
                val typ_var = tipoReal((#ty (trvar (SimpleVar s, nl))), tenv)
            in 
                if tiposIguales typ_exp typ_var then { exp=(), ty=TUnit }
                else error("El tipo de la variable y el de la expresión no coinciden", nl)
            end
		| trexp(AssignExp({var, exp}, nl)) =
            let val typ_exp = tipoReal((#ty (trexp exp)), tenv)
                val typ_var = tipoReal((#ty (trvar (var, nl))), tenv)
            in 
                if tiposIguales typ_exp typ_var then { exp=(), ty=TUnit }
                else error("El tipo de la variable y el de la expresión no coinciden", nl)
            end
		| trexp(IfExp({test, then', else'=SOME else'}, nl)) =
			let val {exp=testexp, ty=tytest} = trexp test
			    val {exp=thenexp, ty=tythen} = trexp then'
			    val {exp=elseexp, ty=tyelse} = trexp else'
			in
				if tipoReal(tytest,tenv)=TInt andalso tiposIguales tythen tyelse then {exp=(), ty=tythen}
				else error("Error de tipos en if" ,nl)
			end
		| trexp(IfExp({test, then', else'=NONE}, nl)) =
			let val {exp=exptest,ty=tytest} = trexp test
			    val {exp=expthen,ty=tythen} = trexp then'
			in
				if tipoReal(tytest,tenv)=TInt andalso tythen=TUnit then {exp=(), ty=TUnit}
				else error("Error de tipos en if", nl)
			end
		| trexp(WhileExp({test, body}, nl)) =
			let
				val ttest = trexp test
				val tbody = trexp body
			in
				if tipoReal(#ty ttest, tenv) = TInt andalso #ty tbody = TUnit then {exp=(), ty=TUnit}
				else if tipoReal(#ty ttest, tenv) <> TInt then error("Error de tipo en la condición", nl)
				else error("El cuerpo de un while no puede devolver un valor", nl)
			end
		| trexp(ForExp({var, escape, lo, hi, body}, nl)) =
            let val _ = if tiposIguales (#ty (trexp lo)) TInt andalso tiposIguales (#ty (trexp hi)) TInt
                        then () else error("Cotas no enteras", nl)
                val venv' = fromTab venv
                val venv'' = tabInserta (var, VIntro, venv')
                val {exp=_,ty=bt} = transExp(venv'', tenv) body
			in if tiposIguales bt TUnit then {exp=(), ty=TUnit} else error("Cuerpo del for tiene tipo incorrecto", nl)
            end
		| trexp(LetExp({decs, body}, _)) =
			let
				val (venv', tenv', _) = List.foldl (fn (d, (v, t, _)) => trdec(v, t) d) (venv, tenv, []) decs
				val {exp=expbody,ty=tybody}=transExp (venv', tenv') body
			in 
				{exp=(), ty=tybody}
			end
		| trexp(BreakExp nl) =
			{exp=(), ty=TUnit} (*COMPLETAR*)
		| trexp(ArrayExp({typ, size, init}, nl)) =
            let val st = #ty (trexp size)
                val it = #ty (trexp init)
                val _ = if tiposIguales st TInt then () else error("Tamaño del arreglo no es entero", nl)
                val (typ_id,n) = case (tabBusca(typ,tenv))
                                 of (SOME(TArray(t,n))) => (t, n)
                                    | _ => error("El tipo no es un tipo de arreglo", nl)
                val _ = if tiposIguales it (tipoReal(!typ_id, tenv)) then () else error("Tipo del valor inicial del arreglo no coincide con tipo del arreglo", nl)
            in {exp=(), ty=TArray(typ_id,n)}
            end
		and trvar(SimpleVar s, nl) =
            (case tabBusca(s, venv)
              of SOME(Var({ty=typ})) =>
                 {exp=(), ty=typ}
               | SOME(VIntro) => {exp=(), ty=TInt}
               | _ => (error("Variable no definida " ^ s, nl)))
		| trvar(FieldVar(v, s), nl) =
            let val {exp=e', ty=var_type} = trvar (v, nl)
                val listFields = case tipoReal(var_type,tenv)
                                  of (TRecord(ts,_)) => ts
                                     | _ => error("FieldVar apunta a una variable que no es un Record", nl)
                val (t',i) = (case List.find (fn x => (#1 x) = s) listFields
                               of SOME(x) => (#2 x, #3 x)
                                  | NONE => error(s^" no es un miembro", nl))
            in { exp=(), ty=(!t') }
            end
		| trvar(SubscriptVar(v, e), nl) =
            let val elem_type = case (trvar (v, nl)) of
                                 {exp=_, ty=TArray(t, _)} => t
                                 | _ => error("La variable no es un arreglo", nl)
                val _ = case (trexp e) of
                         {exp=_, ty=TInt} => ()
                         | _ => error("El subíndice no es un entero", nl)
             in {exp=(), ty=(!elem_type)}
             end
		and trdec (venv, tenv) (VarDec ({name,escape,typ=NONE,init},pos)) = 
            let val {exp=_, ty=init_typ} = transExp (venv, tenv) init
                val _ = case init_typ
                         of TNil => error("If the initializing expression is nil, then the long form must be used", pos)
                            | _ => ()
                val venv' = tabRInserta (name, Var({ty=init_typ}), venv)
            in (venv', tenv, [])
            end
		| trdec (venv,tenv) (VarDec ({name,escape,typ=SOME s,init},pos)) =
            let val {exp=_, ty=init_typ} = transExp (venv, tenv) init
                val real_s = case tabBusca(s, tenv)
                              of SOME(x) => tipoReal(x, tenv)
                                 | _ => error("Type of declared variable does not exist", pos)
                val _ = if (tiposIguales real_s init_typ) then () else error("Initializing expression type does not match variable declarated type", pos)
                val venv' = tabRInserta (name, Var({ty=real_s}), venv)
            in (venv', tenv, [])
            end
		| trdec (venv,tenv) (FunctionDec(fs)) =
             let fun checkTip(name,pos) = case tabBusca(name, tenv) of
                                            SOME(t) => t 
                                            |_ => error("Type not defined "^name, pos)
                  fun typeToString(typ) = case typ of
                                          TUnit => "TUnit"
                                          | TInt => "TInt"
                                          | TNil => "TNil"
                                          | TString => "TString"
                                          | TRecord(_) => "TRecord"
                                          | _ => "other"
                 fun transTy(NameTy(s), pos) = checkTip(s,pos)
                     | transTy(_, pos) = TUnit
                 fun get_params_tips(fields,pos) = map (fn({name=n,escape=_,typ=t}) => (transTy(t, pos))) fields
                 fun get_sig({name=s, params=ps, result=SOME(rt), body=_}, pos) = (s, get_params_tips(ps,pos), checkTip(rt,pos))
                     | get_sig({name=s, params=ps, result=NONE, body=e}, pos) = (s, get_params_tips(ps,pos), TUnit)
                 fun get_func_entry(name, params, result) = (name, Func({level=(), label=tigertemp.newlabel(), formals=params, result=result, extern=false}))(*TODO ver label y extern*)
                 val sigs = map get_sig fs
                 fun has_more_that_one_definition(f_name, signature_list) =  
                    let val number_definitions = length (List.filter (fn(s) => (#1 s)=f_name) signature_list)
                    in (number_definitions > 1)
                    end

                 val _ = if (List.exists (fn(s) => has_more_that_one_definition(#1 s, sigs)) sigs) then error("Two functions with the same name in a sequence of mutually recursive functions", #2 (hd fs)) else ()

                 val func_entries_with_name = map get_func_entry sigs
                 val venv_with_funentries = foldr (fn((name,funentry),env) => tabRInserta(name,funentry,env)) venv func_entries_with_name
                 fun get_formal_params({name=_, params=ps, result=_, body=_}, pos) = map (fn({name=n,escape=_,typ=t}) => (n, transTy(t, pos))) ps 
                 fun add_formal_params_to_env(fparams) = foldr (fn(param, env) => (tabRInserta(#1 param, Var({ty=(#2 param)}), env))) venv_with_funentries fparams
                 fun check_function(singleFunctionDec) =
                   let val form_params = get_formal_params(singleFunctionDec)
                       val pos = #2 singleFunctionDec
                       val venv_with_params = add_formal_params_to_env(form_params)
                       val body = #body (#1 singleFunctionDec)
                       val type_body = #ty (transExp(venv_with_params, tenv) body)
                       val type_ret = #3 (get_sig singleFunctionDec)
                       val _ = if tiposIguales type_body type_ret then () else error("Function body does not match return type", pos)
                    in ()
                    end
                  val _ = map check_function fs

			 in (venv_with_funentries, tenv, [])
             end
		| trdec (venv,tenv) (TypeDec []) = (venv, tenv, [])
		| trdec (venv,tenv) (TypeDec ldecs) =
            let open List
                fun reps [] = (false, 0)
                | reps (({name=s,...},pos)::t) = if List.exists (fn({name=x,...},p) => x=s) t then (true, pos) else reps t
                val _ = if #1 (reps ldecs) then error("Repated type names",#2 (reps ldecs)) else ()
                val pos_first_dec = #2 (hd ldecs)
                val ldecs' = map #1 ldecs
                val tenv' = (tigertopsort.fijaTipos ldecs' tenv)
                            handle tigertopsort.Ciclo => error("Cycle in types declaration", pos_first_dec)
                                   | noExiste => error("Type not declared", pos_first_dec)
			in (venv, tenv', [])
            end
	in trexp end
fun transProg ex =
	let	val main =
				LetExp({decs=[FunctionDec[({name="_tigermain", params=[],
								result=(SOME "int"), body=ex}, 0)]],
						body=UnitExp 0}, 0)
		val _ = transExp(tab_vars, tab_tipos) main
	in	print "bien!\n" end
end
