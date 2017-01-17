structure tigerseman :> tigerseman =
struct

open tigerabs
open tigersres
open tigertrans

type expty = {exp: unit, ty: Tipo}

type venv = (string, EnvEntry) tigertab.Tabla
type tenv = (string, Tipo) tigertab.Tabla

val tab_tipos : (string, Tipo) Tabla = tabInserList(
	tabNueva(),
	[("int", TInt), ("string", TString)])

val levelPila: tigertrans.level tigerpila.Pila = tigerpila.nuevaPila1(tigertrans.outermost) 
fun pushLevel l = tigerpila.pushPila levelPila l
fun popLevel() = tigerpila.popPila levelPila 
fun topLevel() = tigerpila.topPila levelPila

val tab_vars : (string, EnvEntry) Tabla = tabInserList(
	tabNueva(),
	[("print", Func{level=topLevel(), label="print",
		formals=[TString], result=TUnit, extern=true}),
	("flush", Func{level=topLevel(), label="flush",
		formals=[], result=TUnit, extern=true}),
	("getchar", Func{level=topLevel(), label="getstr",
		formals=[], result=TString, extern=true}),
	("ord", Func{level=topLevel(), label="ord",
		formals=[TString], result=TInt, extern=true}),
	("chr", Func{level=topLevel(), label="chr",
		formals=[TInt], result=TString, extern=true}),
	("size", Func{level=topLevel(), label="size",
		formals=[TString], result=TInt, extern=true}),
	("substring", Func{level=topLevel(), label="substring",
		formals=[TString, TInt, TInt], result=TString, extern=true}),
	("concat", Func{level=topLevel(), label="concat",
		formals=[TString, TString], result=TString, extern=true}),
	("not", Func{level=topLevel(), label="not",
		formals=[TInt], result=TInt, extern=true}),
	("exit", Func{level=topLevel(), label="exit",
		formals=[TInt], result=TUnit, extern=true})
	])

fun tipoReal (TTipo (s, ref (SOME (t)))) = tipoReal t
  | tipoReal t = t

fun tiposIguales (TRecord _) TNil = true
  | tiposIguales TNil (TRecord _) = true 
  | tiposIguales (TRecord (_, u1)) (TRecord (_, u2 )) = (u1=u2)
  | tiposIguales (TArray (_, u1)) (TArray (_, u2)) = (u1=u2)
  | tiposIguales (TTipo (_, r)) b =
		let
			val a = case !r of
				SOME t => t
				| NONE => raise Fail "No debería pasar! (1)"
		in
			tiposIguales a b
		end
  | tiposIguales a (TTipo (_, r)) =
		let
			val b = case !r of
				SOME t => t
				| NONE => raise Fail "No debería pasar! (2)"
		in
			tiposIguales a b
		end
  | tiposIguales a b = (a=b)

fun transExp(venv, tenv) =
	let fun error(s, p) = raise Fail ("Error -- línea "^Int.toString(p)^": "^s^"\n")
		fun trexp(VarExp v) = trvar(v)
		| trexp(UnitExp _) = {exp=unitExp(), ty=TUnit}
		| trexp(NilExp _)= {exp=nilExp(), ty=TNil}
		| trexp(IntExp(i, _)) = {exp=intExp i, ty=TInt}
		| trexp(StringExp(s, _)) = {exp=stringExp(s), ty=TString}
		| trexp(CallExp({func=f, args=a}, nl)) =
            (case tabBusca(f, venv) of
              SOME(Func({level=l, label=labl, formals=formals, result=r, extern=e})) =>
				let val args_processed = map (fn (arg_exp) => (trexp(arg_exp))) a
				    val argsTypes = map (fn (arg_exp) => #ty (arg_exp)) args_processed
				    val ci_argsExps = map (fn (arg_exp) => #exp (arg_exp)) args_processed
                    fun join(t1, t2, b) = b andalso (tiposIguales t1 t2)
                    open ListPair
                    val areArgsTypesEqual = (ListPair.foldlEq join true (argsTypes, formals))
                    handle UnequalLengths => error("Number of formal arguments does not match number of actual arguments", nl)
                    val _ = if areArgsTypesEqual then () else error("Los tipos de los argumentos no coinciden con los definidos para la funcion " ^ f, nl)
                    val is_procedure = (tiposIguales r TUnit)
                    (*val _ = pushLevel l  esto va?*)
                    val ci_e = callExp(labl, e, is_procedure, l, ci_argsExps) 
                in 
                    {exp=ci_e, ty=r}
                end
              | _ => error("Funcion no definida " ^ f, nl))
		| trexp(OpExp({left, oper=EqOp, right}, nl)) =
			let
				val {exp=expl, ty=tyl} = trexp left
				val {exp=expr, ty=tyr} = trexp right
			in
				if tiposIguales tyl tyr andalso not (tyl=TNil andalso tyr=TNil) andalso tyl<>TUnit then 
					{exp=if tiposIguales tyl TString then binOpStrExp {left=expl,oper=EqOp,right=expr} else binOpIntRelExp {left=expl,oper=EqOp,right=expr}, ty=TInt}
					else error("Tipos no comparables", nl)
			end
		| trexp(OpExp({left, oper=NeqOp, right}, nl)) = 
			let
				val {exp=expl, ty=tyl} = trexp left
				val {exp=expr, ty=tyr} = trexp right
			in
				if tiposIguales tyl tyr andalso not (tyl=TNil andalso tyr=TNil) andalso tyl<>TUnit then 
					{exp=if tiposIguales tyl TString then binOpStrExp {left=expl,oper=NeqOp,right=expr} else binOpIntRelExp {left=expl,oper=NeqOp,right=expr}, ty=TInt}
					else error("Tipos no comparables", nl)
			end
		| trexp(OpExp({left, oper, right}, nl)) = 
			let
				val {exp=expl, ty=tyl} = trexp left
				val {exp=expr, ty=tyr} = trexp right
			in
				if tiposIguales tyl tyr then
					case oper of
						PlusOp => if tipoReal tyl=TInt then {exp=binOpIntExp {left=expl, oper=oper, right=expr},ty=TInt} else error("Error de tipos", nl)
						| MinusOp => if tipoReal tyl=TInt then {exp=binOpIntExp {left=expl, oper=oper, right=expr},ty=TInt} else error("Error de tipos", nl)
						| TimesOp => if tipoReal tyl=TInt then {exp=binOpIntExp {left=expl, oper=oper, right=expr},ty=TInt} else error("Error de tipos", nl)
						| DivideOp => if tipoReal tyl=TInt then {exp=binOpIntExp {left=expl, oper=oper, right=expr},ty=TInt} else error("Error de tipos", nl)
						| LtOp => if tipoReal tyl=TInt orelse tipoReal tyl=TString then
							{exp=if tipoReal tyl=TInt then binOpIntRelExp {left=expl,oper=oper,right=expr} else binOpStrExp {left=expl,oper=oper,right=expr},ty=TInt} 
							else error("Error de tipos", nl)
						| LeOp => if tipoReal tyl=TInt orelse tipoReal tyl=TString then 
							{exp=if tipoReal tyl=TInt then binOpIntRelExp {left=expl,oper=oper,right=expr} else binOpStrExp {left=expl,oper=oper,right=expr},ty=TInt} 
							else error("Error de tipos", nl)
						| GtOp => if tipoReal tyl=TInt orelse tipoReal tyl=TString then
							{exp=if tipoReal tyl=TInt then binOpIntRelExp {left=expl,oper=oper,right=expr} else binOpStrExp {left=expl,oper=oper,right=expr},ty=TInt} 
							else error("Error de tipos", nl)
						| GeOp => if tipoReal tyl=TInt orelse tipoReal tyl=TString then
							{exp=if tipoReal tyl=TInt then binOpIntRelExp {left=expl,oper=oper,right=expr} else binOpStrExp {left=expl,oper=oper,right=expr},ty=TInt} 
							else error("Error de tipos", nl)
						| _ => raise Fail "No debería pasar! (3)"
				else error("Error de tipos", nl)
			end
		| trexp(RecordExp({fields, typ}, nl)) =
			let
				(* Traducir cada expresión de fields *)
				val tfields = map (fn (sy,ex) => (sy, trexp ex)) fields

				(* Buscar el tipo *)
				val (tyr, cs) = case tabBusca(typ, tenv) of
					SOME t => (case tipoReal t of
						TRecord (cs, u) => (TRecord (cs, u), cs)
						| _ => error(typ^" no es de tipo record", nl))
					| NONE => error("Tipo inexistente ("^typ^")", nl)
				
				(* Verificar que cada campo esté en orden y tenga una expresión del tipo que corresponde *)
				fun verificar _ [] [] = []
				  | verificar _ (c::cs) [] = error("Faltan campos", nl)
				  | verificar _ [] (c::cs) = error("Sobran campos", nl)
				  | verificar n ((s,t,_)::cs) ((sy,{exp,ty})::ds) =
						if s<>sy then error("Error de campo", nl)
						else if tiposIguales ty t then (exp, n)::(verificar (n+1) cs ds)
							 else error("Error de tipo del campo "^s, nl)
				val lf = verificar 0 cs tfields
			in
				{exp=recordExp lf, ty=tyr}
			end
		| trexp(SeqExp(s, nl)) =
			let	val lexti = map trexp s
				val exprs = map (fn{exp, ty} => exp) lexti
				val {exp, ty=tipo} = hd(rev lexti)
			in	{ exp=seqExp (exprs), ty=tipo } end
		| trexp(AssignExp({var=SimpleVar s, exp}, nl)) =
	        let val _ = case tabBusca(s, venv)
                         of SOME(VIntro(_)) => 
                            error("Error: asignación a entero de sólo lectura "^s, nl)
                          | _ => ()
                val exp_translated = trexp exp
                val typ_exp = tipoReal(#ty exp_translated) 
                val var_translated = trvar(SimpleVar s, nl)
                val typ_var = tipoReal(#ty var_translated)
                val _ = if tiposIguales typ_exp typ_var then () else error("The types of the variable and the expression do not match", nl)
                val right_exp = #exp exp_translated
                val var_exp = #exp var_translated
                val e = assignExp({var=var_exp, exp=right_exp})
            in 
                { exp=e, ty=TUnit }
            end
		| trexp(AssignExp({var, exp}, nl)) =
            let val exp_translated = trexp exp
                val typ_exp = tipoReal(#ty exp_translated) 
                val var_translated = trvar(var, nl)
                val typ_var = tipoReal(#ty var_translated)
                val _ = if tiposIguales typ_exp typ_var then () else error("The types of the variable and the expression do not match", nl)
                val right_exp = #exp exp_translated
                val var_exp = #exp var_translated
                val e = assignExp({var=var_exp, exp=right_exp})
            in 
                { exp=e, ty=TUnit }
            end
		| trexp(IfExp({test, then', else'=SOME else'}, nl)) =
			let val {exp=testexp, ty=tytest} = trexp test
			    val {exp=thenexp, ty=tythen} = trexp then'
			    val {exp=elseexp, ty=tyelse} = trexp else'
			in
				if tipoReal tytest=TInt andalso tiposIguales tythen tyelse then
				{exp=if tipoReal tythen=TUnit then ifThenElseExpUnit {test=testexp,then'=thenexp,else'=elseexp} else ifThenElseExp {test=testexp,then'=thenexp,else'=elseexp}, ty=tythen}
				else error("Type error in if expression" ,nl)
			end
		| trexp(IfExp({test, then', else'=NONE}, nl)) =
			let val {exp=exptest,ty=tytest} = trexp test
			    val {exp=expthen,ty=tythen} = trexp then'
			in
				if tipoReal tytest=TInt andalso tythen=TUnit then
				{exp=ifThenExp{test=exptest, then'=expthen}, ty=TUnit}
				else error("Error de tipos en if", nl)
			end
		| trexp(WhileExp({test, body}, nl)) =
			let
				val ttest = trexp test
				val tbody = trexp body
			in
				if tipoReal (#ty ttest) = TInt andalso #ty tbody = TUnit then {exp=whileExp {test=(#exp ttest), body=(#exp tbody), lev=topLevel()}, ty=TUnit}
				else if tipoReal (#ty ttest) <> TInt then error("Error in condition type", nl)
				else error("While expression cannot return a value", nl)
			end
		| trexp(ForExp({var, escape, lo, hi, body}, nl)) =
            let val {exp=explo, ty=tylo} = trexp lo
                val {exp=exphi, ty=tyhi} = trexp hi
                val _ = if tiposIguales tylo TInt andalso tiposIguales tyhi TInt
                        then () else error("For subscripts are not integers", nl)
                val level = getActualLev()
                val acc' = allocLocal (topLevel()) (!escape)
                val _ = preWhileForExp()
                val venv' = fromTab venv
                val venv'' = tabInserta (var, VIntro({access=acc', level=level}), venv')
                val {exp=eb',ty=tb'} = transExp(venv'', tenv) body
                val _ = if tiposIguales tb' TUnit then () else error("For expression cannot return a value", nl)
                val ev' = simpleVar(acc', 0)
                val ef'= forExp({lo=explo, hi=exphi, var=ev', body=eb'})
                val _ = postWhileForExp()
			in {exp=eb', ty=tb'} 
            end
		| trexp(LetExp({decs, body}, _)) =
			let
				fun aux (d, (v, t, exps1)) =
				let
					val (v', t', exps2) = trdec (v, t) d
				in
					(v', t', exps1@exps2)
				end
				val (venv', tenv', expdecs) = List.foldl aux (venv, tenv, []) decs
				val {exp=expbody,ty=tybody}=transExp (venv', tenv') body
			in 
				{exp=seqExp(expdecs@[expbody]), ty=tybody}
			end
		| trexp(BreakExp nl) =
			{exp=breakExp(), ty=TUnit} (*COMPLETAR.. falta algo mas?*)
		| trexp(ArrayExp({typ, size, init}, nl)) =
            let val {exp=expsize, ty=tysize} = trexp size
                val {exp=expinit, ty=tyinit} = trexp init
                val _ = if tiposIguales tysize TInt then () else error("Array size is not an integer", nl)
                val (typ_id,n) = case (tabBusca(typ,tenv))
                                 of (SOME(TArray(t,n))) => (t, n)
                                    | _ => error("Type is not array", nl)
                val _ = if tiposIguales tyinit (tipoReal(typ_id)) then () else error("Initializing value does not match array's type", nl)
                val exparr = arrayExp({size=expsize, init=expinit})
            in {exp=exparr, ty=TArray(typ_id,n)}
            end
		and trvar(SimpleVar s, nl) =
            (case tabBusca(s, venv)
              of SOME(Var({ty=typ,access=acc,level=lvl})) =>
                 {exp=simpleVar(acc,lvl), ty=typ}
               | SOME(VIntro({access=acc, level=lvl})) =>
                 {exp=simpleVar(acc,lvl), ty=TInt}
               | _ => (error("Undefined variable " ^ s, nl)))
		| trvar(FieldVar(v, s), nl) =
            let val {exp=e', ty=var_type} = trvar (v, nl)
                val listFields = case tipoReal(var_type)
                                  of (TRecord(ts,_)) => ts
                                     | _ => error("Variable is not a record", nl)
                val (t',i) = (case List.find (fn x => (#1 x) = s) listFields
                               of SOME(x) => (#2 x, #3 x)
                                  | NONE => error(s^" is not a record member", nl))
            in 
                {exp=fieldVar(e',i), ty=t'}
            end
		| trvar(SubscriptVar(v, e), nl) =
            let val (expvar, elemtype) = case (trvar (v, nl)) of
                                              {exp=e, ty=TArray(elem_typ, _)} => (e, elem_typ)
                                              | _ => error("Variable is not an array", nl)
                val {exp=expsub, ty=tysub} = case (trexp e) of
                                              {exp=expsub, ty=TInt} => {exp=expsub, ty=TInt}
                                              | _ => error("Subscript is not an integer", nl)
             in {exp=subscriptVar(expvar, expsub), ty=elemtype}
             end
		and trdec (venv, tenv) (VarDec ({name,escape,typ=NONE,init},pos)) = 
            let val {exp=_, ty=init_typ} = transExp (venv, tenv) init
                val _ = case init_typ
                         of TNil => error("If the initializing expression is nil, then the long form must be used", pos)
                            | _ => ()
                val acc = allocLocal (topLevel()) (!escape)
                val lvl = getActualLev()
                val venv' = tabRInserta (name, Var({ty=init_typ, access=acc, level=lvl}), venv)
            in (venv', tenv, [])
            end
		| trdec (venv,tenv) (VarDec ({name,escape,typ=SOME s,init},pos)) =
            let val {exp=_, ty=init_typ} = transExp (venv, tenv) init
                val real_s = case tabBusca(s, tenv)
                              of SOME(x) => tipoReal(x)
                                 | _ => error("Type of declared variable does not exist", pos)
                val _ = if (tiposIguales real_s init_typ) then () else error("Initializing expression type does not match variable declarated type", pos)
                val acc = allocLocal (topLevel()) (!escape)
                val lvl = getActualLev()
                val venv' = tabRInserta (name, Var({ty=real_s, access=acc, level=lvl}), venv)
            in (venv', tenv, [])
            end
		| trdec (venv,tenv) (FunctionDec fs) =
             let fun checkTip(name,pos) = case tabBusca(name, tenv) of
                                            SOME(t) => t 
                                            |_ => error("Type not defined "^name, pos)
                 fun transTy(NameTy(s), pos) = checkTip(s,pos)
                     | transTy(_, pos) = TUnit
                 fun get_params_tips(fields,pos) = map (fn({name=n,escape=_,typ=t}) => (transTy(t, pos))) fields
                 fun get_sig({name=s, params=ps, result=SOME(rt), body=_}, pos) = (s, get_params_tips(ps,pos), checkTip(rt,pos))
                     | get_sig({name=s, params=ps, result=NONE, body=e}, pos) = (s, get_params_tips(ps,pos), TUnit)
                 fun get_func_entry(name, params, result) = 
                   let val parent=topLevel()
                       val new_level=newLevel({parent=parent, name=name, formals=[]})
                   in (name, Func({level=new_level, label=tigertemp.newlabel(), formals=params, result=result, extern=false}))(*TODO ver label y extern*)
                   end
                 val sigs = map get_sig fs
                 fun has_more_that_one_definition(f_name, signature_list) =  
                    let val number_definitions = length (List.filter (fn(s) => (#1 s)=f_name) signature_list)
                    in (number_definitions > 1)
                    end

                 val _ = if (List.exists (fn(s) => has_more_that_one_definition(#1 s, sigs)) sigs) then error("Two functions with the same name in a sequence of mutually recursive functions", #2 (hd fs)) else ()

                 val func_entries_with_name = map get_func_entry sigs
                 val venv_with_funentries = foldr (fn((name,funentry),env) => tabRInserta(name,funentry,env)) venv func_entries_with_name

                 fun get_formal_params({name=n, params=ps, result=_, body=_}, pos) = 
                  let val fun_ventry = tabBusca(n, venv_with_funentries)
                      val lvl = case fun_ventry of
                                 SOME(Func(x)) => (#level(x))
                                 | _ => error("Internal error 1", 0)
                   in map (fn({name=n,escape=e,typ=t}) => (n, transTy(t, pos), e, 3)) ps 
                   end
                 fun add_formal_params_to_env(fparams,lvl) = 
                    foldr (fn(param, env) => (tabRInserta(#1 param, Var({ty=(#2 param), access=(allocLocal (topLevel()) (!(#3 param))), level=lvl}), env))) venv_with_funentries fparams
                 fun check_and_push_function(singleFunctionDec) =
                   let val form_params = get_formal_params(singleFunctionDec)
                       val pos = #2 singleFunctionDec
                       val name = #name (#1 singleFunctionDec)
                       val lvl_fun = case tabBusca(name, venv_with_funentries)
                                      of SOME(Func({level=l,...})) => l
                                         | _ => error("Internal error 1", pos)
                       val _ = pushLevel lvl_fun
                       val venv_with_params = add_formal_params_to_env(form_params,getActualLev())
                       (*COMPLETAR falta poplevel*)
                       val body = #body (#1 singleFunctionDec)
                       val type_body = #ty (transExp(venv_with_params, tenv) body)
                       val type_ret = #3 (get_sig singleFunctionDec)
                       val _ = if tiposIguales type_body type_ret then () else error("Function body does not match return type", pos)
                    in ()
                    end
                  val _ = map check_and_push_function fs

			 in (venv_with_funentries, tenv, [])
             end
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
