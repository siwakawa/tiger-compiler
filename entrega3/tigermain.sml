open tigerlex
open tigergrm
open tigerescap
open tigerseman
open BasicIO Nonstdio

fun lexstream(is: instream) =
	Lexing.createLexer(fn b => fn n => buff_input is b 0 n);
fun errParsing(lbuf) = (print("Error en parsing!("
	^(makestring(!num_linea))^
	")["^(Lexing.getLexeme lbuf)^"]\n"); raise Fail "fin!")
fun main(args) =
	let	fun arg(l, s) =
			(List.exists (fn x => x=s) l, List.filter (fn x => x<>s) l)
		val (arbol, l1)		= arg(args, "-arbol")
		val (escapes, l2)	= arg(l1, "-escapes") 
		val (ir, l3)		= arg(l2, "-ir") 
		val (canon, l4)		= arg(l3, "-canon") 
		val (code, l5)		= arg(l4, "-code") 
		val (flow, l6)		= arg(l5, "-flow") 
		val (inter, l7)		= arg(l6, "-inter") 
		val (fold, l8)		= arg(l7, "-fold") 
		val (live, l9)		= arg(l8, "-live") 
		val entrada =
			case l9 of
			[n] => ((open_in n)
					handle _ => raise Fail (n^" no existe!"))
			| [] => std_in
			| _ => raise Fail "opcio'n dsconocida!"
		val lexbuf = lexstream entrada
		val expr = prog Tok lexbuf handle _ => errParsing lexbuf
		val _ = findEscape(expr)
		val _ = if arbol then tigerpp.exprAst expr else ()

		val _ = transProg(expr);
        val frags = tigertrans.getResult()
        fun filter_fun_frags (tigerframe.PROC(_)) = true
            | filter_fun_frags _  = false 
        val fun_frags = List.filter filter_fun_frags frags
        val string_frags = List.filter (fn x => not (filter_fun_frags x)) frags

        val canonized_blocks = List.map (fn(tigerframe.PROC({body=b,frame=f})) => ((tigercanon.traceSchedule o tigercanon.basicBlocks o tigercanon.linearize) b, f) |_ => raise Fail "Internal error") fun_frags
        val unpacked_string_flags = List.map (fn(tigerframe.STRING(x)) => x | _ => raise Fail "Internal error") string_frags
        val _ = if inter then tigerinterp.inter true canonized_blocks unpacked_string_flags else ()

         val canonized_blocks = List.map (fn(tigerframe.PROC({body=b,frame=f})) => ((tigercanon.traceSchedule o tigercanon.basicBlocks o tigercanon.linearize) b, f) |_ => raise Fail "Internal error") fun_frags

         val folded_canonized_blocks = List.map (fn(stm_ls, f) => ((map tigerfold.foldStm stm_ls), f)) canonized_blocks

         val _ = if fold then tigerinterp.inter true folded_canonized_blocks unpacked_string_flags else ()

         val assem_trees = List.map (fn(stm_list, f) => 
                             let val asm_without_prolog = List.concat (List.map (fn(stm) => tigercodegen.codegen f stm) stm_list)
                             in (tigerframe.procEntryExit3(f, asm_without_prolog), f)
                             end) canonized_blocks

         val asm_formatter = tigerassem.format(tigertemp.makeString)

         val _ = if code then (List.app (fn(({prolog=p,body=b,epilog=e}, f)) => 
                            let val bodies_w_format = List.map asm_formatter b
                            in print p; map print bodies_w_format; print e
                            end) assem_trees)
                         else ()

        val fgraphs_with_frames = List.map (fn({body=b,...}, f) => (tigerflowgraph.instrs2graph b, f)) assem_trees
        val fgraphs = List.map (#1) fgraphs_with_frames
        fun print_fgraph(fg) = let
            val defs_list = List.map (fn((tigerflowgraph.FGRAPH({def=ds,...}),_)) => ds) fgraphs
            val uses_list = List.map (fn((tigerflowgraph.FGRAPH({use=us,...}),_)) => us) fgraphs
            val ismove_list = List.map (fn((tigerflowgraph.FGRAPH({ismove=i,...}),_)) => i) fgraphs
            val nodes_graph_list = List.map (fn((tigerflowgraph.FGRAPH({control=g,...}),_)) => tigergraph.nodes g) fgraphs
            fun get_list_nodes_string(ns) = String.concatWith "," (List.map (fn((g,n)) => Int.toString n) ns)
            fun print_node_pred_suc(g,n) = print("Node "^(Int.toString(n))^", Preds: "^get_list_nodes_string(tigergraph.pred(g,n))^ "; Succs: "^get_list_nodes_string(tigergraph.succ(g,n))^"\n")
    
            fun print_defs_dictentry(n, temp_list) = print("Node: "^(Int.toString(n)) ^", Defs: "^(String.concatWith ";" temp_list) ^"\n")
            fun print_uses_dictentry(n, temp_list) = print("Node: "^(Int.toString(n)) ^", Uses: "^(String.concatWith ";" temp_list) ^"\n")
            fun print_ismove_dictentry(n, im) = print("Node: "^(Int.toString(n)) ^", IsMove: "^(Bool.toString(im)) ^"\n")
            val _ = print("Defs of each node: \n")
            val _ = List.app (fn(dic) => Splaymap.app print_defs_dictentry dic) defs_list
            val _ = print("Uses of each node: \n")
            val _ = List.app (fn(dic) => Splaymap.app print_uses_dictentry dic) uses_list
            val _ = print("IsMove of each node: \n")
            val _ = List.app (fn(dic) => Splaymap.app print_ismove_dictentry dic) ismove_list
            val _ = print("Succs and preds of each node: \n")
            val _ = List.app (fn(nodes) => List.app print_node_pred_suc nodes) nodes_graph_list
         in () end

       val _ = if flow then print_fgraph(fgraphs) else ()

       val igraphs = List.map (tigerliveness.interferenceGraph o #1) fgraphs
       
       val _ = if live then List.app (tigerliveness.show o #1) igraphs else ()

       val assigned_ins = ListPair.map tigercolor.main (fgraphs_with_frames, igraphs)
       val prolog_epilog = List.map (fn(({prolog=p,body=b,epilog=e}, f)) => (p, e)) assem_trees
       val _ = List.app (fn((_, map)) => Splaymap.app (fn(t,c)=> print(t ^ ": "^Int.toString(c) ^ "\n")) map) assigned_ins

       (* Print strings *)
       val _ = print(".data\n")
       val _ = List.app (fn(lab, str) => print(lab^":\n"^str^"\n")) unpacked_string_flags

       (* Print code *)
       val _ = print(".text\n")
       val _ =  (ListPair.app (fn((ins, coloring), (prolog,epilog)) => 
                            let val bodies_w_format = List.map asm_formatter ins 
                            in print(prolog); List.app print bodies_w_format; print(epilog)
                            end) (assigned_ins, prolog_epilog))



	in
		print "yes!!\n"
	end	handle Fail s => print("Fail: "^s^"\n")

val _ = main(CommandLine.arguments())
