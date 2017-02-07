structure tigercolor =
struct

    open tigergraph
    open tigerflowgraph
    open tigerliveness
    open tigerframe

    val emptyStringSet = Splayset.empty(String.compare)
    val emptyIntSet = Splayset.empty(Int.compare)
    
    val K = List.length(tigerframe.usable_regs)
    val precolored = ref (Splayset.addList(Splayset.empty(String.compare), tigerframe.list_regs))
    val initial = ref (Splayset.empty(String.compare))
    val spillWorklist = ref (Splayset.empty(String.compare))
    val spilledNodes = ref (Splayset.empty(String.compare))
    val coalescedNodes = ref (Splayset.empty(String.compare))
    val coloredNodes = ref (Splayset.empty(String.compare))
    val freezeWorklist = ref (Splayset.empty(String.compare))
    val simplifyWorklist = ref (Splayset.empty(String.compare))
    val selectStack = ref [](* : (ref (tigertemp.temp list))*)

    fun moveOrder((from1,to1),(from2,to2)) = if from1=from2 then String.compare(to1,to2) else String.compare(from1,from2)
    val moveList = ref (Splaymap.mkDict(String.compare)) : (tigertemp.temp, (tigertemp.temp * tigertemp.temp) Splayset.set) Splaymap.dict ref
(*    val getMoves = ref (fn(x) => Splayset.empty(moveOrder))*)
    val alias = ref (Splaymap.mkDict(String.compare)) : (tigertemp.temp, tigertemp.temp) Splaymap.dict ref
    val color = ref (Splaymap.mkDict(String.compare)) : (tigertemp.temp, int) Splaymap.dict ref
    val _ = List.app (fn(n) => color := Splaymap.insert(!color, List.nth(tigerframe.usable_regs, n), n)) (List.tabulate(K, (fn(x) => x)))
    val _ = List.app (fn(n) => color := Splaymap.insert(!color, List.nth(tigerframe.non_usable_regs, n), n+K)) (List.tabulate(List.length(non_usable_regs), (fn(x) => x)))
(*    val _ = List.app (fn(map) => Splaymap.app (fn(t,c)=> print(t ^ ": "^Int.toString(c) ^ "\n")) map) [!color] *)
    val coalescedMoves = ref (Splayset.empty(moveOrder))
    val constrainedMoves = ref (Splayset.empty(moveOrder))
    val frozenMoves = ref (Splayset.empty(moveOrder))
    val worklistMoves = ref (Splayset.empty(moveOrder))
    val activeMoves = ref (Splayset.empty(moveOrder))
    fun edgeOrder(x) = moveOrder(x)
    (* set of tuples representing edges *)
    val adjSet = ref (Splayset.empty(edgeOrder))

    (* map of nodes to nodes, representing adjacency *)
    val adjList = ref (Splaymap.mkDict(String.compare)) : (tigertemp.temp, tigertemp.temp Splayset.set) Splaymap.dict ref
    (* map of nodes to degree (int) *)
    val degree = ref (Splaymap.mkDict(String.compare)) : (tigertemp.temp, int) Splaymap.dict ref

    fun reset_globals(init_initial) = let
      val _ = precolored := (Splayset.addList(Splayset.empty(String.compare), tigerframe.list_regs))
      (*initial cannot have precolored temporaries *)
      val _ = initial := Splayset.difference(init_initial, !precolored)
      val _ = spillWorklist := (Splayset.empty(String.compare))
      val _ = spilledNodes := (Splayset.empty(String.compare))
      val _ = coalescedNodes := (Splayset.empty(String.compare))
      val _ = coloredNodes := (Splayset.empty(String.compare))
      val _ = freezeWorklist := (Splayset.empty(String.compare))
      val _ = simplifyWorklist := (Splayset.empty(String.compare))
      val _ = selectStack := [](* : (ref (tigertemp.temp list))*)

      val _ = moveList := (Splaymap.mkDict(String.compare)) 
(*      val _ = getMoves := (fn(x) => Splayset.empty(moveOrder))*)
      val _ = alias := (Splaymap.mkDict(String.compare))
      val _ = color := (Splaymap.mkDict(String.compare))
      val _ = List.app (fn(n) => color := Splaymap.insert(!color, List.nth(tigerframe.usable_regs, n), n)) (List.tabulate(K, (fn(x) => x)))
      val _ = List.app (fn(n) => color := Splaymap.insert(!color, List.nth(tigerframe.non_usable_regs, n), n+K)) (List.tabulate(List.length(non_usable_regs), (fn(x) => x)))
  (*    val _ = List.app (fn(map) => Splaymap.app (fn(t,c)=> print(t ^ ": "^Int.toString(c) ^ "\n")) map) [!color] *)
      val _ = coalescedMoves := (Splayset.empty(moveOrder))
      val _ = constrainedMoves := (Splayset.empty(moveOrder))
      val _ = frozenMoves := (Splayset.empty(moveOrder))
      val _ = worklistMoves := (Splayset.empty(moveOrder))
      val _ = activeMoves := (Splayset.empty(moveOrder))
      (* set of tuples representing edges *)
      val _ = adjSet := (Splayset.empty(edgeOrder))

      (* map of nodes to nodes, representing adjacency *)
      val _ = adjList := (Splaymap.mkDict(String.compare))
      (* map of nodes to degree (int) *)
      val _ = degree := (Splaymap.mkDict(String.compare))

    in () end



    fun addEdge(u, v) = let 
        val _ = if Splayset.member(!adjSet, (u,v)) orelse u=v then ()
                else
                    let val _ = adjSet := Splayset.addList(!adjSet, [(u,v),(v,u)])
 (*                       val _ = if u="T8" orelse v="T8" then print("("^u^", "^v^")\n") else ()*)
                        val adjList_u = case Splaymap.peek(!adjList, u) of SOME(x) => x | NONE => emptyStringSet
                        val adjList_v = case Splaymap.peek(!adjList, v) of SOME(x) => x | NONE => emptyStringSet
                        val degree_u = case Splaymap.peek(!degree, u) of SOME(x) => x | NONE => 0
                        val degree_v = case Splaymap.peek(!degree, v) of SOME(x) => x | NONE => 0
                        val singleton_v = Splayset.singleton String.compare v
                        val singleton_u = Splayset.singleton String.compare u
                        val _ = if (not (Splayset.member(!precolored, u))) then
                                  (adjList := Splaymap.insert(!adjList, u, Splayset.union(adjList_u, singleton_v));
(*                                   if u="T8" orelse v="T8" then print("aa("^u^", "^v^")\n") else ();*)
                                   degree := Splaymap.insert(!degree, u, degree_u + 1))
                                 else ()
                        val _ = if (not (Splayset.member(!precolored, v))) then
                                  (adjList := Splaymap.insert(!adjList, v, Splayset.union(adjList_v, singleton_u));
(*                                   if u="T8" orelse v="T8" then print("bb("^u^", "^v^")\n") else ();*)
                                   degree := Splaymap.insert(!degree, v, degree_v + 1))
                                 else ()
                    in () end
        in () end 

                     
                      
    
    fun build((flowgraph, nodeToIns), (intgraph, liveMap)) =
        let val FGRAPH({control, def, use, ismove}) = flowgraph
(*            val IGRAPH{graph=ig, gtemp=nodeToTemp, moves=getMovesFun, tnode=tempToNode} = intgraph*)
(*           val _ = getMoves := getMovesFun*)
            val instructions = List.rev(nodes control)
            fun isMoveInstruction(n) = Splaymap.find(ismove,n) 
            fun getInstrMove(MOVE{dst=d,src=s,...}) = [(s, d)]
               |getInstrMove(_) = []

            fun processInstruction((g, instr)) = 
                let val live = (liveMap(instr))
                    (*val _ = Splayset.app(fn(s) => (print(s);print(", "))) (!live)*)
                    (*val _ = print("\n")*)
                    val use_i_list = Splaymap.find(use, instr)
                    val def_i_list = Splaymap.find(def, instr)
                    val use_i_set = Splayset.addList(Splayset.empty(String.compare), use_i_list)  
                    val def_i_set = Splayset.addList(Splayset.empty(String.compare), def_i_list)
                    val singleton_i = (Splayset.singleton Int.compare instr)
                    val real_ins = Splaymap.find(nodeToIns, instr)
                    val moves_ins = getInstrMove(real_ins) 
                    val moves_ins_set = Splayset.addList(Splayset.empty(moveOrder), moves_ins)
                    val _ = if isMoveInstruction(instr) 
                            then (let
                               fun getMoveList(n) = case Splaymap.peek(!moveList, n) of SOME(x) => x | NONE => Splayset.empty(moveOrder)
                               val move_i = (hd(use_i_list), hd(def_i_list))
                               val move_i_singleton = Splayset.singleton moveOrder move_i
                               val _ = Splayset.app (fn(n) => moveList := Splaymap.insert(!moveList, n, Splayset.union(getMoveList(n), move_i_singleton))) (Splayset.union(use_i_set, def_i_set))
                               val _ = worklistMoves := Splayset.union(!worklistMoves, moves_ins_set)
                              in () end)
                            else ()
                    val _ = Splayset.app (fn(d) => Splayset.app (fn(l) => addEdge(l, d)) live ) def_i_set
                in ()
                end 
        in List.map processInstruction instructions
        end

    fun nodeMoves(n) = let
        val moveList_n = case Splaymap.peek(!moveList, n) of SOME(x) => x | NONE => (Splayset.empty(moveOrder))
        in Splayset.intersection(moveList_n, Splayset.union(!activeMoves, !worklistMoves))
        end

    fun moveRelated(n) = not (Splayset.isEmpty(nodeMoves(n)))

    fun makeWorklist() = 
         let fun process(t) =
                let val singleton_t = Splayset.singleton String.compare t
                    val _ = initial := Splayset.difference(!initial, singleton_t)
                    val degree_t = case Splaymap.peek(!degree, t) of SOME(x) => x | NONE => 0
                    val set_to_modify = if degree_t >= K then spillWorklist else (if moveRelated(t) then freezeWorklist else simplifyWorklist)
                    val _ = set_to_modify := Splayset.union(!set_to_modify, singleton_t)

                 in () end
             val orig_initial = (!initial)
         in Splayset.app process orig_initial
         end

    fun adjacent(n) = let
        val adjList_n = case Splaymap.peek(!adjList, n) of SOME(x) => x | NONE => emptyStringSet
        val selectStack_set = Splayset.addList(emptyStringSet, !selectStack)
        in Splayset.difference(adjList_n, Splayset.union(selectStack_set, !coalescedNodes))
        end

    fun enableMoves(nodes) = let
        fun processMove(m as (from,to)) = let
            val singleton_m = Splayset.singleton moveOrder m
            val _  = if Splayset.member(!activeMoves, m) then
                    (activeMoves := Splayset.difference(!activeMoves, singleton_m);
                     worklistMoves := Splayset.union(!worklistMoves, singleton_m))
                    else ()
            in () end
        in Splayset.app (fn(n) => Splayset.app processMove (nodeMoves(n))) nodes
        end



    fun decrementDegree(m) = let
        val d = case Splaymap.peek(!degree, m) of SOME(x) => x | NONE => 0
        val singleton_m = Splayset.singleton String.compare m
        val new_d = if d=0 then 0 else d-1
        val _ = degree := Splaymap.insert(!degree, m, new_d)
        (*val _ = if d=0 then (raise Fail ("decrementDegree de nodo con degree 0: "^m^"\n")) else ()*)
        val _ = if d=K then (enableMoves(Splayset.union(singleton_m, adjacent(m)));
                            spillWorklist := Splayset.difference(!spillWorklist, singleton_m);
                            if moveRelated(m) then freezeWorklist := Splayset.union(!freezeWorklist, singleton_m)
                                              else simplifyWorklist := Splayset.union(!simplifyWorklist, singleton_m))
                else ()
        in () end


    fun simplify() = let
        val n = List.hd(Splayset.listItems(!simplifyWorklist))
        val singleton_n = Splayset.singleton String.compare n
        val _ = simplifyWorklist := Splayset.difference(!simplifyWorklist, singleton_n)
        (* push *)
        val _ = selectStack := n::(!selectStack)
        in Splayset.app decrementDegree (adjacent(n))
        end

    fun getAlias(n) = if Splayset.member(!coalescedNodes, n) 
                      then getAlias(Splaymap.find(!alias, n))
                      else n

    fun addWorkList(u) = if (not (Splayset.member(!precolored, u)) andalso
                                       not (moveRelated(u)) andalso 
                                       Splaymap.find(!degree, u) < K
                                      )
                                   then (let
                                       val singleton_u = Splayset.singleton String.compare u
                                     in (freezeWorklist := Splayset.difference(!freezeWorklist, singleton_u);
                                         simplifyWorklist := Splayset.union(!simplifyWorklist, singleton_u))
                                     end)
                                   else ()

    fun ok(t, r) = let 
        val degree_t = case Splaymap.peek(!degree, t) of SOME(x) => x | NONE => 0
      in degree_t < K orelse 
         Splayset.member(!precolored, t) orelse 
         Splayset.member(!adjSet, (t,r)) end

    fun conservative(nodes) = let
        fun get_degree(n) = case Splaymap.peek(!degree, n) of SOME(x)=>x |NONE => 0
        fun aux(n, k) = if get_degree(n) >= K then k+1 else k
        val k = Splayset.foldr aux 0 nodes
      in (k < K)
      end

    fun combine((u,v)) = let
(*        val _ = print("combining "^u^" and "^v^"\n")*)
        val singleton_u = Splayset.singleton String.compare u
        val singleton_v = Splayset.singleton String.compare v
        val _ = if Splayset.member(!freezeWorklist, v)
                then freezeWorklist := Splayset.difference(!freezeWorklist, singleton_v) 
                else spillWorklist := Splayset.difference(!spillWorklist, singleton_v) 
        val _ = coalescedNodes := Splayset.union(!coalescedNodes, singleton_v)
        val _ = alias := Splaymap.insert(!alias, v, u)
        val aux = Splayset.union(Splaymap.find(!moveList, u), Splaymap.find(!moveList, v)) (*handle NotFound => (print("combine, aux\n"); emptyIntSet)*)
        val _ = moveList := Splaymap.insert(!moveList, u, aux)
        val _ = enableMoves(singleton_v)
        fun aux'(t) = (addEdge(t, u);decrementDegree(t))
        val _ = Splayset.app aux' (adjacent(v)) (*handle NotFound => (print("combine, aux'\n"))*)
        (*val _ = if u="T8" orelse v="T8" then (Splayset.app (fn(s) => print(s^", ")) (adjacent(getAlias "T8")); print("\n")) else ()*)
        val degree_u = case Splaymap.peek(!degree, u) of SOME(x) => x | NONE => 0
        val _ = if degree_u >= K andalso Splayset.member(!freezeWorklist, u)
                then (freezeWorklist := Splayset.difference(!freezeWorklist, singleton_u);
                     spillWorklist := Splayset.union(!spillWorklist, singleton_u))
                else ()
(*        val _ = if u="T9" andalso v="T8" then Splayset.app (fn(t)=>print(t^"\n\n\n\n")) (Splaymap.find(!adjList, "T10")) else ()*)
      in () end

    
    fun coalesce() = let
        val m as (x, y) = List.hd(Splayset.listItems(!worklistMoves))
        val singleton_m = Splayset.singleton moveOrder m
        val (x', y') = (getAlias(x), getAlias(y)) (*handle NotFound => (print("getAlias\n"); ("x", "x")) *)
        val (u, v) = if Splayset.member(!precolored, y) then (y',x') else (x',y')
        val _ = worklistMoves := Splayset.difference(!worklistMoves, singleton_m)
        val _ = if (u=v) then (coalescedMoves := Splayset.union(!coalescedMoves, singleton_m);
                               addWorkList(u) (*handle NotFound => print("addWorklist\n")*))
                else (if (Splayset.member(!precolored, v) orelse Splayset.member(!adjSet, (u,v)))
                      then (constrainedMoves := Splayset.union(!constrainedMoves, singleton_m);
                           addWorkList(u) (*handle NotFound => print("addWorkList\n")*);
                           addWorkList(v) (*handle NotFound => print("addWorkList\n")*))
                      else (if (Splayset.member(!precolored, u) andalso (List.all ok (List.map (fn(t) => (t,u)) (Splayset.listItems(adjacent(v))))))
                               orelse (not (Splayset.member(!precolored, u)) andalso conservative(Splayset.union(adjacent(u), adjacent(v))))
                            then (coalescedMoves := Splayset.union(!coalescedMoves, singleton_m); 
(*                                  if u="T8" orelse v="T8" then print(u^", "^v^"\n") else ();*)
                                  combine((u,v)) (*handle NotFound => print("combine\n") *);
(*                                  if u="T8" orelse v="T8" then print(getAlias(u)^", "^getAlias(v)^"\n") else ();*)
                                  addWorkList(u) (*handle NotFound => print("addWorkList\n")*) ) 
                            else
                                activeMoves := Splayset.union(!activeMoves, singleton_m)))
                         
        in () end

    fun freezeMoves(u) = let
        fun aux(m as (x, y)) = let
            val singleton_m = Splayset.singleton moveOrder m
            val v = if getAlias(y)=getAlias(u)
                    then getAlias(x)
                    else getAlias(y)
            val singleton_v = Splayset.singleton String.compare v
            val _ = activeMoves := Splayset.difference(!activeMoves, singleton_m)
            val _ = frozenMoves := Splayset.union(!frozenMoves, singleton_m)
            val degree_v = case Splaymap.peek(!degree, v) of SOME(x) => x | NONE => 0
            val _ = if Splayset.isEmpty(nodeMoves(v)) andalso degree_v < K
                    then (freezeWorklist := Splayset.difference(!freezeWorklist, singleton_v);
                         simplifyWorklist := Splayset.union(!simplifyWorklist, singleton_v))
                    else ()
          in () end
        val _ = Splayset.app aux (nodeMoves(u))
      in () end 

    fun freeze() = let
        val u = List.hd(Splayset.listItems(!freezeWorklist))
        val singleton_u = Splayset.singleton String.compare u
        val _ = freezeWorklist := Splayset.difference(!freezeWorklist, singleton_u)
        val _ = simplifyWorklist := Splayset.union(!simplifyWorklist, singleton_u)
      in freezeMoves(u)
      end

    fun selectSpill() = let
    (* heuristic: select the temporaries created earlier, i.e: t1 is better than t200 *)
        val ordered_spills = Listsort.sort(String.compare) (Splayset.listItems(!spillWorklist))
        val m = hd(ordered_spills)
        val singleton_m = Splayset.singleton String.compare m
        val _ = spillWorklist := Splayset.difference(!spillWorklist, singleton_m)
        val _ = simplifyWorklist := Splayset.union(!simplifyWorklist, singleton_m)
      in freezeMoves(m)
      end

    fun assignColors() = let
        val _ = if (List.null(!selectStack))
                then Splayset.app (fn(n) => (color := Splaymap.insert(!color, n, Splaymap.find(!color, getAlias(n)) handle NotFound => (print(n ^ ", alias: "^getAlias(n)^"\n");0)))) (!coalescedNodes)
                else (let
                    (* pop *)
                    val n = hd(!selectStack)        
                    val _ = selectStack := List.tl(!selectStack)
                    val singleton_n = Splayset.singleton String.compare n
                    val okColors = Splayset.addList(Splayset.empty(Int.compare), List.tabulate(K, (fn(x) => x)))
                    (*fun color_alias(n) = case Splaymap.peek(!color, getAlias(n)) of SOME(x)=>(Splayset.singleton Int.compare x) | NONE => emptyIntSet*)
                    fun color_alias(n) = Splayset.singleton Int.compare (Splaymap.find(!color, getAlias(n)))
                    fun aux(w, set) = if Splayset.member(Splayset.union(!coloredNodes, !precolored), getAlias(w))
                                      then Splayset.difference(set, color_alias(w))
                                      else set
                    val adjList_n = case Splaymap.peek(!adjList, n) of SOME(x) => x | NONE => emptyStringSet
                    val okColors' = Splayset.foldr aux okColors adjList_n
                    val _ = if Splayset.isEmpty(okColors')
                            then spilledNodes := Splayset.union(!spilledNodes, singleton_n)
                            else (coloredNodes := Splayset.union(!coloredNodes, singleton_n);
                                 color := Splaymap.insert(!color, n, hd(Splayset.listItems(okColors'))))
                  in assignColors()  end)
      in () end

    fun rewriteProgram(frame, instructions) = let
        fun allocNodesFold(n, map) = Splaymap.insert(map, n, allocLocal frame true)
        val allocatedNodes = Splayset.foldr allocNodesFold (Splaymap.mkDict(String.compare)) (!spilledNodes)
        val newTemps = ref (Splayset.empty(String.compare))
        fun processInstr(ins as OPER{assem=a, dst=ds, src=ss, jump=j}) = let
            fun processDef(d, (prevs, posts, uses, defs)) = 
                if not (Splayset.member(!spilledNodes, d))
                then (prevs, posts, uses, d::defs)
                else let
                    val newTemp = tigertemp.newtemp()
                    val _ = newTemps := Splayset.add(!newTemps, newTemp)
                    val stackPos = case Splaymap.find(allocatedNodes, d) of
                        (InFrame s) => s
                        |_ => raise Fail "Internal error, allocated spilled node as register"
                    val (prev, post, newUses, newDefs) = 
                        ([], [OPER{assem="movl `s0, "^ Int.toString stackPos ^"(`s1)", src=[newTemp, fp], dst=[], jump=NONE}], [], [newTemp]) 

                  in (prev@prevs, post@posts, newUses@uses, newDefs@defs) end
            fun processUse(u, (prevs, posts, uses, defs)) =
                if not (Splayset.member(!spilledNodes, u))
                then (prevs, posts, u::uses, defs)
                else let
                    val newTemp = tigertemp.newtemp()
                    val _ = newTemps := Splayset.add(!newTemps, newTemp)
                    val stackPos = case Splaymap.find(allocatedNodes, u) of
                        (InFrame s) => s
                        |_ => raise Fail "Internal error, allocated spilled node as register"
                    val (prev, post, newUses, newDefs) = 
                        ([OPER{assem="movl "^ Int.toString stackPos^ "(`s0), `d0", src=[fp], dst=[newTemp], jump=NONE}], [], [newTemp], [])
                  in (prev@prevs, post@posts, newUses@uses, newDefs@defs) end

            val (_, post, _, newDefs) = List.foldr processDef ([], [], [], []) ds
            val (prev, _, newUses, _) = List.foldr processUse ([], [], [], []) ss 
            val newIns = OPER{assem=a, dst=newDefs, src=newUses, jump=j}
        in prev@[newIns]@post end

        | processInstr(ins as MOVE{assem=a, dst=dest, src=src}) = let
            fun processDef(d, (prevs, posts, uses, defs)) =
                if not (Splayset.member(!spilledNodes, d))
                then (prevs, posts, uses, d::defs)
                else let
                    val newTemp = tigertemp.newtemp()
                    val _ = newTemps := Splayset.add(!newTemps, newTemp)
                    val stackPos = case Splaymap.find(allocatedNodes, d) of
                        (InFrame s) => s
                        |_ => raise Fail "Internal error, allocated spilled node as register"
                    val (prev, post, newUses, newDefs) = 
                        ([], [OPER{assem="movl `s0, "^ Int.toString stackPos ^"(`s1)", src=[newTemp, fp], dst=[], jump=NONE}], [], [newTemp])
                  in (prev@prevs, post@posts, newUses@uses, newDefs@defs) end
            fun processUse(u, (prevs, posts, uses, defs)) =
                if not (Splayset.member(!spilledNodes, u))
                then (prevs, posts, u::uses, defs)
                else let
                    val newTemp = tigertemp.newtemp()
                    val _ = newTemps := Splayset.add(!newTemps, newTemp)
                    val stackPos = case Splaymap.find(allocatedNodes, u) of
                        (InFrame s) => s
                        |_ => raise Fail "Internal error, allocated spilled node as register"
                    val (prev, post, newUses, newDefs) = 
                        ([OPER{assem="movl "^ Int.toString stackPos^ "(`s0), `d0", src=[fp], dst=[newTemp], jump=NONE}], [], [newTemp], [])
                  in (prev@prevs, post@posts, newUses@uses, newDefs@defs) end
            val (_, post, _, newDefs) = processDef(dest, ([], [], [], []))
            val (prev, _, newUses, _) = processUse (src, ([], [], [], []))
            val _ = if List.length(newDefs) <> 1 orelse List.length(newUses) <> 1 then raise Fail "Internal error rewriteProgram tigercolor" else ()
            val newIns = MOVE{assem=a, dst=hd(newDefs), src=hd(newUses)}
        in prev@[newIns]@post end


        | processInstr(x) = [x]

        val newIns = List.concat (List.map processInstr instructions)
        val _ = spilledNodes := Splayset.empty(String.compare)
        val _ = initial := Splayset.union(Splayset.union(!coloredNodes, !coalescedNodes), !newTemps)
        val _ = coloredNodes := Splayset.empty(String.compare)
        val _ = coalescedNodes := Splayset.empty(String.compare)
        in (frame, newIns, !initial) end


    fun assign_registers(instructions) = let
        val color_to_reg = Splayset.foldr (fn(reg,newMap) => Splaymap.insert(newMap, Splaymap.find(!color, reg), reg)) (Splaymap.mkDict(Int.compare)) (!precolored)
        fun replace_temp_with_reg(t) = Splaymap.find(color_to_reg, Splaymap.find(!color, t) (*handle NotFound => (print("hola\n");0)*) )
        fun assignInstr(OPER{assem=a, dst=ds, src=ss, jump=j}) = let
            val newDst = List.map replace_temp_with_reg ds
            val newSrc = List.map replace_temp_with_reg ss
          in OPER{assem=a, dst=newDst, src=newSrc, jump=j} end
         | assignInstr(MOVE{assem=a, dst=d, src=s}) = let
            val newDst = replace_temp_with_reg d
            val newSrc = replace_temp_with_reg s
          in MOVE{assem=a, dst=newDst, src=newSrc} end
         | assignInstr(x) = x
        
      in List.map assignInstr instructions end

    fun delete_redundant_moves(instructions) = let
         fun is_redundant(MOVE{assem=a, dst=d, src=s}) = d=s
             | is_redundant(_) = false
         in List.filter (fn(i) => not (is_redundant i)) instructions end
        
            

(* This main' is for recursive calls. It uses the 'initial' passed as an argument. instruction_list is a list of tigerassem.instr *)
    fun main'(instruction_list, frame, initial') = let
        val _ = reset_globals(initial')


        val (flowgraph, nodeToIns) = tigerflowgraph.instrs2graph instruction_list
        val (intgraph, liveMap) = tigerliveness.interferenceGraph flowgraph

        val FGRAPH({control, def, use, ismove}) = flowgraph
        val IGRAPH{graph=ig, gtemp=nodeToTemp, moves=getMovesFun, tnode=tempToNode} = intgraph
        val nodes_ig = List.map (nodeToTemp o #2) (nodes ig)
(*        val _ = print("Nodes igraph: \n")
        val _ = List.app (fn(x) => print(x^", ")) (Listsort.sort String.compare nodes_ig)
        val _ = print("\n")
        val _ = print("initial items: \n")
        val _ = List.app (fn(x) => print(x^", ")) (Listsort.sort String.compare (Splayset.listItems (!initial)))
        val _ = print("\n")*)

        (* We don't reverse the instructions here, because this var is only used in rewriteProgram() *)
        val instructions_nodes = (nodes control)
        val instructions = map (fn((g,n))=>Splaymap.find(nodeToIns, n)) instructions_nodes (*handle NotFound =>(print("nodeToIns\n");[])*)
        
        val _ = build((flowgraph,nodeToIns), (intgraph, liveMap)) (*handle NotFound => (print("build\n");[]) *)
        val _ = makeWorklist() (*handle NotFound => (print("makeWorkList\n")) *)
        
        fun aux() = let
            val _ = if not (Splayset.isEmpty(!simplifyWorklist))
                    then (simplify()) (*handle NotFound => (print("simplify")) *)
                    else if not (Splayset.isEmpty(!worklistMoves))
                         then (coalesce())(* handle NotFound => (print("coalesce"))*)
                         else if not (Splayset.isEmpty(!freezeWorklist))
                              then freeze() (*handle NotFound => (print("freeze")) *)
                              else if not (Splayset.isEmpty(!spillWorklist))
                                   then selectSpill() (*handle NotFound => (print("selectSpill"))*)
                                   else ()
             in () end 
         val _ = aux() (*handle NotFound => (print("aux"))*)
         val _ = while (not (Splayset.isEmpty(!simplifyWorklist)) orelse not (Splayset.isEmpty(!worklistMoves))
                       orelse not (Splayset.isEmpty(!freezeWorklist)) orelse not (Splayset.isEmpty(!spillWorklist)))
                 do (aux()) (*handle NotFound => (print("aux while\n")) *)
         val _ = assignColors() (*handle NotFound => print("assignColors")*)
         
 (*       val _ = List.app (fn(x) => print(x^", ")) (Listsort.sort String.compare (Splayset.listItems newInitial))*)
(*        val _ = print("\n")*)
(*         val _  = Splaymap.app(fn(k,v) => print("Temp: "^k^", Color: "^(Int.toString(v))^"\n")) (!color)*)
         val needsRewrite = not (Splayset.isEmpty(!spilledNodes))

         in if needsRewrite
            then (let val (frame', newIns, newInitial) = rewriteProgram(frame, instructions)
                  in main'(newIns, frame', newInitial) (*handle NotFound => (print("rewriteProgram\n"); (frame, instructions,!initial))*)
                  end)
            else (instructions, !color)
        end


    (* This is the main called from other modules. It initializes initial. It takes as an argument instruction_list=output of procEntryExit3*)
    fun main(instruction_list, frame) = let
        val _ = reset_globals(emptyStringSet)
        val {prolog=p,body=b,epilog=e} = instruction_list

        val (flowgraph, nodeToIns) = tigerflowgraph.instrs2graph b
        val (intgraph, liveMap) = tigerliveness.interferenceGraph flowgraph

        (*Initalize var initial *)
        val IGRAPH{graph=ig, gtemp=nodeToTemp, moves=getMovesFun, tnode=tempToNode} = intgraph
        val initial_ls = List.map (nodeToTemp o #2) (nodes ig)
(*        val _ = List.app (fn(x) => print(x^", ")) (Listsort.sort String.compare initial_ls)*)
 (*       val _ = print("\n")*)
        val _ = initial := Splayset.addList(Splayset.empty(String.compare), initial_ls)
        val _ = initial := Splayset.difference(!initial, !precolored)
 
        val (newIns, final_color) = main'(b, frame, !initial)
        val assigned_ins = assign_registers(newIns) (*handle NotFound => (print("assign_registers\n");newIns)*)
        val simplified_ins = delete_redundant_moves(assigned_ins)(* handle NotFound => (print("delete_redundant_moves\n");newIns)*)

     in (simplified_ins, final_color)
     end
end


