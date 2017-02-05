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
    val moveList = ref (Splaymap.mkDict(String.compare)) : (tigertemp.temp, int Splayset.set) Splaymap.dict ref
    val getMoves = ref (fn(x) => Splayset.empty(moveOrder))
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

    fun reset_globals() = let
      val _ = precolored := (Splayset.addList(Splayset.empty(String.compare), tigerframe.list_regs))
      val _ = initial := (Splayset.empty(String.compare))
      val _ = spillWorklist := (Splayset.empty(String.compare))
      val _ = spilledNodes := (Splayset.empty(String.compare))
      val _ = coalescedNodes := (Splayset.empty(String.compare))
      val _ = coloredNodes := (Splayset.empty(String.compare))
      val _ = freezeWorklist := (Splayset.empty(String.compare))
      val _ = simplifyWorklist := (Splayset.empty(String.compare))
      val _ = selectStack := [](* : (ref (tigertemp.temp list))*)

      val _ = moveList := (Splaymap.mkDict(String.compare)) 
      val _ = getMoves := (fn(x) => Splayset.empty(moveOrder))
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
            val IGRAPH{graph=ig, gtemp=nodeToTemp, moves=getMovesFun, tnode=tempToNode} = intgraph
            val initial_ls = List.map (nodeToTemp o #2) (nodes ig)
            val _ = initial := Splayset.addList(Splayset.empty(String.compare), initial_ls)
            val _ = initial := Splayset.difference(!initial, !precolored)
            val _ = getMoves := getMovesFun
            val instructions = List.rev(nodes control)
            fun isMoveInstruction(n) = Splaymap.find(ismove,n) 
            fun getInstrMove(MOVE{dst=d,src=s,...}) = [(s, d)]
               |getInstrMove(OPER{dst=ds,src=ss,...}) = List.concat (List.map (fn(s) => List.map (fn(d) => (d, s)) ds) ss)
               |getInstrMove(_) = []

            fun processInstruction((g, instr)) = 
                let val live = ref (liveMap(instr))
                    (*val _ = Splayset.app(fn(s) => (print(s);print(", "))) (!live)*)
                    (*val _ = print("\n")*)
                    val use_i = Splayset.addList(Splayset.empty(String.compare), Splaymap.find(use, instr))  
                    val def_i = Splayset.addList(Splayset.empty(String.compare), Splaymap.find(def, instr))
                    val singleton_i = (Splayset.singleton Int.compare instr)
                    val real_ins = Splaymap.find(nodeToIns, instr)
                    val moves_ins = getInstrMove(real_ins) 
                    val moves_ins_set = Splayset.addList(Splayset.empty(moveOrder), moves_ins)
                    val _ = if isMoveInstruction(instr) 
                            then (let
                               val _ = live := Splayset.difference(!live, use_i)
                               fun getMoveList(n) = case Splaymap.peek(!moveList, n) of SOME(x) => x | NONE => emptyIntSet
                               val _ = Splayset.app (fn(n) => moveList := Splaymap.insert(!moveList, n, Splayset.union(getMoveList(n), singleton_i))) (Splayset.union(use_i, def_i))
                               val _ = worklistMoves := Splayset.union(!worklistMoves, moves_ins_set)
                              in () end)
                            else ()
                    val _ = live := Splayset.union(!live, def_i)
                    val _ = Splayset.app (fn(d) => Splayset.app (fn(l) => addEdge(l, d)) (!live) ) def_i 
                    (* not necessary since we already have the liveMap *)
                in ()
                end 
            

        in List.map processInstruction instructions
        end

    fun nodeMoves(n) = let
        val moveList_n = !getMoves(n)
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
        val selectStack_set = Splayset.addList(Splayset.empty(String.compare), !selectStack)
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
        val _ = degree := Splaymap.insert(!degree, m, d-1)
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
        in Splayset.app (fn(m) => decrementDegree(m)) (adjacent(n))
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
        val _ = print("combining "^u^" and "^v^"\n")
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
        fun aux'(t) = (addEdge(t, u); print("adding edge "^t^" and "^u^"\n");decrementDegree(t))
        val _ = Splayset.app aux' (adjacent(v)) (*handle NotFound => (print("combine, aux'\n"))*)
        (*val _ = if u="T8" orelse v="T8" then (Splayset.app (fn(s) => print(s^", ")) (adjacent(getAlias "T8")); print("\n")) else ()*)
        val degree_u = case Splaymap.peek(!degree, u) of SOME(x) => x | NONE => 0
        val _ = if degree_u >= K andalso Splayset.member(!freezeWorklist, u)
                then (freezeWorklist := Splayset.difference(!freezeWorklist, singleton_u);
                     freezeWorklist := Splayset.union(!spillWorklist, singleton_u))
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
            val v = if getAlias(x)=getAlias(y)
                    then getAlias(x)
                    else getAlias(y)
            val singleton_v = Splayset.singleton String.compare v
            val _ = activeMoves := Splayset.difference(!activeMoves, singleton_m)
            val _ = frozenMoves := Splayset.union(!frozenMoves, singleton_m)
            val _ = if Splayset.isEmpty(nodeMoves(v)) andalso Splaymap.find(!degree, v) < K
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
    (* TODO heuristic *)
        val m = hd(Splayset.listItems(!spillWorklist))
        val singleton_m = Splayset.singleton String.compare m
        val _ = spillWorklist := Splayset.difference(!spillWorklist, singleton_m)
        val _ = simplifyWorklist := Splayset.union(!simplifyWorklist, singleton_m)
      in freezeMoves(m)
      end

    fun assignColors() = let
        val _ = if (List.null(!selectStack))
                then Splayset.app (fn(n) => (color := Splaymap.insert(!color, n, Splaymap.find(!color, getAlias(n))))) (!coalescedNodes)
                else (let
                    (* pop *)
                    val n = hd(!selectStack)        
                    val _ = selectStack := List.tl(!selectStack)
                    val singleton_n = Splayset.singleton String.compare n
                    val okColors = Splayset.addList(Splayset.empty(Int.compare), List.tabulate(K, (fn(x) => x)))
                    fun color_alias(n) = case Splaymap.peek(!color, getAlias(n)) of SOME(x)=>(Splayset.singleton Int.compare x) | NONE => emptyIntSet
(*                    val _ = if n="T9" then Splayset.app (fn(x) => print(Int.toString(x)^" AAA\n\n\n")) (color_alias("T9")) else ()*)
(*                    val _ = if n="T10" then print(getAlias("T8")^" AAAA\n\n\n")  else ()*)
(*                    val _ = if n="T8" then Splayset.app (fn(x) => print(Int.toString(x)^"\n")) (color_alias("T10")) else () *)
                    fun aux(w, set) = if Splayset.member(Splayset.union(!coloredNodes, !precolored), getAlias(w))
                                      then Splayset.difference(set, color_alias(w))
                                      else set
                    val adjList_n = case Splaymap.peek(!adjList, n) of SOME(x) => x | NONE => emptyStringSet
                    (*val _ = if n=getAlias("T8") then Splayset.app (fn(x)=>print(x^"\n")) adjList_n else ()*)
                    val okColors' = Splayset.foldr aux okColors adjList_n
(*                    val _ = if n="T10" then Splayset.app (fn(x)=>print(Int.toString(x)^", ")) okColors' else () *)
                    val _ = if Splayset.isEmpty(okColors')
                            then spilledNodes := Splayset.union(!spilledNodes, singleton_n)
                            else (coloredNodes := Splayset.union(!coloredNodes, singleton_n);
                                 color := Splaymap.insert(!color, n, hd(Splayset.listItems(okColors')));
                                 if n="T8" then print("\n" ^(Int.toString (Splaymap.find(!color, n)) ^"\n")) else ())
                  in assignColors()  end)
      in () end

    fun rewriteProgram(frame, instructions) = let
        fun allocNodesFold(n, map) = Splaymap.insert(map, n, allocLocal frame true)
        val allocatedNodes = Splayset.foldr allocNodesFold (Splaymap.mkDict(String.compare)) (!spilledNodes)
        fun replaceTemp(old, new, ls) = List.map (fn(x) => if x=old then new else x) ls
        val newTemps = ref (Splayset.empty(String.compare))
        fun processInstr(ins as OPER{assem=a, dst=ds, src=ss, jump=j}) = let
            fun processDef(d, (prevs, posts, uses, defs)) = let
                val newTemp = tigertemp.newtemp()
                val _ = newTemps := Splayset.add(!newTemps, newTemp)
                val stackPos = case Splaymap.find(allocatedNodes, d) of
                    InFrame s => s
                    | _ => raise Fail "Internal error, allocated spilled node as register"
                val (prev, post, newUses, newDefs) = if Splayset.member(!spilledNodes, d)
                             then ([], [OPER{assem="movl `s0 "^ Int.toString stackPos ^"(`d0)", src=[newTemp, fp], dst=[], jump=NONE}], [], [newTemp]) 
                             else ([], [], [], [d])
                in (prev@prevs, post@posts, newUses@uses, newDefs@defs) end
            fun processUse(u, (prevs, posts, uses, defs)) = let
                val newTemp = tigertemp.newtemp()
                val _ = newTemps := Splayset.add(!newTemps, newTemp)
                val stackPos = case Splaymap.find(allocatedNodes, u) of
                    InFrame s => s
                    | _ => raise Fail "Internal error, allocated spilled node as register"
                val (prev, post, newUses, newDefs) = if Splayset.member(!spilledNodes, u)
                             then ([OPER{assem="movl "^ Int.toString stackPos^ "(`s0) `d0", src=[fp], dst=[newTemp], jump=NONE}], [], [newTemp], [])
                             else ([], [], [u], [])
                in (prev@prevs, post@posts, newUses@uses, newDefs@defs) end
            val (prev, post, newUses, newDefs) = List.foldr processDef ([], [], [], []) ds
            val (prev', post', newUses', newDefs') = List.foldr processUse ([], [], [], []) ss 
            val newIns = OPER{assem=a, dst=newDefs', src=newUses', jump=j}
        in prev'@[newIns]@post' end

        | processInstr(ins as MOVE{assem=a, dst=dest, src=src}) = let
            fun processDef(d, (prevs, posts, uses, defs)) = let
                val newTemp = tigertemp.newtemp()
                val _ = newTemps := Splayset.add(!newTemps, newTemp)
                val stackPos = case Splaymap.find(allocatedNodes, d) of
                    InFrame s => s
                    | _ => raise Fail "Internal error, allocated spilled node as register"
                val (prev, post, newUses, newDefs) = if Splayset.member(!spilledNodes, d)
                             then ([], [OPER{assem="movl `s0 "^ Int.toString stackPos ^"(`d0)", src=[newTemp, fp], dst=[], jump=NONE}], [], [newTemp])
                             else ([], [], [], [d])
                in (prev@prevs, post@posts, newUses@uses, newDefs@defs) end
            fun processUse(u, (prevs, posts, uses, defs)) = let
                val newTemp = tigertemp.newtemp()
                val _ = newTemps := Splayset.add(!newTemps, newTemp)
                val stackPos = case Splaymap.find(allocatedNodes, u) of
                    InFrame s => s
                    | _ => raise Fail "Internal error, allocated spilled node as register"
                val (prev, post, newUses, newDefs) = if Splayset.member(!spilledNodes, u)
                             then ([OPER{assem="movl "^ Int.toString stackPos^ "(`s0) `d0", src=[fp], dst=[newTemp], jump=NONE}], [], [newTemp], [])
                             else ([], [], [u], [])
                in (prev@prevs, post@posts, newUses@uses, newDefs@defs) end
            val (prev, post, newUses, newDefs) = processDef(dest, ([], [], [], []))
            val (prev', post', newUses', newDefs') = processUse (src, ([], [], [], []))
            val newIns = MOVE{assem=a, dst=hd(newDefs'), src=hd(newUses')}
        in prev'@[newIns]@post' end


        | processInstr(x) = [x]

        val newIns = List.concat (List.map processInstr instructions)
        val _ = spilledNodes := Splayset.empty(String.compare)
        val _ = initial := Splayset.union(Splayset.union(!coloredNodes, !coalescedNodes), !newTemps)
        val _ = coloredNodes := Splayset.empty(String.compare)
        val _ = coalescedNodes := Splayset.empty(String.compare)
        in (frame, newIns) end


    fun assign_registers(instructions) = let
        val color_to_reg = Splayset.foldr (fn(reg,newMap) => Splaymap.insert(newMap, Splaymap.find(!color, reg), reg)) (Splaymap.mkDict(Int.compare)) (!precolored)
        fun replace_temp_with_reg(t) = Splaymap.find(color_to_reg, Splaymap.find(!color, t))
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
        
            

    fun main(((flowgraph, nodeToIns), frame), (intgraph, liveMap)) = let
        val _ = reset_globals()
        val FGRAPH({control, def, use, ismove}) = flowgraph
        val instructions_nodes = List.rev(nodes control)
        val instructions = map (fn((g,n))=>Splaymap.find(nodeToIns, n)) instructions_nodes
        val _ = build((flowgraph,nodeToIns), (intgraph, liveMap)) (*handle NotFound => (print("build\n");[]) *)
        val _ = (Splayset.app (fn(s) => print(s^", ")) (adjacent(getAlias "T8")); print("\n"))
        val _ = makeWorklist() (*handle NotFound => (print("makeWorkList\n")) *)
        fun aux() = let
            val _ = if not (Splayset.isEmpty(!simplifyWorklist))
                    then (simplify()) (*handle NotFound => (print("simplify")) *)
                    else if not (Splayset.isEmpty(!worklistMoves))
                         then coalesce()(* handle NotFound => (print("coalesce"))*)
                         else if not (Splayset.isEmpty(!freezeWorklist))
                              then freeze() (*handle NotFound => (print("freeze")) *)
                              else if not (Splayset.isEmpty(!spillWorklist))
                                   then selectSpill() (*handle NotFound => (print("selectSpill")) *)
                                   else ()
             in () end 
         val _ = aux() (*handle NotFound => (print("aux"))*)
         val _ = while (not (Splayset.isEmpty(!simplifyWorklist)) orelse not (Splayset.isEmpty(!worklistMoves))
                       orelse not (Splayset.isEmpty(!freezeWorklist)) orelse not (Splayset.isEmpty(!spillWorklist)))
                 do (aux()) (*handle NotFound => (print("aux while\n")) *)
         val _ = assignColors()
         
         val needsRewrite = not (Splayset.isEmpty(!spilledNodes))
         val (frame', newIns) = if needsRewrite
                                then rewriteProgram(frame, instructions)
                                else (frame, instructions)
         val _ = if needsRewrite 
                 then main(((flowgraph, nodeToIns), frame'), (intgraph, liveMap))
                 else ([], Splaymap.mkDict(String.compare))

         val assigned_ins = assign_registers(newIns)
         val simplified_ins = delete_redundant_moves(assigned_ins)

        val _ = (Splayset.app (fn(s) => print(s^", ")) (adjacent(getAlias "T8")); print("\n"))
        val _ = print(getAlias "T8" ^"\n")
         in (List.rev simplified_ins, !color) end
end


