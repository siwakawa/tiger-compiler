structure tigercolor =
struct

    open tigergraph
    open tigerflowgraph
    open tigerliveness
    
    val K = List.length(tigerframe.list_regs)
    val precolored = ref (Splayset.addList(Splayset.empty(String.compare), tigerframe.list_regs))
    val spillWorklist = ref (Splayset.empty(String.compare))
    val spilledNodes = ref (Splayset.empty(String.compare))
    val coalescedNodes = ref (Splayset.empty(String.compare))
    val coloredNodes = ref (Splayset.empty(String.compare))
    val freezeWorklist = ref (Splayset.empty(String.compare))
    val simplifyWorklist = ref (Splayset.empty(String.compare))
    val selectStack = ref [](* : (ref (tigertemp.temp list))*)

    fun moveOrder((from1,to1),(from2,to2)) = if from1=from2 then String.compare(to1,to2) else String.compare(from1,from2)
    val moveList = ref (Splaymap.mkDict(String.compare)) : (tigertemp.temp, int Splayset.set) Splaymap.dict ref
    val alias = ref (Splaymap.mkDict(String.compare)) : (tigertemp.temp, tigertemp.temp) Splaymap.dict ref
    val color = ref (Splaymap.mkDict(String.compare)) : (tigertemp.temp, int) Splaymap.dict ref
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

    fun addEdge(u, v) = let 
        val _ = if Splayset.member(!adjSet, (u,v)) orelse u=v then ()
                else
                    let val _ = adjSet := Splayset.addList(!adjSet, [(u,v),(v,u)])
                        val adjList_u = Splaymap.find(!adjList, u)
                        val adjList_v = Splaymap.find(!adjList, v)
                        val degree_u = Splaymap.find(!degree, u)
                        val degree_v = Splaymap.find(!degree, v)
                        val singleton_v = Splayset.singleton String.compare v
                        val singleton_u = Splayset.singleton String.compare u
                        val _ = if (not (Splayset.member(!precolored, u))) then
                                  (adjList := Splaymap.insert(!adjList, u, Splayset.union(adjList_u, singleton_v));
                                   degree := Splaymap.insert(!degree, u, degree_u + 1))
                                 else ()
                        val _ = if (not (Splayset.member(!precolored, v))) then
                                  (adjList := Splaymap.insert(!adjList, v, Splayset.union(adjList_v, singleton_u));
                                   degree := Splaymap.insert(!degree, v, degree_v + 1))
                                 else ()
                    in () end
        in () end

                     
                      
    
    fun build((flowgraph, nodeToIns), (intgraph, liveMap), moveList, worklistMoves) =
        let val FGRAPH({control, def, use, ismove}) = flowgraph
            val instructions = List.rev(nodes control)
            fun isMoveInstruction(n) = Splaymap.find(ismove,n)
            fun processInstruction(instr) = 
                let val live = ref (liveMap(instr))
                    val use_i = Splayset.addList(Splayset.empty(String.compare), Splaymap.find(use, instr))
                    val def_i = Splayset.addList(Splayset.empty(String.compare), Splaymap.find(def, instr))
                    val singleton_i = (Splayset.singleton Int.compare instr)
                    
                    val _ = if isMoveInstruction(instr) then 
                        (live := Splayset.difference(!live, use_i);
                         Splayset.app (fn(n) => moveList := Splaymap.insert(!moveList, n, Splayset.union(Splaymap.find(!moveList, n), singleton_i))) (Splayset.union(use_i, def_i));
                         worklistMoves := Splayset.union(!worklistMoves, singleton_i); ())
                            else ()
                    val _ = live := Splayset.union(!live, def_i)
                    val _ = Splayset.app (fn(d) => Splayset.app (fn(l) => addEdge(l, d)) (!live) ) def_i
                    (* not necessary since we already have the liveMap *)
                in ()
                end
            

        in ()
        end

    fun nodeMoves(n, getMoves) = let
        val moveList_n = getMoves(n)
        in Splayset.intersection(moveList_n, Splayset.union(!activeMoves, !worklistMoves))
        end

    fun moveRelated(n, getMoves) = not (Splayset.isEmpty(nodeMoves(n, getMoves)))

    fun makeWorklist(IGRAPH{graph=ig, gtemp=nodeToTemp, moves=getMoves, tnode=tempToNode}) = 
        let val initial_ls = List.map (nodeToTemp o #2) (nodes ig)
            val initial = ref (Splayset.addList(Splayset.empty(String.compare), initial_ls))
            fun process(t) =
                let val singleton_t = Splayset.singleton String.compare t
                    val _ = initial := Splayset.difference(!initial, singleton_t)
                    val degree_t = Splaymap.find(!degree, t)
                    val set_to_modify = if degree_t >= K then spillWorklist else (if moveRelated(t, getMoves) then freezeWorklist else simplifyWorklist)
                    val _ = set_to_modify := Splayset.union(!set_to_modify, singleton_t)

                 in () end
         in Splayset.app process (!initial)
         end

    fun adjacent(n) = let
        val adjList_n = Splaymap.find(!adjList, n) 
        val selectStack_set = Splayset.addList(Splayset.empty(String.compare), !selectStack)
        in Splayset.difference(adjList_n, Splayset.union(selectStack_set, !coalescedNodes))
        end

    fun enableMoves(nodes, getMoves) = let
        fun processMove(m as (from,to)) = let
            val singleton_m = Splayset.singleton moveOrder m
            val _  = if Splayset.member(!activeMoves, m) then
                    (activeMoves := Splayset.difference(!activeMoves, singleton_m);
                     worklistMoves := Splayset.union(!worklistMoves, singleton_m))
                    else ()
            in () end
        in Splayset.app (fn(n) => Splayset.app processMove (nodeMoves(n, getMoves))) nodes
        end



    fun decrementDegree(m, getMoves) = let
        val d = Splaymap.find(!degree, m)
        val singleton_m = Splayset.singleton String.compare m
        val _ = degree := Splaymap.insert(!degree, m, d-1)
        val _ = if d=K then (enableMoves(Splayset.union(singleton_m, adjacent(m)), getMoves);
                            spillWorklist := Splayset.difference(!spillWorklist, singleton_m);
                            if moveRelated(m, getMoves) then freezeWorklist := Splayset.union(!freezeWorklist, singleton_m)
                                              else simplifyWorklist := Splayset.union(!simplifyWorklist, singleton_m))
                else ()
        in () end


    fun simplify(getMoves) = let
        val n = List.hd(Splayset.listItems(!simplifyWorklist))
        val singleton_n = Splayset.singleton String.compare n
        val _ = simplifyWorklist := Splayset.difference(!simplifyWorklist, singleton_n)
        (* push *)
        val _ = selectStack := (!selectStack)@[n]
        in Splayset.app (fn(m) => decrementDegree(m, getMoves)) (adjacent(n))
        end

    fun getAlias(n) = if Splayset.member(!coalescedNodes, n) 
                      then getAlias(Splaymap.find(!alias, n))
                      else n

    fun addWorkList(u, getMoves) = if (not (Splayset.member(!precolored, u)) andalso
                                       not (moveRelated(u, getMoves)) andalso 
                                       Splaymap.find(!degree, u) < K
                                      )
                                   then (let
                                       val singleton_u = Splayset.singleton String.compare u
                                     in (freezeWorklist := Splayset.difference(!freezeWorklist, singleton_u);
                                         simplifyWorklist := Splayset.union(!simplifyWorklist, singleton_u))
                                     end)
                                   else ()

    fun ok(t, r) = Splaymap.find(!degree, t) < K orelse
                   Splayset.member(!precolored, t) orelse 
                   Splayset.member(!adjSet, (t,r))

    fun conservative(nodes) = let
        fun aux(n, k) = if Splaymap.find(!degree, n) >= K then k+1 else k
        val k = Splayset.foldr aux 0 nodes
      in (k < K)
      end

    fun combine((u,v), getMoves) = let
        val singleton_u = Splayset.singleton String.compare u
        val singleton_v = Splayset.singleton String.compare v
        val _ = if Splayset.member(!freezeWorklist, v)
                then freezeWorklist := Splayset.difference(!freezeWorklist, singleton_v) 
                else spillWorklist := Splayset.difference(!spillWorklist, singleton_v) 
        val _ = coalescedNodes := Splayset.union(!coalescedNodes, singleton_v)
        val _ = alias := Splaymap.insert(!alias, v, u)
        val aux = Splayset.union(Splaymap.find(!moveList, u), Splaymap.find(!moveList, v))
        val _ = moveList := Splaymap.insert(!moveList, u, aux)
        val _ = enableMoves(singleton_v, getMoves)
        fun aux'(t) = (addEdge(t, u); decrementDegree(t, getMoves))
        val _ = Splayset.app aux' (adjacent(v))
        val _ = if Splaymap.find(!degree, u) >= K andalso Splayset.member(!freezeWorklist, u)
                then (freezeWorklist := Splayset.difference(!freezeWorklist, singleton_u);
                     freezeWorklist := Splayset.union(!spillWorklist, singleton_u))
                else ()
      in () end

    
    fun coalesce(fnodeToIns, getMoves) = let
        val m  = List.hd(Splayset.listItems(!worklistMoves))
        val singleton_m = Splayset.singleton moveOrder m
        val (x, y) = case Splaymap.find(fnodeToIns, m) of
          MOVE{assem=_, dst=y, src=x} => (getAlias x, getAlias y)
          | _ => raise Fail "Internal error coalescing: node in worklistMoves not a MOVE"
        val (u, v) = if Splayset.member(!precolored, y) then (y,x) else (x,y)
        val _ = worklistMoves := Splayset.difference(!worklistMoves, singleton_m)
        val _ = if (u=v) then (coalescedMoves := Splayset.union(!coalescedMoves, singleton_m);
                               addWorkList(u, getMoves))
                else (if (Splayset.member(!precolored, v) orelse Splayset.member(!adjSet, (u,v)))
                      then (constrainedMoves := Splayset.union(!constrainedMoves, singleton_m);
                           addWorkList(u, getMoves);
                           addWorkList(v, getMoves))
                      else (if (Splayset.member(!precolored, u) andalso (List.all ok (List.map (fn(t) => (t,u)) (Splayset.listItems(adjacent(v))))))
                               orelse (not (Splayset.member(!precolored, u)) andalso conservative(Splayset.union(adjacent(u), adjacent(v))))
                            then (coalescedMoves := Splayset.union(!coalescedMoves, singleton_m); 
                                  combine((u,v), getMoves);
                                  addWorkList(u, getMoves))
                            else
                                activeMoves := Splayset.union(!activeMoves, singleton_m)))
                         
        in () end

    fun freezeMoves(u, getMoves) = let
        fun aux(m as (x, y)) = let
            val singleton_m = Splayset.singleton moveOrder m
            val v = if getAlias(x)=getAlias(y)
                    then getAlias(x)
                    else getAlias(y)
            val singleton_v = Splayset.singleton String.compare v
            val _ = activeMoves := Splayset.difference(!activeMoves, singleton_m)
            val _ = frozenMoves := Splayset.union(!frozenMoves, singleton_m)
            val _ = if Splayset.isEmpty(nodeMoves(v, getMoves)) andalso Splaymap.find(!degree, v) < K
                    then (freezeWorklist := Splayset.difference(!freezeWorklist, singleton_v);
                         simplifyWorklist := Splayset.union(!simplifyWorklist, singleton_v))
                    else ()
          in () end
        val _ = Splayset.app aux (nodeMoves(u, getMoves))
      in () end

    fun freeze(getMoves) = let
        val u = List.hd(Splayset.listItems(!freezeWorklist))
        val singleton_u = Splayset.singleton String.compare u
        val _ = freezeWorklist := Splayset.difference(!freezeWorklist, singleton_u)
        val _ = simplifyWorklist := Splayset.union(!simplifyWorklist, singleton_u)
      in freezeMoves(u, getMoves)
      end

    fun selectSpill(getMoves) = let
    (* TODO heuristic *)
        val m = hd(Splayset.listItems(!spillWorklist))
        val singleton_m = Splayset.singleton String.compare m
        val _ = spillWorklist := Splayset.difference(!spillWorklist, singleton_m)
        val _ = simplifyWorklist := Splayset.union(!simplifyWorklist, singleton_m)
      in freezeMoves(m, getMoves)
      end

    fun assignColors() = let
        val _ = if (List.null(!selectStack))
                then Splayset.app (fn(n) => color := Splaymap.insert(!color, n, Splaymap.find(!color, getAlias(n)))) (!coalescedNodes)
                else (let
                    (* pop *)
                    val n = hd(!selectStack)        
                    val _ = selectStack := List.tl(!selectStack)
                    val singleton_n = Splayset.singleton String.compare n
                    val okColors = Splayset.addList(Splayset.empty(Int.compare), List.tabulate(K, (fn(x) => x)))
                    fun aux(w, set) = if Splayset.member(Splayset.union(!coloredNodes, !precolored), getAlias(w))
                                      then Splayset.difference(okColors, Splayset.singleton Int.compare (Splaymap.find(!color, getAlias(w))))
                                      else set
                    val okColors' = Splayset.foldr aux okColors (Splaymap.find(!adjList, n))
                    val _ = if Splayset.isEmpty(okColors')
                            then spilledNodes := Splayset.union(!spilledNodes, singleton_n)
                            else (coloredNodes := Splayset.union(!coloredNodes, singleton_n);
                                 color := Splaymap.insert(!color, n, hd(Splayset.listItems(okColors'))))
                  in assignColors()  end)
      in () end

end


