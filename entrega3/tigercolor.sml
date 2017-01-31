structure tigercolor =
struct

    open tigergraph
    open tigerflowgraph
    open tigerliveness
    
    val K = List.length(tigerframe.list_regs)
    val precolored = ref (Splayset.addList(Splayset.empty(String.compare), tigerframe.list_regs))
    val spillWorklist = ref (Splayset.empty(String.compare))
    val coalescedNodes = ref (Splayset.empty(String.compare))
    val freezeWorklist = ref (Splayset.empty(String.compare))
    val simplifyWorklist = ref (Splayset.empty(String.compare))
    val selectStack = ref [](* : (ref (tigertemp.temp list))*)

    val moveList = ref (Splaymap.mkDict(String.compare)) : (tigertemp.temp, int Splayset.set) Splaymap.dict ref
    val coalescedMoves = ref (Splayset.empty(Int.compare))
    val constrainedMoves = ref (Splayset.empty(Int.compare))
    val worklistMoves = ref (Splayset.empty(Int.compare))
    val activeMoves = ref (Splayset.empty(Int.compare))
    fun edgeOrder((from1,to1),(from2,to2)) = if from1=from2 then String.compare(to1,to2) else String.compare(from1,from2)
    (* set of tuples representing edges *)
    val adjSet = ref (Splayset.empty(edgeOrder))

    (* map of nodes to nodes, representing adjacency *)
    val adjList = ref (Splaymap.mkDict(String.compare)) : (tigertemp.temp, tigertemp.temp Splayset.set) Splaymap.dict ref
    (* map of nodes to degree (int) *)
    val degree = ref (Splaymap.mkDict(String.compare)) : (tigertemp.temp, int) Splaymap.dict ref

    fun addEdge(u, v) = let 
                    (* if (u,v) notin adjSet ^ (u /= v) *)
        val _ = if Splayset.member(!adjSet, (u,v)) orelse u=v then ()
                else
                        (*adjSet <- adjSet U [(u,v),(v,u)] *)
                    let val _ = adjSet := Splayset.addList(!adjSet, [(u,v),(v,u)])
                        val adjList_u = Splaymap.find(!adjList, u)
                        val adjList_v = Splaymap.find(!adjList, v)
                        val degree_u = Splaymap.find(!degree, u)
                        val degree_v = Splaymap.find(!degree, v)
                        val singleton_v = Splayset.singleton String.compare v
                        val singleton_u = Splayset.singleton String.compare u
                        (* if u not in precolored *)
                        val _ = if (not (Splayset.member(!precolored, u))) then
                                  (* adjList[u] <- adjList[u] U {v} *)
                                  (adjList := Splaymap.insert(!adjList, u, Splayset.union(adjList_u, singleton_v));
                                  (* degree[u] <- degree[u] +1 *)
                                   degree := Splaymap.insert(!degree, u, degree_u + 1))
                                 else ()
                        (* if v not in precolored *)
                        val _ = if (not (Splayset.member(!precolored, v))) then
                                  (* adjList[v] <- adjList[v] U {u} *)
                                  (adjList := Splaymap.insert(!adjList, v, Splayset.union(adjList_v, singleton_u));
                                  (* degree[v] <- degree[v] +1 *)
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
                        (* live = <- live \ use(i) *)
                        (live := Splayset.difference(!live, use_i);
                        (* forall n in def(i) U use(i), moveList[n] <- moveList[n] U {i}*)
                         Splayset.app (fn(n) => moveList := Splaymap.insert(!moveList, n, Splayset.union(Splaymap.find(!moveList, n), singleton_i))) (Splayset.union(use_i, def_i));
                        (* worlistMoves <- worlistMoves U {i} *)
                         worklistMoves := Splayset.union(!worklistMoves, singleton_i); ())
                            else ()
                    val _ = live := Splayset.union(!live, def_i)
                    (* forall d in def(I), l in live, AddEdge(l,d) *)
                    val _ = Splayset.app (fn(d) => Splayset.app (fn(l) => addEdge(l, d)) (!live) ) def_i
                    (* live <- use(I) U (live\def(I)) *)
                    (* not necessary since we already have the liveMap *)
                    (*val _ = live := Splayset.union(use_i, Splayset.difference(!live, def_i))*)
                in ()
                end
            

        in ()
        end

    fun nodeMoves(n, getMoves) = let
        val moveList_n = getMoves(n)
        (*nodeMoves(n) =  moveList[n] intersection (activeMoves U worklistMoves) *)
        in Splayset.intersection(moveList_n, Splayset.union(!activeMoves, !worklistMoves))
        end

    (* moveRelated(n) = nodeMoves(n) /= {} *)
    fun moveRelated(n, getMoves) = not (Splayset.isEmpty(nodeMoves(n, getMoves)))

    fun makeWorklist(IGRAPH{graph=ig, gtemp=nodeToTemp, getMoves=getMoves, tnode=tempToNode,...}) = 
        let val initial_ls = List.map (nodeToTemp o #2) (nodes ig)
            val initial = ref (Splayset.addList(Splayset.empty(String.compare), initial_ls))
            fun process(t) =
                let val singleton_t = Splayset.singleton String.compare t
                    (* initial <- initial \ {n} *)
                    val _ = initial := Splayset.difference(!initial, singleton_t)
                    val degree_t = Splaymap.find(!degree, t)
                    val set_to_modify = if degree_t >= K then spillWorklist else (if moveRelated(tempToNode t, getMoves) then freezeWorklist else simplifyWorklist)
                    val _ = set_to_modify := Splayset.union(!set_to_modify, singleton_t)

                 in () end
             (* forall n in initial *)
         in Splayset.app process (!initial)
         end

    fun adjacent(n) = let
        val adjList_n = Splaymap.find(!adjList, n) 
        val selectStack_set = Splayset.addList(Splayset.empty(String.compare), !selectStack)
        (* adjacent(n) = adjList[n] \ (selectStack U coalescedNodes) *)
        in Splayset.difference(adjList_n, Splayset.union(selectStack_set, !coalescedNodes))
        end

    fun enableMoves(nodes, getMoves) = let
        fun processMove(m) = let
            val singleton_m = Splayset.singleton Int.compare m
            (* if m in activeMoves *)
            val _  = if Splayset.member(!activeMoves, m) then
                    (* activeMoves <- activeMoves \ {m} *)
                    (activeMoves := Splayset.difference(!activeMoves, singleton_m);
                    (* worklistMoves <- worklistMoves U {m} *)
                     worklistMoves := Splayset.union(!worklistMoves, singleton_m))
                    else ()
            in () end
            (* forall n in nodes: forall m in NodeMoves(n) *)
        in Splayset.app (fn(n) => Splayset.app processMove (nodeMoves(n, getMoves))) nodes
        end



    fun decrementDegree(m, getMoves) = let
        (* let d = degree[m] *)
        val d = Splaymap.find(!degree, m)
        val singleton_m = Splayset.singleton String.compare m
        (* degree[m] <- d-1 *)
        val _ = degree := Splaymap.insert(!degree, m, d-1)
        (* if d=k then enableMoves({m} U Adjacent(m)) *)
        val _ = if d=K then (enableMoves(Splayset.union(singleton_m, adjacent(m)), getMoves);
                            (* spillWorklist <- spillWorklist \ {m} *)
                            spillWorklist := Splayset.difference(!spillWorklist, singleton_m);
                            (* if MoveRelated(m) then freezeWorklist <- freezeWorklist U {m}
                                                 else simplifyWorklist <- simplifyWorklist U {m} *)
                            if moveRelated(m, getMoves) then freezeWorklist := Splayset.union(!freezeWorklist, singleton_m)
                                              else simplifyWorklist := Splayset.union(!simplifyWorklist, singleton_m))
                else ()
        in () end


    fun simplify(getMoves) = let
        (* let n in simplifyWorklist *)
        val n = List.hd(Splayset.listItems(!simplifyWorklist))
        val singleton_n = Splayset.singleton String.compare n
        (* simplifyWorklist <- simplifyWorklist \ {n} *)
        val _ = simplifyWorklist := Splayset.difference(!simplifyWorklist, singleton_n)
        (* push(n, selectStack) *)
        val _ = selectStack := (!selectStack)@[n]
        (* forall m in Adjacent(n): DecrementDegree(m) *)
        in Splayset.app (fn(m) => decrementDegree(m, getMoves)) (adjacent(n))
        end


    fun addWorkList(u) = () 

    fun ok(t, r) = true

    fun conservative(nodes) = true

    fun combine(u,v) = ()
    
    fun coalesce(fnodeToIns) = let
        val m  = List.hd(Splayset.listItems(!worklistMoves))
        val singleton_m = Splayset.singleton Int.compare m
        val (x, y) = case Splaymap.find(fnodeToIns, m) of
          MOVE{assem=_, dst=y, src=x} => (x,y)
          | _ => raise Fail "Internal error coalescing: node in worklistMoves not a MOVE"
        val (u, v) = if Splayset.member(!precolored, y) then (y,x) else (x,y)
        val _ = worklistMoves := Splayset.difference(!worklistMoves, singleton_m)
        val _ = if (u=v) then (coalescedMoves := Splayset.union(!coalescedMoves, singleton_m);
                               addWorkList(u))
                else (if (Splayset.member(!precolored, v) orelse Splayset.member(!adjSet, (u,v)))
                      then (constrainedMoves := Splayset.union(!constrainedMoves, singleton_m);
                           addWorkList(u);
                           addWorkList(v))
                      else (if (Splayset.member(!precolored, u) andalso (List.all ok (List.map (fn(t) => (t,u)) (Splayset.listItems(adjacent(v))))))
                               orelse (not (Splayset.member(!precolored, u)) andalso conservative(Splayset.union(adjacent(u), adjacent(v))))
                            then (coalescedMoves := Splayset.union(!coalescedMoves, singleton_m); 
                                  combine(u,v);
                                  addWorkList(u))
                            else
                                activeMoves := Splayset.union(!activeMoves, singleton_m)))
                         
        in () end

end


