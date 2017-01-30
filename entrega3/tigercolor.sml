structure tigercolor =
struct

    open tigergraph
    open tigerflowgraph
    
    val precolored = ref (Splayset.addList(Splayset.empty(String.compare), tigerframe.list_regs))

    val moveList = ref (Splaymap.mkDict(String.compare)) : (tigertemp.temp, int Splayset.set) Splaymap.dict ref
    val worklistMoves = ref (Splayset.empty(Int.compare))
    fun edgeOrder((from1,to1),(from2,to2)) = if from1=from2 then String.compare(to1,to2) else String.compare(from1,from2)
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





end


