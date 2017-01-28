structure tigerliveness :> tigerliveness = struct
    open tigergraph                                                                 
    open tigerflowgraph

    datatype igraph = 
        IGRAPH of {graph: tigergraph.graph,
                   tnode: tigertemp.temp -> tigergraph.node',
                   gtemp: tigergraph.node' -> tigertemp.temp,
                   moves: (tigertemp.temp * tigertemp.temp) list}

    (*This function takes a flowgraph and returns a pair of maps (ins, outs), where ins[n] is the set of all temporaries live-in at node n (and similarly, outs[n]) *)
    fun get_liveness_maps(FGRAPH(fgraph)) = let val nodes = tigergraph.nodes(#control fgraph)
                           val new_ins = Splaymap.mkDict(Int.compare)
                           val new_outs = Splaymap.mkDict(Int.compare)
                           (* sets_changed is a bool that indicates that (for some node n), the news ins/outs obtained are different from the old ones *)
                           fun fold_algo'((g, n) : node, (ins, outs, keep_iterating)) =
                               let val control = #control fgraph
                                   val ins_n = case Splaymap.peek(ins, n) of
                                                SOME(s) => s
                                                | NONE => Splayset.empty(String.compare)
                                   val outs_n = case Splaymap.peek(outs, n) of
                                                 SOME(s) => s
                                                 | NONE => Splayset.empty(String.compare)
                                   val defs_n = Splaymap.find(#def fgraph, n)
                                   val uses_n = Splaymap.find(#use fgraph, n)
                                   val defs_set_n = Splayset.addList(Splayset.empty(String.compare), defs_n)
                                   val uses_set_n = Splayset.addList(Splayset.empty(String.compare), uses_n)
                                   val ins_n' = Splayset.union(uses_set_n, Splayset.difference(outs_n, defs_set_n))
                                   fun union_fold((node, set)) = let val ins_node = case Splaymap.peek(ins, node) of
                                                                                     SOME(s) => s
                                                                                     | NONE => Splayset.empty(String.compare)
                                                                 in Splayset.union(set, ins_node) 
                                                                 end
                                   val succ_n = List.map (#2) (tigergraph.succ((g,n)))
                                   val outs_n' = List.foldr union_fold (Splayset.empty(String.compare)) succ_n
                                   val ins' = Splaymap.insert(ins, n, ins_n')
                                   val outs' = Splaymap.insert(outs, n, outs_n')

(*                                   val _ = Splaymap.app(fn(n, set)=>print("Node " ^Int.toString(n) ^", Outs: "^ Int.toString(Splayset.numItems(ins_n'))^ "\n")) outs*)
                                   val are_ins_n_changed = not(Splayset.equal(ins_n, ins_n'))
                                   val are_outs_n_changed = not(Splayset.equal(outs_n, outs_n'))

                               in (ins', outs', keep_iterating orelse (are_ins_n_changed orelse are_outs_n_changed))
                               end
                           fun iterate_algo_once(ins, outs) = List.foldr fold_algo' (ins, outs, false) nodes
                           fun iterate_until_solution(ins, outs) = let val (ins', outs', keep_iterating) = iterate_algo_once(ins, outs)
                                                                   in if keep_iterating then iterate_until_solution(ins', outs') else (ins', outs')
                                                                   end

                        val (final_ins, final_outs) = iterate_until_solution(new_ins, new_outs)
                        in (final_ins, final_outs) 
                        end

    fun getLiveMap(fg as FGRAPH(flowgraph)) = let val (ins, outs) = get_liveness_maps(fg)
                                                  val _ = Splaymap.app(fn(n, set)=>print("Node " ^Int.toString(n) ^", lives: "^ Int.toString(Splayset.numItems(set))^ "\n")) outs
                                                  val nodes = nodes (#control flowgraph)
                                                  fun get_outs_node(n) = Splaymap.find(outs, n)
                                                  val outs_sets = List.map (fn((g, n)) => (n, get_outs_node n)) nodes
                                                  val emptyMap = Splaymap.mkDict(Int.compare)
                                                  val liveMap = List.foldr (fn((n,outs_n), map) => Splaymap.insert(map, n, outs_n)) emptyMap outs_sets
                                        in liveMap end

    fun interferenceGraph(fg as FGRAPH(flowgraph)) = let val liveMap = getLiveMap fg
(*                                                         val _ = Splaymap.app(fn(n, set)=>print("Node " ^Int.toString(n) ^", lives: "^ Int.toString(Splayset.numItems(set))^ "\n")) liveMap*)
                                                         val emptyIGraph = newGraph()
                                                         val emptyMap = Splaymap.mkDict(Int.compare)
                                                         val temps_set = Splaymap.foldr (fn(n, outs_n_set, all_outs_set) => Splayset.union(all_outs_set, outs_n_set)) (Splayset.empty(String.compare)) liveMap
                                                         val (igraph, list_nodesxtemps) = Splayset.foldr (fn(t,(g, pairs_node_temp)) => let val (g', n) = newNode g
                                                                                                                                        in (g', (n, t)::pairs_node_temp) end) (emptyIGraph, []) temps_set
                                                         val tnode_dict = List.foldr (fn((n, t), map)=>Splaymap.insert(map, t, n))(Splaymap.mkDict(String.compare)) list_nodesxtemps
                                                         val gtemp_dict = List.foldr (fn((n, t), map)=>Splaymap.insert(map, n, t)) emptyMap list_nodesxtemps
                                                         val tnode = fn(t) => Splaymap.find(tnode_dict, t)
                                                         val gtemp = fn(n) => Splaymap.find(gtemp_dict, n)

                                                         fun ismove(n) = Splaymap.find(#ismove flowgraph, n)
                                                         fun getdefs(n) = Splaymap.find(#def flowgraph, n)
                                                         fun getuses(n) = Splaymap.find(#use flowgraph, n)
                                                         val moves = List.map (fn((g, fg_node)) => if ismove(fg_node) then
                                                                                                (if (length(getdefs(fg_node)) <> 1) orelse (length(getuses(fg_node)) <> 1) then
                                                                                                     raise Fail "Internal error: Move instruction with #uses/=1 or #defs /=1"
                                                                                                else [(hd(getdefs(fg_node)), hd(getuses(fg_node)))])
                                                                                              else []) (nodes (#control flowgraph))
                                                         val moves' = List.concat moves
                                                         fun liveMap_fun(fg_node) = Splaymap.find(liveMap, fg_node)
                                                        (*Faltan agregar las aristas al igraph*) 
                                                         in (IGRAPH({graph=igraph, tnode=tnode, gtemp=gtemp, moves=moves'}), liveMap_fun) end

    fun show(IGRAPH(igraph)) = let val ns = nodes (#graph igraph)
                                   val _ = print(Int.toString(List.length(ns)))
                                   val gtemp = #gtemp igraph
                                   val _ = List.app (fn(n) => print("Temp " ^ gtemp(#2 n) ^", Adjacents: " ^ String.concatWith ";" (List.map (Int.toString o #2) (adj (n))) ^ "\n")) ns
                               in () end


end
