structure tigerflowgraph =
struct
    open tigergraph
    datatype flowgraph = FGRAPH of {control: tigergraph.graph,
				    def: (node, tigertemp.temp list) Splaymap.dict,
				    use: (node, tigertemp.temp list) Splaymap.dict,
				    ismove: (node, bool) Splaymap.dict}

  (* Note:  any "use" within the block is assumed to be BEFORE a "def" 
        of the same variable.  If there is a def(x) followed by use(x)
       in the same block, do not mention the use in this data structure,
       mention only the def.

     More generally:
       If there are any nonzero number of defs, mention def(x).
       If there are any nonzero number of uses BEFORE THE FIRST DEF,
           mention use(x).

     For any node in the graph,  
           Graph.Table.look(def,node) = SOME(def-list)
           Graph.Table.look(use,node) = SOME(use-list)
   *)

    open tigerassem

    fun getDef(OPER{dst=ds,...}) = ds
      | getDef(MOVE{dst=ds,...}) = [ds]
      | getDef(_) = []


    fun getUse(OPER{src=ss,...}) = ss
      | getUse(MOVE{src=ss,...}) = [ss]
      | getUse(_) = []

    fun isMove(MOVE{...}) = true
      | isMove(_) = false



(* This function creates the flowgraph without filling the succ and pred information, instead saving in edgeInfo a map label -> node'; and in predInfo a map node'->labels*)
    fun firstPass(fgraph, edgeInfo, predInfo,  []) = (fgraph, edgeInfo, predInfo)
      | firstPass(fgraph, edgeInfo, predInfo, (ins as LABEL({lab=l,...}))::t) = let val FGRAPH{control=g, def=d, use=u, ismove=im} = fgraph
                                                                           val n' = newNode g
                                                                           val edgeInfo' = Splaymap.insert(edgeInfo, l, #2 n')
                                                                           val newDef = Splaymap.insert(d, n', (getDef ins))
                                                                           val newUse = Splaymap.insert(u, n', (getUse ins))
                                                                           val newIsMove = Splaymap.insert(im, n', isMove ins )
                                                                           val g' = FGRAPH{control=(#1 n'), def=newDef, use=newUse, ismove=newIsMove}
                                                                       in  firstPass(g', edgeInfo', predInfo, t)
                                                                       end
       | firstPass(fgraph, edgeInfo, predInfo, (ins as OPER({jump=SOME(ls),...}))::t) = let val FGRAPH{control=g, def=d, use=u, ismove=im} = fgraph
                                                                                   val n' = newNode g
                                                                                   val predInfo' = Splaymap.insert(predInfo, #2 n', ls)
                                                                                   val newDef = Splaymap.insert(d, n', (getDef ins))
                                                                                   val newUse = Splaymap.insert(u, n', (getUse ins))
                                                                                   val newIsMove = Splaymap.insert(im, n', isMove ins )
                                                                                   val g' = FGRAPH{control=(#1 n'), def=newDef, use=newUse, ismove=newIsMove}
                                                                               in  firstPass(g', edgeInfo, predInfo', t)
                                                                               end
      | firstPass(fgraph, edgeInfo, predInfo, ins::t) =  let val FGRAPH{control=g, def=d, use=u, ismove=im} = fgraph
                                                 val n' = newNode g
                                                 val newDef = Splaymap.insert(d, n', (getDef ins))
                                                 val newUse = Splaymap.insert(u, n', (getUse ins))
                                                 val newIsMove = Splaymap.insert(im, n', isMove ins )
                                                 val g' = FGRAPH{control=(#1 n'), def=newDef, use=newUse, ismove=newIsMove}
                                             in  firstPass(g', edgeInfo, predInfo, t)
                                             end
 

    fun createFlowGraph(fgraph, instructions) = let val predInfo= Splaymap.mkDict(Int.compare)
                                         val edgeInfo= Splaymap.mkDict(String.compare)
                                         val (FGRAPH{control=g', def=d, use=u, ismove=im}, labelToNodeMap, nodeToPredLabels) = firstPass(fgraph, edgeInfo, predInfo, instructions)
                                         fun add_preds_and_sucs((g, n)) = let val pred_labels = case Splaymap.peek(nodeToPredLabels, n) of
                                                                                                 SOME(ls) => ls
                                                                                               | NONE => []
                                                                          in List.app (fn(l) => mk_edge({from=(g, Splaymap.find(labelToNodeMap, l)), to=(g, n)})) pred_labels
                                                                          end
                                         val _ = List.map add_preds_and_sucs (nodes g')
                                     in (FGRAPH{control=g', def=d, use=u, ismove=im}, nodes g')
                                     end

    fun instrs2graph(inst_ls) = let 
                                    fun forder((g1,n1),(g2,n2)) = Int.compare(n1, n2)
                                    val empty_fg = FGRAPH{control=newGraph(), def=Splaymap.mkDict(forder), use=Splaymap.mkDict(forder), ismove=Splaymap.mkDict(forder)}
                                in createFlowGraph(empty_fg, inst_ls)
                                end


                                                                 
                                                                                      
    fun algo(FGRAPH(fgraph)) = let val nodes = tigergraph.nodes(#control fgraph)
                           fun comp_node((g1,n1),(g2,n2)) = Int.compare(n1, n2)
                           val new_ins = Splaymap.mkDict(comp_node)
                           val new_outs = Splaymap.mkDict(comp_node)
                           (* sets_changed is a bool that indicates that (for some node n), the news ins/outs obtained are different from the old ones *)
                           fun fold_algo'(n : node, (ins, outs, keep_iterating)) =
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
                                   val succ_n = List.map (fn(gr,nod) => nod) (tigergraph.succ(n))
                                   val ins_n' = Splayset.union(uses_set_n, Splayset.difference(outs_n, defs_set_n))
                                   fun union_fold((node, set)) = let val ins_node = case Splaymap.peek(ins, n) of
                                                                                     SOME(s) => s
                                                                                     | NONE => Splayset.empty(String.compare)
                                                                 in Splayset.union(set, ins_node) 
                                                                 end
                                   val succs_node = List.map (fn(gr,nod) => nod) (tigergraph.succ(n))
                                   val outs_n' = List.foldr union_fold (Splayset.empty(String.compare)) succs_node
                                   val ins' = Splaymap.insert(ins, n, ins_n')
                                   val outs' = Splaymap.insert(outs, n, outs_n')

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

end
