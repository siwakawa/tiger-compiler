structure tigerflowgraph =
struct
    open tigergraph
    datatype flowgraph = FGRAPH of {control: tigergraph.graph,
				    def: (node', tigertemp.temp list) Splaymap.dict,
				    use: (node', tigertemp.temp list) Splaymap.dict,
				    ismove: (node', bool) Splaymap.dict}

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



(* This function creates the flowgraph filling the succ and pred information of only the adjacent nodes. The succ and pred information related to jumps is saved in edgeInfo (a map label -> node'); and in succInfo (a map node'->labels)*)
    fun firstPass(fgraph, edgeInfo, succInfo, lastNode, []) = (fgraph, edgeInfo, succInfo)
      | firstPass(fgraph, edgeInfo, succInfo, lastNode, (ins as LABEL({lab=l,...}))::t) = let val FGRAPH{control=g, def=d, use=u, ismove=im} = fgraph
                                                                           val (g', n') = newNode g
                                                                           (* We create an edge from the last node to the current one *)
                                                                           val _ = if lastNode <> ~1 then mk_edge{from=(g', lastNode), to=(g',n')} else ()
                                                                           val edgeInfo' = Splaymap.insert(edgeInfo, l, n')
                                                                           val newDef = Splaymap.insert(d, n', (getDef ins))
                                                                           val newUse = Splaymap.insert(u, n', (getUse ins))
                                                                           val newIsMove = Splaymap.insert(im, n', isMove ins )
                                                                           val fg' = FGRAPH{control=g', def=newDef, use=newUse, ismove=newIsMove}
                                                                       in  firstPass(fg', edgeInfo', succInfo, n', t)
                                                                       end
       | firstPass(fgraph, edgeInfo, succInfo, lastNode, (ins as OPER({jump=SOME(ls),...}))::t) = let val FGRAPH{control=g, def=d, use=u, ismove=im} = fgraph
                                                                                   val (g', n') = newNode g
                                                                           (* We create an edge from the last node to the current one *)
                                                                           val _ = if lastNode <> ~1 then mk_edge{from=(g', lastNode), to=(g',n')} else ()
                                                                                   val succInfo' = Splaymap.insert(succInfo, n', ls)
                                                                                   val newDef = Splaymap.insert(d, n', (getDef ins))
                                                                                   val newUse = Splaymap.insert(u, n', (getUse ins))
                                                                                   val newIsMove = Splaymap.insert(im, n', isMove ins )
                                                                                   val fg' = FGRAPH{control=g' , def=newDef, use=newUse, ismove=newIsMove}
                                                                               (* We want the next instruction to not consider this one as a predecessor, because this one will jump *)
                                                                               in  firstPass(fg', edgeInfo, succInfo', ~1, t)
                                                                               end
      | firstPass(fgraph, edgeInfo, succInfo, lastNode, ins::t) =  let val FGRAPH{control=g, def=d, use=u, ismove=im} = fgraph
                                                 val (g', n') = newNode g
                                                (* We create an edge from the last node to the current one *)
                                                val _ = if lastNode <> ~1 then mk_edge{from=(g', lastNode), to=(g',n')} else ()
                                                 val newDef = Splaymap.insert(d, n', (getDef ins))
                                                 val newUse = Splaymap.insert(u, n', (getUse ins))
                                                 val newIsMove = Splaymap.insert(im, n', isMove ins )
                                                 val fg' = FGRAPH{control=g', def=newDef, use=newUse, ismove=newIsMove}
                                             in  firstPass(fg', edgeInfo, succInfo, n',  t)
                                             end
 

    fun createFlowGraph(fgraph, instructions) = let val succInfo= Splaymap.mkDict(Int.compare)
                                         val edgeInfo=Splaymap.mkDict(String.compare)
                                         val (FGRAPH{control=g', def=d, use=u, ismove=im}, labelToNodeMap, nodeToPredLabels) = firstPass(fgraph, edgeInfo, succInfo, ~1, instructions)
                                         fun add_preds_and_sucs((g, n)) = let val succ_labels = case Splaymap.peek(nodeToPredLabels, n) of
                                                                                                 SOME(ls) => ls
                                                                                               | NONE => []
                                                                          in List.app (fn(l) => mk_edge({to=(g, Splaymap.find(labelToNodeMap, l)), from=(g, n)})) succ_labels
                                                                          end
                                         val _ = List.map add_preds_and_sucs (nodes g')
                                     in (FGRAPH{control=g', def=d, use=u, ismove=im}, nodes g')
                                     end

    fun instrs2graph(inst_ls) = let 
                                    val empty_fg = FGRAPH{control=newGraph(), def=Splaymap.mkDict(Int.compare), use=Splaymap.mkDict(Int.compare), ismove=Splaymap.mkDict(Int.compare)}
                                in createFlowGraph(empty_fg, inst_ls)
                                end


end
