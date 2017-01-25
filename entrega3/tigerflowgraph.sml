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

    val empty_fg = let fun forder((g1,n1),(g2,n2)) = Int.compare(n1, n2)
                   in FGRAPH{control=newGraph(), def=Splaymap.mkDict(forder), use=Splaymap.mkDict(forder), ismove=Splaymap.mkDict(forder)}
                   end

    fun addInsToFGraph(fgraph, instruction) = let val FGRAPH{control=g, def=d, use=u, ismove=im} = fgraph
                                                  val n' = newNode g
                                                  val newDef = Splaymap.insert(d, n', (getDef instruction))
                                                  val newUse = Splaymap.insert(u, n', (getUse instruction))
                                                  val newIsMove = Splaymap.insert(im, n', isMove instruction )
                                              in FGRAPH{control=(#1 n'), def=newDef, use=newUse, ismove=newIsMove}
                                              end

end
