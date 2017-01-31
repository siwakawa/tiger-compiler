signature tigerliveness = sig
     datatype igraph = 
        IGRAPH of {graph: tigergraph.graph,
                   tnode: tigertemp.temp -> tigergraph.node',
                   gtemp: tigergraph.node' -> tigertemp.temp,
                   moves: (tigertemp.temp * tigertemp.temp) list,
                   getMoves: tigergraph.node' -> tigergraph.node' Splayset.set}

       val interferenceGraph: tigerflowgraph.flowgraph -> 
                                igraph * (tigergraph.node' -> tigertemp.temp Splayset.set) 

        val show : igraph -> unit
end
