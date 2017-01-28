signature tigerliveness = sig
        type igraph
        val interferenceGraph: tigerflowgraph.flowgraph -> 
                                igraph * (tigergraph.node' -> tigertemp.temp Splayset.set) 

        val show : igraph -> unit
end
