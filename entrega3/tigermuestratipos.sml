structure tigermuestratipos:> tigermuestratipos =
struct
open tigertips

fun buscaRecordArray unique lenv =
	case List.find(fn(_, TArray(_, u)) => u=unique | (_, TRecord(_, u)) => u=unique | _ => false) lenv of
	SOME (k, v) => k
	| NONE => raise Fail "error interno76543"
fun printTipo(n, t, lenv) =
	let
    	fun prnt TUnit = print "TUnit\n"
    	| prnt TNil = print "TNil\n"
    	| prnt TInt = print "TInt\n"
    	| prnt TString = print "TString\n"
    	| prnt(TArray(t, _)) = (print "TArray of "; prnt t)
    	| prnt(TRecord(l, u)) =
			let fun aux [] = ()
				| aux ((sr, (TTipo(tr,_)), ir)::t) =
								print("TRecord(TTipo "^tr^" "^Int.toString(ir)^")\n")
				| aux ((sr, (TRecord(_, u)), ir)::t) = (print (buscaRecordArray u lenv); print(" "^Int.toString ir^" "); aux t)
				| aux ((sr, (TArray(_, u)), ir)::t) = (print (buscaRecordArray u lenv); print(" "^Int.toString ir^" "); aux t)
				| aux ((sr,  tr , ir)::t) = (prnt tr; print(" "^Int.toString ir^" "); aux t)
			in print "TRecord["; aux l; print "]\n" end
		| prnt(TTipo (s,_)) =
			print("TTipo "^s)
        | prnt _ = ()
    in	print(n^" = "); prnt t end
fun printTTipos tips = List.app (fn(s,t) => printTipo(s, t, tips)) tips
end
