structure tigerassem =
struct

    type reg = string
    type temp = tigertemp.temp
    type label = tigertemp.label

    datatype instr = OPER of {assem: string,
                              dst: temp list,
                              src: temp list,
                              jump: label list option}
                   | LABEL of {assem: string,
                               lab: tigertemp.label}
                   | MOVE of {assem: string,
                              dst: temp,
                              src: temp}


    fun format saytemp =
        let fun speak(assem,src,dst,jump) = 
            let val saylab = tigertab.name
                fun f(#"`":: #"s":: i::rest) =
                      ((explode (saytemp(List.nth(src, ord(i) - ord(#"0")))) @ f rest) handle Subscript => raise Fail ("Internal error: saytemp, index: s"^ Char.toString i ^", rest: " ^ implode(rest)))
                   |f(#"`":: #"d":: i::rest) = 
                      ((explode (saytemp(List.nth(dst, ord(i) - ord(#"0")))) @ f rest) handle Subscript => raise Fail ("Internal error: saytemp, assem: " ^ assem ^"||| dst: "^String.concat(dst)^ "||| src: "^String.concat(src)))
                   |f(#"`":: #"j":: i::rest) = 
                      ((explode (saytemp(List.nth(jump, ord(i) - ord(#"0")))) @ f rest) handle Subscript => raise Fail ("Internal error: saytemp, index: j"^ Char.toString i ^", rest: " ^ implode(rest)))
                   |f(#"`":: #"`":: rest) = #"`":: f rest
                   |f(#"`":: _ ::rest) =  raise Fail ("Bad assem format: ")
                   |f(c :: rest) = c :: f rest
                   |f nil = nil
            in implode(f(explode assem))
            end
            fun replace_tilde(#"~") = "-"
              | replace_tilde(x) = String.str x
            fun rewrite(a) = String.translate replace_tilde a
        in fn OPER{assem,dst,src,jump=NONE} => speak(rewrite assem,src,dst,nil) ^ "\n"
            | OPER{assem,dst,src,jump=SOME j} => speak(rewrite assem,src,dst,j) ^ "\n"
	        | LABEL{assem,...} => assem ^ "\n"
	        | MOVE{assem,dst,src} => speak(rewrite assem,[src],[dst],nil) ^ "\n"
        end



end
