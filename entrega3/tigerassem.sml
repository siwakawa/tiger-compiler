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

(*val format : (temp->string) -> instr -> string*)

fun codegen frame stm = 
    let val ilist = ref [] : instr list ref
        fun emit i = ilist := i::(!ilist)
        fun saveCallerSaves() =
            let fun emiteDefs s = emit(OPER{assem="pushL `s0", src=[s], dst=[], jump=NONE})
            in List.map emiteDefs tigerframe.callersaves
            end
        fun restoreCallerSaves() =
            let fun emiteDefs s = emit(OPER{assem="popL `d0", src=[], dst=[s], jump=NONE})
                val _ = List.map emiteDefs (List.rev tigerframe.callersaves)
            in ()
            end

        open tigertree

        fun relOp relop = case relop of
                            EQ => "je"
                            | NE => "jne"
                            | LT => "jl"
                            | GT => "jg"
                            | LE => "jle"
                            | GE => "jge"
                            | ULT => "jb"
                            | UGT => "ja"
                            | ULE => "jbe"
                            | UGE => "jae"


        fun munchExp(_) = tigertemp.newtemp()


        fun munchArgs params =
            let fun munchArgsST [] = []
                    | munchArgsST (h::t) = 
                        let val (instr, e) = case h of
                                                CONST i => (OPER{assem="pushL" ^Int.toString i, src=[], dst=[], jump=NONE}, "")
                                                | NAME n => (OPER{assem="pushL $" ^n, src=[], dst=[], jump=NONE}, "")
                                                | TEMP t => (OPER{assem="pushL " ^t, src=[t], dst=[], jump=NONE}, "")
                                                | MEM (CONST x) => (OPER{assem="pushL "^Int.toString x, src=[], dst=[], jump=NONE}, "")
                                                | MEM (TEMP r) => (OPER{assem="pushL (" ^r ^")", src=[r], dst=[], jump=NONE}, "")
                                                | e => (OPER{assem="pushL `s0", src=[munchExp e], dst=[], jump=NONE}, "")
                        in munchArgsST t
                        end
            in munchArgsST params
            end




        fun munchStm(SEQ(a,b)) = (munchStm a; munchStm b)
            | munchStm(MOVE(TEMP t1, MEM(BINOP(PLUS, CONST i, TEMP t2)))) = 
                emit(OPER{assem="movL "^Int.toString(i)^ "(`s0), `d0", dst=[t1], src=[t2], jump=NONE})
            | munchStm(MOVE(TEMP t1, MEM(BINOP(PLUS, TEMP t2, CONST i)))) = 
                emit(OPER{assem="movL "^Int.toString(i)^ "(`s0), `d0",  dst=[t1], src=[t2], jump=NONE})
            | munchStm(MOVE(MEM e1, MEM e2)) =  
                let val t = tigertemp.newtemp() 
                in emit(OPER{assem="movL (`s0), `d0", dst=[t], src=[munchExp e2], jump=NONE});
                   emit(OPER{assem="movL `s0, (`d0)", dst=[munchExp e1], src=[t], jump=NONE})
                end
            | munchStm(MOVE(MEM(CONST i), e)) =
                emit(OPER{assem="movl `s0, " ^Int.toString i, src=[munchExp e], dst=[], jump=NONE})
            | munchStm(MOVE(MEM e1, e2)) =  
                let val t = tigertemp.newtemp() 
                in emit(OPER{assem="movL `s0, `d0", dst=[t], src=[munchExp e2], jump=NONE});
                   emit(OPER{assem="movL `s0, (`d0)", dst=[munchExp e1], src=[t], jump=NONE})
                end
            (* general case for MOVE *)
            | munchStm(MOVE(e1, e2)) = 
                let val t = tigertemp.newtemp() 
                in emit(OPER{assem="movL `s0, `d0", dst=[t], src=[munchExp e2], jump=NONE});
                   emit(OPER{assem="movL `s0, `d0", dst=[munchExp e1], src=[t], jump=NONE})
                end
            | munchStm(EXP(CALL(NAME f, args))) = 
                (saveCallerSaves();
                 emit(OPER{assem="call "^f, src=munchArgs args, dst=tigerframe.calldefs, jump=NONE});
                 restoreCallerSaves())
            (* general case for EXP *)
            | munchStm(EXP(e)) = emit(OPER{assem="movl `s0, `d0", src=[munchExp e], dst=[tigertemp.newtemp()], jump=NONE})


            | munchStm(CJUMP(relop, e, CONST i, l1, l2)) =
                let val _ = emit(OPER{assem="cmpl `s1, $"^Int.toString i, src=[munchExp e], dst=[], jump=SOME[l1,l2]})
                in emit(OPER{assem=relOp relop ^ " " ^ l1, src=[], dst=[], jump=SOME[l1]})
                end
            | munchStm(CJUMP(relop, CONST i, e, l1, l2)) =
                let val _ = emit(OPER{assem="cmpl $" ^Int.toString i ^ ", `s0", src=[munchExp e], dst=[], jump=SOME[l1,l2]})
                in emit(OPER{assem=relOp relop ^ " " ^ l1, src=[], dst=[], jump=SOME[l1]})
                end
             | munchStm(CJUMP(relop, CONST i, CONST j, l1, l2)) =
                let val c = case relop of
                              EQ => i=j
                            | NE => i<>j
                            | LT => i<j
                            | GT => i>j
                            | LE => i<=j
                            | GE => i>=j
                            | ULT => i<j
                            | UGT => i>j
                            | ULE => i<=j
                            | UGE => i>=j
                    val l' = if c then l1 else l2
                in emit(OPER{assem="jmp "^l', src=[], dst=[], jump=SOME[l']})
                end
            (* general case for CJUMP *)
            | munchStm(CJUMP(relop, e1, e2, l1, l2)) =

                let val _ = emit(OPER{assem="cmpl `s0, `d0", src=[munchExp e1, munchExp e2], dst=[], jump=SOME[l1,l2]})
                in emit(OPER{assem=relOp relop ^ " " ^ l1, src=[], dst=[], jump=SOME[l1]})
                end

(*            | munchStm(LABEL l) = emit(tigerassem.LABEL{assem=l ^ ":\n", lab=l}) *)


     in 0
     end


end

