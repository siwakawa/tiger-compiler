structure tigercodegen :> tigercodegen =
struct

open tigerassem
open tigertree
open tigerframe

fun codegen frame stm = 
    let val ilist = ref [] : instr list ref
        fun emit i = ilist := i::(!ilist)
        fun saveCallerSaves() =
            let fun emiteDefs s = emit(OPER{assem="pushl `s0", src=[s], dst=[], jump=NONE})
            in List.map emiteDefs tigerframe.callersaves
            end
        fun restoreCallerSaves() =
            let fun emiteDefs s = emit(OPER{assem="popl `d0", src=[], dst=[s], jump=NONE})
                val _ = List.map emiteDefs (List.rev tigerframe.callersaves)
            in ()
            end


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

        fun munchStm(SEQ(a,b)) = (munchStm a; munchStm b)
            | munchStm(MOVE(TEMP t1, MEM(BINOP(PLUS, CONST i, TEMP t2)))) = 
                emit(OPER{assem="movl "^Int.toString(i)^ "(`s0), `d0", dst=[t1], src=[t2], jump=NONE})
            | munchStm(MOVE(TEMP t1, MEM(BINOP(PLUS, TEMP t2, CONST i)))) = 
                munchStm(MOVE(TEMP t1, MEM(BINOP(PLUS, CONST i, TEMP t2))))

            | munchStm(MOVE(MEM(BINOP(PLUS, TEMP t2, CONST i)), TEMP t1)) = 
                emit(OPER{assem="movl `s0, "^(Int.toString i)^"(`s1)",  dst=[], src=[t1, t2], jump=NONE})
            | munchStm(MOVE(MEM(BINOP(PLUS, CONST i, TEMP t2)), TEMP t1)) = 
                munchStm(MOVE(MEM(BINOP(PLUS, TEMP t2, CONST i)), TEMP t1)) 

            | munchStm(MOVE(MEM(BINOP(PLUS, TEMP t2, CONST i)), CONST i2)) = 
                emit(OPER{assem="movl $"^(Int.toString i2)^", "^(Int.toString i)^"(`s0)",  dst=[], src=[t2], jump=NONE})
            | munchStm(MOVE(MEM(BINOP(PLUS, CONST i, TEMP t2)), CONST i2)) = 
                munchStm(MOVE(MEM(BINOP(PLUS, TEMP t2, CONST i)), CONST i2)) 


            | munchStm(MOVE(MEM(BINOP(PLUS, CONST i, TEMP t2)), e1)) = 
                let val t = tigertemp.newtemp() 
                in emit(OPER{assem="movl `s0, `d0", dst=[t], src=[munchExp e1], jump=NONE});
                   emit(OPER{assem="movl `s0, "^(Int.toString i)^"(`s1)",  dst=[], src=[t, t2], jump=NONE})
                end
            | munchStm(MOVE(MEM(BINOP(PLUS, TEMP t2, CONST i)), e1)) = 
                munchStm(MOVE(MEM(BINOP(PLUS, CONST i, TEMP t2)), e1)) 

            | munchStm(MOVE(MEM e1, CONST i)) =  
                emit(OPER{assem="movl $"^(Int.toString i)^", (`s0)", dst=[], src=[munchExp e1], jump=NONE})

            | munchStm(MOVE(MEM e1, TEMP t1)) =  
                emit(OPER{assem="movl `s0, (`s1)", dst=[], src=[t1, munchExp e1], jump=NONE})
            | munchStm(MOVE(TEMP t1, MEM e1)) =  
                emit(OPER{assem="movl (`s0), `d0", dst=[t1], src=[munchExp e1], jump=NONE})

            | munchStm(MOVE(TEMP t1, CONST i)) =  
                emit(OPER{assem="movl $"^(Int.toString i)^", `d0", dst=[t1], src=[], jump=NONE})

            | munchStm(MOVE(TEMP t1, e1)) =  
                emit(tigerassem.MOVE{assem="movl `s0, `d0", dst=t1, src=(munchExp e1)})

            | munchStm(MOVE(MEM e1, MEM e2)) =  
                let val t = tigertemp.newtemp() 
                in emit(OPER{assem="movl (`s0), `d0", dst=[t], src=[munchExp e2], jump=NONE});
                   emit(OPER{assem="movl `s0, (`s1)", dst=[], src=[t, munchExp e1], jump=NONE})
                end

            | munchStm(MOVE(MEM(CONST i), e)) =
                emit(OPER{assem="movl `s0, " ^Int.toString i, src=[munchExp e], dst=[], jump=NONE})
            | munchStm(MOVE(MEM e1, e2)) =  
                let val t = tigertemp.newtemp() 
                in emit(OPER{assem="movl `s0, `d0", dst=[t], src=[munchExp e2], jump=NONE});
                   emit(OPER{assem="movl `s0, (`s1)", dst=[], src=[t, munchExp e1], jump=NONE})
                end


            (* general case for MOVE *)
            | munchStm(MOVE(e1, e2)) = 
                let val t = tigertemp.newtemp() 
                in emit(tigerassem.MOVE{assem="movl `s0, `d0", dst=t, src=(munchExp e2)});
                   emit(tigerassem.MOVE{assem="movl `s0, `d0", dst=(munchExp e1), src=t})
                end
            | munchStm(EXP(CALL(NAME f, args))) = 
               (* We don't save the caller saves, we just put them in dst so the register allocator will know they can be overwritten inside the call *)
               (* (saveCallerSaves(); *)
                 (munchArgs (List.rev args);
                  emit(OPER{assem="call "^f, src=[], dst=tigerframe.callersaves, jump=NONE}))
               (* restoreCallerSaves()) *)
            (* general case for EXP *)
            | munchStm(EXP(e)) = 
                emit(OPER{assem="movl `s0, `d0", src=[munchExp e], dst=[tigertemp.newtemp()], jump=NONE})


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
                in emit(OPER{assem="jmp `j0", src=[], dst=[], jump=SOME[l']})
                end
            | munchStm(CJUMP(relop, e, CONST i, l1, l2)) =
                   (emit(OPER{assem="cmpl $"^Int.toString i ^", `s0", src=[munchExp e], dst=[], jump=NONE});
                    emit(OPER{assem=relOp relop ^ " `j0" , src=[], dst=[], jump=SOME[l1, l2]}))
            | munchStm(CJUMP(relop, CONST i, e, l1, l2)) =
                   (emit(OPER{assem="cmpl $" ^Int.toString i ^ ", `s0", src=[munchExp e], dst=[], jump=NONE});
                    emit(OPER{assem=relOp relop ^ " `j0", src=[], dst=[], jump=SOME[l1, l2]}))
            (* general case for CJUMP *)
            | munchStm(CJUMP(relop, e1, e2, l1, l2)) =
                   (emit(OPER{assem="cmpl `s0, `s1", src=[munchExp e2, munchExp e1], dst=[], jump=NONE});
                    emit(OPER{assem=relOp relop ^ " `j0", src=[], dst=[], jump=SOME[l1, l2]}))
            | munchStm(JUMP((NAME l),ls)) = 
                emit(OPER{assem="jmp `j0", src=[], dst=[], jump=SOME ls})
            | munchStm(JUMP(e,ls)) = 
                emit(OPER{assem="jmp *`s0", src=[munchExp e], dst=[], jump=SOME ls})
            | munchStm(LABEL l) = 
                emit(tigerassem.LABEL{assem=l ^ ":", lab=l})

        and result(gen) = let val t = tigertemp.newtemp() in gen t; t end

        and  munchExp(MEM(BINOP(PLUS, CONST i, (TEMP t)))) = 
                result(fn r => emit(OPER{assem="movl "^ Int.toString i ^"(`s0), `d0", src=[t], dst=[r], jump=NONE}))
            | munchExp(MEM(BINOP(PLUS, (TEMP t), CONST i))) = 
                munchExp(MEM(BINOP(PLUS, CONST i, (TEMP t))))
 
            | munchExp(MEM(BINOP(PLUS, e1, CONST i))) = 
                result(fn r => emit(OPER{assem="movl "^ Int.toString i ^"(`s0), `d0", src=[munchExp e1], dst=[r], jump=NONE}))
            | munchExp(MEM(BINOP(PLUS, CONST i, e1))) =
                 result(fn r => emit(OPER{assem="movl "^ Int.toString i ^"(`s0), `d0", src=[munchExp e1], dst=[r], jump=NONE}))
            | munchExp(MEM(CONST i)) = 
                result(fn r => emit(OPER{assem="movl ("^Int.toString i ^ "), `d0", src=[], dst=[r], jump=NONE}))
            | munchExp(MEM(e1)) = 
                result(fn r => emit(OPER{assem="movl (`s0), `d0", src=[munchExp e1], dst=[r], jump=NONE}))
            | munchExp(BINOP(PLUS, CONST i, TEMP t1 )) = 
                result(fn r => (emit(tigerassem.MOVE{assem="movl `s0, `d0", src=t1, dst=r});
                                emit(OPER{assem="addl $"^(Int.toString i)^", `d0", src=[], dst=[r], jump=NONE})))
            | munchExp(BINOP(PLUS, TEMP t1, CONST i )) = 
                munchExp(BINOP(PLUS, CONST i, TEMP t1 ))
            | munchExp(BINOP(PLUS, e1, e2)) = 
                result(fn r => (emit(tigerassem.MOVE{assem="movl `s0, `d0", src=(munchExp e1), dst=r}); 
                                emit(OPER{assem="addl `s0, `d0", src=[munchExp e2, r], dst=[r], jump=NONE})))
            | munchExp(BINOP(MINUS, e1, e2)) = 
                result(fn r => (emit(tigerassem.MOVE{assem="movl `s0, `d0", src=(munchExp e1), dst=r}); 
                                emit(OPER{assem="subl `s0, `d0", src=[munchExp e2, r], dst=[r], jump=NONE})))
            | munchExp(BINOP(MUL, e1, e2)) = 
                result(fn r => (emit(tigerassem.MOVE{assem="movl `s0, `d0", src=(munchExp e1), dst=r}); 
                                emit(OPER{assem="imull `s0, `d0", src=[munchExp e2, r], dst=[r], jump=NONE})))
            | munchExp(BINOP(DIV, e1, e2)) = result(fn r => 
                (emit(tigerassem.MOVE{assem="movl `s0, `d0", src=(munchExp e1), dst=rv}); 
                 emit(OPER{assem="movl $0, `d0", src=[], dst=[ov], jump=NONE}); 
                 emit(OPER{assem="idivl `s0", src=[munchExp e2, rv, ov], dst=[rv, ov], jump=NONE});
                 emit(tigerassem.MOVE{assem="movl `s0, `d0", src=rv, dst=r})))
            | munchExp(BINOP(AND, e1, e2)) = 
                result(fn r => (emit(tigerassem.MOVE{assem="movl `s0, `d0", src=(munchExp e1), dst=r}); 
                                emit(OPER{assem="andl `s0, `d0", src=[munchExp e2, r], dst=[r], jump=NONE})))
            | munchExp(BINOP(OR, e1, e2)) = 
                result(fn r => (emit(tigerassem.MOVE{assem="movl `s0, `d0", src=(munchExp e1), dst=r}); 
                                emit(OPER{assem="orl `s0, `d0", src=[munchExp e2, r], dst=[r], jump=NONE})))
            | munchExp(BINOP(LSHIFT, e1, e2)) = 
                result(fn r => (emit(tigerassem.MOVE{assem="movl `s0, `d0", src=(munchExp e1), dst=r}); 
                                emit(OPER{assem="shll `s0, `d0", src=[munchExp e2, r], dst=[r], jump=NONE})))
            | munchExp(BINOP(RSHIFT, e1, e2)) = 
                result(fn r => (emit(tigerassem.MOVE{assem="movl `s0, `d0", src=(munchExp e1), dst=r}); 
                                emit(OPER{assem="shrl `s0, `d0", src=[munchExp e2, r], dst=[r], jump=NONE})))
            | munchExp(BINOP(ARSHIFT, e1, e2)) = 
                result(fn r => (emit(tigerassem.MOVE{assem="movl `s0, `d0", src=(munchExp e1), dst=r}); 
                                emit(OPER{assem="sarl `s0, `d0", src=[munchExp e2, r], dst=[r], jump=NONE})))
            | munchExp(BINOP(XOR, e1, e2)) = 
                result(fn r => (emit(tigerassem.MOVE{assem="movl `s0, `d0", src=(munchExp e1), dst=r}); 
                                emit(OPER{assem="xorl `s0, `d0", src=[munchExp e2, r], dst=[r], jump=NONE})))
            | munchExp(CONST(i)) = 
                result(fn r => emit(tigerassem.OPER{assem="movl $"^Int.toString i ^", `d0", src=[], dst=[r], jump=NONE}))
            | munchExp(NAME(l)) = 
                result(fn r => emit(tigerassem.OPER{assem="movl $" ^ l ^ ", `d0", src=[], dst=[r], jump=NONE}))
            | munchExp(TEMP(r)) = r
            | munchExp(CALL(NAME f, args)) = 
                result(fn r => (munchArgs (List.rev args); 
                                emit(OPER{assem="call "^f, src=[], dst=tigerframe.callersaves, jump=NONE}); 
                                emit(tigerassem.MOVE{assem="movl `s0, `d0", src=rv, dst=r})))
            | munchExp((_)) = raise Fail "Internal error: munchExp unhandled case"


        and munchArgs params =
            let fun munchArgsST [] = []
                  | munchArgsST (h::t) = 
                        let val (instr, e) = 
                            case h of
                                CONST i => (OPER{assem="pushl $" ^Int.toString i, src=[], dst=[], jump=NONE}, "")
                              | NAME n => (OPER{assem="pushl $" ^n, src=[], dst=[], jump=NONE}, "")
                              | TEMP t => (OPER{assem="pushl `s0", src=[t], dst=[], jump=NONE}, "")
                              | MEM (CONST x) => (OPER{assem="pushl "^Int.toString x, src=[], dst=[], jump=NONE}, "")
                              | MEM (TEMP r) => (OPER{assem="pushl (`s0)", src=[r], dst=[], jump=NONE}, "")
                              | e => (OPER{assem="pushl `s0", src=[munchExp e], dst=[], jump=NONE}, "")
                        in emit instr; munchArgsST t
                        end
            in munchArgsST params
            end



     in munchStm stm;
        rev(!ilist)
     end

end

