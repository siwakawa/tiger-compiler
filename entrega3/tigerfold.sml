structure tigerfold = 
struct

open tigertree

fun
    foldStm(MOVE(e1,e2)) = MOVE(foldtree e1, foldtree e2)
  | foldStm(EXP e) = EXP(foldtree e) 
  | foldStm(JUMP(e,ls)) = JUMP(foldtree e, ls)
  | foldStm(CJUMP(ope, e1, e2, l1, l2)) = CJUMP(ope, foldtree e1, foldtree e2, l1, l2)
  | foldStm(SEQ(s1, s2)) = SEQ(foldStm s1, foldStm s2)
  | foldStm(s) = s

and
 (* Non-BINOP cases *)
    foldtree(CONST(i)) = (CONST i)
  | foldtree(NAME(l)) = (NAME l)
  | foldtree(TEMP(t)) = (TEMP t)
  | foldtree(MEM(e)) = MEM(foldtree e)
  | foldtree(CALL(e1, els)) = CALL(foldtree e1, map foldtree els)
  | foldtree(ESEQ(s, e)) = ESEQ(foldStm s, foldtree e)
 (* Base cases *)
  | foldtree(BINOP(PLUS, CONST c1, CONST c2)) = CONST (c1+c2)
  | foldtree(BINOP(MINUS, CONST c1, CONST c2)) = CONST (c1-c2)
  | foldtree(BINOP(MUL, CONST c1, CONST c2)) = CONST (c1*c2)
  | foldtree(BINOP(DIV, CONST c1, CONST c2)) = 
            let val _ = if c2=0 then print("Warning: dividing by zero") else ()
            in (CONST (Int.div(c1, c2)))
            end

 (* Recursive cases *)
  | foldtree(BINOP(PLUS, t1, (BINOP(PLUS, t2, t3)))) = foldtree(BINOP(PLUS,BINOP(PLUS, foldtree t1, foldtree t2), foldtree t3))
  | foldtree(BINOP(MUL, t1, (BINOP(MUL, t2, t3)))) = foldtree(BINOP(MUL,BINOP(MUL, foldtree t1, foldtree t2), foldtree t3))

  | foldtree(BINOP(PLUS, BINOP(PLUS, CONST c1, t), CONST c2)) = foldtree(BINOP(PLUS, CONST (c1 + c2), foldtree t))
  | foldtree(BINOP(PLUS, BINOP(PLUS, t, CONST c1), CONST c2)) = foldtree(BINOP(PLUS, CONST (c1 + c2), foldtree t))
  | foldtree(BINOP(MUL, BINOP(MUL, CONST c1, t), CONST c2)) = foldtree(BINOP(MUL, CONST (c1 + c2), foldtree t))
  | foldtree(BINOP(MUL, BINOP(MUL, t, CONST c1), CONST c2)) = foldtree(BINOP(MUL, CONST (c1 + c2), foldtree t))


  | foldtree(BINOP(MUL, BINOP(PLUS, CONST c1, t), CONST c2)) = foldtree(BINOP(PLUS, CONST (c1 * c2), foldtree(BINOP(MUL, foldtree t, CONST c2))))
  | foldtree(BINOP(MUL, BINOP(PLUS, t, CONST c1), CONST c2)) = foldtree(BINOP(PLUS, CONST (c1 * c2), foldtree(BINOP(MUL, foldtree t, CONST c2))))
  | foldtree(BINOP(MUL, BINOP(MINUS, CONST c1, t), CONST c2)) = foldtree(BINOP(MINUS, CONST (c1 * c2), foldtree(BINOP(MUL, foldtree t, CONST c2))))
  | foldtree(BINOP(MUL, BINOP(MINUS, t, CONST c1), CONST c2)) = foldtree(BINOP(MINUS, foldtree (BINOP(MUL, foldtree t, CONST c2)), CONST (c1-c2)))
  
  | foldtree(BINOP(MUL, BINOP(PLUS, t1, t2), t3)) = foldtree(BINOP(PLUS, foldtree(BINOP(MUL, foldtree t1, foldtree t3)), foldtree(BINOP(MUL, foldtree t2, foldtree t3))))

  | foldtree(BINOP(ope, t1, t2)) = let val t1' = foldtree t1
                                       val t2' = foldtree t2
                                   in if t1=t1' andalso t2=t2' then BINOP(ope, t1, t2) else foldtree(BINOP(ope, t1', t2'))
                                   end

end
