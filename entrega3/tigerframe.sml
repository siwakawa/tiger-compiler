(*
	Frames para el 80386 (sin displays ni registers).

		|    argn    |	fp+4*(n+1)
		|    ...     |
		|    arg2    |	fp+16
		|    arg1    |	fp+12
		|	fp level |  fp+8
		|  retorno   |	fp+4
		|   fp ant   |	fp
		--------------	fp
		|   local1   |	fp-4
		|   local2   |	fp-8
		|    ...     |
		|   localn   |	fp-4*n
*)

structure tigerframe :> tigerframe = struct

open tigertree

type level = int

val fp = "FP"				(* frame pointer (ebp in 386)*)
val sp = "SP"				(* stack pointer (esp in 386) *)
val rv = "RV"				(* return value  (eax in 386) *)
val ov = "OV"				(* overflow value (edx en el 386) *)
val ebx = "EBX"               (* base of array (ebx in 386) *)
val ecx = "ECX"               (* counter (ecx in 386) *)
val esi = "ESI"               (* source index for string operations (esi in 386) *)
val edi = "EDI"               (* destination index for string operations (esi in 386) *)
val eip = "EIP"               (* instruction pointer (eip in 386) *)
val wSz = 4					(* word size in bytes *)
val log2WSz = 2				(* base two logarithm of word size in bytes *)
val fpPrev = 0				(* offset (bytes) *)
val fpPrevLev = 8			(* offset (bytes) *)
val argsInicial = 0			(* words *)
val argsOffInicial = 0		(* words *)
val argsGap = wSz			(* bytes *)
val regInicial = 1			(* reg *)
val localsInicial = 0		(* words *)
val localsGap = ~4 			(* bytes *)
val calldefs = [rv]
val specialregs = [rv, fp, sp]
val argregs = []
val callersaves = [rv, ecx, ov]
val calleesaves = [fp, ebx, edi, esi]

type frame = {
	name: string,
	formals: bool list,
	locals: bool list,
	actualArg: int ref,
	actualLocal: int ref,
	actualReg: int ref
}
type register = string
datatype access = InFrame of int | InReg of tigertemp.label
datatype frag = PROC of {body: tigertree.stm, frame: frame}
	| STRING of tigertemp.label * string
fun newFrame{name, formals} = {
	name=name,
	formals=formals,
	locals=[],
	actualArg=ref argsInicial,
	actualLocal=ref localsInicial,
	actualReg=ref regInicial
}
fun name(f: frame) = #name f
fun string(l, s) = l^tigertemp.makeString(s)^"\n"
fun formals({formals=f, ...}: frame) = 
	let	fun aux(n, []) = []
		| aux(n, h::t) = InFrame(n)::aux(n+argsGap, t)
	in aux(argsInicial, f) end
fun maxRegFrame(f: frame) = !(#actualReg f)
fun allocArg (f: frame) b = 
	case b of
	true =>
		let	val ret = (!(#actualArg f)+argsOffInicial)*wSz
			val _ = #actualArg f := !(#actualArg f)+1
		in	InFrame ret end
	| false => InReg(tigertemp.newtemp())
fun allocLocal (f: frame) b = 
	case b of
	true =>
		let	val ret = InFrame(!(#actualLocal f)+localsGap)
		in	#actualLocal f:=(!(#actualLocal f)-1); ret end
	| false => InReg(tigertemp.newtemp())
fun exp(InFrame k) e = MEM(BINOP(PLUS, TEMP(fp), CONST k))
| exp(InReg l) e = TEMP l
fun externalCall(s, l) = CALL(NAME s, l)

(* based on tigertrans.seq *)
fun create_stm_seq [] = EXP (CONST 0)
    | create_stm_seq [x] = x
    | create_stm_seq (x::xs) = SEQ (x, create_stm_seq xs)

fun procEntryExit1 (frame,body) =
    let
        val callee_data = map (fn(r) => {reg=TEMP(r), stack_access=allocLocal frame true}) calleesaves
        (* save the values in the registers to the stack (exp's second argument does not matter*)
        val save_callees_instructions = map (fn({reg=r, stack_access=acc}) => MOVE(exp acc 0, r)) callee_data

        (* restore the saved values to their respective registers *)
        val restore_callees_instructions = map (fn({reg=r, stack_access=acc}) => MOVE(r, exp acc 0)) callee_data
    in
        (* save the registers, execute the body, and restore the registers *)
        create_stm_seq (save_callees_instructions @ [body] @ restore_callees_instructions)
end

end
