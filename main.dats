(*
** Hello, world!
** following: http://dragonbook.stanford.edu/lecture-notes/Stanford-CS143/08-Bottom-Up-Parsing.pdf
** currently contains: source code for an LR(0) automaton interpreter,
** geared for work with the tables given in the lecture notes (pg. 6)
*)

(* ****** ****** *)

#include
"share/atspre_staload.hats"

(* ****** ****** *)
//
staload "./Grammar.sats"
staload "./Automaton.sats"
//
(* ****** ****** *)
//
(*
refs:
http://lara.epfl.ch/w/cc09:automata_for_lr_parsing_without_lookahead
http://www.cis.upenn.edu/~jean/old511/html/cis51108lr0.pdf
http://web.stanford.edu/class/archive/cs/cs143/cs143.1128/
*)
//
(* ****** ****** *)
//
staload "./Input.sats"
staload "./LR0.sats"
//
(* ****** ****** *)
//
dynload "./Grammar.dats"
dynload "./Input.dats"
dynload "./Automaton.dats"
dynload "./LR0Configuration.dats"
dynload "./LR0.dats"
//
(* ****** ****** *)
//
implement
main0 () = {
//
//
// terminals:
val nD = Symbol_make_ntm("D") // extended symbol!
val nE = Symbol_make_ntm("E")
val nT = Symbol_make_ntm("T")
// nonterminals:
val tID = Symbol_make_term("id")
val tPLUS = Symbol_make_term("+")
//val tEOF = Symbol_make_term("$") // extended symbol!
val tLPAREN = Symbol_make_term("(")
val tRPAREN = Symbol_make_term(")")
// productions:
//val _p0 = Production_make (nD, '[nE]) // designated initial rule
//val _p0 = Production_make (nD, '[nE, tEOF]) // extended rule!
val _p1 = Production_make (nE, '[nE, tPLUS, nT])
val _p2 = Production_make (nE, '[nT])
val _p3 = Production_make (nT, '[tLPAREN, nE, tRPAREN])
val _p4 = Production_make (nT, '[tID])
val _p5 = Production_augment (nE)
//
val () = grammar_print ()
//
val () = println! ("beginning construction!")
val s0 = LR0_construct (_p5)
val () = println! ("construction finished!")
val () = automaton_print ()
(*
//
val _s0 = State_make ()
val _s1 = State_make ()
val _s2 = State_make ()
val _s3 = State_make ()
val _s4 = State_make ()
val _s5 = State_make ()
val _s6 = State_make ()
val _s7 = State_make ()
val _s8 = State_make ()
//
val () = Action_put_shift (_s0, tID, _s4)
val () = Action_put_shift (_s0, tLPAREN, _s3)
val () = Action_put_shift (_s1, tPLUS, _s5)
val () = Action_put_accept (_s1, tEOF)
val () = Action_put_reduce (_s2, tPLUS, _p2)
val () = Action_put_reduce (_s2, tEOF, _p2)
val () = Action_put_reduce (_s2, tLPAREN, _p2)
val () = Action_put_reduce (_s2, tRPAREN, _p2)
val () = Action_put_reduce (_s2, tID, _p2)
val () = Action_put_shift (_s3, tID, _s4)
val () = Action_put_shift (_s3, tLPAREN, _s3)
val () = Action_put_reduce (_s4, tPLUS, _p4)
val () = Action_put_reduce (_s4, tEOF, _p4)
val () = Action_put_reduce (_s4, tLPAREN, _p4)
val () = Action_put_reduce (_s4, tRPAREN, _p4)
val () = Action_put_reduce (_s4, tID, _p4)
val () = Action_put_shift (_s5, tID, _s4)
val () = Action_put_shift (_s5, tLPAREN, _s3)
val () = Action_put_shift (_s6, tPLUS, _s5)
val () = Action_put_shift (_s6, tRPAREN, _s7)
//
val () = Action_put_reduce (_s7, tPLUS, _p3)
val () = Action_put_reduce (_s7, tEOF, _p3)
val () = Action_put_reduce (_s7, tLPAREN, _p3)
val () = Action_put_reduce (_s7, tRPAREN, _p3)
val () = Action_put_reduce (_s7, tID, _p3)
//
val () = Action_put_reduce (_s8, tPLUS, _p1)
val () = Action_put_reduce (_s8, tEOF, _p1)
val () = Action_put_reduce (_s8, tLPAREN, _p1)
val () = Action_put_reduce (_s8, tRPAREN, _p1)
val () = Action_put_reduce (_s8, tID, _p1)
//
val () = Goto_put (_s0, nE, _s1)
val () = Goto_put (_s0, nT, _s2)
val () = Goto_put (_s3, nE, _s6)
val () = Goto_put (_s3, nT, _s2)
val () = Goto_put (_s5, nT, _s8)
//
val () = println! ("Hello, world!")
//
*)
#define :: list_cons
val input1 = Input_make_list (
"id" :: "+" :: "(" :: "id" :: ")" :: "$" :: nil()
)
//
extern
castfn
s2s (LR0StateNr): State
//
val () = automaton_run (input1, (s2s)s0(*_s0*))
//
val input2 = Input_make_list (
"id" :: "+" :: "(" :: "id" :: "+" :: "id" :: "+" :: "id" :: ")" :: "$" :: nil()
)
//
val () = automaton_run (input2, (s2s)s0(*_s0*))
//
}
//
(* ****** ****** *)
