(*
* SLR(1) parser test
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
// nonterminals:
(*
S -> E + S
S -> E
E -> num
*)
val nD = Symbol_make_ntm("D") // extended symbol
val nS = Symbol_make_ntm("S")
val nE = Symbol_make_ntm("E")
// terminals:
val tNUM = Symbol_make_term("num")
val tPLUS = Symbol_make_term("+")
// productions:
val _p0 = Production_make (nD, '[nS])
val _p1 = Production_make (nS, '[nE, tPLUS, nS])
val _p2 = Production_make (nS, '[nE])
val _p3 = Production_make (nE, '[tNUM])
val _p4 = Production_augment (nD)
//
val () = grammar_print ()
//
val () = println! ("beginning construction!")
implement
LR0_use_SLR1<> () = true
val s0 = LR0_construct (_p4)
val () = println! ("construction finished!")
val () = automaton_print ()
//
#define :: list_cons
val input1 = Input_make_list (
"num" :: "+" :: "num" :: "+" :: "num" :: "$" :: nil()
)
//
extern
castfn
s2s (LR0StateNr): State
//
val () = automaton_run (input1, (s2s)s0)
//
val input2 = Input_make_list (
"num" :: "+" :: "num" :: "+" :: "num" :: "+" :: "num" :: "+" :: "num" :: "$" :: nil()
)
//
val () = automaton_run (input2, (s2s)s0)
//
}
//
(* ****** ****** *)
