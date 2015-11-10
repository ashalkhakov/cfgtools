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
//
// TODO: grammar and table construction
(*
refs:
http://lara.epfl.ch/w/cc09:automata_for_lr_parsing_without_lookahead
http://www.cis.upenn.edu/~jean/old511/html/cis51108lr0.pdf
http://web.stanford.edu/class/archive/cs/cs143/cs143.1128/
*)

abst@ype ConfigurationNr = int
// allocate a configuration with the dot pointing to the first item of the production
// NOTE: not applicable to epsilon productions!
extern
fun
Configuration_make (ProductionNr): ConfigurationNr
// get the production of the configuration:
extern
fun
Configuration_production (ConfigurationNr): ProductionNr
// get position of the dot in production's right-hand side:
extern
fun
Configuration_dot (ConfigurationNr): int(*before the focussed item of production*)
(*
property:
p:ProductionNr,c:ConfigurationNr,
p = prod(c),
d:int,
d = dot(c),
d >= 0,
d <= Production_item_count(p)
*)
// is there an item after the dot?
extern
fun
Configuration_is_final (ConfigurationNr): bool
(*
is_final(c) := dot(c) = Production_item_count(prod(c))
*)
// advance the dot, returning the new configuration
// NOTE: only applicable if configuration is not final
extern
fun
Configuration_advance (ConfigurationNr): ConfigurationNr
(*
examples:

1) Y ::= a X b Y Z
-->
Production_item_count(1) = 5
Production_yields(1) = Y
Production_item(1,0) = a
Production_item(1,1) = X
Production_item(1,2) = b
Production_item(1,3) = Y
Production_item(1,4) = Z

Y ::= .a X b Y Z
prod(1) = 1
dot(1) = 0

Y ::= a X b Y Z .
prod(2) = 1
dot(2) = 5
*)

// to implement configurations
// - configuration is just ConfigurationNr <-> ProductionNr,Dot:integer
// - growable array to allocate and store configurations?
// - figure out how to map a configuration's production+item
//   back to ConfigurationNr (no dups! it's a set)
//   - need some kind of a hashtable, doable on desktop ATS

(* ****** ****** *)

(*
LR0 State: StateNr identifies it
- LR0 State is set of "dotted productions" (aka configurations)
  - just a set of ConfigurationNr's
- dotted production (aka configuration):  X ::= p.q
  - where X ::= pq is a grammar rule, p, q stand for strings of symbols (terminals or nonterminals)
of the production RHS)
  - symbols of configuration which are to the left of dot are "seen" (to the left = their ItemNr < dot position), the dot is conceptually BEFORE the sequence of symbols on its right
*)

(*
example grammar (it is extended grammar: we have added "eof" marker to the user-supplied initial rule, the new initial rule should consume all input):

D' ::= E eof
E ::= T
E ::= E + T
T ::= ID
example state I_0 (StateNr=0):
{ D' ::= .E eof,
  E ::= .T,
  E ::= .E + T,
  T ::= .ID }
*)

(*
new notion: set of states
- type: stateset
- yes, just the set of states given above
- stateset identified by StateSetNr

new function:
- closure(stateset):stateset

Assuming I:stateset, then closure(I) is least set such that:
- I subsetof closure(I)
- if (X ::= p.Yq) in I, and (Y ::= r) in Grammar, then (Y ::= .r) in closure(I)

Example: Take the singleton set

{ D' ::= .E eof }
Then closure of this set is I_0:

{ D' ::= .E eof,
  E ::= .T,
  E ::= .E + T,
  T ::= .ID }
where rules are added in this order using the definition.

implementation of closure?

1. go over all states in stateset

2. for every state I, add state I to result

2. for every state I, go over all configurations in I

3. for every configuration C, if dot(C) is not final, and symbol in prod(C) after dot(C) is nonterminal E, go over all productions in grammar which yield nonterminal E = dot(C), and add configuration (E ::= .<X>) to result, where <X> is a sequence of symbols

*)

(*
new function: goto(stateset,Symbol):stateset

goto(I,X) = closure({Y ::= qX.r | (Y ::= q.Xr) in I})

Example: Let us compute goto($I_0$, ID). Because only one element contains .ID, we obtain

{ T ::= ID. }
and the closure remains the same because . does not appear before a non-terminal.

I1 = goto(I0, E) = { E ::= E . + T }
I2 = goto(I1, +) = { E ::= E + . T , T ::= . ID }
I3 = goto(I2, T) = { E ::= E + T. }
implementation of goto(I,X):
- allocate empty result:stateset
- iterate over configurations in I, looking for configurations where dot is followed by any non-terminal, say X (so, the configuration should have the form Y ::= q.Xr)
- advance the dot, creating new configuration Y ::= qX.r, and put it into result
- return closure(result)
*)

//
(* ****** ****** *)
//
staload "./Input.sats"
//
(* ****** ****** *)
//
dynload "./Grammar.dats"
dynload "./Input.dats"
dynload "./Automaton.dats"
//
(* ****** ****** *)
//
implement
main0 () = {
//
//
// terminals:
val nS = Symbol_make_ntm("S") // extended symbol!
val nE = Symbol_make_ntm("E")
val nT = Symbol_make_ntm("T")
// nonterminals:
val tPLUS = Symbol_make_term("+")
val tEOF = Symbol_make_term("$") // extended symbol!
val tLPAREN = Symbol_make_term("(")
val tRPAREN = Symbol_make_term(")")
val tID = Symbol_make_term("id")
// productions:
val _p0 = Production_make (nS, '[nE, tEOF]) // extended rule!
val _p1 = Production_make (nE, '[nE, tPLUS, nT])
val _p2 = Production_make (nE, '[nT])
val _p3 = Production_make (nT, '[tLPAREN, nE, tRPAREN])
val _p4 = Production_make (nT, '[tID])
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
#define :: list_cons
val input1 = Input_make_list (
"id" :: "+" :: "(" :: "id" :: ")" :: "$" :: nil()
)
//
val () = automaton_run (input1, _s0)
//
val input2 = Input_make_list (
"id" :: "+" :: "(" :: "id" :: "+" :: "id" :: ")" :: "$" :: nil()
)
//
val () = automaton_run (input2, _s0)
//
}
//
(* ****** ****** *)
