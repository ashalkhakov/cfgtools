//
staload SET = "libats/SATS/funset_avltree.sats"
stadef set = $SET.set
staload MAP = "libats/SATS/funmap_avltree.sats"
stadef map = $MAP.map
//
staload DG = "./../utils/SATS/fundigraph.sats"
//
(* ****** ****** *)
//
abst@ype Symbol (b:bool) = ptr
typedef Terminal = Symbol(true)
typedef Nonterminal = Symbol(false)
typedef Symbol = [b:bool] Symbol (b)
//
val sym_EOF: Terminal
//
val sym_EPS: Terminal
//
fun
fprint_Symbol (FILEref, Symbol): void
overload fprint with fprint_Symbol
//
fun
fprint_Nonterminal (FILEref, Nonterminal): void
overload fprint with fprint_Nonterminal of 10
//
fun
fprint_Terminal (FILEref, Terminal): void
overload fprint with fprint_Terminal of 10
//
fun
compare_Symbol_Symbol (x: Symbol, y: Symbol):<> int
overload compare with compare_Symbol_Symbol
//
fun
eq_Symbol_Symbol (x: Symbol, y: Symbol):<> bool
overload = with eq_Symbol_Symbol
//
fun
neq_Symbol_Symbol (x: Symbol, y: Symbol):<> bool
overload <> with neq_Symbol_Symbol
//
fun
Symbol_is_terminal {b:bool} (Symbol b): bool b
//
fun
Symbol_is_nonterminal {b:bool} (Symbol b): bool (~b)
//
fun
Symbol_terminal (string): Terminal
//
fun
Symbol_nonterminal (string): Nonterminal
//
(* ****** ****** *)
//
datatype Production = {n:pos} Prod of (Nonterminal, list(Symbol, n))
//
fun
fprint_Production (FILEref, Production): void
overload fprint with fprint_Production
//
fun
compare_Production_Production (Production, Production):<> int
//
fun
Production_derives (Production): Nonterminal
//
(* ****** ****** *)
//
abstype Grammar = ptr
//
fun
Grammar_get_syms (Grammar): set(Symbol)
//
fun
Grammar_get_prods (Grammar): map (Production, size_t(*tag*))
//
fun
Grammar_make_nil (): Grammar
//
fun
Grammar_add_terminal (&Grammar >> _, string): Terminal
//
fun
Grammar_add_nonterminal (&Grammar >> _, string): Nonterminal
//
fun
Grammar_add_empty_production (&Grammar >> _, Nonterminal): size_t
//
fun
Grammar_add_production {n:pos} (&Grammar >> _, Nonterminal, list(Symbol, n)): size_t
//
fun
Grammar_set_start (&Grammar >> _, size_t(*tag*)): void
//
fun
Grammar_get_start (Grammar): size_t
//
fun
fprint_Grammar (FILEref, Grammar): void
overload fprint with fprint_Grammar
//
(* ****** ****** *)
//
fun
Grammar_nonterminals (
  Grammar
, &ptr? >> arrayptr (Nonterminal, n)
, &ptr? >> map (Nonterminal, size_t)
): #[n:int] size_t(n)
//
