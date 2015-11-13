abst@ype Symbol (bool) = ptr
typedef Symbol = [b:bool] Symbol(b)

fun
symbol_is_term {b:bool} (Symbol b): bool b

fun
symbol_is_nt {b:bool} (Symbol b): bool (~b)

typedef Terminal = Symbol (true)
typedef Nonterminal = Symbol (false)

val
sym_EOF : Terminal // technically, not part of the alphabet
val
sym_EPS : Terminal // technically, not part of the alphabet

fun
compare_Symbol_Symbol {b1,b2:bool} (Symbol b1, Symbol b2):<> int

fun Symbol_make_ntm (string): Nonterminal

fun Symbol_make_term (string): Terminal

fun eq_Symbol_Symbol (Symbol, Symbol):<> bool
overload = with eq_Symbol_Symbol

fun
Symbol_fprint (FILEref, Symbol): void
overload fprint with Symbol_fprint
fun
Symbol_print (Symbol): void
overload print with Symbol_print

fun{env:vt0p}
Symbol_foreach$fwork (Symbol, env: &(env) >> _): void
fun{env:vt0p}
Symbol_foreach_env (env: &(env) >> _): void

abst@ype ProductionNr = int

fun
compare_ProductionNr_ProductionNr (ProductionNr, ProductionNr):<> int

fun
Production_make {n:pos} (Nonterminal, list (Symbol, n)): ProductionNr
fun
Production_make_eps (Nonterminal): ProductionNr
fun
Production_is_eps (ProductionNr): bool

// make the augmented production
fun
Production_augment (Symbol): ProductionNr

fun
Production_yields (ProductionNr): Nonterminal

fun
Production_item_count (ProductionNr): int(*item count*)

fun
Production_item (ProductionNr, int(*itemNr*)): Symbol

fun{env:vt0p}
Production_head_foreach$fwork (ProductionNr, env: &(env) >> _): void
fun{env:vt0p}
Production_head_foreach_env (Nonterminal, env: &(env) >> _): void

fun
Production_fprint (FILEref, ProductionNr): void
overload fprint with Production_fprint

fun
Production_print (ProductionNr): void
overload print with Production_print

fun
grammar_print (): void

// set of terminals, possibly including EOF and/or EPS
abstype termset = ptr
//
fun
termset_fprint (FILEref, termset): void
overload fprint with termset_fprint
//
fun
termset_print (termset): void
overload print with termset_print
//
fun{env:vt0p}
termset_foreach$fwork (Terminal, &(env) >> _): void
fun{env:vt0p}
termset_foreach_env (termset, &(env) >> _): void
//
fun
first (List(Symbol)): termset
// NOTE: first probably includes eps
fun
follow (Nonterminal): termset
// NOTE: follow probably includes eof
