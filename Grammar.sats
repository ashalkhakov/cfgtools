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

// Grammar: maps ProductionNr to Production info
// Production: ?
// Configuration: ?

abst@ype ProductionNr = int

fun
compare_ProductionNr_ProductionNr (ProductionNr, ProductionNr):<> int

fun
Production_make (Nonterminal, List(Symbol)): ProductionNr

// make the augmented production
fun
Production_augment (Symbol): ProductionNr
//fun
//Production_is_augmented (ProductionNr): bool

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
