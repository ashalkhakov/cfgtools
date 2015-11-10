abst@ype Symbol (bool) = ptr
typedef Symbol = [b:bool] Symbol(b)

fun
symbol_is_term {b:bool} (Symbol b): bool b

fun
symbol_is_nt {b:bool} (Symbol b): bool (~b)

typedef Terminal = Symbol (true)
typedef Nonterminal = Symbol (false)

fun Symbol_make_ntm (string): Nonterminal

fun Symbol_make_term (string): Terminal

fun Symbol_foreach (Symbol -<cloref1> void): void

// Grammar: maps ProductionNr to Production info
// Production: ?
// Configuration: ?

abst@ype ProductionNr = int

fun
Production_make (Nonterminal, List(Symbol)): ProductionNr

fun
Production_yields (ProductionNr): Nonterminal

fun
Production_item_count (ProductionNr): int(*item count*)

fun
Production_item (ProductionNr, int(*itemNr*)): Symbol
