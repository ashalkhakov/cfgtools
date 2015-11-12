staload "./Grammar.sats"

abst@ype LR0ConfigurationNr = int
// allocate a configuration with the dot pointing to the first item of the production
// NOTE: not applicable to epsilon productions!

fun
compare_LR0ConfigurationNr_LR0ConfigurationNr (LR0ConfigurationNr, LR0ConfigurationNr):<> int

fun
LR0Configuration_make (ProductionNr): LR0ConfigurationNr
// get the production of the configuration:

fun
LR0Configuration_production (LR0ConfigurationNr): ProductionNr
// get position of the dot in production's right-hand side:

fun
LR0Configuration_dot (LR0ConfigurationNr): int(*before the focussed item of production*)
(*
property:
p:ProductionNr,c:LR0ConfigurationNr,
p = prod(c),
d:int,
d = dot(c),
d >= 0,
d <= Production_item_count(p)
*)
// is there an item after the dot?

fun
LR0Configuration_is_final (LR0ConfigurationNr): bool
(*
is_final(c) := dot(c) = Production_item_count(prod(c))
*)
fun
LR0Configuration_is_accepting (LR0ConfigurationNr): bool

// advance the dot, returning the new configuration
// NOTE: only applicable if configuration is not final

fun
LR0Configuration_advance (LR0ConfigurationNr): LR0ConfigurationNr
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
fun
LR0Configuration_fprint (FILEref, LR0ConfigurationNr): void
overload fprint with LR0Configuration_fprint
fun
LR0Configuration_print (LR0ConfigurationNr): void
overload print with LR0Configuration_print
