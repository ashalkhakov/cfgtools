staload "./Grammar.sats"

abst@ype ConfigurationNr = int
// allocate a configuration with the dot pointing to the first item of the production
// NOTE: not applicable to epsilon productions!

fun
compare_ConfigurationNr_ConfigurationNr (ConfigurationNr, ConfigurationNr):<> int

fun
Configuration_make (ProductionNr): ConfigurationNr
// get the production of the configuration:

fun
Configuration_production (ConfigurationNr): ProductionNr
// get position of the dot in production's right-hand side:

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

fun
Configuration_is_final (ConfigurationNr): bool
(*
is_final(c) := dot(c) = Production_item_count(prod(c))
*)
fun
Configuration_is_accepting (ConfigurationNr): bool

// advance the dot, returning the new configuration
// NOTE: only applicable if configuration is not final

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
fun
Configuration_fprint (FILEref, ConfigurationNr): void
overload fprint with Configuration_fprint
fun
Configuration_print (ConfigurationNr): void
overload print with Configuration_print
