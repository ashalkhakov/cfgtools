staload "./Grammar.sats"
staload "./LR0Configuration.sats"

abst@ype LR0StateNr = int

fun
LR0State_fprint (FILEref, LR0StateNr): void
//overload fprint with LR0State_fprint

fun
LR0State_print (LR0StateNr): void
//overload print with LR0State_print

fun{env:vt0p}
LR0State_foreach_env$fwork (LR0ConfigurationNr, env: &(env) >> _): void

fun{env:vt0p}
LR0State_foreach_env (LR0StateNr, env: &(env) >> _): void

fun
LR0State_is_empty (LR0StateNr): bool

fun
LR0State_is_accepting (LR0StateNr): bool

fun
LR0_initial (ProductionNr): LR0StateNr

fun
LR0_closure (LR0StateNr): LR0StateNr
fun
LR0_goto (LR0StateNr, Symbol): LR0StateNr

fun{env:vt0p}
LR0_foreach$fwork (LR0StateNr, env: &(env) >> _): void
fun{env:vt0p}
LR0_foreach_env (env: &(env) >> _): void

fun{}
LR0_use_SLR1 (): bool // false=use LR(0), true=use SLR(1)

fun
LR0_construct (ProductionNr(*augmented production*)): LR0StateNr
