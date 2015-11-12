staload "./Grammar.sats"
staload "./Configuration.sats"

abst@ype LR0StateNr = int

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

fun
LR0_construct (ProductionNr(*augmented production*)): LR0StateNr

