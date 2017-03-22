staload "./Grammar.sats"
//
abstype Input = ptr
//

fun Input_make_list (List(string)): Input

fun Input_isnot_empty (Input): bool

fun Input_peek (Input): Terminal

fun Input_pop (Input): Input
