staload "./Grammar.sats"
staload "./Input.sats"

abst@ype State = int

fun
State_make (): State

datatype ActionType =
  | ATreduce of ProductionNr
  | ATshift of State
  | ATaccept


fun
Action_put_shift (State, Terminal, State): void

fun
Action_put_reduce (State, Terminal, ProductionNr): void

fun
Action_put_accept (State, Terminal): void

fun
Goto_put (State, Nonterminal, State): void
//

fun Action (State, Terminal): Option (ActionType)

fun Goto (State, Nonterminal): Option (State)

//
fun
automaton_run (Input, State(*initial*)): void
