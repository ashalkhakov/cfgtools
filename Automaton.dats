staload "./Grammar.sats"
staload "./Automaton.sats"
staload "./Input.sats"

(* ****** ****** *)
//
staload _ = "prelude/DATS/basics.dats"
staload _ = "prelude/DATS/integer.dats"
staload _ = "prelude/DATS/reference.dats"
staload _ = "prelude/DATS/list.dats"
staload _ = "prelude/DATS/pointer.dats"
staload _ = "prelude/DATS/gorder.dats"
//
staload _= "./Grammar.dats"
staload _= "./Input.dats"
//
local
//
assume State = int
val the_state_cnt = ref(0) : ref(int)
//
staload "libats/SATS/funmap_rbtree.sats"
//
staload
_(*anon*) = "libats/DATS/qlist.dats"
staload
_(*anon*) = "libats/DATS/funmap_rbtree.dats"
staload
_(*anon*) = "prelude/DATS/unsafe.dats"
//
typedef key = @(State,Terminal)
typedef key1 = @(State,Nonterminal)
typedef itm = ActionType
typedef itm1 = State
typedef map = map (key, itm)
typedef map1 = map (key1, itm1)
//
val the_actions = ref (funmap_make_nil{key,itm} ())
val the_goto = ref (funmap_make_nil{key1,itm1} ())
//
in // in of [local]
//
implement
compare_key_key<State> (x, y) = compare (x, y)
//
implement
compare_key_key<key> (x, y) = let
  val c = compare_key_key<State> (x.0, y.0)
in
  if c = 0 then let
    val res = compare_key_key<Symbol> (x.1, y.1)
    val () = ignoret(0) // HX: to circumvent a tail-call optimization bug in patsopt!!!
  in
    res
  end else c
end
//
implement
compare_key_key<key1> (x, y) = let
  val c = compare_key_key<State> (x.0, y.0)
in
  if c = 0 then let
    val res = compare_key_key<Symbol> (x.1, y.1)
    val () = ignoret(0) // HX: to circumvent a tail-call optimization bug in patsopt!!!
  in
    res
  end else c
end
//
implement
State_make () = let
  val next_state = the_state_cnt[]
  val () = the_state_cnt[] := next_state + 1
in
  next_state
end

implement
Action_put_shift (s0, t, s1) = let
  var res: itm?
  var map = the_actions[]
  val k = @(s0, t)
  val-false = funmap_insert<key,itm> (map, k, ATshift(s1), res)
  val () = the_actions[] := map
  prval () = opt_clear (res)
in
  (*empty*)
end

implement
Action_put_reduce (s0, t, p) = let
  var res: itm?
  var map = the_actions[]
  val-false = funmap_insert<key,itm> (map, @(s0, t), ATreduce(p), res)
  val () = the_actions[] := map
  prval () = opt_clear (res)
in
  (*empty*)
end

implement
Action_put_accept (s0, t) = let
  var res: itm?
  var map = the_actions[]
  val k = @(s0, t)
  val-false = funmap_insert<key,itm> (map, k, ATaccept(), res)
  val () = the_actions[] := map
  prval () = opt_clear (res)
in
  (*empty*)
end
//
implement
Goto_put (s0, nt, s1) = let
  var res: itm1?
  var map = the_goto[]
  val k = @(s0, nt)
  val-false = funmap_insert<key1,itm1> (map, k, s1, res)
  val () = the_goto[] := map
  prval () = opt_clear (res)
in
  (*empty*)
end
//
implement
Action (s, t) = let
  val map = the_actions[]
  var act : itm
  val k = @(s, t)
  val res = $effmask_ref (funmap_search<key,itm> (map, k, act))
in
  if :(act : itm?) => res then let
    val action = opt_unsome_get<itm> (act)
  in
    Some(action)
  end else let
    prval () = opt_unnone {itm} (act)
  in
    None()
  end
end
//
implement
Goto (s, nt) = let
  val map = the_goto[]
  var goto : itm1
  val k = @(s, nt)
  val res = $effmask_ref (funmap_search<key1,itm1> (map, k, goto))
in
  if :(goto : itm1?) => res then let
    val state = opt_unsome_get<itm1> (goto)
  in
    Some(state)
  end else let
    prval () = opt_unnone {itm1} (goto)
  in
    None()
  end
end
//
end
//
(* ****** ****** *)
//
abstype Stack = ptr
//
extern
fun Stack_make_empty (): Stack
extern
fun Stack_pop_many (Stack, int): Stack
extern
fun Stack_pop_one (Stack): Stack
extern
fun Stack_peek_top (Stack): State
extern
fun Stack_push (Stack, State): Stack
//
//
local
//
assume Stack = List(State)
//
in // in of [local]
//
implement
Stack_make_empty () = list_nil ()
//
implement
Stack_pop_many (s, i) = let
  val i = (g1ofg0)i
  prval () = lemma_list_param (s)
  val len = list_length (s)
  val () = assert_errmsg (i >= 0, "Stack_pop_many failed: i < 0")
  val () = assert_errmsg (i <= len, "Stack_pop_many failed: i <= len")
in
  list_drop (s, i)
end
//
implement
Stack_pop_one (s) = let
  val- list_cons (_, s1) = s
in
  s1
end
//
implement Stack_peek_top (s) = let
  val- list_cons (x, s1) = s
in
  x
end
//
implement Stack_push (s, x) = let
  prval () = lemma_list_param (s)
in
  list_cons (x, s)
end
//
end // end of [local]

(* ****** ****** *)

//
datatype
AutomatonResult =
  | Success of ()
  | Error of string
  | Cont of (bool(*true: consume the input symbol*), Stack)
//
extern
fun
automaton_step (Terminal, Stack): AutomatonResult
//
implement
automaton_step (trm, stack) = let
//
val s = Stack_peek_top (stack)
//
in
//
case+ Action (s, trm) of
| None () => Error ("no action for state and terminal")
| Some act => (
//
case+ act of
| ATshift s => let
  val stack = Stack_push (stack, s)
in
  Cont (true(*consume*), stack)
end
| ATreduce p => let
//
  val np = Production_item_count (p)
  val stack = Stack_pop_many (stack, np)
  val s = Stack_peek_top (stack)
  val opt = Goto (s, Production_yields (p))
//
in
//
case+ opt of
| None () => Error ("goto undefined for state and nonterminal")
| Some s => let
//
val stack = Stack_push (stack, s)
//
in
  Cont (false(*retain*), stack)
end
//
end
//
| ATaccept () => Success ()
//
)
//
end
//
(* ****** ****** *)
//
implement
automaton_run (input, initial) = let
//
fun
aux (input: Input, stack: Stack): void =
//
if Input_isnot_empty (input) then let
  val i = Input_peek (input)
  val input1 = Input_pop (input)
  val res = automaton_step (i, stack)
in
  case+ res of
  | Success () => println!("success!")
  | Error msg => println!("error! message: ", msg)
  | Cont (consume, stack) => let
    val input2 = if consume then input1 else input
  in
    aux (input2, stack)
  end
//
end // end of [list_cons]
else {
  val () = println!("error: premature EOF!")
}
// end of [aux]
//
val stack = Stack_make_empty ()
val stack = Stack_push (stack, initial)
//
in
  aux (input, stack)
end
//
