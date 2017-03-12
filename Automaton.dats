staload "./Grammar.sats"
staload "./Automaton.sats"
staload "./Input.sats"

(* ****** ****** *)
//
staload _ = "prelude/DATS/basics.dats"
staload _ = "prelude/DATS/integer.dats"
staload _ = "prelude/DATS/reference.dats"
staload _ = "prelude/DATS/list.dats"
staload _ = "prelude/DATS/list_vt.dats"
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
fprint_val<State> (out, s) = fprint!(out, s)
//
implement
print_State (s) = fprint!(stdout_ref, s)
//
implement
fprint_val<ActionType> (out, act) =
  case+ act of
  | ATreduce p => (
    fprint!(out, "reduce(");
    fprint_val<ProductionNr> (out, p);
    fprint!(out,")")
  )
  | ATshift s => (
    fprint!(out, "shift(");
    fprint_val<State> (out, s);
    fprint!(out, ")")
  )
  | ATaccept () => fprint!(out, "accept")
//
implement
ActionType_print (act) = fprint_val<ActionType> (stdout_ref, act)
//
implement
compare_key_key<State> (x, y) = compare (x, y)
//
implement
compare_key_key<key> (x, y) = let
  val c = compare_key_key<State> (x.0, y.0)
in
  if c = 0 then let
    val res = compare_Symbol_Symbol (x.1, y.1)
    val () = ignoret(0) // HX: to circumvent a tail-call optimization bug in patsopt!!!
  in
    res
  end else c
end
//
implement
compare_key_key<key1> (x, y) = let
  val c = compare (x.0, y.0)
in
  if c = 0 then let
    val res = compare_Symbol_Symbol (x.1, y.1)
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
//
fun
the_state_count () = the_state_cnt[]
//
implement
Action_put_shift (s0, t, s1) = let
  var res: itm?
  var map = the_actions[]
  val k = @(s0, t)
  //
  val shift = ATshift(s1)
  //
  val ex = funmap_insert<key,itm> (map, k, shift, res)
  val () = the_actions[] := map
in
  if :(res: itm?) => ex then let
    val new = opt_unsome_get (res)
  in
    print!("conflict: new is ");
    ActionType_print (shift);
    print!(", old is ");
    ActionType_print (new);
    print_newline ()
  end else let
    prval () = opt_clear (res)
  in
    (*empty*)
  end
end

implement
Action_put_reduce (s0, t, p) = let
  var res: itm?
  var map = the_actions[]
  //
  val reduce = ATreduce(p)
  //
  val ex = funmap_insert<key,itm> (map, @(s0, t), reduce, res)
  val () = the_actions[] := map
in
  if :(res: itm?) => ex then let
    val new = opt_unsome_get (res)
  in
    print!("conflict: new is ");
    ActionType_print (reduce);
    print!(", old is ");
    ActionType_print (new);
    print_newline ()
  end else let
    prval () = opt_clear (res)
  in
    (*empty*)
  end
end

implement
Action_put_accept (s0, t) = let
  var res: itm?
  var map = the_actions[]
  val k = @(s0, t)
  //
  val accept = ATaccept ()
  //
  val ex = funmap_insert<key,itm> (map, k, accept, res)
  val () = the_actions[] := map
in
  if :(res: itm?) => ex then let
    val new = opt_unsome_get (res)
  in
    print!("conflict: new is ");
    ActionType_print (accept);
    print!(", old is ");
    ActionType_print (new);
    print_newline ()
  end else let
    prval () = opt_clear (res)
  in
    (*empty*)
  end
end
//
implement
fprint_val<key> (out, k) = let
  val (k0, k1) = k
  val () = fprint!(out, "(")
  val () = fprint_val<State> (out, k0)
  val () = fprint!(out, ", ")
  val () = fprint_val<Symbol> (out, k1)
  val () = fprint!(out, ")")
in
end
//
implement
fprint_val<key1> (out, k) = let
  val (k0, k1) = k
  val () = fprint!(out, "(")
  val () = fprint_val<State> (out, k0)
  val () = fprint!(out, ", ")
  val () = fprint_val<Symbol> (out, k1)
  val () = fprint!(out, ")")
in
end
//
fun
print_action (): void = let
  val map_actions = the_actions[]
  implement{}
  fprint_funmap$sep (out) = fprint_string (out, "\n")
  val () = fprint_funmap<key,itm> (stdout_ref, map_actions)
in
end
//
fun
print_goto (): void = let
  val map_goto = the_goto[]
  implement{}
  fprint_funmap$sep (out) = fprint_string (out, "\n")
  val () = fprint_funmap<key1,itm1> (stdout_ref, map_goto)
in
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

extern
fun
fprint_aux (out: FILEref, r: ResultTree): void

local

fun aux0 (out: FILEref, i:int, xs: List(ResultTree)): void = let
in
//
case+ xs of
//
| list_nil () => ()
| list_cons (x, xs) => (
  if i > 0 then fprint_string (out, ", ");
  aux1 (out, x);
  aux0 (out, i+1, xs)
)
//
end // end of [aux0]
//
and aux1 (out: FILEref, x: ResultTree): void = (
//
case+ x of
//
| RTleaf trm => fprint!(out, trm)
| RTnode (ntm, lst) => {
//
val () = fprint!(out, ntm, "{")
val () = aux0 (out, 0, lst)
val () = fprint!(out, "}")
//
}
//
) (* end of [aux1] *)

in // in of [local]

implement
fprint_aux (out, r) = aux1 (out, r)

end // end of [local]

implement
fprint_val<ResultTree> (out, r) = fprint_aux (out, r)
implement
ResultTree_fprint (out, r) = fprint_aux (out, r)
implement
ResultTree_print (r) = ResultTree_fprint (stdout_ref, r)

(* ****** ****** *)

//
datatype
AutomatonResult =
  | Success of ResultTree
  | Error of string
  | Cont of (bool(*true: consume the input symbol*), Stack, List(ResultTree))
//
extern
fun
automaton_step (Terminal, Stack, List(ResultTree)): AutomatonResult
//
implement
automaton_step (trm, stack, result) = let
//
val s = Stack_peek_top (stack)
//
in
//
case+ Action (s, trm) of
| None () => let

  extern
  castfn
  s2i (State): int
  val () = print!("Action: no action for state ", (s2i)s)
  val () = print!(" and terminal ")
  val () = Symbol_print(trm)
  val () = print_newline ()

in
  Error ("no action for state and terminal")
end
| Some act => (
//
case+ act of
| ATshift s => let
  val stack = Stack_push (stack, s)
  prval () = lemma_list_param (result)
  val result = list_cons (RTleaf trm, result)
in
  Cont (true(*consume*), stack, result)
end
| ATreduce p => let
//
  val np = Production_item_count (p)
  val stack = Stack_pop_many (stack, np)
  val s = Stack_peek_top (stack)
  val head = Production_yields (p)

  val np1 = (g1ofg0)np
  val () = assert_errmsg (np1 >= 0, "np1 < 0")
  val () = assert_errmsg (np1 <= list_length(result), "np1 is wrong!")
  val (itms, result1) = list_split_at (result, np1)
  val itms = list_vt_reverse (itms)
  val itms = list_vt2t (itms)
  val result2 = list_cons (RTnode (head, itms), result1)

  val opt = Goto (s, head)
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
  Cont (false(*retain*), stack, result2)
end
//
end
//
| ATaccept () => let
  val fst = list_head_exn(result)
in
  Success fst
end
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
aux (input: Input, stack: Stack, result: List(ResultTree)): void =
//
if Input_isnot_empty (input) then let
  val i = Input_peek (input)
  val input1 = Input_pop (input)
  val res = automaton_step (i, stack, result)
in
  case+ res of
  | Success result => (
    println!("success! result of parsing:");
    println!(result)
  ) (* end of [Success] *)
  | Error msg => println!("error! message: ", msg)
  | Cont (consume, stack, result) => let
    val input2 = if consume then input1 else input
  in
    aux (input2, stack, result)
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
val result = list_nil ()
//
in
  aux (input, stack, result)
end
//
implement
automaton_print () = let
//
  val () = println!("automaton printout below")
//
  val () = println!("states: from 0 to ", the_state_count ())
//
  val () = println!("action table:")
  val () = print_action ()
  val () = print_newline ()
  val () = println!("goto table:")
  val () = print_goto ()
  val () = print_newline ()
//
in
end
