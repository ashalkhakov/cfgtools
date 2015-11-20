#include "share/atspre_staload.hats"

staload UN = "prelude/SATS/unsafe.sats"

(* ****** ****** *)

staload "./fundigraph.sats"

datatype Digraph (int) = {n:nat} Digraph (n) of (size_t n, arrayref (List (size_t), n))

assume digraph_type (n:int) = Digraph (n)

implement
fundigraph_make {n} (n) = let
  val nil = list_nil{size_t} ()
  val aref = arrayref_make_elt<List(size_t)> (n, nil)
  val res = Digraph (n, aref)
in
  res
end // end of [fundigraph_make]

implement
fundigraph_insert_edge {n,i,j} (dg, src, dst) = let
  val Digraph (sz, aref) = dg
  var adj = arrayref_get_at (aref, src)
  val dst = (g0ofg1)dst
  // NOTE: we should be checking for duplicates here!
  prval () = lemma_list_param (adj)
  val adj = list_cons (dst, adj)
  val () = arrayref_set_at (aref, src, adj)
in
  (*empty*)
end // end of [fundigraph_insert_edge]

implement
fundigraph_size (dg) = let
  val Digraph (sz, aref) = dg
in
  sz
end // end of [fundigraph_size]

implement{}
fprint_fundigraph$sep (out: FILEref) = fprint! (out, "; ")
implement{}
fprint_fundigraph$edgeto (out: FILEref) = fprint!(out, "->")
implement
fprint_fundigraph (out, dg) = {
//
val Digraph (sz, aref) = dg
prval [n:int] EQINT () = eqint_make_guint (sz)
//  
implement
fprint_list$sep<> (out) = fprint_fundigraph$sep<> (out)
//
implement(env)
array_iforeach$fwork<List(size_t)><env> (i, xs, env) = {
  val () =
    if i > (i2sz)0 then fprint_fundigraph$sep<> (out)
  // end of [val]
  val () = fprint!(out, "vertex ", i, " {")
  val () = fprint_list<size_t> (out, xs)
  val () = fprint!(out, "}")
} (* end of [arrayref_foreach$fwork] *)
//
val _(*length*) = arrayref_iforeach<List(size_t)> (aref, sz)
//
} (* end of [fprint_fundigraph] *)

implement{env}
fundigraph_foreach_dfs$fwork (src, dst, env) = ()
implement{env}
fundigraph_foreach_dfs_from_env {n} (dg, root, env) = let
  val Digraph (sz, aref) = dg
  val (pf_vis, pf_visf | p_vis) = array_ptr_alloc<bool> (sz)
  prval [l:addr] EQADDR () = eqaddr_make_ptr (p_vis)
  val () = array_initize_elt<bool> (!p_vis, sz, false)

  typedef T = size_t

  fun
  aux {m:nat} (
    pf_vis: !array_v (bool, l, n) >> _
  | stack: list_vt (T, m)
  , env: &(env) >> _
  ): void =
    case+ :(pf_vis: array_v (bool, l, n), env: env) => stack of
    | ~list_vt_cons (x0, stack1) => let
      val x = $UN.cast{sizeLt(n)} (x0)
    in
      if :(pf_vis: array_v (bool, l, n), env: env) => ~(!p_vis.[x]) then let
        val () = array_set_at_guint (!p_vis, x, true)
        val () = fundigraph_foreach_dfs$fwork<env> ((g0ofg1)root, (g0ofg1)x, env)
        val xs = arrayref_get_at (aref, x)
        //
        vtypedef senv0 = ptr
        vtypedef senv1 = (array_v (bool, l, n) | List_vt(T))
        //
        extern
        castfn senv_to (senv0):<> senv1
        extern
        castfn senv_fro (senv1):<> senv0
        //
        implement
        list_foreach$fwork<T><senv0> (dst, env) = let
          val (pf_arr | stack) = senv_to (env)
          val dst = $UN.cast{sizeLt(0)}(dst)
        in
          if :(env: senv0) => !p_vis.[dst] = false then let
            prval () = lemma_list_vt_param {T} (stack)
            val dst = (g0ofg1)dst
            val list = list_vt_cons (dst, stack)
            val () = env := senv_fro (@(pf_arr | list))
          in
            (*empty*)
          end else let
            val () = env := senv_fro (@(pf_arr | stack))
          in
          end
        end // end of [list_foreach$fwork]
        //
        val senv = (pf_vis | stack1)
        var senv_ = senv_fro (senv)
        val () = list_foreach_env<T><senv0> (xs, senv_)
        val senv = senv_to (senv_)
        prval () = pf_vis := senv.0
        val stack2 = senv.1
        prval () = lemma_list_vt_param (stack2)
      in
        aux (pf_vis | stack2, env)
      end else begin
        aux (pf_vis | stack1, env)
      end
    end // end of [let]
    | ~list_vt_nil () => ()
  // end of [aux]

  val stack = list_vt_sing (root)

  val () = aux (pf_vis | stack, env)

  val () = array_ptr_free {bool} (pf_vis, pf_visf | p_vis)
in
end // end of [fundigraph_foreach_reachable]
//
implement{env}
fundigraph_foreach_edge$fwork (src, dst, env) = ()
implement{env}
fundigraph_foreach_edge {n} (dg, env) = let
//
val Digraph (sz, aref) = dg
//
implement
array_iforeach$fwork<List(size_t)><env> (i, xs, env) = {
  implement
  list_foreach$fwork<size_t><env> (j, env) =
    fundigraph_foreach_edge$fwork<env> (i, j, env)
  // end of [...]
  val () = list_foreach_env<size_t><env> (xs, env)
} (* end of [...] *)
val _(*length*) = arrayref_iforeach_env<List(size_t)><env> (aref, sz, env)
//
in
end
//
implement{env}
fundigraph_scc$beg (env) = ()
implement{env}
fundigraph_scc$node (v, env) = ()
implement{env}
fundigraph_scc$end (env) = ()
//
local
//
typedef
vertex_info = @{onstack=bool, index=int, lowlink= int}
//
in // in of [local]
//
implement{env}
fundigraph_scc {n} (dg, E) = let
  val Digraph (sz, aref) = dg
  
  typedef T = size_t

  #define UNDEFINED ~1

  var cur = 0 : int
  val p_cur = addr@(cur)
  prval [lc:addr] EQADDR () = eqaddr_make_ptr (p_cur)
  
  var stack = list_vt_nil {size_t} ()
  val p_stack = addr@stack
  prval [ls:addr] EQADDR () = eqaddr_make_ptr (p_stack)

  val (pf_vi, pf_vif | p_vi) = array_ptr_alloc<vertex_info> (sz)
  prval [l:addr] EQADDR () = eqaddr_make_ptr (p_vi)
  implement
  array_initize$init<vertex_info> (i, x) = {
    val () = x.onstack := false
    val () = x.index := UNDEFINED
    val () = x.lowlink := UNDEFINED
  } (* end of [array_initize$init] *)
  val () = array_initize<vertex_info> (!p_vi, sz)

  //
  viewdef V = (array_v (vertex_info, l, n), int @ lc, List_vt(T) @ ls)
  //

  fun
  strongconnect(pf: !V >> _ | v: sizeLt(n), env: &(env) >> _): void = let  
    // Set the depth index for v to the smallest unused index
    val curindex = !p_cur + 1
    val () = !p_vi.[v].index := curindex
    val () = !p_vi.[v].lowlink := curindex
    val () = !p_cur := curindex

    val () = !p_vi.[v].onstack := true
    prval () = lemma_list_vt_param (!p_stack)
    val () = !p_stack := list_vt_cons{size_t}((g0ofg1)v, !p_stack)
//
//    val () = println!("pushed: ", v)
//
    // Consider successors of v 
    fun
    aux (pf: !V >> _ | xs: List (size_t), env: &(env)): void =
      case+ xs of
      | list_nil () => ()
      | list_cons (w, xs) => let
        val w = $UN.cast{sizeLt(n)} (w)
      in
        if :(env: env) => !p_vi.[w].index = UNDEFINED then begin
          // Successor w has not yet been visited; recurse on it
          strongconnect (pf | w, env);
          !p_vi.[v].lowlink := min (!p_vi.[v].lowlink, !p_vi.[w].lowlink)
        end else if :(env: env) => !p_vi.[w].onstack then begin
          // Successor w is in stack S and hence in the current SCC
          !p_vi.[v].lowlink := min (!p_vi.[v].lowlink, !p_vi.[w].index)
        end;
        aux (pf | xs, env)
      end
//
    val xs = arrayref_get_at (aref, v)
    val () = aux (pf | xs, env)
//
    fun aux0 (pf: !V >> _ | env: &env >> _): void = let
      val- ~list_vt_cons (w, xs) = !p_stack
      val () = !p_stack := xs
      
//      val () = println!("popped: ", w, " vs ", v)
      
      val w = $UN.cast{sizeLt(n)} (w)
      var vr = array_get_at_guint (!p_vi, w)
      val () = vr.onstack := false
      val () = array_set_at_guint (!p_vi, w, vr)

//      val () = println!("calling [node]:")

      val () = fundigraph_scc$node<env> (w, env)
    in
      if w <> v then aux0 (pf | env)
    end
  in
    // If v is a root node, pop the stack and generate an SCC
    if !p_vi.[v].lowlink = !p_vi.[v].index then let
      val () = fundigraph_scc$beg<env> (env)
      val () = aux0 (pf | env)
      val () = fundigraph_scc$end<env> (env)
    in
    end
  end // end of [strongconnect]
//
  fun
  loop {i:nat | i <= n} (pf: !V >> _ | v: size_t i, env: &(env) >> _): void =
    if :(env: env) => v < sz then let
    in
      if:(env: env) => !p_vi.[v].index = UNDEFINED then
        strongconnect(pf | v, env);
      loop (pf | succ(v), env)
    end // end of [loop]
  prval pf = (pf_vi, view@cur, view@stack)
  val () = loop (pf | (i2sz)0, E)
  prval () = $effmask_wrt (pf_vi := pf.0)
  prval () = $effmask_wrt (view@cur := pf.1)
  prval () = $effmask_wrt (view@stack := pf.2)
  
  val () = array_ptr_free {vertex_info} (pf_vi, pf_vif | p_vi)
  val- ~list_vt_nil () = !p_stack
in
end

end // end of [fundigraph_scc]

(* ****** ****** *)
//
typedef ENODE (n:int, l:addr, m:int) = @{sz=size_t n, p=ptr l, ncomp=int m}
typedef ENODE0 = ENODE (0, null, 0)?
absvt@ype E (n:int, m:int) = [l:addr] ENODE (n, l, m)
vtypedef E (m:int) = [n:int] E (n, m)
vtypedef E = [m:int] E (m)

extern
fun
E_init {n:int} (size_t n, &ENODE0 >> E (n, 0)): void
extern
fun
E_free {n,m:int} (&E (n, m) >> ENODE0): void
extern
fun
E_ncomp_get {n,m:int} (&E (n, m)): int(m)
extern
fun
E_ncomp_inc {n,m:int} (&E (n, m) >> E (n, m+1)): void
extern
fun
E_nnode_get {n,m:int} (&E (n, m)): size_t(n)
extern
fun
E_comp_set {n,m:int} (&E (n, m) >> _, sizeLt(n)): void
extern
fun
E_comp_get {n,m:int} (&E (n, m), sizeLt(n)): sizeLt(m)
extern
fun
fprint_E (FILEref, &E): void

local

assume E (n:int, m:int) = [l1:addr] @{
  pf_compa= array_v (int, l1, n)
, pf_compf= mfree_gc_v (l1)
, n= size_t n
, pcomp= ptr l1
, ncomp= int m
} (* end of [assume] *)

in // in of [local]

implement
E_init {n} (sz, env) = let
//
  prval () = let
    extern praxi
      __assert (!ENODE0 >> E (0, 0)): void
  in
    __assert (env)
  end
//
fun aux (env: &E (0, 0) >> E (n, 0)): void = {
//
  val (pf_node_scc, pf_node_scc_free | p_node_scc) = array_ptr_alloc<int> (sz)
  prval [l1:addr] EQADDR () = eqaddr_make_ptr (p_node_scc)
//
  val () = array_initize_elt<int> (!p_node_scc, sz, ~1)
  prval () = array_v_unnil {int} (env.pf_compa)
  prval () = $effmask_wrt (env.pf_compa := pf_node_scc)
  prval () = __assert (env.pf_compf) where {
    extern
    prfun
    __assert {l:addr} (mfree_gc_v (l)): void
  } (* end of [prval] *)
  prval () = $effmask_wrt (env.pf_compf := pf_node_scc_free)
  val () = env.n := sz
  val () = env.pcomp := p_node_scc
  val () = env.ncomp := 0
} (* end of [aux] *)
//
val () = aux (env)
//
in
  (*empty*)
end // end of [E_init]
//
implement
E_free {n,m} (env) = {
  val () = array_ptr_free (env.pf_compa, env.pf_compf | env.pcomp)
  prval () = __assert (env) where {
    extern
    prfun
    __assert {a:vt0p} (&a >> ENODE0): void
  } (* end of [val] *)
} (* end of [E_free] *)
//
implement
E_ncomp_get {n,m} (env) = env.ncomp
//
implement
E_ncomp_inc {n,m} (env) = {
  val () = env.ncomp := succ(env.ncomp)
} (* end of [E_ncomp_inc] *)
//
implement
E_nnode_get {n,m} (env) = env.n
//
implement
E_comp_set {n,m} (env, v) = {
  val ncomp = (g0ofg1)env.ncomp
  val () = !(env.pcomp).[v] := ncomp
} (* end of [E_comp_set] *)
//
implement
E_comp_get {n,m} (env, v) = let
  val res = array_get_at_guint<int> (!(env.pcomp), v)
  val res = $UN.cast{sizeLt(m)} (res)
in
  res
end // end of [E_comp_get]
//
implement
fprint_E (out, env) = {
  val () = fprint_array<int> (stdout_ref, !(env.pcomp), env.n)
} (* end of [fprint_E] *)
//
end // end of [local]

vtypedef E1NODE (n:int, m:int, l:addr) = @{comp= E (n, m), p_adj=ptr l}
typedef E1NODE0 = E1NODE (0, 0, null)?
absvt@ype E1 (n:int, m:int) = [l:addr] E1NODE (n, m, l)
vtypedef E1 (m:int) = [n:int] E1 (n, m)
vtypedef E1 = [m:int] E1 (m)

extern
fun E1_init {n,m:int} (&E (n, m) >> ENODE0, &E1NODE0 >> E1 (n, m)): void
extern
fun E1_free {n,m:int} (&E1 (n, m) >> E1NODE0): void
extern
fun E1_nnode_get {n,m:int} (&E1 (n, m)): size_t n
extern
fun E1_ncomp_get {n,m:int} (&E1 (n, m)): size_t m
extern
fun E1_edge_set {n,m:int} (env: &E1 (n, m) >> E1 (n, m), src: sizeLt(n), dst: sizeLt(n)): void
extern
fun
E1_step {n,m:int}
  (env: &E1 (n, m) >> E1 (n, m), k: sizeLt(m), i: sizeLt(m), j: sizeLt(m)): void
extern
fun E1_reachable {n,m:int} (env: &E1 (n, m), src: sizeLt(n), dst: sizeLt(n)): bool
extern
fun fprint_E1 (FILEref, &E1): void

local

assume E1 (n:int, m:int) = [l:addr] @{
  comp= E (n, m)
, pf_adja= matrix_v (bool, l, m, m)
, pf_adjf= mfree_gc_v (l)
, p_adj= ptr l
} (* end of [assume] *)

in // in of [local]

implement
E1_init {n,m} (e, env) = {
//
  prval () = let
    extern praxi
      __assert (!E1NODE0 >> E1 (0)): void
  in
    __assert (env)
  end
//
  val ncomp = E_ncomp_get (e)
  val () = assert_errmsg (ncomp >= 0, "nr components < 0!")
  val ncomp = (i2sz)ncomp
  prval [m:int] EQINT () = eqint_make_guint (ncomp)
  val (pf_adj, pf_adj_free | p_adj) = matrix_ptr_alloc<bool> (ncomp, ncomp)
//
  implement
  matrix_initize$init<bool> (i, j, x) = {
    // this is a matrix of paths, and there is always a 0-length path
    // from any vertex to itself
    val () = x := (i = j)
  } (* end of [matrix_initize$init] *)
  val () = matrix_initize<bool> (!p_adj, ncomp, ncomp)
  prval pf_adja0 = matrix2array_v {bool} (env.pf_adja)
  prval () = array_v_unnil {bool} (pf_adja0)
  prval () = $effmask_wrt (env.pf_adja := pf_adj)
  prval () = __assert (env.pf_adjf) where {
    extern
    prfun
    __assert {l:addr} (mfree_gc_v (l)): void
  } (* end of [prval] *)
  prval () = $effmask_wrt (env.pf_adjf := pf_adj_free)
  val () = let
    extern praxi
      __assert {a:vt0p} (!a >> ENODE0): void
    prval () = __assert (env.comp)
    val () = env.comp := e
    prval () = __assert (e)
  in
  end // end of [prval]
  val () = env.p_adj := p_adj
} (* end of [E1_init] *)
//
implement
E1_free {n,m} (env) = {
  val () = E_free (env.comp)
  val () = matrix_ptr_free {bool} (
    env.pf_adja
  , env.pf_adjf
  | env.p_adj
  ) (* end of [val] *)
  prval () = __assert (env) where {
    extern
    prfun
    __assert {a:vt0p} (&a >> E1NODE0): void
  } (* end of [val] *)
} (* end of [E1_free] *)
//
implement
E1_nnode_get {n,m} (env) = E_nnode_get (env.comp)
//
implement
E1_ncomp_get {n,m} (env) = let
  val ncomp = E_ncomp_get (env.comp)
  // NOTE: ncomp >= 0
  val ncomp = $UN.cast{size_t(m)} (ncomp)
  // val ncomp = (i2sz)ncomp
in
  ncomp
end // end of [E1_ncomp_get]
//
fun get_arr {n,m:int} (env: &E(n, m) >> E(n, m), i: sizeLt(n)): sizeLt(m) = let
  val res = E_comp_get {n,m} (env, i)
in
  res
end // end of [get_arr]
//
implement
E1_edge_set {n,m} (env, src, dst) = {
  val i = get_arr (env.comp, src)
  val j = get_arr (env.comp, dst)

  val () = fprintln!(stdout_ref, "edge componentized: ", i, "->", j)

  val ncomp = E_ncomp_get (env.comp)
  val ncomp = (i2sz)ncomp
  prval pf_mat = env.pf_adja
  val p_mat = env.p_adj
  val () = matrix_set_at_size<bool> (!(p_mat), i, ncomp, j, true)
  prval () = $effmask_wrt (env.pf_adja := pf_mat)
} (* end of [E1_edge_set] *)
//
implement
E1_step {n,m} (env, k, i, j) = let
  val ncomp = E1_ncomp_get (env)
  prval pf_mat = env.pf_adja
  val p_mat = env.p_adj
  val ij = matrix_get_at_size<bool> (!p_mat, i, ncomp, j)
  val ik = matrix_get_at_size<bool> (!p_mat, i, ncomp, k)
  val kj = matrix_get_at_size<bool> (!p_mat, k, ncomp, j)
  val res = ij || ik && kj
  val () = matrix_set_at_size<bool> (!(p_mat), i, ncomp, j, res)
  prval () = $effmask_wrt (env.pf_adja := pf_mat)
in
end // end of [E1_step]
//
implement
E1_reachable {n,m} (env, src, dst) = let
  val i = get_arr (env.comp, src)
  val j = get_arr (env.comp, dst)
//
  val () = fprint!(
    stdout_ref, "reachable: (src=", src, ",dst=", dst, ") maps to (", i, ",", j, "): result ")
//
in
//
if i = j then let

  val () = fprintln! (stdout_ref, "true (same component)")

in
  true
end else let
  val ncomp = E_ncomp_get (env.comp)
  val ncomp = (i2sz)ncomp
  prval pf_mat = env.pf_adja
  val p_mat = env.p_adj
  // is component j reachable from component i?
  val res = matrix_get_at_size<bool> (!(p_mat), i, ncomp, j)
  prval () = $effmask_wrt (env.pf_adja := pf_mat)

  val () = fprintln! (stdout_ref, res)

in
  res
end // end of [if]
//
end // end of [E1_reachable]
//
implement
fprint_E1 (out, env) = {
  val ncomp = E_ncomp_get (env.comp)
  implement
  fprint_matrix$sep2<> (out) = fprint_newline (out)
  val () = fprint_matrix<bool> (stdout_ref, !(env.p_adj), ncomp, ncomp)
} (* end of [fprint_E1] *)
//
end // end of [local]
//
datavtype DIGRAPH_RTC (int) = {n,m:int} DIGRAPH_RTC (n) of E1 (n, m)
assume digraph_rtc (n:int) = DIGRAPH_RTC (n)
//
implement
fundigraph_rtc_init {n} (g) = let
//
  val sz = fundigraph_size (g)
  var scc_info : ENODE (0, null, 0)
  val () = E_init (sz, scc_info)
//
  implement
  fundigraph_scc$beg<E> (env) = () (*println!("beg of component: ", E_ncomp_get(env))*)
//
  implement
  fundigraph_scc$node<E> (v, env) = {
    val n = E_nnode_get (env)
    prval [n:int] EQINT() = eqint_make_guint (n)
    (*
    val () = println!("component assigned: ", v, " to: ", E_ncomp_get (env))
    *)
    val v = $UN.cast{sizeLt(n)} (v)
    val () = E_comp_set (env, v)
  } (* end of [...] *)
//
  implement
  fundigraph_scc$end<E> (env) = {
    val () = E_ncomp_inc (env)
  } (* end of [...] *)
//
  val () = fundigraph_scc<E> (g, scc_info)
(*
  val () = fprintln!(stdout_ref, "initial graph:")
  val () = fprint_fundigraph (stdout_ref, g)
  val () = fprintln!(stdout_ref)
  val () = println!("total components identified: ", E_ncomp_get (scc_info))
  val () = println!("assignment of nodes to components: ")
  val () = fprint_E (stdout_ref, scc_info)
  val () = println!()
*)
//
  val res = DIGRAPH_RTC (_)
  // build a DAG
  val+DIGRAPH_RTC (env1) = res
  prval () = let
    extern prfun
    __assert {a:vt0p} (&a >> E1NODE0): void
  in
    __assert (env1)
  end
//
  val () = E1_init (scc_info, env1)
//
  (*
  val () = println!("DAG of components:")
  *)
  implement
  fundigraph_foreach_edge$fwork<E1> (src, dst, env) = {
    val n = E1_nnode_get (env)
    prval [n:int] EQINT () = eqint_make_guint (n)
    val src = $UN.cast{sizeLt(n)} (src)
    val dst = $UN.cast{sizeLt(n)} (dst)
    val () = fprintln!(stdout_ref, "edge: ", src, "->", dst)
    val () = E1_edge_set (env, src, dst)
  } (* end of [fundigraph_foreach_edge$fwork] *)
//
  // add in the edges from the source graph
  val () = fundigraph_foreach_edge<E1> (g, env1)
  // finally, compute the transitive closure
  val m = E1_ncomp_get (env1)
  prval [m:int] EQINT () = eqint_make_guint (m)
  //
  prval () = lemma_g1uint_param (m)
  var k = (i2sz)0
  //
  val () =
  for*
    {k:nat | k <= m} .<m-k>. (env1: E1 (m), k: size_t k) =>
    (k := (i2sz)0; k < m; k := succ(k)) (let
    var i = (i2sz)0
  in
    for*
      {i:nat | i <= m} .<m-i>. (env1: E1 (m), i: size_t i) =>
      (i := (i2sz)0; i < m; i := succ(i)) (let
      var j = (i2sz)0
    in
      for* {j:nat | j <= m} .<m-j>. (env1: E1 (m), j: size_t j) =>
      (j := (i2sz)0; j < m; j := succ(j))
        E1_step (env1, k, i, j);
      j := (i2sz)0 // for lvar preservation
    end); (* end of [for*] *)
    i := (i2sz)0 // for lvar preservation
  end) // end of [for*]
  //
  val () = k := (i2sz)0 // for lvar preservation
//
  (*
  val () = fprintln!(stdout_ref, "adjacency matrix: ")
  val () = fprint_E1 (stdout_ref, env1)
  val () = fprintln!(stdout_ref)
  *)
//
  val () = assert_errmsg (sz = E1_nnode_get(env1), "node count mismatch")
  prval () = fold@ (res)
//
in
  res
end // end of [fundigraph_rtc_init]
//
implement
fundigraph_rtc_free {n} (rtc) = {
val+@DIGRAPH_RTC (env) = rtc
val () = E1_free (env)
val () = free@rtc
} (* end of [fundigraph_rtc_free] *)
//
implement
fundigraph_rtc_reachable_from {n} (rtc, src, dst) = let
  val+@DIGRAPH_RTC (env) = rtc
  val res = E1_reachable (env, src, dst)
  val () = fold@rtc
in
  res
end // end of [fundigraph_rtc_reachable_from]
//
(* ****** ****** *)

(*

implement
main0 () = {

  var dg = fundigraph_make ((i2sz)4)

  val () = fundigraph_insert_edge (dg, (i2sz)0, (i2sz)1)
  val () = fundigraph_insert_edge (dg, (i2sz)0, (i2sz)2)
  val () = fundigraph_insert_edge (dg, (i2sz)1, (i2sz)2)
  val () = fundigraph_insert_edge (dg, (i2sz)2, (i2sz)0)
  val () = fundigraph_insert_edge (dg, (i2sz)2, (i2sz)3)
  val () = fundigraph_insert_edge (dg, (i2sz)3, (i2sz)3)
  
  val () = fprintln!(stdout_ref, "digraph: ", dg)
  implement(env)
  fundigraph_foreach_dfs$fwork<env> (src, dst, e) = {
    val () = println!("started at: ", src, ", found: ", dst)
  } (* end of [fundigraph_foreach_dfs$fwork] *)
  var env: void
  val () = println!("testing DFS:")
  val () = fundigraph_foreach_dfs_from_env (dg, (i2sz)2, env)
  // should print: 2 0 1 3

  val () = println!("finished!")

  // test strongly connected components
  var dg1 = fundigraph_make ((i2sz)5)

  val () = fundigraph_insert_edge (dg1, (i2sz)1, (i2sz)0)
  val () = fundigraph_insert_edge (dg1, (i2sz)0, (i2sz)2)
  val () = fundigraph_insert_edge (dg1, (i2sz)2, (i2sz)1)
  val () = fundigraph_insert_edge (dg1, (i2sz)0, (i2sz)3)
  val () = fundigraph_insert_edge (dg1, (i2sz)3, (i2sz)4)

  val () = fprintln!(stdout_ref, "digraph: ", dg1)

  absvt@ype E = @{sz=size_t, p=ptr, ncomp=int}
  assume E = [n:int;l1:addr] @{pf_compa=array_v (int, l1, n), pf_compf=mfree_gc_v (l1), n=size_t n, pcomp=ptr l1, ncomp=int}

  val (pf_node_scc, pf_node_scc_free | p_node_scc) = array_ptr_alloc<int> ((i2sz)5)
  prval [l1:addr] EQADDR () = eqaddr_make_ptr (p_node_scc)
  
  val () = array_initize_elt<int> (!p_node_scc, (i2sz)5, ~1)
  var scc_info = @{pf_compa=pf_node_scc, pf_compf=pf_node_scc_free, n=(i2sz)5, pcomp=p_node_scc, ncomp=0} : E
  
  implement
  fundigraph_scc$beg<E> (env) = println!("beg of component: ", env.ncomp)
  implement
  fundigraph_scc$node<E> (v, env) = let
    prval [n:int] EQINT() = eqint_make_guint (env.n)
    val () = println!("component assigned: ", v, " to: ", env.ncomp)
    val v = $UN.cast{sizeLt(n)} (v)
    val () = !(env.pcomp).[v] := env.ncomp
  in
  end // end of [...]
  implement
  fundigraph_scc$end<E> (env) = let
    val () = env.ncomp := succ(env.ncomp)
  in
  end // end of [...]
   
  val () = println!("testing SCC:")
  val () = fundigraph_scc<E> (dg1, scc_info)
  val () = println!("total components identified: ", scc_info.ncomp)
  val () = println!("assignment of nodes to components: ")
  val () = fprint_array<int> (stdout_ref, !(scc_info.pcomp), scc_info.n)
  
  val () = array_ptr_free {int} (scc_info.pf_compa, scc_info.pf_compf | scc_info.pcomp)
}

*)
