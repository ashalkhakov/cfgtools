#include "share/atspre_staload.hats"

staload UN = "prelude/SATS/unsafe.sats"

staload "./../SATS/fundigraph.sats"
staload _ = "./../DATS/fundigraph.dats"

dynload "./../DATS/fundigraph.dats"

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
