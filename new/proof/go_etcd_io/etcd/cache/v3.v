Require Export New.golang.theory.
From New.generatedproof Require Import go_etcd_io.etcd.cache.v3.
From New.proof Require Export sync sort fmt.

Section wps.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : cache.Assumptions}.
Collection W := sem + package_sem.
Set Default Proof Using "W".

(* TODO: move these. *)
#[global] Instance : IsPkgInit (iProp Σ) cmp := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf (iProp Σ) cmp := build_get_is_pkg_init_wf.

#[global] Instance : IsPkgInit (iProp Σ) btree := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf (iProp Σ) btree := build_get_is_pkg_init_wf.

#[global] Instance : IsPkgInit (iProp Σ) rpc.status.pkg_id.status := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf (iProp Σ) rpc.status.pkg_id.status := build_get_is_pkg_init_wf.

#[global] Instance : IsPkgInit (iProp Σ) pkg_id.status := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf (iProp Σ) pkg_id.status := build_get_is_pkg_init_wf.

#[global] Instance : IsPkgInit (iProp Σ) codes := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf (iProp Σ) codes := build_get_is_pkg_init_wf.

#[global] Instance : IsPkgInit (iProp Σ) rpctypes := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf (iProp Σ) rpctypes := build_get_is_pkg_init_wf.

#[global] Instance : IsPkgInit (iProp Σ) cache := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf (iProp Σ) cache := build_get_is_pkg_init_wf.

(* Cannot be persistent because of RWMutex. *)
Definition own_store (s : loc) : iProp Σ :=
  "Hmu" ∷ own_RWMutex (s.[cache.store.t, "mu"]) (λ q, True) ∗
  "_" ∷ True.

(* TODO: import etcd client specs ecomps; value should be mvccpb.KeyValue. *)
Definition is_snapshot (snap_ptr : loc) (kvs : gmap go_string go_string) : iProp Σ :=
  True.

Definition is_etcd_state (rev : w64) (kvs : gmap go_string go_string) : iProp Σ :=
  True.

(* FIXME: shouldn't the returned revision be the same as the requested, at least
   by the time Get() returns? Wonder if that's also a bug. *)

Lemma wp_store__getSnapshot s (rev : w64) :
  {{{ is_pkg_init cache ∗ "Hs" ∷ own_store s }}}
    s @! (go.PointerType cache.store) @! "getSnapshot" #rev
  {{{ snap_ptr snap_rev err, RET (#snap_ptr, #snap_rev, #err);
      match err with
      | interface.nil =>
          (∃ kvs,
              is_snapshot snap_ptr kvs ∗
              is_etcd_state snap_rev kvs)
      | _ => True
      end
  }}}.
Proof.
  wp_start as "@".
  wp_apply wp_with_defer as "%defer defer". simpl subst.
  iNamed "Hs".
  wp_auto.
  wp_apply (wp_RWMutex__RLock with "[$Hmu]").
  iIntros "[Hrlocked Hown]". wp_auto.
Admitted.

End wps.
