Require Export New.golang.theory.
From New.generatedproof Require Import go_etcd_io.etcd.cache.v3.
From New.proof Require Export sync sort fmt go_etcd_io.etcd.client.v3.

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

Axiom own_BTree : ∀ (tree : loc) (dq : dfrac) (kvs : gmap go_string KeyValue.t), iProp Σ.

(* Cannot be persistent because of RWMutex. *)
Definition own_store (s : loc) : iProp Σ :=
  "Hmu" ∷ own_RWMutex (s.[cache.store.t, "mu"])
    (λ q,
       ∃ snapshot kvs,
       "latest" ∷ s.[cache.store.t, "latest"] ↦ snapshot ∗
       "latest_tree" ∷ own_BTree snapshot.(cache.snapshot.tree') (DfracOwn q) kvs ∗
       (* latest.rev seems like it must be monotonic, since linearizable Get
          relies on checking lower bound before reading. *)
       True
    ) ∗
  "_" ∷ True.

Definition is_snapshot (snap_ptr : loc) (kvs : gmap go_string KeyValue.t) : iProp Σ :=
  True.

Definition is_etcd_state (rev : w64) (kvs : gmap go_string KeyValue.t) : iProp Σ :=
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
  iNamedSuffix "Hown" "_inv". wp_auto.
  wp_if_destruct.
  { (* TODO: global ErrNotReady pointsto *) admit. }
  wp_if_destruct.
  { (* TODO: fmt.Errorf spec *) admit. }
  wp_if_destruct.
  { (* TODO: join the proof of the case rev==0. *) admit. }
  wp_if_destruct.
  { (* TODO: rpctypes global error variable. *) admit. }
  (* TODO: spec for peekoldest *)
Admitted.

End wps.
