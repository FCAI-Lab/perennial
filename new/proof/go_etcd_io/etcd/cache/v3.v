Require Export New.golang.theory.
From New.generatedproof Require Import go_etcd_io.etcd.cache.v3.
From New.proof Require Export sync sort fmt go_etcd_io.etcd.client.v3
  k8s_io.utils.third_party.forked.golang.btree.

Section init.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : cache.Assumptions}.
Collection W := sem + package_sem.
Local Set Default Proof Using "W".

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

End init.

Section ring_buffer.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : cache.Assumptions}.
Collection W := sem + package_sem.
Local Set Default Proof Using "W".

(* [buf] is an append-only list of everything that has ever been appended. An
   arbitrary prefix of the appended stuff might have been physically compacted
   away. *)
Axiom own_ringBuffer :
  ∀ (r : loc) [T'] `[!ZeroVal T'] `[!TypedPointsto (Σ:=Σ) T'] [V]
    (is_item : T' → V → iProp Σ) (item_rev : V → w64) (buf : list V), iProp Σ.

Axiom wp_ringBuffer__PeekOldest :
  ∀ (r : loc) [T'] `[!ZeroVal T'] `[!TypedPointsto (Σ:=Σ) T'] `[!IntoValTyped T' T] [V]
    (is_item : T' → V → iProp Σ) (item_rev : V → w64) (buf : list V),
  {{{ is_pkg_init cache ∗
      own_ringBuffer r is_item item_rev buf }}}
    r @! (go.PointerType (cache.ringBuffer T)) @! "PeekOldest" #()
  {{{ RET #(last (item_rev <$> buf) (W64 0));
      own_ringBuffer r is_item item_rev buf }}}.

End ring_buffer.


Section store.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : cache.Assumptions}.
Collection W := sem + package_sem.
Local Set Default Proof Using "W".

Definition kvItem : Type := (go_string + KeyValue.t).
Axiom is_kvItem : loc → kvItem → iProp Σ.
Axiom less_kvItem : kvItem → kvItem → Prop.

(* Cannot be persistent because of RWMutex. *)
Definition own_store (s : loc) : iProp Σ :=
  "Hmu" ∷ own_RWMutex (s.[cache.store.t, "mu"])
    (λ q,
       ∃ snapshot kvs_ordered,
       "latest" ∷ s.[cache.store.t, "latest"] ↦ snapshot ∗
       "latest_tree" ∷ (own_BTree (snapshot.(cache.snapshot.tree'))
                          is_kvItem less_kvItem kvs_ordered (DfracOwn q)) ∗
       (* latest.rev seems like it must be monotonic, since linearizable Get
          relies on checking lower bound before reading. *)
       True
    ) ∗
  "_" ∷ True.

Definition is_snapshot (snap_ptr : loc) (kvs : gmap go_string KeyValue.t) : iProp Σ :=
  True.

Definition is_etcd_state (rev : w64) (kvs : gmap go_string KeyValue.t) : iProp Σ :=
  True.

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

End store.
