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

(* If [buf] reaches capacity, the first entry may be removed during Append() to make space *)
Axiom own_ringBuffer :
  ∀ (r : loc) [T'] `[!ZeroVal T'] `[!TypedPointsto (Σ:=Σ) T'] [V]
    (is_item : T' → V → iProp Σ) (rev_item : V → w64) (buf : list V), iProp Σ.

Context [T'] `[!ZeroVal T'] `[!TypedPointsto (Σ:=Σ) T'] [V] `[!IntoValTyped T' T]
    {is_item : T' → V → iProp Σ} {rev_item : V → w64}.

Axiom wp_ringBuffer__PeekOldest :
  ∀ r buf,
  {{{ is_pkg_init cache ∗
      own_ringBuffer r is_item rev_item buf }}}
    r @! (go.PointerType (cache.ringBuffer T)) @! "PeekOldest" #()
  {{{ RET #(hd (W64 0) (rev_item <$> buf));
      own_ringBuffer r is_item rev_item buf }}}.

(* [P i] is the invariant that holds after [iter] has been called [i] times on
   the appropriate items. *)
Axiom wp_ringBuffer__DescendLessOrEqual :
  ∀ P (pivot : w64) (iter : func.t) r buf Φ,
  let iter_itemvs := reverse (filter (λ item, sint.Z (rev_item item) ≤ sint.Z pivot) buf) in
  is_pkg_init cache ∗
  own_ringBuffer r is_item rev_item buf ∗
  P O -∗
  (∀ i item itemv,
     {{{ P i ∗ ⌜ iter_itemvs !! i = Some itemv ⌝ ∗ is_item item itemv }}}
       #iter #(rev_item itemv) #item
     {{{ (continue : bool), RET #continue;
         if continue then P (S i) else (own_ringBuffer r is_item rev_item buf -∗ Φ #()) }}}) -∗
  (own_ringBuffer r is_item rev_item buf -∗ P (length iter_itemvs) -∗ Φ #()) -∗
  WP r @! (go.PointerType (cache.ringBuffer T)) @! "DescendLessOrEqual" #pivot #iter {{ Φ }}.

End ring_buffer.

Section store.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : cache.Assumptions}.
Collection W := sem + package_sem.
Local Set Default Proof Using "W".

(* for BTree *)
Definition kvItem : Type := (go_string + KeyValue.t).
Axiom is_kvItem : loc → kvItem → iProp Σ.
Axiom less_kvItem : kvItem → kvItem → Prop.

(* for ringbuffer *)
Definition snap : Type := (w64 * list KeyValue.t).
Axiom is_snapshotItem : loc → snap → iProp Σ.
Definition rev_snapshotItem : snap → w64 := fst.

Axiom is_etcd_kvs :
  ∀ (revision : w64) (prefix : go_string) (key_values : gmap go_string KeyValue.t), iProp Σ.
Axiom is_etcd_kvmap_pers : ∀ revision prefix key_values,
  Persistent (is_etcd_kvs revision prefix key_values).
Global Existing Instance is_etcd_kvmap_pers.

Definition ordered_kvs_to_map (kvs : list KeyValue.t) : gmap go_string KeyValue.t :=
  list_to_map ((λ kv, (kv.(KeyValue.key), kv)) <$> kvs).

(* Cannot be persistent because of RWMutex. *)
Definition own_store (s : loc) (prefix : go_string) : iProp Σ :=
  "Hmu" ∷ own_RWMutex (s.[cache.store.t, "mu"])
    (λ q,
       ∃ snapshot kvs_ordered history,
       "latest" ∷ s.[cache.store.t, "latest"] ↦ snapshot ∗
       "latest_tree" ∷ (own_BTree (snapshot.(cache.snapshot.tree'))
                          is_kvItem less_kvItem (inr <$> kvs_ordered) (DfracOwn q)) ∗
       "history" ∷ (own_ringBuffer (s.[cache.store.t, "history"])
                       is_snapshotItem rev_snapshotItem history) ∗
       "#Hhistory" ∷ (
           let history' := history ++ [(snapshot.(cache.snapshot.rev'), kvs_ordered)] in
           ∀ revision i prev next,
             ⌜ (history' !! i) = Some prev ∧
               (history' !! (S i)) = Some next ∧
               (sint.Z prev.1 ≤ sint.Z revision < sint.Z next.1) ⌝ →
             is_etcd_kvs revision prefix (ordered_kvs_to_map prev.2)
         ) ∗
       (* latest.rev seems like it must be monotonic, since linearizable Get
          relies on checking lower bound before reading. *)
       True
    ) ∗
  "_" ∷ True.

Definition is_snapshot (snap_ptr : loc) (kvs : gmap go_string KeyValue.t) : iProp Σ :=
  True.

Definition is_etcd_state (rev : w64) (kvs : gmap go_string KeyValue.t) : iProp Σ :=
  True.

(* FIXME: the history can be empty only if there was a progres notification, but
   no normal watch response. That's the only case in which DescendLessOrEqual
   would never run iter. Otherwise, by the time it's called, DescendLessOrEqual
   is guaranteed to run.

   TODO: have to reason about PeekOldest guaranteeing that DescendLessOrEqual
   will succeed.
 *)
Lemma wp_store__getSnapshot s (rev : w64) prefix :
  {{{ is_pkg_init cache ∗ "Hs" ∷ own_store s prefix }}}
    s @! (go.PointerType cache.store) @! "getSnapshot" #rev
  {{{ snap_ptr snap_rev err, RET (#snap_ptr, #snap_rev, #err);
      own_store s prefix ∗
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
  wp_apply (wp_ringBuffer__PeekOldest with "[$history_inv]").
  iIntros "history_inv". wp_auto.
  wp_if_destruct.
  { (* TODO: global rpctypes.ErrCompacted *) admit. }

  simpl in *.
  rename Φ into Ψ. iRename "HΦ" into "HΨ".
  wp_apply (wp_ringBuffer__DescendLessOrEqual (λ i, "->" ∷ ⌜ i = O ⌝ ∗ _)%I with "[-]").
  { iFrame. iSplitR; first done. iNamedAccu. }
  { iIntros "*".
    wp_start as "(@ & %Hlookup & Hitem)".
    wp_auto. wp_alloc rev_ptr2 as "rev2". wp_auto.
    wp_end. iIntros "history_inv". wp_auto. wp_if_destruct.
    { exfalso. admit. (* TODO: prove is_snapshotItem -> non-null *) }
    iCombineNamed "*_inv" as "Hinv".
    wp_apply (wp_RWMutex__RUnlock with "[$Hrlocked Hinv]").
    { iNamed "Hinv". iFrame "∗#%". }
    iIntros "Hmu". wp_auto.
    iApply "HΨ".
    iFrame. admit. (* TODO: fill in postcondition *)
  }
  {
    iIntros "history_inv @". wp_auto.
    (* TODO: spec for newClonedSnapshot *)
    wp_func_call. wp_call. wp_auto.
    wp_apply (wp_BTree__Clone with "[latest_tree_inv]").
    { (* FIXME: data race in implementation. *) admit. }
    admit.
  }
Admitted.

End store.
