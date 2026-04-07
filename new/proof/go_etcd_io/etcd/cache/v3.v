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

Definition is_rpctypes_init : iProp Σ :=
  ∃ err_future_rev err_compacted,
  "#ErrFutureRev" ∷ (global_addr rpctypes.ErrFutureRev) ↦□ interface.ok err_future_rev ∗
  "#ErrCompacted" ∷ (global_addr rpctypes.ErrCompacted) ↦□ interface.ok err_compacted.
#[global] Instance : IsPkgInit (iProp Σ) rpctypes := define_is_pkg_init is_rpctypes_init%I.
#[global] Instance : GetIsPkgInitWf (iProp Σ) rpctypes := build_get_is_pkg_init_wf.

Definition is_init : iProp Σ :=
  ∃ err_not_ready,
  "#ErrNotRead" ∷ (global_addr cache.ErrNotReady) ↦□ interface.ok err_not_ready.
#[global] Instance : IsPkgInit (iProp Σ) cache := define_is_pkg_init is_init.
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
Notation snap := (w64 * list KeyValue.t)%type.
Definition is_snapshotItem (l : loc) (s : snap) : iProp Σ :=
  ∃ tree,
    "#snapshot" ∷ l ↦□ (cache.snapshot.mk s.1 tree) ∗
    "#tree" ∷ (own_BTree tree is_kvItem less_kvItem (inr <$> s.2) DfracDiscarded).

Definition rev_snapshotItem : snap → w64 := fst.

Axiom is_etcd_kvs :
  ∀ (revision : w64) (prefix : go_string) (key_values : gmap go_string KeyValue.t), iProp Σ.
Axiom is_etcd_kvmap_pers : ∀ revision prefix key_values,
  Persistent (is_etcd_kvs revision prefix key_values).
Global Existing Instance is_etcd_kvmap_pers.

Definition ordered_kvs_to_map (kvs : list KeyValue.t) : gmap go_string KeyValue.t :=
  list_to_map ((λ kv, (kv.(KeyValue.key), kv)) <$> kvs).

Record store_names :=
  {
    latest_rev_gn : gname
  }.

(* Cannot be persistent because of RWMutex. *)
Definition own_store (s : loc) γstore (prefix : go_string) : iProp Σ :=
  "Hmu" ∷ own_RWMutex (s.[cache.store.t, "mu"])
    (λ q,
       ∃ snapshot kvs_ordered history,
       "latest" ∷ s.[cache.store.t, "latest"] ↦ snapshot ∗
       "latest_tree" ∷ (own_BTree (snapshot.(cache.snapshot.tree'))
                          is_kvItem less_kvItem (inr <$> kvs_ordered) (DfracOwn q)) ∗
       "history" ∷ (own_ringBuffer (s.[cache.store.t, "history"])
                       is_snapshotItem rev_snapshotItem history) ∗
       "Hrev" ∷ mono_nat_auth_own γstore.(latest_rev_gn) 1 (sint.nat snapshot.(cache.snapshot.rev')) ∗
       "#Hhistory" ∷ (
           ∀ revision i s,
             ⌜ (history !! i) = Some s ∧
               (sint.Z s.1 ≤ sint.Z revision ∧
                (match history !! (S i) with
                 | Some next => sint.Z revision < sint.Z next.1
                 | None => sint.Z revision ≤ sint.Z snapshot.(cache.snapshot.rev')
                 end)) ⌝ →
             is_etcd_kvs revision prefix (ordered_kvs_to_map s.2)
         )
    ) ∗
  "_" ∷ True.

Lemma wp_store__getSnapshot rev_lb s γstore (rev : w64) prefix :
  {{{ is_pkg_init cache ∗ "Hs" ∷ own_store s γstore prefix ∗
      "#Hlb" ∷ mono_nat_lb_own γstore.(latest_rev_gn) rev_lb
  }}}
    s @! (go.PointerType cache.store) @! "getSnapshot" #rev
  {{{ snap_ptr (latest_rev : w64) err, RET (#snap_ptr, #latest_rev, #err);
      own_store s γstore prefix ∗
      match err with
      | interface.nil =>
          (∃ kvs snap_rev,
              is_snapshotItem snap_ptr (snap_rev, kvs) ∗
              ∃ rev',
                ⌜ if decide (rev = W64 0) then
                    rev_lb ≤ sint.nat rev'
                  else rev' = rev ⌝ ∗
                  is_etcd_kvs rev' prefix (ordered_kvs_to_map kvs))
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
  { iDestruct (is_pkg_init_access with "[$]") as "@".
    wp_auto.
    iCombineNamed "*_inv" as "Hinv".
    wp_apply (wp_RWMutex__RUnlock with "[$Hrlocked Hinv]").
    { iNamed "Hinv". iFrame "∗#%". }
    iIntros "Hmu". wp_auto. wp_end. }
  wp_if_destruct.
  { wp_apply wp_slice_literal.
    { iIntros. wp_auto. iFrame. }
    iIntros "% [Hsl _]". wp_auto.
    wp_apply (wp_Errorf with "[$Hsl]") as "%err _".
    wp_auto.
    iCombineNamed "*_inv" as "Hinv".
    wp_apply (wp_RWMutex__RUnlock with "[$Hrlocked Hinv]").
    { iNamed "Hinv". iFrame "∗#%". }
    iIntros "Hmu". wp_auto. wp_end. }

  iPersist "s".
  wp_if_join (λ v, ⌜ v = execute_val ⌝ ∗
                   "latest_inv" ∷ s.[cache.store.t, "latest"] ↦ snapshot ∗
                   "rev" ∷ rev_ptr ↦ (if decide (rev = W64 0) then snapshot.(cache.snapshot.rev')
                                      else rev)
             )%I with "[latest_inv rev]".
  { iFrame. done. }
  { rewrite decide_False //. iFrame. done. }
  iDestruct (mono_nat_lb_own_valid with "[$] [$]") as "%Hle".
  iIntros "% [-> @]".
  wp_auto.
  wp_if_destruct.
  { iAssert (is_pkg_init rpctypes) with "[]" as "#H".
    { iPkgInit. }
    iDestruct (is_pkg_init_access with "[$H]") as "@".
    wp_auto.
    iCombineNamed "*_inv" as "Hinv".
    wp_apply (wp_RWMutex__RUnlock with "[$Hrlocked Hinv]").
    { iNamed "Hinv". iFrame "∗#%". }
    iIntros "Hmu". wp_auto. wp_end. }
  simpl in *.
  rename Φ into Ψ. iRename "HΦ" into "HΨ".
  wp_apply (wp_ringBuffer__DescendLessOrEqual (λ i, "->" ∷ ⌜ i = O ⌝ ∗ _)%I with "[-]").
  { iFrame. iSplitR; first done. iNamedAccu. }
  { iIntros "*".
    wp_start as "(@ & %Hlookup & Hitem)".
    wp_auto. wp_end. iIntros "history_inv". wp_auto. wp_if_destruct.
    { iExFalso. iNamed "Hitem". iDestruct (typed_pointsto_not_null with "snapshot") as %Hbad.
      done. }
    iCombineNamed "*_inv" as "Hinv".
    wp_apply (wp_RWMutex__RUnlock with "[$Hrlocked Hinv]").
    { iNamed "Hinv". iFrame "∗#%". }
    iIntros "Hmu". wp_auto.
    iApply "HΨ". iFrame.
    rewrite reverse_lookup_Some in Hlookup. destruct Hlookup as [Hlookup ?].
    ereplace (?[x] - 1)%nat with (Nat.pred ?x) in Hlookup.
    2:{ lia. }
    pose proof (list_elem_of_lookup_2 _ _ _ Hlookup) as Hitemv.
    rewrite list_elem_of_filter in Hitemv.
    rewrite -last_lookup in Hlookup.
    apply last_filter_Some in Hlookup as (old_history & new_history & ? & Hnot).
    subst.
    iExists (if decide (rev = W64 0) then snapshot.(cache.snapshot.rev') else rev).
    iSplitR.
    { iPureIntro. destruct decide; word. }
    iApply "Hhistory_inv". iPureIntro.
    split_and!.
    - instantiate (1:=length old_history).
      rewrite lookup_app_r; last by len.
      rewrite Nat.sub_diag. done.
    - destruct itemv; simpl in *. word.
    - rewrite lookup_app_r.
      2:{ word. }
      ereplace (S ?[x] - ?x)%nat with 1%nat by lia. simpl.
      destruct new_history; simpl.
      { word. }
      { destruct p. rewrite Forall_cons_iff in Hnot. simpl in *. word. }
  }
  {
    iIntros "history_inv @". wp_auto.
    iAssert (is_pkg_init rpctypes) with "[]" as "#H".
    { iPkgInit. }
    iDestruct (is_pkg_init_access with "[$H]") as "@".
    wp_auto.
    iCombineNamed "*_inv" as "Hinv".
    wp_apply (wp_RWMutex__RUnlock with "[$Hrlocked Hinv]").
    { iNamed "Hinv". iFrame "∗#%". }
    iIntros "Hmu". wp_auto. iApply "HΨ". iFrame.
  }
Qed.

Lemma wp_store__LatestRev s γstore prefix :
  {{{ is_pkg_init cache ∗ own_store s γstore prefix }}}
    s @! (go.PointerType cache.store) @! "LatestRev" #()
  {{{ (r : w64), RET #r; own_store s γstore prefix }}}.
Proof.
  wp_start as "@". wp_apply wp_with_defer as "%defer defer". simpl subst.
  wp_auto.
  wp_apply (wp_RWMutex__RLock with "[$Hmu]").
  iIntros "[Hrlocked Hown]". wp_auto.
  iNamedSuffix "Hown" "_inv". wp_auto.
  iCombineNamed "*_inv" as "Hinv".
  wp_apply (wp_RWMutex__RUnlock with "[$Hrlocked Hinv]").
  { iNamed "Hinv". iFrame "∗#%". }
  iIntros "Hmu". wp_auto. wp_end.
Qed.

Definition own_Cache c_ptr : iProp Σ :=
  ∃ c γstore,
    "c" ∷ c_ptr ↦ c ∗
    "store" ∷ own_store c.(cache.Cache.store') γstore c.(cache.Cache.prefix')
.

Lemma wp_Cache__Get c (ctx : interface.t) (key : go_string) opts_sl (opts : list v3.clientv3.OpOption.t):
  {{{ is_pkg_init cache ∗
      "opts_sl" ∷ opts_sl ↦* opts ∗
      "cache" ∷ own_Cache c
  }}}
    c @! (go.PointerType cache.Cache) @! "Get" #ctx #key #opts_sl
  {{{
        (resp : loc) (err : error.t), RET (#resp, #err); True
  }}}.
Proof.
  wp_start as "@". iNamedSuffix "cache" "_c".
  wp_auto.
  wp_apply (wp_store__LatestRev with "[$store_c]") as "% store_c".
  wp_auto.
  wp_if_destruct.
  { (* TODO: spec for WaitReady() *) admit. }
Admitted.

End store.
