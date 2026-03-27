Require Export New.golang.theory.
From New.generatedproof Require Import k8s_io.utils.third_party.forked.golang.btree.
From New.proof Require Export sync sort fmt go_etcd_io.etcd.client.v3.

Section wps.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : btree.Assumptions}.
Collection W := sem + package_sem.
Local Set Default Proof Using "W".
#[global] Instance : IsPkgInit (iProp Σ) cmp := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf (iProp Σ) cmp := build_get_is_pkg_init_wf.

#[global] Instance : IsPkgInit (iProp Σ) btree := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf (iProp Σ) btree := build_get_is_pkg_init_wf.

Axiom own_BTree :
  ∀ (t : loc) [T'] `[!ZeroVal T'] `[!TypedPointsto (Σ:=Σ) T'] [V]
    (is_item : ∀ (p : T') (v : V), iProp Σ) (less : V → V → Prop)
    (items : list V) (dq : dfrac),
  iProp Σ.

Axiom own_BTree_dfractional :
  ∀ (t : loc) [T'] `[!ZeroVal T'] `[!TypedPointsto (Σ:=Σ) T'] [V]
    (is_item : ∀ (p : T') (v : V), iProp Σ) (less : V → V → Prop)
    (items : list V),
  DFractional (own_BTree t is_item less items).
#[global] Existing Instance own_BTree_dfractional.

Axiom wp_BTree__Clone :
  ∀ [T'] `[!ZeroVal T'] `[!TypedPointsto (Σ:=Σ) T'] `[!IntoValTyped T' T] [V]
    (is_item : ∀ (p : T') (v : V), iProp Σ) (less : V → V → Prop)
    (items : list V),

  ∀ (t : loc),
  {{{ is_pkg_init btree ∗
      own_BTree t is_item less items (DfracOwn 1) }}}
    t @! (go.PointerType (btree.BTree T)) @! "Clone" #()
  {{{ t', RET #t';
      own_BTree t is_item less items (DfracOwn 1) ∗
      own_BTree t' is_item less items (DfracOwn 1) }}}.

Axiom wp_BTree__Get :
  ∀ [T'] `[!ZeroVal T'] `[!TypedPointsto (Σ:=Σ) T'] `[!IntoValTyped T' T] [V]
    (is_item : ∀ (p : T') (v : V), iProp Σ) (less : V → V → Prop)
    (items : list V),

  ∀ (t : loc) (key_item : T') (key : V) dq,
  {{{ is_pkg_init btree ∗
      own_BTree t is_item less items dq ∗ is_item key_item key }}}
    t @! (go.PointerType (btree.BTree T)) @! "Get" #key
  {{{ (item : T') found, RET (#item, #found);
      own_BTree t is_item less items dq ∗
      match found with
      | false => ⌜ item = zero_val T' ⌝
      | true => ∃ itv, is_item item itv ∗ ⌜ ¬(less itv key) ∧ ¬(less key itv) ∧ itv ∈ items ⌝
      end
  }}}.

Axiom wp_BTree__ReplaceOrInsert :
  ∀ [T'] `[!ZeroVal T'] `[!TypedPointsto (Σ:=Σ) T'] `[!IntoValTyped T' T] [V]
    (is_item : ∀ (p : T') (v : V), iProp Σ) (less : V → V → Prop)
    (items : list V),

  ∀ (t : loc) (item : T') (itv : V),
  {{{ is_pkg_init btree ∗
      own_BTree t is_item less items (DfracOwn 1) ∗ is_item item itv }}}
    t @! (go.PointerType (btree.BTree T)) @! "ReplaceOrInsert" #key
  {{{ (old_item : T') (found : bool) items', RET (#old_item, #found);
      own_BTree t is_item less items' (DfracOwn 1)
      (* TODO: this is a conservative but weak spec; it does not constrain the
         final tree state. *)
  }}}.

End wps.
