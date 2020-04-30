Require Import HahnBase.
Require Import List.
Require Import Permissions.
Require Import PermSolver.
Require Import Permutation.
Require Import PermutationTactic.
Require Import Prelude.
Require Import Process.
Require Import QArith.
Require Import Qcanon.
Require Import Setoid.
Require Import Utf8.

Import ListNotations.

Set Implicit Arguments.


(** * Heaps *)

Module Type Heaps(dom : Domains).
  Export dom.


(** ** Ordinary heaps *)

Definition Heap := Val -> option Val.

(** The _identity heap_ is empty at every location: *)

Definition hIden : Heap := fun _ => None.

(** Update operation for heaps: *)

Definition hUpdate (h : Heap)(l : Val)(v : option Val) :=
  update val_eq_dec h l v.


(** *** Finiteness *)

(** A heap is _finite_ if all mappings that are not free
    can be mapped to some finite structure, in this case a list. *)

Definition hFinite (h : Heap) : Prop :=
  exists xs : list Val, forall l, h l <> None -> In l xs.

Lemma hFinite_iden : hFinite hIden.
Proof. red. exists nil. intros l H. vauto. Qed.

(** The most important property of finite heaps is that
    one can always find a free entry, as shown below. *)

Lemma hFinite_free :
  forall h, hFinite h -> exists l, h l = None.
Proof.
  intros h (xs&FIN).
  assert (H1 : exists l, ~ In l xs) by apply val_inf.
  destruct H1 as (l&H).
  specialize FIN with l.
  exists l. tauto.
Qed.

(** Any heap update preserves finiteness. *)

Lemma hFinite_update :
  forall h l v,
  hFinite h -> hFinite (hUpdate h l v).
Proof.
  intros p l val (xs&FIN).
  assert (H1 : val = None \/ ~ val = None) by apply classic.
  destruct H1 as [H1|H1].
  (* [val] is free *)
  - exists xs. intros l' H2. apply FIN.
    unfold hUpdate, update in H2. desf.
  (* [val] is not free *)
  - exists (l :: xs).
    intros l' H2. specialize FIN with l'. simpls.
    unfold hUpdate, update in H2.
    destruct (val_eq_dec l l') as [|H3]; vauto.
    right. by apply FIN.
Qed.


(** ** Permission heaps cells *)

(** The set [PermHeapCell] of _permission heap cells_
    is later used as the codomain of permission heaps. *)

(** Permission heap cells can be free, invalid or occupied.
    There are three kinds of occupied heap cells, which correspond
    to the three different heap ownership predicates in the logic. *)

(** Notice that _action heap cells_ hold an extra value,
    which is a copy of the value at that heap location,
    made at the moment the action heap cell was created. *)

Inductive PermHeapCell :=
  | PHCfree
  | PHCstd(q : Qc)(v : Val)
  | PHCproc(q : Qc)(v : Val)
  | PHCact(q : Qc)(v v' : Val)
  | PHCinvalid.

Add Search Blacklist "PermHeapCell_rect".
Add Search Blacklist "PermHeapCell_ind".
Add Search Blacklist "PermHeapCell_rec".
Add Search Blacklist "PermHeapCell_sind".


(** *** Validity *)

(** Any permission heap cell [phc] is _valid_ if [phc]
    is not (explicitly) invalid, and any underlying
    fractional permission is valid. *)

Definition phcValid (phc : PermHeapCell) : Prop :=
  match phc with
    | PHCfree => True
    | PHCstd q _
    | PHCproc q _
    | PHCact q _ _ => perm_valid q
    | PHCinvalid => False
  end.

Notation "√ phc" :=
  (phcValid phc)
  (only printing, at level 80).

(** Free cells are always valid, whereas invalid cells are never valid. *)

Lemma phcValid_free : phcValid PHCfree.
Proof. ins. Qed.

Lemma phcValid_contra :
  forall phc, phcValid phc -> phc <> PHCinvalid.
Proof.
  intros phc H. unfold phcValid in H. desf.
Qed.

Hint Resolve phcValid_free phcValid_contra : core.


(** *** Disjointness *)

(** Any two permission heap cells are said to be _disjoint_
    if their underlying fractional permissions are disjoint,
    an all other components are equal apart from that. *)

(** Invalid heap cells are never disjoint with any other heap cell,
    while free heap cells are disjoint with other valid heap cells. *)

Definition phcDisj (phc1 phc2 : PermHeapCell) : Prop :=
  match phc1, phc2 with
    | PHCinvalid, _
    | _, PHCinvalid => False
    | PHCfree, PHCfree => True
    | PHCfree, phc
    | phc, PHCfree => phcValid phc
    | PHCstd q1 v1, PHCstd q2 v2 =>
        perm_disj q1 q2 /\ v1 = v2
    | PHCstd _ _, _
    | _, PHCstd _ _ => False
    | PHCproc q1 v1, PHCproc q2 v2 =>
        perm_disj q1 q2 /\ v1 = v2
    | PHCproc _ _, _
    | _, PHCproc _ _ => False
    | PHCact q1 v1 v1', PHCact q2 v2 v2' =>
        perm_disj q1 q2 /\ v1 = v2 /\ v1' = v2'
  end.

Notation "phc1 ⟂ phc2" :=
  (phcDisj phc1 phc2)
  (only printing, at level 80).

(** Heap cell disjointness is a symmetric relation *)

Global Instance phcDisj_symm : Symmetric phcDisj.
Proof.
  unfold phcDisj. red.
  ins; desf; simpls; intuition.
Qed.

(** Below are the identity laws for disjointness: *)

Lemma phcDisj_free_l :
  forall phc, phcValid phc -> phcDisj phc PHCfree.
Proof. ins. red. desf. Qed.
Lemma phcDisj_free_r :
  forall phc, phcValid phc -> phcDisj PHCfree phc.
Proof. ins. desf. Qed.

Hint Resolve phcDisj_free_l phcDisj_free_r : core.

(** Below are some other useful properties of disjointness. *)

Lemma phcDisj_valid_l :
  forall phc1 phc2, phcDisj phc1 phc2 -> phcValid phc1.
Proof.
  unfold phcDisj, phcValid.
  intros ?? H.
  repeat desf; try (by apply perm_disj_valid in H; desf).
Qed.
Lemma phcDisj_valid_r :
  forall phc1 phc2, phcDisj phc1 phc2 -> phcValid phc2.
Proof.
  intros ?? H. symmetry in H.
  by apply phcDisj_valid_l in H.
Qed.
Lemma phcDisj_valid :
  forall phc1 phc2,
  phcDisj phc1 phc2 -> phcValid phc1 /\ phcValid phc2.
Proof.
  intros phc1 phc2 H. split.
  - by apply phcDisj_valid_l in H.
  - by apply phcDisj_valid_r in H.
Qed.


(** *** Union *)

(** The (disjoint) union of two permission heap cells
    is defined as the addition of their underlying
    fractional permissions. *)

(** [PHCfree] heap cells are neutral with respect to
    disjoint union, while [PHCinvalid] are absorbing. *)

Lemma val_pair_eq_dec :
  forall x y : Val * Val, {x = y} + {x <> y}.
Proof.
  decide equality; apply val_eq_dec.
Qed.

Definition phcUnion (phc1 phc2 : PermHeapCell) : PermHeapCell :=
  match phc1, phc2 with
    | PHCinvalid, _
    | _, PHCinvalid => PHCinvalid
    | PHCfree, phc
    | phc, PHCfree => phc
    | PHCstd q1 v1, PHCstd q2 v2 =>
        if val_eq_dec v1 v2
        then PHCstd (q1 + q2) v1
        else PHCinvalid
    | PHCstd _ _, _
    | _, PHCstd _ _ => PHCinvalid
    | PHCproc q1 v1, PHCproc q2 v2 =>
        if val_eq_dec v1 v2
        then PHCproc (q1 + q2) v1
        else PHCinvalid
    | PHCproc _ _, _
    | _, PHCproc _ _ => PHCinvalid
    | PHCact q1 v1 v1', PHCact q2 v2 v2' =>
        if val_pair_eq_dec (v1, v1') (v2, v2')
        then PHCact (q1 + q2) v1 v1'
        else PHCinvalid
  end.

Notation "phc1 ⨄ phc2" :=
  (phcUnion phc1 phc2)
  (only printing, at level 80, right associativity).

(** The [phcUnion] relation is associative and commutative. *)

Lemma phcUnion_assoc :
  forall phc1 phc2 phc3,
  phcUnion phc1 (phcUnion phc2 phc3) =
  phcUnion (phcUnion phc1 phc2) phc3.
Proof.
  intros phc1 phc2 phc3.
  destruct phc1, phc2, phc3; simpls; desf;
    unfold phcUnion; desf; by rewrite Qcplus_assoc.
Qed.

Lemma phcUnion_comm :
  forall phc1 phc2,
  phcUnion phc1 phc2 = phcUnion phc2 phc1.
Proof.
  unfold phcUnion. ins.
  repeat desf; by rewrite Qcplus_comm.
Qed.

Hint Resolve phcUnion_assoc phcUnion_comm : core.

(** The following lemmas show that [PHCfree] is neutral for union. *)

Lemma phcUnion_free_l :
  forall phc, phcUnion phc PHCfree = phc.
Proof. unfold phcUnion. ins. desf. Qed.
Lemma phcUnion_free_r :
  forall phc, phcUnion PHCfree phc = phc.
Proof. unfold phcUnion. ins. desf. Qed.

Hint Rewrite phcUnion_free_l phcUnion_free_r : core.

(** Below are various other useful properties of heap cell union. *)

Lemma phcUnion_valid :
  forall phc1 phc2,
  phcDisj phc1 phc2 -> phcValid (phcUnion phc1 phc2).
Proof.
  unfold phcDisj, phcUnion, phcValid.
  ins. repeat desf; by apply perm_add_valid.
Qed.

Lemma phcDisj_union_l :
  forall phc1 phc2 phc3,
  phcDisj phc1 phc2 ->
  phcDisj (phcUnion phc1 phc2) phc3 ->
  phcDisj phc2 phc3.
Proof.
  intros ??? H1 H2.
  unfold phcUnion, phcDisj in *.
  desf; simpls; intuition; permsolve.
Qed.
Lemma phcDisj_union_r :
  forall phc1 phc2 phc3,
  phcDisj phc2 phc3 ->
  phcDisj phc1 (phcUnion phc2 phc3) ->
  phcDisj phc1 phc2.
Proof.
  intros phc1 phc2 phc3 H1 H2.
  symmetry in H1, H2.
  rewrite phcUnion_comm in H2; auto.
  apply phcDisj_union_l in H2; auto.
  by symmetry.
Qed.

Lemma phcDisj_assoc_l :
  forall phc1 phc2 phc3,
  phcDisj phc1 phc2 ->
  phcDisj (phcUnion phc1 phc2) phc3 ->
  phcDisj phc1 (phcUnion phc2 phc3).
Proof.
  unfold phcDisj, phcUnion.
  intros phc1 phc2 phc3 H1 H2.
  desf; simpls; intuition vauto; permsolve.
Qed.
Lemma phcDisj_assoc_r :
  forall phc1 phc2 phc3,
  phcDisj phc2 phc3 ->
  phcDisj phc1 (phcUnion phc2 phc3) ->
  phcDisj (phcUnion phc1 phc2) phc3.
Proof.
  intros phc1 phc2 phc3 H1 H2.
  symmetry in H1, H2.
  rewrite phcUnion_comm in H2; auto.
  apply phcDisj_assoc_l in H2; auto.
  rewrite phcUnion_comm in H2; auto.
  by symmetry.
Qed.

Lemma phcDisj_middle :
  forall phc1 phc2 phc3 phc4,
  phcDisj phc1 phc2 ->
  phcDisj phc3 phc4 ->
  phcDisj (phcUnion phc1 phc2) (phcUnion phc3 phc4) ->
  phcDisj phc2 phc3.
Proof.
  intros phc1 phc2 phc3 phc4 H1 H2 H3.
  apply phcDisj_union_l with phc1; auto.
  by apply phcDisj_union_r with phc4.
Qed.

Lemma phcDisj_compat :
  forall phc1 phc2 phc3 phc4,
  phcDisj phc1 phc3 ->
  phcDisj phc2 phc4 ->
  phcDisj (phcUnion phc1 phc3) (phcUnion phc2 phc4) ->
  phcDisj (phcUnion phc1 phc2) (phcUnion phc3 phc4).
Proof.
  intros phc1 phc2 phc3 phc4 H1 H2 H3.
  apply phcDisj_assoc_r.
  rewrite phcUnion_comm.
  apply phcDisj_assoc_l; auto.
  symmetry. by apply phcDisj_union_l in H3.
  rewrite phcUnion_comm.
  rewrite <- phcUnion_assoc.
  apply phcDisj_assoc_l; auto.
  by rewrite phcUnion_comm with phc4 phc2.
Qed.

Lemma phcUnion_swap_l :
  forall phc1 phc2 phc3,
  phcUnion phc1 (phcUnion phc2 phc3) =
  phcUnion phc2 (phcUnion phc1 phc3).
Proof.
  intros phc1 phc2 phc3.
  rewrite phcUnion_assoc.
  rewrite phcUnion_comm with phc1 phc2.
  by rewrite phcUnion_assoc.
Qed.
Lemma phcUnion_swap_r :
  forall phc1 phc2 phc3,
  phcUnion (phcUnion phc1 phc2) phc3 =
  phcUnion (phcUnion phc1 phc3) phc2.
Proof.
  intros phc1 phc2 phc3.
  rewrite phcUnion_comm.
  rewrite phcUnion_swap_l.
  by rewrite phcUnion_assoc.
Qed.

Lemma phcUnion_compat :
  forall phc1 phc2 phc3 phc4,
  phcUnion (phcUnion phc1 phc3) (phcUnion phc2 phc4) =
  phcUnion (phcUnion phc1 phc2) (phcUnion phc3 phc4).
Proof.
  intros phc1 phc2 phc3 phc4.
  rewrite phcUnion_swap_l.
  repeat rewrite phcUnion_assoc.
  by rewrite phcUnion_comm with phc2 phc1.
Qed.

Lemma phcUnion_free :
  forall phc1 phc2,
  phcUnion phc1 phc2 = PHCfree <-> phc1 = PHCfree /\ phc2 = PHCfree.
Proof.
  intros phc1 phc2; split; intro H1.
  - unfold phcUnion in H1. desf.
  - destruct H1 as (H1&H2). clarify.
Qed.

Lemma phcUnion_not_free :
  forall phc1 phc2,
  phcUnion phc1 phc2 <> PHCfree <-> phc1 <> PHCfree \/ phc2 <> PHCfree.
Proof.
  intros phc1 phc2. split; intro H.
  - unfold phcUnion in H. desf; vauto.
  - unfold phcUnion. desf; vauto.
Qed.


(** *** Orderings *)

(** The following (strict) partial order defines the
    'less than' relation on permission heap cells. *)

Definition phcLt (phc1 phc2 : PermHeapCell) : Prop :=
  match phc1, phc2 with
    | PHCfree, PHCfree => False
    | PHCfree, _ => True
    | PHCstd q1 v1, PHCstd q2 v2
    | PHCproc q1 v1, PHCproc q2 v2 => q1 < q2 /\ v1 = v2
    | PHCact q1 v1 v1', PHCact q2 v2 v2' => q1 < q2 /\ v1 = v2 /\ v1' = v2'
    | _, _ => False
  end.

Notation "phc1 ≺ phc2" :=
  (phcLt phc1 phc2)
  (only printing, at level 80).

(** The [phcLt] relation is a strict partial order
    (i.e., irreflexive, asymmetric and transitive).  *)

Global Instance phcLt_irrefl : Irreflexive phcLt.
Proof.
  red. red. intros phc H.
  unfold phcLt in H. repeat desf.
  - by apply Qclt_irrefl with q.
  - by apply Qclt_irrefl with q.
  - by apply Qclt_irrefl with q.
Qed.
Global Instance phcLt_trans : Transitive phcLt.
Proof.
  red. intros phc1 phc2 phc3 H1 H2.
  unfold phcLt in *.
  repeat desf; intuition vauto.
  - by apply Qclt_trans with q1.
  - by apply Qclt_trans with q1.
  - by apply Qclt_trans with q1.
Qed.
Global Instance phcLt_asymm : Asymmetric phcLt.
Proof.
  red. intros phc1 phc2 H1 H2.
  assert (H3 : phcLt phc1 phc1) by by (transitivity phc2).
  by apply phcLt_irrefl in H3.
Qed.
Global Instance phcLt_strictorder : StrictOrder phcLt.
Proof. split; intuition. Qed.

(** Below are several other useful properties of [phcLt]. *)

Lemma phcLt_mono_pos :
  forall phc1 phc2,
  phcDisj phc1 phc2 ->
  phcLt PHCfree phc2 ->
  phcLt phc1 (phcUnion phc1 phc2).
Proof.
  intros phc1 phc2 H1 H2.
  unfold phcDisj, phcValid in H1.
  unfold phcLt in *. unfold phcUnion.
  repeat desf; simpls; intuition vauto.
  - permsolve.
  - permsolve.
  - permsolve.
Qed.

Lemma phcLt_mono_l :
  forall phc1 phc2 phc3,
  phcDisj phc3 phc2 ->
  phcLt phc1 phc2 ->
  phcLt (phcUnion phc3 phc1) (phcUnion phc3 phc2).
Proof.
  intros phc1 phc2 phc3 H1 H2.
  destruct phc3; vauto.
  (* [phc3] is free *)
  - by repeat rewrite phcUnion_free_r.
  (* [phc3] is a standard heap cell *)
  - unfold phcDisj, phcUnion, phcLt in *.
    repeat desf; intuition.
    + permsolve.
    + clear H1. by apply Qcplus_lt_mono_l.
  (* [phc3] is a process heap cell *)
  - unfold phcDisj, phcUnion, phcLt in *.
    repeat desf; intuition.
    + permsolve.
    + clear H1. by apply Qcplus_lt_mono_l.
  (* [phc3] is an action heap cell *)
  - unfold phcDisj, phcUnion, phcLt in *.
    repeat desf; intuition.
    + permsolve.
    + clear H1. by apply Qcplus_lt_mono_l.
Qed.
Lemma phcLt_mono_r :
  forall phc1 phc2 phc3,
  phcDisj phc2 phc3 ->
  phcLt phc1 phc2 ->
  phcLt (phcUnion phc1 phc3) (phcUnion phc2 phc3).
Proof.
  intros phc1 phc2 phc3 H1 H2.
  rewrite phcUnion_comm with phc1 phc3.
  rewrite phcUnion_comm with phc2 phc3.
  apply phcLt_mono_l; auto. by symmetry.
Qed.

Lemma phcLt_diff :
  forall phc1 phc2,
  phcValid phc1 ->
  phcValid phc2 ->
  phcLt phc1 phc2 ->
  exists phc3, phcDisj phc1 phc3 /\ phcUnion phc1 phc3 = phc2.
Proof.
  intros phc1 phc2 H1 H2 H3.
  unfold phcValid in H1, H2.
  unfold phcLt in H3. repeat desf; vauto.
  (* [phc1] is free and [phc2] a 'standard' cell *)
  - exists (PHCstd q v). vauto.
  (* [phc1] is free and [phc2] a 'process' cell *)
  - exists (PHCproc q v). vauto.
  (* [phc1] is free and [phc2] an 'action' cell *)
  - exists (PHCact q v v'). vauto.
  (* [phc1] and [phc2] are both 'standard' cells *)
  - apply perm_lt_diff in H3; auto.
    destruct H3 as (q'&H3&H4); vauto.
    exists (PHCstd q' v0). intuition vauto.
    unfold phcUnion. desf.
  (* [phc1] and [phc2] are both 'process' cells *)
  - apply perm_lt_diff in H3; auto.
    destruct H3 as (q'&H3&H4); vauto.
    exists (PHCproc q' v0). intuition vauto.
    unfold phcUnion. desf.
  (* [phc1] and [phc2] are both 'action' cells *)
  - apply perm_lt_diff in H3; vauto.
    destruct H3 as (q'&H3&H4); vauto.
    exists (PHCact q' v0 v'0). intuition vauto.
    unfold phcUnion. desf.
Qed.

Lemma phcDisj_lt :
  forall phc1 phc2 phc3,
  phcValid phc1 ->
  phcDisj phc2 phc3 ->
  phcLt phc1 phc2 ->
  phcDisj phc1 phc3.
Proof.
  intros phc1 phc2 phc3 H1 H2 H3.
  generalize H2. intros H4.
  apply phcDisj_valid in H4.
  destruct H4 as (H4&H5).
  unfold phcLt in H3.
  unfold phcDisj, phcValid in *.
  repeat desf; intuition vauto.
  - by apply perm_disj_lt with q1.
  - by apply perm_disj_lt with q1.
  - by apply perm_disj_lt with q1.
Qed.

(** The following partial order defines the 'less than or equal to'
    relation on permission heap cells. *)

Definition phcLe (phc1 phc2 : PermHeapCell) : Prop :=
  match phc1, phc2 with
    | PHCfree, _ => True
    | PHCstd q1 v1, PHCstd q2 v2
    | PHCproc q1 v1, PHCproc q2 v2 => q1 <= q2 /\ v1 = v2
    | PHCact q1 v1 v1', PHCact q2 v2 v2' => q1 <= q2 /\ v1 = v2 /\ v1' = v2'
    | PHCinvalid, PHCinvalid => True
    | _, _ => False
  end.

Notation "phc1 ≼ phc2" :=
  (phcLe phc1 phc2)
  (only printing, at level 80).

(** The [phcLe] relation is a non-strict partial order. *)

Global Instance phcLe_refl : Reflexive phcLe.
Proof.
  red. intro phc. red.
  repeat desf; intuition vauto; by apply Qcle_refl.
Qed.

Hint Resolve phcLe_refl : core.

Lemma phcLt_le_weak :
  forall phc1 phc2,
  phcLt phc1 phc2 -> phcLe phc1 phc2.
Proof.
  intros phc1 phc2 H.
  unfold phcLt in H.
  unfold phcLe. repeat desf; intuition vauto.
  - by apply Qclt_le_weak.
  - by apply Qclt_le_weak.
  - by apply Qclt_le_weak.
Qed.

Lemma phcLe_lt_or_eq :
  forall phc1 phc2,
  phcLe phc1 phc2 <->
  phc1 = phc2 \/ phcLt phc1 phc2.
Proof.
  intros phc1 phc2. split; intro H.
  (* left-to-right *)
  - unfold phcLe in H. repeat desf; vauto.
    + destruct phc2; vauto.
    + apply Qcle_lt_or_eq in H. desf; vauto.
    + apply Qcle_lt_or_eq in H. desf; vauto.
    + apply Qcle_lt_or_eq in H. desf; vauto.
  (* right-to-left *)
  - destruct H as [H|H]; vauto.
    by apply phcLt_le_weak.
Qed.

Global Instance phcLe_antisym :
  Antisymmetric PermHeapCell eq phcLe.
Proof.
  red. intros phc1 phc2 H1 H2.
  apply phcLe_lt_or_eq in H1.
  apply phcLe_lt_or_eq in H2.
  destruct H1 as [H1|H1], H2 as [H2|H2]; vauto.
  by apply phcLt_asymm in H1.
Qed.
Global Instance phcLe_trans : Transitive phcLe.
Proof.
  red. intros phc1 phc2 phc3 H1 H2.
  apply phcLe_lt_or_eq in H1.
  apply phcLe_lt_or_eq in H2.
  destruct H1 as [H1|H1], H2 as [H2|H2]; vauto.
  - by apply phcLt_le_weak.
  - by apply phcLt_le_weak.
  - apply phcLt_le_weak.
    by transitivity phc2.
Qed.
Global Instance phcLe_preorder : PreOrder phcLe.
Proof. split; intuition. Qed.
Global Instance phcLe_partialorder : PartialOrder eq phcLe.
Proof.
  split.
  - intros H1. red. red. red. intuition vauto.
    red. auto.
  - intros H1. red in H1. red in H1. red in H1.
    destruct H1 as (H1&H2). red in H2.
    by apply phcLe_antisym.
Qed.

(** Below are various other useful properties of [phcLe]. *)

Lemma phcLe_valid :
  forall phc, phcLe PHCfree phc.
Proof.
  ins.
Qed.

Lemma phcLe_lt_trans :
  forall phc1 phc2 phc3,
  phcLe phc1 phc2 ->
  phcLt phc2 phc3 ->
  phcLt phc1 phc3.
Proof.
  intros phc1 phc2 phc3 H1 H2.
  apply phcLe_lt_or_eq in H1.
  destruct H1 as [H1|H1]; vauto.
  by transitivity phc2.
Qed.

Lemma phcLt_le_trans :
  forall phc1 phc2 phc3,
  phcLt phc1 phc2 ->
  phcLe phc2 phc3 ->
  phcLt phc1 phc3.
Proof.
  intros phc1 phc2 phc3 H1 H2.
  apply phcLe_lt_or_eq in H2.
  destruct H2 as [H2|H2]; vauto.
  by transitivity phc2.
Qed.

Lemma phcLt_weaken :
  forall phc1 phc2 phc3,
  phcDisj phc2 phc3 ->
  phcLt phc1 phc2 ->
  phcLt phc1 (phcUnion phc2 phc3).
Proof.
  intros phc1 phc2 phc3 H1 H2.
  apply phcLt_le_trans with phc2; auto.
  assert (H3 : PHCfree = phc3 \/ phcLt PHCfree phc3). {
    apply phcLe_lt_or_eq, phcLe_valid. }
  destruct H3 as [H3|H3].
  (* [phc3] is free *)
  - clarify. by rewrite phcUnion_free_l.
  (* [phc3] is occupied *)
  - rewrite phcLe_lt_or_eq. right.
    by apply phcLt_mono_pos.
Qed.

Lemma phcLe_weaken :
  forall phc1 phc2 phc3,
  phcDisj phc2 phc3 ->
  phcLe phc1 phc2 ->
  phcLe phc1 (phcUnion phc2 phc3).
Proof.
  intros phc1 phc2 phc3 H1 H2.
  apply phcLe_lt_or_eq in H2.
  destruct H2 as [H2|H2]; vauto.
  (* the 'equals' case *)
  - assert (H2 : PHCfree = phc3 \/ phcLt PHCfree phc3). {
      apply phcLe_lt_or_eq, phcLe_valid. }
    destruct H2 as [H2|H2].
    + clarify. by rewrite phcUnion_free_l.
    + apply phcLt_le_weak.
      by apply phcLt_mono_pos.
  (* the 'less than' case *)
  - by apply phcLt_le_weak, phcLt_weaken.
Qed.

Lemma phcLe_mono_l :
  forall phc1 phc2 phc3,
  phcDisj phc3 phc2 ->
  phcLe phc1 phc2 ->
  phcLe (phcUnion phc3 phc1) (phcUnion phc3 phc2).
Proof.
  intros phc1 phc2 phc3 H1 H2.
  apply phcLe_lt_or_eq in H2.
  destruct H2 as [H2|H2]; vauto.
  apply phcLt_le_weak.
  by apply phcLt_mono_l.
Qed.
Lemma phcLe_mono_r :
  forall phc1 phc2 phc3,
  phcDisj phc2 phc3 ->
  phcLe phc1 phc2 ->
  phcLe (phcUnion phc1 phc3) (phcUnion phc2 phc3).
Proof.
  intros phc1 phc2 phc3 H1 H2.
  rewrite phcUnion_comm with phc1 phc3.
  rewrite phcUnion_comm with phc2 phc3.
  apply phcLe_mono_l; auto.
  by symmetry.
Qed.

Lemma phcLe_mono_pos :
  forall phc1 phc2,
  phcDisj phc1 phc2 ->
  phcLe phc1 (phcUnion phc1 phc2).
Proof.
  intros phc1 phc2 H1.
  transitivity (phcUnion phc1 PHCfree).
  - by rewrite phcUnion_free_l.
  - apply phcLe_mono_l; vauto.
Qed.

Lemma phcLe_compat :
  forall phc1 phc2 phc3 phc4,
  phcDisj phc1 phc4 ->
  phcDisj phc3 phc4 ->
  phcLe phc1 phc3 ->
  phcLe phc2 phc4 ->
  phcLe (phcUnion phc1 phc2) (phcUnion phc3 phc4).
Proof.
  intros phc1 phc2 phc3 phc4.
  transitivity (phcUnion phc1 phc4).
  apply phcLe_mono_l; auto.
  apply phcLe_mono_r; auto.
Qed.

Lemma phcLe_diff :
  forall phc1 phc2,
  phcValid phc1 ->
  phcValid phc2 ->
  phcLe phc1 phc2 ->
  exists phc3, phcDisj phc1 phc3 /\ phcUnion phc1 phc3 = phc2.
Proof.
  intros phc1 phc2 H1 H2 H3.
  apply phcLe_lt_or_eq in H3.
  destruct H3 as [H3|H3]; clarify.
  (* the 'equals' case *)
  - exists PHCfree. split.
    + by apply phcDisj_free_l.
    + by rewrite phcUnion_free_l.
  (* the 'less than' case *)
  - apply phcLt_diff in H3; auto.
Qed.

Lemma phcDisj_le :
  forall phc1 phc2 phc3,
  phcValid phc1 ->
  phcDisj phc2 phc3 ->
  phcLe phc1 phc2 ->
  phcDisj phc1 phc3.
Proof.
  intros phc1 phc2 phc3 H1 H2 H3.
  apply phcLe_lt_or_eq in H3.
  destruct H3 as [H3|H3]; vauto.
  by apply phcDisj_lt with phc2.
Qed.


(** *** Entirety *)

(** Any permission heap cell [phc] is said to be _entire_
    if [phc] is occupied and holds a fractional permission [perm_full]. *)

Definition phcEntire (phc : PermHeapCell) : Prop :=
  match phc with
    | PHCfree
    | PHCinvalid => False
    | PHCstd q _
    | PHCproc q _
    | PHCact q _ _ => q = perm_full
  end.

Lemma phcEntire_union_l :
  forall phc1 phc2,
  phcDisj phc1 phc2 ->
  phcEntire phc1 ->
  phcEntire (phcUnion phc1 phc2).
Proof.
  intros phc1 phc2 H1 H2.
  unfold phcDisj in H1.
  unfold phcEntire in *.
  unfold phcUnion.
  desf; desf; permsolve.
Qed.
Lemma phcEntire_union_r :
  forall phc1 phc2,
  phcDisj phc1 phc2 ->
  phcEntire phc2 ->
  phcEntire (phcUnion phc1 phc2).
Proof.
  intros phc1 phc2 H1 H2. rewrite phcUnion_comm.
  apply phcEntire_union_l; auto.
  by symmetry.
Qed.
Lemma phcEntire_union :
  forall phc1 phc2,
  phcDisj phc1 phc2 ->
  phcEntire phc1 \/ phcEntire phc2 ->
  phcEntire (phcUnion phc1 phc2).
Proof.
  intros phc1 phc2 H1 H2.
  destruct H2 as [H2|H2].
  - by apply phcEntire_union_l.
  - by apply phcEntire_union_r.
Qed.

Lemma phcEntire_lt_neg :
  forall phc1 phc2,
  phcValid phc2 -> phcEntire phc1 -> ~ phcLt phc1 phc2.
Proof.
  intros phc1 phc2 H1 H2 H3.
  unfold phcValid in H1.
  unfold phcEntire in H2.
  unfold phcLt in H3. repeat desf.
  - permsolve.
  - permsolve.
  - permsolve.
Qed.

Lemma phcEntire_le :
  forall phc1 phc2,
  phcLe phc1 phc2 ->
  phcValid phc2 ->
  phcEntire phc1 ->
  phcEntire phc2.
Proof.
  intros phc1 phc2 H1 H2 H3.
  unfold phcValid, perm_valid in H2.
  unfold phcEntire, perm_full in *.
  desf; simpls; desf.
  - by apply Qcle_antisym.
  - by apply Qcle_antisym.
  - by apply Qcle_antisym.
Qed.

Lemma phcLe_entire_eq :
  forall phc1 phc2,
  phcValid phc2 ->
  phcEntire phc1 ->
  phcLe phc1 phc2 ->
  phc1 = phc2.
Proof.
  intros phc1 phc2 H1 H2 H3.
  apply phcLe_lt_or_eq in H3.
  destruct H3 as [H3|H3]; vauto.
  by apply phcEntire_lt_neg in H3.
Qed.

Lemma phcDisj_entire_free :
  forall phc1 phc2,
  phcDisj phc1 phc2 -> phcEntire phc1 -> phc2 = PHCfree.
Proof.
  intros phc1 phc2 H1 H2.
  unfold phcDisj in H1.
  unfold phcEntire in H2.
  repeat desf; permsolve.
Qed.

Lemma phcLt_entire_free :
  forall phc,
  phcEntire phc -> phcLt PHCfree phc.
Proof.
  intros phc H.
  unfold phcEntire in H.
  unfold phcLt. desf.
Qed.


(** *** Concretisation *)

(** The _concretisation_ of any permission heap cell [phc]
    is the underlying value of [phc] (thus removing all structure
    related to the context of the heap cell). *)

Definition phcConcr (phc : PermHeapCell) : option Val :=
  match phc with
    | PHCfree
    | PHCinvalid => None
    | PHCstd _ v
    | PHCproc _ v
    | PHCact _ v _ => Some v
  end.

Lemma phcConcr_lt_none :
  forall phc1 phc2,
  phcLt phc1 phc2 ->
  phcConcr phc2 = None ->
  phcConcr phc1 = None.
Proof.
  intros phc1 phc2 H1 H2.
  unfold phcConcr in *. desf.
Qed.
Lemma phcConcr_le_none :
  forall phc1 phc2,
  phcLe phc1 phc2 ->
  phcConcr phc2 = None ->
  phcConcr phc1 = None.
Proof.
  intros phc1 phc2 H1 H2.
  apply phcLe_lt_or_eq in H1.
  destruct H1 as [H1|H1]; vauto.
  by apply phcConcr_lt_none in H1.
Qed.

Lemma phcConcr_lt_some :
  forall phc1 phc2 v,
  phcLt phc1 phc2 ->
  phcConcr phc1 = Some v ->
  phcConcr phc2 = Some v.
Proof.
  intros phc1 phc2 v H1 H2.
  unfold phcConcr in *.
  desf; simpls; desf.
Qed.
Lemma phcConcr_le_some :
  forall phc1 phc2 v,
  phcLe phc1 phc2 ->
  phcConcr phc1 = Some v ->
  phcConcr phc2 = Some v.
Proof.
  intros phc1 phc2 v H1 H2.
  apply phcLe_lt_or_eq in H1.
  destruct H1 as [H1|H1]; vauto.
  by apply phcConcr_lt_some with (v:=v) in H1.
Qed.

Lemma phcConcr_none_free :
  forall phc,
  phcValid phc -> phcConcr phc = None -> phc = PHCfree.
Proof.
  intros phc H1 H2.
  unfold phcValid in H1.
  unfold phcConcr in H2. desf.
Qed.

Lemma phcConcr_union :
  forall phc1 phc2 v,
  phcDisj phc1 phc2 ->
  phcConcr phc1 = Some v ->
  phcConcr (phcUnion phc1 phc2) = Some v.
Proof.
  intros phc1 phc2 v H1 H2.
  apply phcConcr_le_some with phc1; vauto.
  by apply phcLe_mono_pos.
Qed.

Lemma phcConcr_compat :
  forall phc1 phc2 phc3 phc4,
  phcDisj phc1 phc2 ->
  phcDisj phc3 phc4 ->
  phcConcr phc1 = phcConcr phc3 ->
  phcConcr phc2 = phcConcr phc4 ->
  phcConcr (phcUnion phc1 phc2) = phcConcr (phcUnion phc3 phc4).
Proof.
  intros phc1 phc2 phc3 phc4 D1 D2 H1 H2.
  unfold phcDisj, phcUnion in *.
  repeat desf; vauto.
Qed.

Lemma phcConcr_disj_union_l :
  forall phc1 phc2 phc3,
  phcDisj phc1 phc3 ->
  phcDisj phc2 phc3 ->
  phcConcr phc1 = phcConcr phc2 ->
  phcConcr (phcUnion phc1 phc3) = phcConcr (phcUnion phc2 phc3).
Proof.
  intros phc1 phc2 phc3 H1 H2 H3.
  apply phcConcr_compat; vauto.
Qed.
Lemma phcConcr_disj_union_r :
  forall phc1 phc2 phc3,
  phcDisj phc1 phc3 ->
  phcDisj phc2 phc3 ->
  phcConcr phc1 = phcConcr phc2 ->
  phcConcr (phcUnion phc3 phc1) = phcConcr (phcUnion phc3 phc2).
Proof.
  intros phc1 phc2 phc3 H1 H2 H3.
  rewrite phcUnion_comm with phc3 phc1.
  rewrite phcUnion_comm with phc3 phc2.
  apply phcConcr_disj_union_l; auto.
Qed.


(** *** Snapshots *)

(** The following operation extracts the _snapshot value_
    out of a given permission heap cell. *)

Definition phcSnapshot (phc : PermHeapCell) : option Val :=
  match phc with
    | PHCfree
    | PHCinvalid
    | PHCstd _ _  => None
    | PHCproc _ v
    | PHCact _ _ v => Some v
  end.

(** Below are several useful properties of snapshot extraction. *)

Lemma phcSnapshot_compat :
  forall phc1 phc2 phc3 phc4,
  phcDisj phc1 phc2 ->
  phcDisj phc3 phc4 ->
  phcSnapshot phc1 = phcSnapshot phc3 ->
  phcSnapshot phc2 = phcSnapshot phc4 ->
  phcSnapshot (phcUnion phc1 phc2) = phcSnapshot (phcUnion phc3 phc4).
Proof.
  intros phc1 phc2 phc3 phc4 D1 D2 H1 H2.
  unfold phcDisj, phcUnion in *.
  repeat desf; vauto.
Qed.

Lemma phcConcr_snapshot_compat :
  forall phc1 phc2 phc3 phc4,
  phcDisj phc1 phc2 ->
  phcDisj phc3 phc4 ->
  phcConcr phc1 = phcSnapshot phc3 ->
  phcConcr phc2 = phcSnapshot phc4 ->
  phcConcr (phcUnion phc1 phc2) = phcSnapshot (phcUnion phc3 phc4).
Proof.
  intros phc1 phc2 phc3 phc4 D1 D2 H1 H2.
  unfold phcDisj, phcUnion in *.
  repeat desf; vauto.
Qed.

Lemma phcSnapshot_disj_union_l :
  forall phc1 phc2 phc3,
  phcDisj phc1 phc3 ->
  phcDisj phc2 phc3 ->
  phcSnapshot phc1 = phcSnapshot phc2 ->
  phcSnapshot (phcUnion phc1 phc3) = phcSnapshot (phcUnion phc2 phc3).
Proof.
  intros phc1 phc2 phc3 H1 H2 H3.
  apply phcSnapshot_compat; vauto.
Qed.
Lemma phcSnapshot_disj_union_r :
  forall phc1 phc2 phc3,
  phcDisj phc1 phc3 ->
  phcDisj phc2 phc3 ->
  phcSnapshot phc1 = phcSnapshot phc2 ->
  phcSnapshot (phcUnion phc3 phc1) = phcSnapshot (phcUnion phc3 phc2).
Proof.
  intros phc1 phc2 phc3 H1 H2 H3.
  rewrite phcUnion_comm with phc3 phc1.
  rewrite phcUnion_comm with phc3 phc2.
  apply phcSnapshot_disj_union_l; auto.
Qed.

Lemma phcSnapshot_lt_none :
  forall phc1 phc2,
  phcLt phc1 phc2 ->
  phcSnapshot phc2 = None ->
  phcSnapshot phc1 = None.
Proof.
  intros phc1 phc2 H1 H2.
  unfold phcSnapshot in *. desf.
Qed.
Lemma phcSnapshot_le_none :
  forall phc1 phc2,
  phcLe phc1 phc2 ->
  phcSnapshot phc2 = None ->
  phcSnapshot phc1 = None.
Proof.
  intros phc1 phc2 H1 H2.
  apply phcLe_lt_or_eq in H1.
  destruct H1 as [H1|H1]; vauto.
  by apply phcSnapshot_lt_none in H1.
Qed.

Lemma phcSnapshot_lt_some :
  forall phc1 phc2 v,
  phcLt phc1 phc2 ->
  phcSnapshot phc1 = Some v ->
  phcSnapshot phc2 = Some v.
Proof.
  intros phc1 phc2 v H1 H2.
  unfold phcSnapshot in *.
  desf; simpls; desf.
Qed.
Lemma phcSnapshot_le_some :
  forall phc1 phc2 v,
  phcLe phc1 phc2 ->
  phcSnapshot phc1 = Some v ->
  phcSnapshot phc2 = Some v.
Proof.
  intros phc1 phc2 v H1 H2.
  apply phcLe_lt_or_eq in H1.
  destruct H1 as [H1|H1]; vauto.
  by apply phcSnapshot_lt_some with (v:=v) in H1.
Qed.

Lemma phcSnapshot_union :
  forall phc1 phc2 v,
  phcDisj phc1 phc2 ->
  phcSnapshot phc1 = Some v ->
  phcSnapshot (phcUnion phc1 phc2) = Some v.
Proof.
  intros phc1 phc2 v H1 H2.
  apply phcSnapshot_le_some with phc1; vauto.
  by apply phcLe_mono_pos.
Qed.


(** *** Heap cell conversion *)

(** Below are three operations for converting the
    type of permission heap cells, named
    [phcConvStd], for converting to standard heap cells;
    [phcConvProc], for converting to process heap cells;
    and [phcConvAct], for converting to action heap cells. *)

Definition phcConvStd (phc : PermHeapCell) : PermHeapCell :=
  match phc with
    | PHCfree => PHCfree
    | PHCstd q v
    | PHCproc q v
    | PHCact q v _ => PHCstd q v
    | PHCinvalid => PHCinvalid
  end.

Notation "'std' { phc }" :=
  (phcConvStd phc)
  (only printing, at level 40).

Definition phcConvProc (phc : PermHeapCell) : PermHeapCell :=
  match phc with
    | PHCfree => PHCfree
    | PHCstd q v
    | PHCproc q v
    | PHCact q v _ => PHCproc q v
    | PHCinvalid => PHCinvalid
  end.

Notation "'proc' { phc }" :=
  (phcConvProc phc)
  (only printing, at level 40).

Definition phcConvAct (phc : PermHeapCell) : PermHeapCell :=
  match phc with
    | PHCfree => PHCfree
    | PHCstd q v
    | PHCproc q v => PHCact q v v
    | PHCact q v1 v2 => PHCact q v1 v2
    | PHCinvalid => PHCinvalid
  end.

Notation "'act' { phc }" :=
  (phcConvAct phc)
  (only printing, at level 40).

(** Converting any heap cell to its original types does not
    have any effect. *)

Lemma phc_std_conv :
  forall q v, PHCstd q v = phcConvStd (PHCstd q v).
Proof. ins. Qed.
Lemma phc_proc_conv :
  forall q v, PHCproc q v = phcConvProc (PHCproc q v).
Proof. ins. Qed.
Lemma phc_act_conv :
  forall q v v', PHCact q v v' = phcConvAct (PHCact q v v').
Proof. ins. Qed.

(** Heap cell conversion is idempotent. *)

Lemma phcConvStd_idemp :
  forall phc, phcConvStd (phcConvStd phc) = phcConvStd phc.
Proof. intro phc. unfold phcConvStd. desf. Qed.
Lemma phcConvProc_idemp :
  forall phc, phcConvProc (phcConvProc phc) = phcConvProc phc.
Proof. intro phc. unfold phcConvProc. desf. Qed.
Lemma phcConvAct_idemp :
  forall phc, phcConvAct (phcConvAct phc) = phcConvAct phc.
Proof. intro phc. unfold phcConvAct. desf. Qed.

(** Free heap cells always convert to free heap cells. *)

Lemma phcConvStd_free :
  phcConvStd PHCfree = PHCfree.
Proof. ins. Qed.
Lemma phcConvProc_free :
  phcConvProc PHCfree = PHCfree.
Proof. ins. Qed.
Lemma phcConvAct_free :
  phcConvAct PHCfree = PHCfree.
Proof. ins. Qed.
Lemma phcConvStd_free2 :
  forall phc, phcConvStd phc = PHCfree <-> phc = PHCfree.
Proof. unfold phcConvStd. intuition desf. Qed.
Lemma phcConvProc_free2 :
  forall phc, phcConvProc phc = PHCfree <-> phc = PHCfree.
Proof. unfold phcConvProc. intuition desf. Qed.
Lemma phcConvAct_free2 :
  forall phc, phcConvAct phc = PHCfree <-> phc = PHCfree.
Proof. unfold phcConvAct. intuition desf. Qed.

(** Invalid heap cells always convert to invalid heap cells. *)

Lemma phcConvStd_invalid :
  phcConvStd PHCinvalid = PHCinvalid.
Proof. ins. Qed.
Lemma phcConvProc_invalid :
  phcConvProc PHCinvalid = PHCinvalid.
Proof. ins. Qed.
Lemma phcConvAct_invalid :
  phcConvAct PHCinvalid = PHCinvalid.
Proof. ins. Qed.
Lemma phcConvStd_invalid2 :
  forall phc, phcConvStd phc = PHCinvalid <-> phc = PHCinvalid.
Proof. unfold phcConvStd. intuition desf. Qed.
Lemma phcConvProc_invalid2 :
  forall phc, phcConvProc phc = PHCinvalid <-> phc = PHCinvalid.
Proof. unfold phcConvProc. intuition desf. Qed.
Lemma phcConvAct_invalid2 :
  forall phc, phcConvAct phc = PHCinvalid <-> phc = PHCinvalid.
Proof. unfold phcConvAct. intuition desf. Qed.

(** Heap cell conversion preserves validity. *)

Lemma phcConvStd_valid :
  forall phc, phcValid phc <-> phcValid (phcConvStd phc).
Proof. ins. unfold phcValid, phcConvStd. intuition desf. Qed.
Lemma phcConvProc_valid :
  forall phc, phcValid phc <-> phcValid (phcConvProc phc).
Proof. ins. unfold phcValid, phcConvProc. intuition desf. Qed.
Lemma phcConvAct_valid :
  forall phc, phcValid phc <-> phcValid (phcConvAct phc).
Proof. ins. unfold phcValid, phcConvAct. intuition desf. Qed.

(** Heap cell conversion preserves disjointness. *)

Add Parametric Morphism : phcConvStd
  with signature phcDisj ==> phcDisj as phcConvStd_disj.
Proof.
  ins. unfold phcDisj in *. unfold phcConvStd.
  repeat desf; intuition simpls; auto.
Qed.
Add Parametric Morphism : phcConvProc
  with signature phcDisj ==> phcDisj as phcConvProc_disj.
Proof.
  ins. unfold phcDisj in *. unfold phcConvProc.
  repeat desf; intuition simpls; auto.
Qed.
Add Parametric Morphism : phcConvAct
  with signature phcDisj ==> phcDisj as phcConvAct_disj.
Proof.
  ins. unfold phcDisj in *. unfold phcConvAct.
  repeat desf; intuition simpls; auto.
Qed.

(** Heap cell conversion preserves entirety. *)

Lemma phcConvStd_entire :
  forall phc, phcEntire (phcConvStd phc) <-> phcEntire phc.
Proof. ins. unfold phcEntire, phcConvStd. intuition desf. Qed.
Lemma phcConvProc_entire :
  forall phc, phcEntire (phcConvProc phc) <-> phcEntire phc.
Proof. ins. unfold phcEntire, phcConvProc. intuition desf. Qed.
Lemma phcConvAct_entire :
  forall phc, phcEntire (phcConvAct phc) <-> phcEntire phc.
Proof. ins. unfold phcEntire, phcConvAct. intuition desf. Qed.

(** Below are several other properties of heap cell conversion
    for later convenience. *)

(** Note: in the following three lemmas, the validity condition
    is not neccessary for the right-to-left implication. *)

Lemma phcLt_conv_std_disj :
  forall phc2 phc3 q v,
  phcValid phc2 ->
  phcLt (PHCstd q v) phc2 ->
  phcDisj (phcConvStd phc2) phc3 <-> phcDisj phc2 phc3.
Proof.
  intros phc2 phc3 q v V1 H1. split; intro H2.
  - unfold phcConvStd in H2. unfold phcDisj in *.
    repeat desf; simpls; intuition vauto.
  - unfold phcConvStd. unfold phcDisj in *.
    repeat desf; simpls; intuition vauto.
Qed.
Lemma phcLt_conv_proc_disj :
  forall phc2 phc3 q v,
  phcValid phc2 ->
  phcLt (PHCproc q v) phc2 ->
  phcDisj (phcConvProc phc2) phc3 <-> phcDisj phc2 phc3.
Proof.
  intros phc2 phc3 q v V1 H1. split; intro D1.
  - unfold phcConvProc in D1. unfold phcDisj in *.
    repeat desf; simpls; intuition vauto.
  - unfold phcConvProc. unfold phcDisj in *.
    repeat desf; simpls; intuition vauto.
Qed.
Lemma phcLt_conv_act_disj :
  forall phc2 phc3 q v1 v2,
  phcValid phc2 ->
  phcLt (PHCact q v1 v2) phc2 ->
  phcDisj (phcConvAct phc2) phc3 <-> phcDisj phc2 phc3.
Proof.
  intros phc2 phc3 q v1 v2 V1 H1. split; intro D1.
  - unfold phcConvAct in D1. unfold phcDisj in *.
    repeat desf; simpls; intuition vauto.
  - unfold phcConvAct. unfold phcDisj in *.
    repeat desf; simpls; intuition vauto.
Qed.

Lemma phcLe_conv_std_disj :
  forall phc2 phc3 q v,
  phcValid phc2 ->
  phcLe (PHCstd q v) phc2 ->
  phcDisj (phcConvStd phc2) phc3 <-> phcDisj phc2 phc3.
Proof.
  intros phc2 phc3 q v V1 H1. split; intro D1.
  - unfold phcConvStd in D1. unfold phcDisj in *.
    repeat desf; simpls; intuition vauto.
  - unfold phcConvStd. unfold phcDisj in *.
    repeat desf; simpls; intuition vauto.
Qed.
Lemma phcLe_conv_proc_disj :
  forall phc2 phc3 q v,
  phcValid phc2 ->
  phcLe (PHCproc q v) phc2 ->
  phcDisj (phcConvProc phc2) phc3 <->
  phcDisj phc2 phc3.
Proof.
  intros phc2 phc3 q v V1 H1. split; intro D1.
  - unfold phcConvProc in D1. unfold phcDisj in *.
    repeat desf; simpls; intuition vauto.
  - unfold phcConvProc. unfold phcDisj in *.
    repeat desf; simpls; intuition vauto.
Qed.
Lemma phcLe_conv_act_disj :
  forall phc2 phc3 q v v',
  phcValid phc2 ->
  phcLe (PHCact q v v') phc2 ->
  phcDisj (phcConvAct phc2) phc3 <-> phcDisj phc2 phc3.
Proof.
  intros phc2 phc3 q v v' V1 H1. split; intro D1.
  - unfold phcConvAct in D1. unfold phcDisj in *.
    repeat desf; simpls; intuition vauto.
  - unfold phcConvAct. unfold phcDisj in *.
    repeat desf; simpls; intuition vauto.
Qed.

Lemma phcConvStd_disj_entire :
  forall phc1 phc2,
  phcEntire phc1 ->
  phcDisj phc1 phc2 ->
  phcDisj (phcConvStd phc1) phc2.
Proof.
  intros phc1 phc2 H1 H2.
  assert (H3 : phcValid phc1) by by apply phcDisj_valid_l in H2.
  apply phcDisj_entire_free in H2; auto. clarify.
  replace PHCfree with (phcConvStd PHCfree); auto.
  by apply phcConvStd_disj, phcDisj_free_r.
Qed.
Lemma phcConvProc_disj_entire :
  forall phc1 phc2,
  phcEntire phc1 ->
  phcDisj phc1 phc2 ->
  phcDisj (phcConvProc phc1) phc2.
Proof.
  intros phc1 phc2 H1 H2.
  assert (H3 : phcValid phc1) by by apply phcDisj_valid_l in H2.
  apply phcDisj_entire_free in H2; auto. clarify.
  replace PHCfree with (phcConvProc PHCfree); auto.
  by apply phcConvProc_disj, phcDisj_free_r.
Qed.
Lemma phcConvAct_disj_entire :
  forall phc1 phc2,
  phcEntire phc1 ->
  phcDisj phc1 phc2 ->
  phcDisj (phcConvAct phc1) phc2.
Proof.
  intros phc1 phc2 H1 H2.
  assert (H3 : phcValid phc1) by by apply phcDisj_valid_l in H2.
  apply phcDisj_entire_free in H2; auto. clarify.
  replace PHCfree with (phcConvAct PHCfree); auto.
  by apply phcConvAct_disj, phcDisj_free_r.
Qed.

Lemma phcConvStd_union :
  forall phc1 phc2,
  phcDisj phc1 phc2 ->
  phcConvStd (phcUnion phc1 phc2) =
  phcUnion (phcConvStd phc1) (phcConvStd phc2).
Proof.
  intros phc1 phc2 H. unfold phcDisj in H.
  unfold phcConvStd, phcUnion. repeat desf.
Qed.
Lemma phcConvProc_union :
  forall phc1 phc2,
  phcDisj phc1 phc2 ->
  phcConvProc (phcUnion phc1 phc2) =
  phcUnion (phcConvProc phc1) (phcConvProc phc2).
Proof.
  intros phc1 phc2 H. unfold phcDisj in H.
  unfold phcConvProc, phcUnion. repeat desf.
Qed.
Lemma phcConvAct_union :
  forall phc1 phc2,
  phcDisj phc1 phc2 ->
  phcConvAct (phcUnion phc1 phc2) =
  phcUnion (phcConvAct phc1) (phcConvAct phc2).
Proof.
  intros phc1 phc2 H. unfold phcDisj in H.
  unfold phcConvAct, phcUnion. repeat desf.
Qed.

Lemma phcConvStd_lt :
  forall phc1 phc2,
  phcValid phc2 ->
  phcLt phc1 phc2 ->
  phcLt (phcConvStd phc1) (phcConvStd phc2).
Proof.
  intros phc1 phc2 H1 H2.
  unfold phcValid in H1.
  unfold phcConvStd, phcLt in *.
  repeat desf.
Qed.
Lemma phcConvProc_lt :
  forall phc1 phc2,
  phcValid phc2 ->
  phcLt phc1 phc2 ->
  phcLt (phcConvProc phc1) (phcConvProc phc2).
Proof.
  intros phc1 phc2 H1 H2.
  unfold phcValid in H1.
  unfold phcConvProc, phcLt in *.
  repeat desf.
Qed.
Lemma phcConvAct_lt :
  forall phc1 phc2,
  phcValid phc2 ->
  phcLt phc1 phc2 ->
  phcLt (phcConvAct phc1) (phcConvAct phc2).
Proof.
  intros phc1 phc2 H1 H2.
  unfold phcValid in H1.
  unfold phcConvAct, phcLt in *.
  repeat desf.
Qed.

Lemma phcConvStd_le :
  forall phc1 phc2,
  phcValid phc2 ->
  phcLe phc1 phc2 ->
  phcLe (phcConvStd phc1) (phcConvStd phc2).
Proof.
  intros phc1 phc2 H1 H2.
  apply phcLe_lt_or_eq in H2.
  destruct H2 as [H2|H2]; vauto.
  by apply phcLt_le_weak, phcConvStd_lt.
Qed.
Lemma phcConvProc_le :
  forall phc1 phc2,
  phcValid phc2 ->
  phcLe phc1 phc2 ->
  phcLe (phcConvProc phc1) (phcConvProc phc2).
Proof.
  intros phc1 phc2 H1 H2.
  apply phcLe_lt_or_eq in H2.
  destruct H2 as [H2|H2]; vauto.
  by apply phcLt_le_weak, phcConvProc_lt.
Qed.
Lemma phcConvAct_le :
  forall phc1 phc2,
  phcValid phc2 ->
  phcLe phc1 phc2 ->
  phcLe (phcConvAct phc1) (phcConvAct phc2).
Proof.
  intros phc1 phc2 H1 H2.
  apply phcLe_lt_or_eq in H2.
  destruct H2 as [H2|H2]; vauto.
  by apply phcLt_le_weak, phcConvAct_lt.
Qed.

Lemma phcConvStd_concr :
  forall phc, phcConcr (phcConvStd phc) = phcConcr phc.
Proof. ins. unfold phcConcr, phcConvStd. desf. Qed.
Lemma phcConvProc_concr :
  forall phc, phcConcr (phcConvProc phc) = phcConcr phc.
Proof. ins. unfold phcConcr, phcConvProc. desf. Qed.
Lemma phcConvAct_concr :
  forall phc, phcConcr (phcConvAct phc) = phcConcr phc.
Proof. ins. unfold phcConcr, phcConvAct. desf. Qed.

Lemma phcSnapshot_conv_proc_occ :
  forall phc,
  phcSnapshot phc <> None ->
  phcSnapshot (phcConvProc phc) <> None.
Proof.
  intros phc H1. unfold phcSnapshot in *.
  unfold phcConvProc. desf.
Qed.
Lemma phcSnapshot_conv_act_occ :
  forall phc,
  phcSnapshot phc <> None ->
  phcSnapshot (phcConvAct phc) <> None.
Proof.
  intros phc H1. unfold phcSnapshot in *.
  unfold phcConvAct. desf.
Qed.

Lemma phcSnapshot_lt_conv_std :
  forall phc1 phc2,
  phcLt phc1 (phcConvStd phc2) ->
  phcSnapshot phc1 = phcSnapshot (phcConvStd phc1).
Proof.
  intros phc1 phc2 H1. unfold phcConvStd in *.
  unfold phcLt in H1. unfold phcSnapshot. desf.
Qed.
Lemma phcSnapshot_lt_conv_proc :
  forall phc1 phc2,
  phcLt phc1 (phcConvProc phc2) ->
  phcSnapshot phc1 = phcSnapshot (phcConvProc phc1).
Proof.
  intros phc1 phc2 H1. unfold phcConvProc in *.
  unfold phcLt in H1. unfold phcSnapshot. desf.
Qed.
Lemma phcSnapshot_lt_conv_act :
  forall phc1 phc2,
  phcLt phc1 (phcConvAct phc2) ->
  phcSnapshot phc1 = phcSnapshot (phcConvAct phc1).
Proof.
  intros phc1 phc2 H1. unfold phcConvAct in *.
  unfold phcLt in H1. unfold phcSnapshot. desf.
Qed.

Lemma phcSnapshot_conv_act_pres :
  forall phc v,
  phcSnapshot phc = Some v ->
  phcSnapshot (phcConvAct phc) = Some v.
Proof.
  intros phc v H.
  unfold phcSnapshot, phcConvAct in *.
  desf.
Qed.

(** Note: the following lemmas does not hold
    for process or action heap cell conversion. *)

Lemma phcConvStd_lt_eq :
  forall q v phc,
  phcLt (PHCstd q v) phc -> phc = phcConvStd phc.
Proof.
  intros q v phc H1. unfold phcConvStd in *.
  unfold phcLt in H1. desf.
Qed.


(** ** Permission heaps *)

(** Permission heaps are defined as (total) mappings
    from values to permission heap cells. *)

Definition PermHeap := Val -> PermHeapCell.

(** The identity permission heap is free at every location *)

Definition phIden : PermHeap := fun _ => PHCfree.

(** An update operation for process maps: *)

Definition phUpdate (ph : PermHeap)(v : Val)(c : PermHeapCell) :=
  update val_eq_dec ph v c.


(** *** Validity *)

(** Any permission heap [ph] is defined to be _valid_
    if every entry of [ph] is valid. *)

Definition phValid (ph : PermHeap) : Prop :=
  forall l, phcValid (ph l).

Notation "√ ph" :=
  (phValid ph)
  (only printing, at level 80).

(** The identity permission heap is valid. *)

Lemma phValid_iden : phValid phIden.
Proof. red. ins. Qed.

Hint Resolve phValid_iden : core.

(** Updating a valid permission heap with a valid entry
    results in a valid permission heap. *)

Lemma phValid_update :
  forall ph phc l,
  phValid ph -> phcValid phc -> phValid (phUpdate ph l phc).
Proof.
  intros ??????. unfold phUpdate, update. desf.
Qed.


(** *** Disjointness *)

(** Any two permission heaps are said to be _disjoint_
    if all their entries are pairwise disjoint. *)

Definition phDisj : relation PermHeap :=
  pointwise_relation Val phcDisj.

Notation "ph1 ⟂ ph2" :=
  (phDisj ph1 ph2)
  (only printing, at level 80).

(** Permission heap disjointness is symmeric. *)

Global Instance phDisj_symm : Symmetric phDisj.
Proof. intros ????. by symmetry. Qed.

(** Permission heap disjointness implies validity. *)

Lemma phDisj_valid_l :
  forall ph1 ph2, phDisj ph1 ph2 -> phValid ph1.
Proof. intros ? ph ? l. by apply phcDisj_valid_l with (ph l). Qed.
Lemma phDisj_valid_r :
  forall ph1 ph2, phDisj ph1 ph2 -> phValid ph2.
Proof. intros ph ?? l. by apply phcDisj_valid_r with (ph l). Qed.
Lemma phDisj_valid :
  forall ph1 ph2, phDisj ph1 ph2 -> phValid ph1 /\ phValid ph2.
Proof.
  intros ph1 ph2 H. split.
  - by apply phDisj_valid_l with ph2.
  - by apply phDisj_valid_r with ph1.
Qed.

(** Any valid permission heap is disjoint
    with the identity permission heap. *)

Lemma phDisj_iden_l :
  forall ph, phValid ph -> phDisj ph phIden.
Proof.
  unfold phValid, phIden.
  intros ???. by apply phcDisj_free_l.
Qed.
Lemma phDisj_iden_r :
  forall ph, phValid ph -> phDisj phIden ph.
Proof.
  unfold phValid, phIden.
  intros ???. by apply phcDisj_free_r.
Qed.

Hint Resolve phDisj_iden_l phDisj_iden_r : core.

(** Updating disjoint permission heaps with entries
    that are disjoint preserves heap disjointness. *)

Lemma phDisj_upd :
  forall ph1 ph2 phc1 phc2 l,
  phcDisj phc1 phc2 ->
  phDisj ph1 ph2 ->
  phDisj (phUpdate ph1 l phc1) (phUpdate ph2 l phc2).
Proof.
  unfold phDisj, phUpdate, update.
  intros ????????. desf.
Qed.

Add Parametric Morphism : phUpdate
  with signature phDisj ==> eq ==> phcDisj ==> phDisj
    as phDisj_upd_mor.
Proof.
  intros ph1 ph1' H1 v ph2 ph2' H2.
  by apply phDisj_upd.
Qed.


(** *** Union *)

(** The (disjoint) union of two permission heaps is defined
    to be the pairwise disjoint union of their heap cells. *)

Definition phUnion (ph1 ph2 : PermHeap) : PermHeap :=
  fun l => phcUnion (ph1 l) (ph2 l).

Notation "ph1 ⨄ ph2" :=
  (phUnion ph1 ph2)
  (only printing, at level 80, right associativity).

(** Identity laws for disjoint union. *)

Lemma phUnion_iden_l :
  forall ph, phUnion ph phIden = ph.
Proof.
  intro ph. extensionality l.
  unfold phUnion, phIden.
  apply phcUnion_free_l.
Qed.
Lemma phUnion_iden_r :
  forall ph, phUnion phIden ph = ph.
Proof.
  intro ph. extensionality l.
  unfold phUnion, phIden.
  apply phcUnion_free_r.
Qed.

Hint Rewrite phUnion_iden_l phUnion_iden_r : core.

(** Disjoint union is associative and commutative. *)

Lemma phUnion_assoc :
  forall ph1 ph2 ph3,
  phUnion (phUnion ph1 ph2) ph3 = phUnion ph1 (phUnion ph2 ph3).
Proof.
  intros ???. extensionality l.
  unfold phUnion.
  by rewrite phcUnion_assoc.
Qed.

Lemma phUnion_comm :
  forall ph1 ph2, phUnion ph1 ph2 = phUnion ph2 ph1.
Proof.
  intros ??. extensionality l.
  by apply phcUnion_comm.
Qed.

(** The union of any two disjoint permission heaps is valid. *)

Lemma phUnion_valid :
  forall ph1 ph2,
  phDisj ph1 ph2 -> phValid (phUnion ph1 ph2).
Proof.
  unfold phUnion. intros ????.
  by apply phcUnion_valid.
Qed.

Hint Resolve phUnion_valid : core.

(** Below are various other useful properties of disjoint union. *)

Lemma phDisj_union_l :
  forall ph1 ph2 ph3,
  phDisj ph1 ph2 ->
  phDisj (phUnion ph1 ph2) ph3 ->
  phDisj ph2 ph3.
Proof.
  intros ph1 ph2 ph3 H1 H2 l.
  apply phcDisj_union_l with (ph1 l); auto.
  by apply H2.
Qed.
Lemma phDisj_union_r :
  forall ph1 ph2 ph3,
  phDisj ph2 ph3 ->
  phDisj ph1 (phUnion ph2 ph3) ->
  phDisj ph1 ph2.
Proof.
  intros ph1 ph2 ph3 H1 H2 l.
  apply phcDisj_union_r with (ph3 l); auto.
  by apply H2.
Qed.

Lemma phDisj_assoc_l :
  forall ph1 ph2 ph3,
  phDisj ph1 ph2 ->
  phDisj (phUnion ph1 ph2) ph3 ->
  phDisj ph1 (phUnion ph2 ph3).
Proof.
  intros ???? H ?.
  apply phcDisj_assoc_l. auto. apply H.
Qed.
Lemma phDisj_assoc_r :
  forall ph1 ph2 ph3,
  phDisj ph2 ph3 ->
  phDisj ph1 (phUnion ph2 ph3) ->
  phDisj (phUnion ph1 ph2) ph3.
Proof.
  intros ???? H ?.
  apply phcDisj_assoc_r. auto. apply H.
Qed.

Lemma phUnion_update :
  forall ph1 ph2 phc1 phc2 l,
  phUpdate (phUnion ph1 ph2) l (phcUnion phc1 phc2) =
  phUnion (phUpdate ph1 l phc1) (phUpdate ph2 l phc2).
Proof.
  ins. extensionality l'.
  unfold phUnion, phUpdate, update. desf.
Qed.

Lemma phUnion_cell :
  forall ph1 ph2 l,
  phcUnion (ph1 l) (ph2 l) = phUnion ph1 ph2 l.
Proof. ins. Qed.

Lemma phDisj_middle :
  forall ph1 ph2 ph3 ph4,
  phDisj ph1 ph2 ->
  phDisj ph3 ph4 ->
  phDisj (phUnion ph1 ph2) (phUnion ph3 ph4) ->
  phDisj ph2 ph3.
Proof.
  intros ph1 ph2 ph3 ph4 H1 H2 H3.
  apply phDisj_union_l with ph1; auto.
  by apply phDisj_union_r with ph4.
Qed.

Lemma phDisj_compat :
  forall ph1 ph2 ph3 ph4,
  phDisj ph1 ph3 ->
  phDisj ph2 ph4 ->
  phDisj (phUnion ph1 ph3) (phUnion ph2 ph4) ->
  phDisj (phUnion ph1 ph2) (phUnion ph3 ph4).
Proof.
  intros ph1 ph2 ph3 ph4 H1 H2 H3.
  apply phDisj_assoc_r.
  rewrite phUnion_comm.
  apply phDisj_assoc_l; auto.
  symmetry. by apply phDisj_union_l in H3.
  rewrite phUnion_comm.
  rewrite phUnion_assoc.
  apply phDisj_assoc_l; auto.
  by rewrite phUnion_comm with ph4 ph2.
Qed.

Lemma phUnion_swap_l :
  forall ph1 ph2 ph3,
  phUnion ph1 (phUnion ph2 ph3) =
  phUnion ph2 (phUnion ph1 ph3).
Proof.
  intros ph1 ph2 ph3.
  rewrite <- phUnion_assoc.
  rewrite phUnion_comm with ph1 ph2.
  by rewrite phUnion_assoc.
Qed.
Lemma phUnion_swap_r :
  forall ph1 ph2 ph3,
  phUnion (phUnion ph1 ph2) ph3 =
  phUnion (phUnion ph1 ph3) ph2.
Proof.
  intros ph1 ph2 ph3.
  rewrite phUnion_comm.
  rewrite phUnion_swap_l.
  by rewrite phUnion_assoc.
Qed.

Lemma phUnion_compat :
  forall ph1 ph2 ph3 ph4,
  phUnion (phUnion ph1 ph3) (phUnion ph2 ph4) =
  phUnion (phUnion ph1 ph2) (phUnion ph3 ph4).
Proof.
  intros ph1 ph2 ph3 ph4.
  rewrite phUnion_swap_l.
  repeat rewrite <- phUnion_assoc.
  by rewrite phUnion_comm with ph2 ph1.
Qed.

Lemma phUnion_update_free :
  forall ph1 ph2 phc l,
  ph2 l = PHCfree ->
  phUnion (phUpdate ph1 l phc) ph2 =
  phUpdate (phUnion ph1 ph2) l phc.
Proof.
  intros ph1 ph2 phc l H1.
  extensionality l'.
  unfold phUpdate, update, phUnion. desf.
  by rewrite H1, phcUnion_free_l.
Qed.


(** *** Concretisation *)

(** The _concretisation_ of a permission heap [ph]
    is the heap that contains the concretisations
    of all heap cells of [ph]. *)

Definition phConcr (ph : PermHeap) : Heap :=
  fun l => phcConcr (ph l).

Lemma phConcr_update :
  forall ph l phc,
  phConcr (phUpdate ph l phc) =
  hUpdate (phConcr ph) l (phcConcr phc).
Proof.
  intros ph l phc. extensionality l'.
  unfold phConcr, phUpdate, hUpdate, update.
  desf.
Qed.

Lemma phConcr_disj_union_l :
  forall ph1 ph2 ph3,
  phDisj ph1 ph3 ->
  phDisj ph2 ph3 ->
  phConcr ph1 = phConcr ph2 ->
  phConcr (phUnion ph1 ph3) = phConcr (phUnion ph2 ph3).
Proof.
  intros ph1 ph2 ph3 H1 H2 H3.
  extensionality l. unfold phConcr.
  repeat rewrite <- phUnion_cell.
  apply phcConcr_disj_union_l; vauto.
  by apply equal_f with l in H3.
Qed.
Lemma phConcr_disj_union_r :
  forall ph1 ph2 ph3,
  phDisj ph1 ph3 ->
  phDisj ph2 ph3 ->
  phConcr ph1 = phConcr ph2 ->
  phConcr (phUnion ph3 ph1) = phConcr (phUnion ph3 ph2).
Proof.
  intros ph1 ph2 ph3 H1 H2 H3.
  rewrite phUnion_comm with ph3 ph1.
  rewrite phUnion_comm with ph3 ph2.
  apply phConcr_disj_union_l; auto.
Qed.


(** *** Snapshot *)

(** The _snapshot_ of any permission heap [ph] is the
    heap constructed from the snapshots of all [ph]s entries. *)

Definition phSnapshot (ph : PermHeap) : Heap :=
  fun l => phcSnapshot (ph l).

(** Several useful properties of permission heap snapshots: *)

Lemma phSnapshot_upd :
  forall ph l phc,
  phSnapshot (phUpdate ph l phc) =
  hUpdate (phSnapshot ph) l (phcSnapshot phc).
Proof.
  intros ph l phc. extensionality l'.
  unfold phSnapshot, phUpdate, hUpdate, update. desf.
Qed.

Lemma phSnapshot_disj_union_l :
  forall ph1 ph2 ph3,
  phDisj ph1 ph3 ->
  phDisj ph2 ph3 ->
  phSnapshot ph1 = phSnapshot ph2 ->
  phSnapshot (phUnion ph1 ph3) = phSnapshot (phUnion ph2 ph3).
Proof.
  intros ph1 ph2 ph3 H1 H2 H3.
  extensionality l. unfold phSnapshot.
  repeat rewrite <- phUnion_cell.
  apply phcSnapshot_disj_union_l; vauto.
  by apply equal_f with l in H3.
Qed.
Lemma phSnapshot_disj_union_r :
  forall ph1 ph2 ph3,
  phDisj ph1 ph3 ->
  phDisj ph2 ph3 ->
  phSnapshot ph1 = phSnapshot ph2 ->
  phSnapshot (phUnion ph3 ph1) = phSnapshot (phUnion ph3 ph2).
Proof.
  intros ph1 ph2 ph3 H1 H2 H3.
  rewrite phUnion_comm with ph3 ph1.
  rewrite phUnion_comm with ph3 ph2.
  apply phSnapshot_disj_union_l; auto.
Qed.


(** *** Finiteness *)

(** A permission heap is _finite_ if all mappings that are
    not free can be mapped to some finite structure,
    in this case a list. *)

Definition phFinite (ph : PermHeap) : Prop :=
  exists xs : list Val, forall l, ph l <> PHCfree -> In l xs.

(** The main property of interest of finite permission heaps,
    is that one can always find a mapping that is free. *)

Lemma phFinite_free :
  forall ph,
  phFinite ph -> exists l, ph l = PHCfree.
Proof.
  intros ph (xs&FIN).
  assert (H : exists l, ~ In l xs) by apply val_inf.
  destruct H as (l&H).
  specialize FIN with l.
  exists l. tauto.
Qed.

(** Finiteness is preserved by any heap updates. *)

Lemma phFinite_update :
  forall ph l phc,
  phFinite ph -> phFinite (phUpdate ph l phc).
Proof.
  intros ph l phc (xs&FIN).
  assert (H1 : phc = PHCfree \/ ~ phc = PHCfree) by apply classic.
  destruct H1 as [H1|H1].
  (* [phc] is free *)
  - exists xs. intros l' H2. apply FIN.
    unfold phUpdate, update in H2. desf.
  (* [phc] is not free *)
  - exists (l :: xs). intros l' H2.
    specialize FIN with l'. simpls.
    unfold phUpdate, update in H2.
    destruct (val_eq_dec l l') as [|H3]; vauto.
    right. by apply FIN.
Qed.

(** The disjoint union of two finite permission heaps is finite. *)

Lemma phFinite_union :
  forall ph1 ph2,
  phFinite (phUnion ph1 ph2) <-> phFinite ph1 /\ phFinite ph2.
Proof.
  intros ph1 ph2. split.
  (* left-to-right *)
  - intros (xs & FIN).
    unfold phFinite. split.
    (* [ph1] is finite *)
    + exists xs. intros l H1.
      apply FIN. intro H2.
      apply phcUnion_not_free in H2; vauto.
    (* [ph2] is finite *)
    + exists xs. intros l H1.
      apply FIN. intro H2.
      apply phcUnion_not_free in H2; vauto.
  (* right-to-left *)
  - intro FIN.
    destruct FIN as ((xs1&FIN1)&(xs2&FIN2)).
    unfold phFinite.
    exists (xs1 ++ xs2). intros l H1.
    apply in_or_app.
    unfold phUnion in H1.
    apply phcUnion_not_free in H1.
    destruct H1 as [H1|H1].
    + left. by apply FIN1.
    + right. by apply FIN2.
Qed.

(** Permission heap concretisation preserves finiteness. *)

Lemma phFinite_concr :
  forall ph,
  phValid ph -> phFinite ph <-> hFinite (phConcr ph).
Proof.
  intros ph H1. split.
  (* left-to-right *)
  - intros (xs & FIN).
    exists xs. intros l H2. apply FIN.
    unfold phConcr, phcConcr in H2. desf.
  (* right-to-left *)
  - intros (xs&FIN).
    exists xs. intros l H2. apply FIN.
    unfold phValid in H1.
    specialize H1 with l.
    unfold phcValid in H1.
    unfold phConcr, phcConcr. desf.
Qed.


(** *** Heap cell conversion *)

(** This section discusses tools to convert the types
    of heap cells in permission heaps. *)

(** The operations [permheap_conv_std], [permheap_conv_proc],
    and [permheap_conv_act] are
    used to convert the heap cell at location [l] in a given
    permission heap [ph] to a _standard_,
    _process_, or _action_ heap cell, respectively.
    Later we define similar operations that work
    on sequences of heap locations. *)

Definition phConvStd (ph : PermHeap)(l : Val) : PermHeap :=
  phUpdate ph l (phcConvStd (ph l)).
Definition phConvProc (ph : PermHeap)(l : Val) : PermHeap :=
  phUpdate ph l (phcConvProc (ph l)).
Definition phConvAct (ph : PermHeap)(l : Val) : PermHeap :=
  phUpdate ph l (phcConvAct (ph l)).

Notation "'std' { ph ',' l }" := (phConvStd ph l).
Notation "'proc' { ph ',' l }" := (phConvProc ph l).
Notation "'act' { ph ',' l }" := (phConvAct ph l).

(** Heap cell conversion is idempotent. *)

Lemma phConvStd_idemp :
  forall ph l, phConvStd (phConvStd ph l) l = phConvStd ph l.
Proof.
  intros ph l. extensionality l'.
  unfold phConvStd, phUpdate, update. desf.
  by apply phcConvStd_idemp.
Qed.
Lemma phConvProc_idemp :
  forall ph l, phConvProc (phConvProc ph l) l = phConvProc ph l.
Proof.
  intros ph l. extensionality l'.
  unfold phConvProc, phUpdate, update. desf.
  by apply phcConvProc_idemp.
Qed.
Lemma phConvAct_idemp :
  forall ph l, phConvAct (phConvAct ph l) l = phConvAct ph l.
Proof.
  intros ph l. extensionality l'.
  unfold phConvAct, phUpdate, update. desf.
  by apply phcConvAct_idemp.
Qed.

(** Heap cell conversion preserves validity. *)

Lemma phConvStd_valid :
  forall ph l,
  phValid ph <-> phValid (phConvStd ph l).
Proof.
  intros ph l. split; intros H l'.
  - unfold phValid in *.
    specialize H with l'.
    unfold phConvStd, phUpdate, update. desf.
    by rewrite <- phcConvStd_valid.
  - unfold phValid in *. specialize H with l'.
    unfold phConvStd, phUpdate, update in H.
    desf. by rewrite phcConvStd_valid.
Qed.
Lemma phConvProc_valid :
  forall ph l,
  phValid ph <-> phValid (phConvProc ph l).
Proof.
  intros ph l. split; intros H l'.
  - unfold phValid in *.
    specialize H with l'.
    unfold phConvProc, phUpdate, update. desf.
    by rewrite <- phcConvProc_valid.
  - unfold phValid in *. specialize H with l'.
    unfold phConvProc, phUpdate, update in H.
    desf. by rewrite phcConvProc_valid.
Qed.
Lemma phConvAct_valid :
  forall ph l,
  phValid ph <-> phValid (phConvAct ph l).
Proof.
  intros ph l. split; intros H l'.
  - unfold phValid in *.
    specialize H with l'.
    unfold phConvAct, phUpdate, update. desf.
    by rewrite <- phcConvAct_valid.
  - unfold phValid in *. specialize H with l'.
    unfold phConvAct, phUpdate, update in H.
    desf. by rewrite phcConvAct_valid.
Qed.

(** Heap cell conversion preserves disjointness. *)

Add Parametric Morphism : phConvStd
  with signature phDisj ==> eq ==> phDisj as phConvStd_disj.
Proof.
  intros ph1 ph2 H1 v. red. intro l.
  red in H1. red in H1. specialize H1 with l.
  unfold phConvStd, phUpdate, update. desf.
  by apply phcConvStd_disj.
Qed.
Add Parametric Morphism : phConvProc
  with signature phDisj ==> eq ==> phDisj as phConvProc_disj.
Proof.
  intros ph1 ph2 H1 v. red. intro l.
  red in H1. red in H1. specialize H1 with l.
  unfold phConvProc, phUpdate, update. desf.
  by apply phcConvProc_disj.
Qed.
Add Parametric Morphism : phConvAct
  with signature phDisj ==> eq ==> phDisj as phConvAct_disj.
Proof.
  intros ph1 ph2 H1 v. red. intro l.
  red in H1. red in H1. specialize H1 with l.
  unfold phConvAct, phUpdate, update. desf.
  by apply phcConvAct_disj.
Qed.

(** Heap cell conversion preserves entirety. *)

Lemma phConvStd_entire :
  forall ph l l',
  phcEntire (phConvStd ph l l') <-> phcEntire (ph l').
Proof.
  intros ph l l'. split; intro H.
  - unfold phConvStd, phUpdate, update in H. desf.
    by rewrite <- phcConvStd_entire.
  - unfold phConvStd, phUpdate, update. desf.
    by rewrite phcConvStd_entire.
Qed.
Lemma phConvProc_entire :
  forall ph l l',
  phcEntire (phConvProc ph l l') <-> phcEntire (ph l').
Proof.
  intros ph l l'. split; intro H.
  - unfold phConvProc, phUpdate, update in H. desf.
    by rewrite <- phcConvProc_entire.
  - unfold phConvProc, phUpdate, update. desf.
    by rewrite phcConvProc_entire.
Qed.
Lemma phConvAct_entire :
  forall ph l l',
  phcEntire (phConvAct ph l l') <-> phcEntire (ph l').
Proof.
  intros ph l l'. split; intro H.
  - unfold phConvAct, phUpdate, update in H. desf.
    by rewrite <- phcConvAct_entire.
  - unfold phConvAct, phUpdate, update. desf.
    by rewrite phcConvAct_entire.
Qed.

(** Heap cell conversion preserves concretisations. *)

Lemma phConvStd_concr :
  forall ph l,
  phConcr (phConvStd ph l) = phConcr ph.
Proof.
  intros ph l. extensionality l'.
  unfold phConcr, phConvStd, phUpdate, update. desf.
  by rewrite phcConvStd_concr.
Qed.
Lemma phConvProc_concr :
  forall ph l,
  phConcr (phConvProc ph l) = phConcr ph.
Proof.
  intros ph l. extensionality l'.
  unfold phConcr, phConvProc, phUpdate, update. desf.
  by rewrite phcConvProc_concr.
Qed.
Lemma phConvAct_concr :
  forall ph l,
  phConcr (phConvAct ph l) = phConcr ph.
Proof.
  intros ph l. extensionality l'.
  unfold phConcr, phConvAct, phUpdate, update. desf.
  by rewrite phcConvAct_concr.
Qed.

(** Heap cell conversion distributes over disjoint union. *)

Lemma phConvStd_union :
  forall ph1 ph2 l,
  phDisj ph1 ph2 ->
  phConvStd (phUnion ph1 ph2) l =
  phUnion (phConvStd ph1 l) (phConvStd ph2 l).
Proof.
  intros ph1 ph2 l H1.
  extensionality l'.
  red in H1. red in H1.
  specialize H1 with l'.
  unfold phUnion, phConvStd, phUpdate, update. desf.
  by apply phcConvStd_union.
Qed.
Lemma phConvProc_union :
  forall ph1 ph2 l,
  phDisj ph1 ph2 ->
  phConvProc (phUnion ph1 ph2) l =
  phUnion (phConvProc ph1 l) (phConvProc ph2 l).
Proof.
  intros ph1 ph2 l H1.
  extensionality l'.
  red in H1. red in H1.
  specialize H1 with l'.
  unfold phUnion, phConvProc, phUpdate, update. desf.
  by apply phcConvProc_union.
Qed.
Lemma phConvAct_union :
  forall ph1 ph2 l,
  phDisj ph1 ph2 ->
  phConvAct (phUnion ph1 ph2) l =
  phUnion (phConvAct ph1 l) (phConvAct ph2 l).
Proof.
  intros ph1 ph2 l H1.
  extensionality l'.
  red in H1. red in H1.
  specialize H1 with l'.
  unfold phUnion, phConvAct, phUpdate, update. desf.
  by apply phcConvAct_union.
Qed.

(** Free heap cells always convert to free heap cells. *)

Lemma phConvStd_free :
  forall ph l, ph l = PHCfree -> phConvStd ph l = ph.
Proof.
  intros ph l H. extensionality l'.
  unfold phConvStd, phUpdate, update. desf.
  rewrite H. by apply phcConvStd_free.
Qed.
Lemma phConvProc_free :
  forall ph l, ph l = PHCfree -> phConvProc ph l = ph.
Proof.
  intros ph l H. extensionality l'.
  unfold phConvProc, phUpdate, update. desf.
  rewrite H. by apply phcConvProc_free.
Qed.
Lemma phConvAct_free :
  forall ph l, ph l = PHCfree -> phConvAct ph l = ph.
Proof.
  intros ph l H. extensionality l'.
  unfold phConvAct, phUpdate, update. desf.
  rewrite H. by apply phcConvAct_free.
Qed.

Lemma phConvStd_free2 :
  forall ph l l',
  (phConvStd ph l) l' = PHCfree <-> ph l' = PHCfree.
Proof.
  intros ph l l'.
  unfold phConvStd, phUpdate, update. desf.
  by apply phcConvStd_free2.
Qed.
Lemma phConvProc_free2 :
  forall ph l l',
  (phConvProc ph l) l' = PHCfree <-> ph l' = PHCfree.
Proof.
  intros ph l l'.
  unfold phConvProc, phUpdate, update. desf.
  by apply phcConvProc_free2.
Qed.
Lemma phConvAct_free2 :
  forall ph l l',
  (phConvAct ph l) l' = PHCfree <-> ph l' = PHCfree.
Proof.
  intros ph l l'.
  unfold phConvAct, phUpdate, update. desf.
  by apply phcConvAct_free2.
Qed.

(** Any heap cell that is not converted stays the same. *)

Lemma phConvStd_pres :
  forall ph l l', l <> l' -> ph l' = phConvStd ph l l'.
Proof.
  intros ph l l' H1.
  unfold phConvStd, phUpdate, update. desf.
Qed.
Lemma phConvProc_pres :
  forall ph l l', l <> l' -> ph l' = phConvProc ph l l'.
Proof.
  intros ph l l' H1.
  unfold phConvProc, phUpdate, update. desf.
Qed.
Lemma phConvAct_pres :
  forall ph l l', l <> l' -> ph l' = phConvAct ph l l'.
Proof.
  intros ph l l' H1.
  unfold phConvAct, phUpdate, update. desf.
Qed.

(** Requesting any converted heap cell gives the converted heap cell. *)

Lemma phConvStd_apply :
  forall ph l, phConvStd ph l l = phcConvStd (ph l).
Proof. ins. unfold phConvStd, phUpdate, update. desf. Qed.
Lemma phConvProc_apply :
  forall ph l, phConvProc ph l l = phcConvProc (ph l).
Proof. ins. unfold phConvProc, phUpdate, update. desf. Qed.
Lemma phConvAct_apply :
  forall ph l, phConvAct ph l l = phcConvAct (ph l).
Proof. ins. unfold phConvAct, phUpdate, update. desf. Qed.

(** Below are various other useful properties of heap cell conversion. *)

Lemma phConvStd_disj_entire :
  forall ph1 ph2 l,
  phcEntire (ph1 l) -> phDisj ph1 ph2 -> phDisj (phConvStd ph1 l) ph2.
Proof.
  intros ph1 ph2 l H1 H2 l'.
  unfold phConvStd, phUpdate, update.
  desf. by apply phcConvStd_disj_entire.
Qed.
Lemma phConvProc_disj_entire :
  forall ph1 ph2 l,
  phcEntire (ph1 l) -> phDisj ph1 ph2 -> phDisj (phConvProc ph1 l) ph2.
Proof.
  intros ph1 ph2 l H1 H2 l'.
  unfold phConvProc, phUpdate, update.
  desf. by apply phcConvProc_disj_entire.
Qed.
Lemma phConvAct_disj_entire :
  forall ph1 ph2 l,
  phcEntire (ph1 l) -> phDisj ph1 ph2 -> phDisj (phConvAct ph1 l) ph2.
Proof.
  intros ph1 ph2 l H1 H2 l'.
  unfold phConvAct, phUpdate, update.
  desf. by apply phcConvAct_disj_entire.
Qed.

Lemma phConvProc_snapshot_occ :
  forall ph l l',
  phSnapshot ph l' <> None ->
  phSnapshot (phConvProc ph l) l' <> None.
Proof.
  intros ph l l' H. unfold phSnapshot in *.
  unfold phConvProc, phUpdate, update. desf.
  by apply phcSnapshot_conv_proc_occ.
Qed.
Lemma phConvAct_snapshot_occ :
  forall ph l l',
  phSnapshot ph l' <> None ->
  phSnapshot (phConvAct ph l) l' <> None.
Proof.
  intros ph l l' H. unfold phSnapshot in *.
  unfold phConvAct, phUpdate, update. desf.
  by apply phcSnapshot_conv_act_occ.
Qed.

Lemma phConvAct_snapshot_pres :
  forall ph l l' v,
  phSnapshot ph l' = Some v ->
  phSnapshot (phConvAct ph l) l' = Some v.
Proof.
  intros ph l l' v H1. unfold phSnapshot in *.
  unfold phConvAct, phUpdate, update. desf.
  by apply phcSnapshot_conv_act_pres.
Qed.


(** *** Heap cell batch conversions *)

(** The following operations are for converting a sequence
    (or set) of heap locations (i.e., for converting a
    batch or bulk of locations). *)

Fixpoint phConvStdMult (ph : PermHeap)(xs : list Val) : PermHeap :=
  match xs with
    | nil => ph
    | l :: xs' => phConvStd (phConvStdMult ph xs') l
  end.
Fixpoint phConvProcMult (ph : PermHeap)(xs : list Val) : PermHeap :=
  match xs with
    | nil => ph
    | l :: xs' => phConvProc (phConvProcMult ph xs') l
  end.
Fixpoint phConvActMult (ph : PermHeap)(xs : list Val) : PermHeap :=
  match xs with
    | nil => ph
    | l :: xs' => phConvAct (phConvActMult ph xs') l
  end.

Notation "'std' { ph ';' xs }" := (phConvStdMult ph xs).
Notation "'proc' { ph ';' xs }" := (phConvProcMult ph xs).
Notation "'act' { ph ';' xs }" := (phConvActMult ph xs).

(** Converting an empty batch of locations leaves the heap unchanged. *)

Lemma phConvStdMult_nil :
  forall ph, ph = phConvStdMult ph nil.
Proof. ins. Qed.
Lemma phConvProcMult_nil :
  forall ph, ph = phConvProcMult ph nil.
Proof. ins. Qed.
Lemma phConvActMult_nil :
  forall ph, ph = phConvActMult ph nil.
Proof. ins. Qed.

(** Properties related to converting a single heap cell: *)

Lemma phConvStdMult_single :
  forall ph l, phConvStd ph l = phConvStdMult ph [l].
Proof. ins. Qed.
Lemma phConvProcMult_single :
  forall ph l, phConvProc ph l = phConvProcMult ph [l].
Proof. ins. Qed.
Lemma phConvActMult_single :
  forall ph l, phConvAct ph l = phConvActMult ph [l].
Proof. ins. Qed.

(** Conversions of a non-empty batch of locations can be unfolded. *)

Lemma phConvStdMult_cons :
  forall xs l ph,
  phConvStdMult ph (l :: xs) = phConvStd (phConvStdMult ph xs) l.
Proof. ins. Qed.
Lemma phConvProcMult_cons :
  forall xs l ph,
  phConvProcMult ph (l :: xs) = phConvProc (phConvProcMult ph xs) l.
Proof. ins. Qed.
Lemma phConvActMult_cons :
  forall xs l ph,
  phConvActMult ph (l :: xs) = phConvAct (phConvActMult ph xs) l.
Proof. ins. Qed.

(** Conversion of two batches of locations can be appended
    into a single batch. *)

Lemma phConvStdMult_app :
  forall xs ys ph,
  phConvStdMult ph (xs ++ ys) = phConvStdMult (phConvStdMult ph ys) xs.
Proof.
  induction xs as [|l xs IH]; [done|].
  intros ys ph. simpls. by rewrite IH.
Qed.
Lemma phConvProcMult_app :
  forall xs ys ph,
  phConvProcMult ph (xs ++ ys) = phConvProcMult (phConvProcMult ph ys) xs.
Proof.
  induction xs as [|l xs IH]; [done|].
  intros ys ph. simpls. by rewrite IH.
Qed.
Lemma phConvActMult_app :
  forall xs ys ph,
  phConvActMult ph (xs ++ ys) = phConvActMult (phConvActMult ph ys) xs.
Proof.
  induction xs as [|l xs IH]; [done|].
  intros ys ph. simpls. by rewrite IH.
Qed.

(** Batch conversions are closed under permutations. *)

Lemma phConvStdMult_permut :
  forall ph xs ys,
  Permutation xs ys -> phConvStdMult ph xs = phConvStdMult ph ys.
Proof.
  intros ph xs ys H. induction H; vauto.
  - simpl. by rewrite IHPermutation.
  - simpls. unfold phConvStd, phUpdate, update.
    extensionality l'. desf.
  - by rewrite IHPermutation1, IHPermutation2.
Qed.
Lemma phConvProcMult_permut :
  forall ph xs ys,
  Permutation xs ys -> phConvProcMult ph xs = phConvProcMult ph ys.
Proof.
  intros ph xs ys H. induction H; vauto.
  - simpl. by rewrite IHPermutation.
  - simpls. unfold phConvProc, phUpdate, update.
    extensionality l'. desf.
  - by rewrite IHPermutation1, IHPermutation2.
Qed.
Lemma phConvActMult_permut :
  forall ph xs ys,
  Permutation xs ys -> phConvActMult ph xs = phConvActMult ph ys.
Proof.
  intros ph xs ys H. induction H; vauto.
  - simpl. by rewrite IHPermutation.
  - simpls. unfold phConvAct, phUpdate, update.
    extensionality l'. desf.
  - by rewrite IHPermutation1, IHPermutation2.
Qed.

Add Parametric Morphism : phConvStdMult
  with signature eq ==> @Permutation Val ==> eq
    as phConvStdMult_permut_mor.
Proof. ins. by apply phConvStdMult_permut. Qed.
Add Parametric Morphism : phConvProcMult
  with signature eq ==> @Permutation Val ==> eq
    as phConvProcMult_permut_mor.
Proof. ins. by apply phConvProcMult_permut. Qed.
Add Parametric Morphism : phConvActMult
  with signature eq ==> @Permutation Val ==> eq
    as phConvActMult_permut_mor.
Proof. ins. by apply phConvActMult_permut. Qed.

(** Batch conversions are idempotent. *)

Lemma phConvStdMult_idemp :
  forall xs ph,
  phConvStdMult (phConvStdMult ph xs) xs = phConvStdMult ph xs.
Proof.
  induction xs as [|l' xs IH]; [done|].
  intros ph. rewrite <- phConvStdMult_app.
  assert (H1 : Permutation ((l' :: xs) ++ l' :: xs) (l' :: l' :: xs ++ xs)) by list_permutation.
  rewrite H1. simpl. rewrite phConvStd_idemp.
  by rewrite phConvStdMult_app, IH.
Qed.
Lemma phConvProcMult_idemp :
  forall xs ph,
  phConvProcMult (phConvProcMult ph xs) xs = phConvProcMult ph xs.
Proof.
  induction xs as [|l' xs IH]; [done|].
  intros ph. rewrite <- phConvProcMult_app.
  assert (H1 : Permutation ((l' :: xs) ++ l' :: xs) (l' :: l' :: xs ++ xs)) by list_permutation.
  rewrite H1. simpl. rewrite phConvProc_idemp.
  by rewrite phConvProcMult_app, IH.
Qed.
Lemma phConvActMult_idemp :
  forall xs ph,
  phConvActMult (phConvActMult ph xs) xs = phConvActMult ph xs.
Proof.
  induction xs as [|l' xs IH]; [done|].
  intros ph. rewrite <- phConvActMult_app.
  assert (H1 : Permutation ((l' :: xs) ++ l' :: xs) (l' :: l' :: xs ++ xs)) by list_permutation.
  rewrite H1. simpl. rewrite phConvAct_idemp.
  by rewrite phConvActMult_app, IH.
Qed.

(** Any duplicate conversions in a batch are subsumed. *)

Lemma phConvStdMult_subsume :
  forall xs l ph,
  In l xs -> phConvStdMult ph (l :: xs) = phConvStdMult ph xs.
Proof.
  induction xs as [|l' xs IH]; [done|].
  intros l ph H1. simpl in H1. destruct H1 as [H1|H1]; vauto.
  - simpls. by rewrite phConvStd_idemp.
  - rewrite perm_swap. simpls. rewrite IH; vauto.
Qed.
Lemma phConvProcMult_subsume :
  forall xs l ph,
  In l xs -> phConvProcMult ph (l :: xs) = phConvProcMult ph xs.
Proof.
  induction xs as [|l' xs IH]; [done|].
  intros l ph H1. simpl in H1. destruct H1 as [H1|H1]; vauto.
  - simpls. by rewrite phConvProc_idemp.
  - rewrite perm_swap. simpls. rewrite IH; vauto.
Qed.
Lemma phConvActMult_subsume :
  forall xs l ph,
  In l xs -> phConvActMult ph (l :: xs) = phConvActMult ph xs.
Proof.
  induction xs as [|l' xs IH]; [done|].
  intros l ph H1. simpl in H1. destruct H1 as [H1|H1]; vauto.
  - simpls. by rewrite phConvAct_idemp.
  - rewrite perm_swap. simpls. rewrite IH; vauto.
Qed.

(** Batch conversions preserve heap validity. *)

Lemma phConvStdMult_valid :
  forall xs ph, phValid ph <-> phValid (phConvStdMult ph xs).
Proof.
  induction xs as [|l xs IH]; [done|].
  intros ph. split; intro H1.
  - simpl. apply phConvStd_valid. by rewrite <- IH.
  - simpl in H1. apply IH. by apply phConvStd_valid with l.
Qed.
Lemma phConvProcMult_valid :
  forall xs ph, phValid ph <-> phValid (phConvProcMult ph xs).
Proof.
  induction xs as [|l xs IH]; [done|].
  intros ph. split; intro H1.
  - simpl. apply phConvProc_valid. by rewrite <- IH.
  - simpl in H1. apply IH. by apply phConvProc_valid with l.
Qed.
Lemma phConvActMult_valid :
  forall xs ph, phValid ph <-> phValid (phConvActMult ph xs).
Proof.
  induction xs as [|l xs IH]; [done|].
  intros ph. split; intro H1.
  - simpl. apply phConvAct_valid. by rewrite <- IH.
  - simpl in H1. apply IH. by apply phConvAct_valid with l.
Qed.

(** Converting a batch of only free locations does not change the heap. *)

Lemma phConvStdMult_free :
  forall xs ph,
  (forall l, In l xs -> ph l = PHCfree) ->
  phConvStdMult ph xs = ph.
Proof.
  induction xs as [|l xs IH]; [done|].
  intros ph H1. simpl.
  rewrite phConvStd_free.
  - apply IH. intros l' H2.
    apply H1. by apply in_cons.
  - rewrite IH.
    + apply H1. vauto.
    + intros l' H2. by apply H1, in_cons.
Qed.
Lemma phConvProcMult_free :
  forall xs ph,
  (forall l, In l xs -> ph l = PHCfree) ->
  phConvProcMult ph xs = ph.
Proof.
  induction xs as [|l xs IH]; [done|].
  intros ph H1. simpl.
  rewrite phConvProc_free.
  - apply IH. intros l' H2.
    apply H1. by apply in_cons.
  - rewrite IH.
    + apply H1. vauto.
    + intros l' H2. by apply H1, in_cons.
Qed.
Lemma phConvActMult_free :
  forall xs ph,
  (forall l, In l xs -> ph l = PHCfree) ->
  phConvActMult ph xs = ph.
Proof.
  induction xs as [|l xs IH]; [done|].
  intros ph H1. simpl.
  rewrite phConvAct_free.
  - apply IH. intros l' H2.
    apply H1. by apply in_cons.
  - rewrite IH.
    + apply H1. vauto.
    + intros l' H2. by apply H1, in_cons.
Qed.

Lemma phConvStdMult_free2 :
  forall xs ph l,
  phConvStdMult ph xs l = PHCfree <-> ph l = PHCfree.
Proof.
  induction xs as [|l' xs IH]; [done|].
  intros ph l. simpl. rewrite phConvStd_free2.
  by rewrite IH.
Qed.
Lemma phConvProcMult_free2 :
  forall xs ph l,
  phConvProcMult ph xs l = PHCfree <-> ph l = PHCfree.
Proof.
  induction xs as [|l' xs IH]; [done|].
  intros ph l. simpl. rewrite phConvProc_free2.
  by rewrite IH.
Qed.
Lemma phConvActMult_free2 :
  forall xs ph l,
  phConvActMult ph xs l = PHCfree <-> ph l = PHCfree.
Proof.
  induction xs as [|l' xs IH]; [done|].
  intros ph l. simpl. rewrite phConvAct_free2.
  by rewrite IH.
Qed.

(** Batch conversions preserve heap disjointness. *)

Lemma phConvStdMult_disj :
  forall xs ph1 ph2,
  phDisj ph1 ph2 -> phDisj (phConvStdMult ph1 xs) (phConvStdMult ph2 xs).
Proof.
  induction xs as [|x xs IH]; [done|].
  intros ph1 ph2 H1. simpl.
  apply phConvStd_disj; [|done]. by apply IH.
Qed.
Lemma phConvProcMult_disj :
  forall xs ph1 ph2,
  phDisj ph1 ph2 -> phDisj (phConvProcMult ph1 xs) (phConvProcMult ph2 xs).
Proof.
  induction xs as [|x xs IH]; [done|].
  intros ph1 ph2 H1. simpl.
  apply phConvProc_disj; [|done]. by apply IH.
Qed.
Lemma phConvActMult_disj :
  forall xs ph1 ph2,
  phDisj ph1 ph2 -> phDisj (phConvActMult ph1 xs) (phConvActMult ph2 xs).
Proof.
  induction xs as [|x xs IH]; [done|].
  intros ph1 ph2 H1. simpl.
  apply phConvAct_disj; [|done]. by apply IH.
Qed.

Add Parametric Morphism : phConvStdMult
  with signature phDisj ==> @Permutation Val ==> phDisj
    as phConvStdMult_disj_mor.
Proof.
  intros ph1 ph2 H1 xs ys H2.
  rewrite H2. clear H2.
  by apply phConvStdMult_disj.
Qed.
Add Parametric Morphism : phConvProcMult
  with signature phDisj ==> @Permutation Val ==> phDisj
    as phConvProcMult_disj_mor.
Proof.
  intros ph1 ph2 H1 xs ys H2.
  rewrite H2. clear H2.
  by apply phConvProcMult_disj.
Qed.
Add Parametric Morphism : phConvActMult
  with signature phDisj ==> @Permutation Val ==> phDisj
    as phConvActMult_disj_mor.
Proof.
  intros ph1 ph2 H1 xs ys H2.
  rewrite H2. clear H2.
  by apply phConvActMult_disj.
Qed.

(** Batch conversions preserve entirety. *)

Lemma phConvStdMult_entire:
  forall xs ph l,
  phcEntire (phConvStdMult ph xs l) <-> phcEntire (ph l).
Proof.
  induction xs as [|l xs IH]; [done|].
  intros ph l'. split; intro H.
  - simpl in H. rewrite <- IH.
    by rewrite <- phConvStd_entire with (l:=l).
  - simpl. rewrite phConvStd_entire with (l:=l).
    by rewrite IH.
Qed.
Lemma phConvProcMult_entire:
  forall xs ph l,
  phcEntire (phConvProcMult ph xs l) <-> phcEntire (ph l).
Proof.
  induction xs as [|l xs IH]; [done|].
  intros ph l'. split; intro H.
  - simpl in H. rewrite <- IH.
    by rewrite <- phConvProc_entire with (l:=l).
  - simpl. rewrite phConvProc_entire with (l:=l).
    by rewrite IH.
Qed.
Lemma phConvActMult_entire:
  forall xs ph l,
  phcEntire (phConvActMult ph xs l) <-> phcEntire (ph l).
Proof.
  induction xs as [|l xs IH]; [done|].
  intros ph l'. split; intro H.
  - simpl in H. rewrite <- IH.
    by rewrite <- phConvAct_entire with (l:=l).
  - simpl. rewrite phConvAct_entire with (l:=l).
    by rewrite IH.
Qed.

(** Batch conversions distribute over disjoint union. *)

Lemma phConvStdMult_union :
  forall xs ph1 ph2,
  phDisj ph1 ph2 ->
  phConvStdMult (phUnion ph1 ph2) xs =
  phUnion (phConvStdMult ph1 xs) (phConvStdMult ph2 xs).
Proof.
  induction xs as [|l xs IH]; [done|].
  intros ph1 ph2 H1. simpl.
  rewrite <- phConvStd_union.
  - by rewrite <- IH.
  - by apply phConvStdMult_disj.
Qed.
Lemma phConvProcMult_union :
  forall xs ph1 ph2,
  phDisj ph1 ph2 ->
  phConvProcMult (phUnion ph1 ph2) xs =
  phUnion (phConvProcMult ph1 xs) (phConvProcMult ph2 xs).
Proof.
  induction xs as [|l xs IH]; [done|].
  intros ph1 ph2 H1. simpl.
  rewrite <- phConvProc_union.
  - by rewrite <- IH.
  - by apply phConvProcMult_disj.
Qed.
Lemma phConvActMult_union :
  forall xs ph1 ph2,
  phDisj ph1 ph2 ->
  phConvActMult (phUnion ph1 ph2) xs =
  phUnion (phConvActMult ph1 xs) (phConvActMult ph2 xs).
Proof.
  induction xs as [|l xs IH]; [done|].
  intros ph1 ph2 H1. simpl.
  rewrite <- phConvAct_union.
  - by rewrite <- IH.
  - by apply phConvActMult_disj.
Qed.

(** Batch conversions preserve heap concretisation. *)

Lemma phConvStdMult_concr :
  forall xs ph, phConcr (phConvStdMult ph xs) = phConcr ph.
Proof.
  induction xs as [|l xs IH]; [done|].
  intros ph. simpl. by rewrite phConvStd_concr, IH.
Qed.
Lemma phConvProcMult_concr :
  forall xs ph, phConcr (phConvProcMult ph xs) = phConcr ph.
Proof.
  induction xs as [|l xs IH]; [done|].
  intros ph. simpl. by rewrite phConvProc_concr, IH.
Qed.
Lemma phConvActMult_concr :
  forall xs ph, phConcr (phConvActMult ph xs) = phConcr ph.
Proof.
  induction xs as [|l xs IH]; [done|].
  intros ph. simpl. by rewrite phConvAct_concr, IH.
Qed.

(** Any location that is not in the conversion batch
    is not affected by batch conversion. *)

Lemma phConvStdMult_pres :
  forall xs l ph, ~ In l xs -> ph l = phConvStdMult ph xs l.
Proof.
  induction xs as [|l xs IH]; [done|].
  intros l' ph H1. simpl. rewrite IH.
  - apply phConvStd_pres. intro H2.
    apply H1. clarify. simpl. by left.
  - intro H2. apply H1. simpl. by right.
Qed.
Lemma phConvProcMult_pres :
  forall xs l ph, ~ In l xs -> ph l = phConvProcMult ph xs l.
Proof.
  induction xs as [|l xs IH]; [done|].
  intros l' ph H1. simpl. rewrite IH.
  - apply phConvProc_pres. intro H2.
    apply H1. clarify. simpl. by left.
  - intro H2. apply H1. simpl. by right.
Qed.
Lemma phConvActMult_pres :
  forall xs l ph, ~ In l xs -> ph l = phConvActMult ph xs l.
Proof.
  induction xs as [|l xs IH]; [done|].
  intros l' ph H1. simpl. rewrite IH.
  - apply phConvAct_pres. intro H2.
    apply H1. clarify. simpl. by left.
  - intro H2. apply H1. simpl. by right.
Qed.

(** Any location in the conversion batch is indeed converted. *)

Lemma phConvStdMult_apply :
  forall xs l ph,
  In l xs -> phConvStdMult ph xs l = phcConvStd (ph l).
Proof.
  induction xs as [|l' xs IH]; [done|].
  intros l ph H1. simpl in H1. destruct H1 as [H1|H1]; vauto.
  - simpl. rewrite phConvStd_apply.
    assert (H2 : In l xs \/ ~ In l xs) by apply classic.
    destruct H2 as [H2|H2]; vauto.
    + rewrite IH; auto. by apply phcConvStd_idemp.
    + by rewrite <- phConvStdMult_pres.
  - simpl. unfold phConvStd, phUpdate, update. desf.
    + rewrite IH; auto. by apply phcConvStd_idemp.
    + by apply IH.
Qed.
Lemma phConvProcMult_apply :
  forall xs l ph,
  In l xs -> phConvProcMult ph xs l = phcConvProc (ph l).
Proof.
  induction xs as [|l' xs IH]; [done|].
  intros l ph H1. simpl in H1. destruct H1 as [H1|H1]; vauto.
  - simpl. rewrite phConvProc_apply.
    assert (H2 : In l xs \/ ~ In l xs) by apply classic.
    destruct H2 as [H2|H2]; vauto.
    + rewrite IH; auto. by apply phcConvProc_idemp.
    + by rewrite <- phConvProcMult_pres.
  - simpl. unfold phConvProc, phUpdate, update. desf.
    + rewrite IH; auto. by apply phcConvProc_idemp.
    + by apply IH.
Qed.
Lemma phConvActMult_apply :
  forall xs l ph,
  In l xs -> phConvActMult ph xs l = phcConvAct (ph l).
Proof.
  induction xs as [|l' xs IH]; [done|].
  intros l ph H1. simpl in H1. destruct H1 as [H1|H1]; vauto.
  - simpl. rewrite phConvAct_apply.
    assert (H2 : In l xs \/ ~ In l xs) by apply classic.
    destruct H2 as [H2|H2]; vauto.
    + rewrite IH; auto. by apply phcConvAct_idemp.
    + by rewrite <- phConvActMult_pres.
  - simpl. unfold phConvAct, phUpdate, update. desf.
    + rewrite IH; auto. by apply phcConvAct_idemp.
    + by apply IH.
Qed.

(** Batch conversions preserve occupied snapshots. *)

Lemma phConvProcMult_snapshot_occ :
  forall xs ph l,
  phSnapshot ph l <> None ->
  phSnapshot (phConvProcMult ph xs) l <> None.
Proof.
  induction xs as [|l xs IH]; [done|].
  intros ph l' H1. simpls.
  by apply phConvProc_snapshot_occ, IH.
Qed.
Lemma phConvActMult_snapshot_occ :
  forall xs ph l,
  phSnapshot ph l <> None ->
  phSnapshot (phConvActMult ph xs) l <> None.
Proof.
  induction xs as [|l xs IH]; [done|].
  intros ph l' H1. simpls.
  by apply phConvAct_snapshot_occ, IH.
Qed.

Lemma phConvActMult_snapshot_pres :
  forall xs ph l v,
  phSnapshot ph l = Some v ->
  phSnapshot (phConvActMult ph xs) l = Some v.
Proof.
  induction xs as [|l xs IH]; [done|].
  intros ph l' v H1. simpls.
  by apply phConvAct_snapshot_pres, IH.
Qed.

(** Below are various other useful properties of batch conversions. *)

Lemma phConvStdMult_disj_entire :
  forall xs ph1 ph2,
  (forall l, In l xs -> phcEntire (ph1 l)) ->
  phDisj ph1 ph2 ->
  phDisj (phConvStdMult ph1 xs) ph2.
Proof.
  induction xs as [|l xs IH]; [done|].
  intros ph1 ph2 H1 H2. simpl.
  apply phConvStd_disj_entire.
  - rewrite phConvStdMult_entire. apply H1. vauto.
  - apply IH; auto. intros l' H3. apply H1. vauto.
Qed.
Lemma phConvProcMult_disj_entire :
  forall xs ph1 ph2,
  (forall l, In l xs -> phcEntire (ph1 l)) ->
  phDisj ph1 ph2 ->
  phDisj (phConvProcMult ph1 xs) ph2.
Proof.
  induction xs as [|l xs IH]; [done|].
  intros ph1 ph2 H1 H2. simpl.
  apply phConvProc_disj_entire.
  - rewrite phConvProcMult_entire. apply H1. vauto.
  - apply IH; auto. intros l' H3. apply H1. vauto.
Qed.
Lemma phConvActMult_disj_entire :
  forall xs ph1 ph2,
  (forall l, In l xs -> phcEntire (ph1 l)) ->
  phDisj ph1 ph2 ->
  phDisj (phConvActMult ph1 xs) ph2.
Proof.
  induction xs as [|l xs IH]; [done|].
  intros ph1 ph2 H1 H2. simpl.
  apply phConvAct_disj_entire.
  - rewrite phConvActMult_entire. apply H1. vauto.
  - apply IH; auto. intros l' H3. apply H1. vauto.
Qed.

End Heaps.
