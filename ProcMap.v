Require Import FunctionalExtensionality.
Require Import HahnBase.
Require Import Heaps.
Require Import List.
Require Import Permissions.
Require Import Permutation.
Require Import Prelude.
Require Import Process.
Require Import QArith.
Require Import Qcanon.
Require Import Utf8.

Import ListNotations.

Set Implicit Arguments.


(** * Process Maps *)

Module Type ProcMaps
  (dom : Domains)
  (heaps: Heaps dom)
  (procs: Processes dom).

Export dom heaps procs.

(** ** Process map entries *)

(** The set [ProcMapEntry] of _process map entries_
    is later used as the codomain of process maps. *)

Inductive ProcMapEntry :=
  | PEelem(q : Qc)(P : Proc)(xs : list ProcVar)(f : ProcVar -> Val)
  | PEfree
  | PEinvalid.

Add Search Blacklist "ProcMapEntry_rect".
Add Search Blacklist "ProcMapEntry_ind".
Add Search Blacklist "ProcMapEntry_rec".
Add Search Blacklist "ProcMapEntry_sind".


(** *** Bisimilarity *)

(** Two process map entries are _equal up to bisimilarity_
    if their components all agree, and their process terms
    are bisimilar. *)

Definition pmeBisim (c1 c2 : ProcMapEntry) : Prop :=
  match c1, c2 with
    | PEelem q1 P1 xs1 f1, PEelem q2 P2 xs2 f2 =>
        q1 = q2 /\ bisim P1 P2 /\ xs1 = xs2 /\ map f1 xs1 = map f2 xs2
    | PEfree, PEfree => True
    | PEinvalid, PEinvalid => True
    | _, _ => False
  end.

Notation "c1 ≃ c2" := (pmeBisim c1 c2) (only printing, at level 80).

(** The [pmeBisim] relation is an equivalence relation. *)

Global Instance pmeBisim_refl : Reflexive pmeBisim.
Proof. intro. red. desf. Qed.
Global Instance pmeBisim_symm : Symmetric pmeBisim.
Proof. unfold pmeBisim. red. ins. desf. intuition. Qed.
Global Instance pmeBisim_trans : Transitive pmeBisim.
Proof.
  unfold pmeBisim.
  red. ins. desf. intuition clarify.
  by transitivity P1. congruence.
Qed.
Global Instance pmeBisim_equiv : Equivalence pmeBisim.
Proof. split; intuition. Qed.

Hint Resolve pmeBisim_refl : core.

(** Bisimilarity is a congruence for [PEelem]. *)

Add Parametric Morphism : PEelem
  with signature eq ==> bisim ==> eq ==> eq ==> pmeBisim
    as PEelem_bisim_mor.
Proof. ins. Qed.

(** Below are several useful properties of [pmeBisim]. *)

Lemma pmeBisim_free :
  forall c1 c2, pmeBisim c1 c2 -> c1 = PEfree -> c2 = PEfree.
Proof.
  intros c1 c2 H1 H2.
  unfold pmeBisim in H1. desf.
Qed.

Lemma pmeBisim_equality :
  forall c q P xs f,
  pmeBisim c (PEelem q P xs f) ->
  exists P' f',
    c = PEelem q P' xs f' /\
    pmeBisim (PEelem q P xs f) (PEelem q P' xs f').
Proof.
  intros [q' P' xs' f'| |] q P xs f H1; vauto.
  exists P', f'. intuition vauto.
  - unfold pmeBisim in H1. repeat desf.
  - rewrite <- H1. unfold pmeBisim in *. repeat desf.
Qed.

Lemma pmeBisim_F :
  forall q P xs F1 F2,
    (forall x : ProcVar, In x xs -> F1 x = F2 x) ->
  pmeBisim (PEelem q P xs F1) (PEelem q P xs F2).
Proof.
  intros q P xs F1 F2 IN1. red.
  repeat split; vauto. by apply map_ext_in.
Qed.


(** *** Validity *)

(** A process map entry is _valid_ if any fractional permission
    it holds is valid. Free entries are always valid, whereas
    invalid entries are never valid. *)

Definition pmeValid (c : ProcMapEntry) : Prop :=
  match c with
    | PEelem q _ _ _ => perm_valid q
    | PEfree => True
    | PEinvalid => False
  end.

Notation "√ c" := (pmeValid c) (only printing, at level 80).

(** Free entries are always valid, whereas
    invalid entries are never valid. *)

Lemma pmeValid_free : pmeValid PEfree.
Proof. ins. Qed.
Lemma pheValid_invalid :
  forall c, pmeValid c -> c <> PEinvalid.
Proof. intros c H1. red in H1. desf. Qed.

Hint Resolve pmeValid_free : core.

(** Process map entry validity is closed under bisimilarity. *)

Lemma pmeValid_bisim :
  forall c1 c2, pmeBisim c1 c2 -> pmeValid c1 -> pmeValid c2.
Proof. unfold pmeBisim, pmeValid. ins. repeat desf. Qed.
Add Parametric Morphism : pmeValid
  with signature pmeBisim ==> iff as pmeValid_bisim_mor.
Proof. ins. split; apply pmeValid_bisim; auto. by symmetry. Qed.


(** *** Disjointness *)

(** Two process map entries are defined to be _disjoint_
    if their permission components are together disjoint. *)

Definition pmeDisj (c1 c2 : ProcMapEntry) : Prop :=
  match c1, c2 with
    | PEelem q1 _ xs1 f1, PEelem q2 _ xs2 f2 =>
        perm_disj q1 q2 /\ xs1 = xs2 /\ map f1 xs1 = map f2 xs2
    | PEelem q _ _ _, PEfree
    | PEfree, PEelem q _ _ _ => perm_valid q
    | PEfree, PEfree => True
    | PEinvalid, _
    | _, PEinvalid => False
  end.

Notation "c1 ⟂ c2" := (pmeDisj c1 c2) (only printing, at level 80).

(** The relation [pmeDisj] is symmetric. *)

Global Instance pmeDisj_symm : Symmetric pmeDisj.
Proof. unfold pmeDisj. red. ins. desf. intuition. Qed.

(** Any valid entry is disjoint with a free entry. *)

Lemma pmeDisj_free_l :
  forall c, pmeValid c -> pmeDisj c PEfree.
Proof. ins. Qed.
Lemma pmeDisj_free_r :
  forall c, pmeValid c -> pmeDisj PEfree c.
Proof. ins. Qed.

Hint Resolve pmeDisj_free_l pmeDisj_free_r : core.

(** No entry is disjoint with an invalid entry. *)

Lemma pmeDisj_invalid_l :
  forall c, ~ pmeDisj c PEinvalid.
Proof. intros c H1. red in H1. desf. Qed.
Lemma pmeDisj_invalid_r :
  forall c, ~ pmeDisj PEinvalid c.
Proof. intros c H1. red in H1. desf. Qed.

(** Any two disjoint entries are also valid. *)

Lemma pmeDisj_valid_l :
  forall c1 c2, pmeDisj c1 c2 -> pmeValid c1.
Proof.
  intros c1 c2 H.
  unfold pmeDisj, pmeValid in *.
  desf. intuition vauto.
  by apply perm_disj_valid_l in H0.
Qed.
Lemma pmeDisj_valid_r :
  forall c1 c2, pmeDisj c1 c2 -> pmeValid c2.
Proof.
  intros c1 c2 H. symmetry in H.
  by apply pmeDisj_valid_l with c1.
Qed.
Lemma pmeDisj_valid :
  forall c1 c2, pmeDisj c1 c2 -> pmeValid c1 /\ pmeValid c2.
Proof.
  intros c1 c2 H. split.
  - by apply pmeDisj_valid_l with c2.
  - by apply pmeDisj_valid_r with c1.
Qed.

Hint Resolve pmeDisj_valid_l pmeDisj_valid_r : core.

(** Disjoint entries can always be replaced by bisimilar ones. *)

Lemma pmeDisj_bisim_l :
  forall c1 c2 c, pmeBisim c1 c2 -> pmeDisj c1 c -> pmeDisj c2 c.
Proof.
  unfold pmeBisim, pmeDisj.
  ins. repeat desf.
  intuition congruence.
Qed.
Lemma pmeDisj_bisim_r :
  forall c1 c2 c, pmeBisim c1 c2 -> pmeDisj c c1 -> pmeDisj c c2.
Proof.
  unfold pmeBisim, pmeDisj.
  intros c1 c2 c H1 H2.
  simpls. repeat desf.
  intuition congruence.
Qed.
Add Parametric Morphism : pmeDisj
  with signature pmeBisim ==> pmeBisim ==> iff
    as pmeDisj_bisim_mor.
Proof.
  intros c1 c1' H1 c2 c2' H2. split; intro H.
  - apply pmeDisj_bisim_l with c1; auto.
    apply pmeDisj_bisim_r with c2; auto.
  - apply pmeDisj_bisim_l with c1'; [by symmetry|].
    apply pmeDisj_bisim_r with c2'; auto. by symmetry.
Qed.


(** *** Disjoint union *)

(** The (disjoint) union of two process map entries is defined
    as the addition of their process and permission components. *)

Definition pmeUnion (c1 c2 : ProcMapEntry) : ProcMapEntry :=
  match c1, c2 with
    | PEelem q1 P1 xs1 f1, PEelem q2 P2 xs2 f2 =>
        if procvars_eq_dec xs1 xs2 then
          if vals_eq_dec (map f1 xs1) (map f2 xs2)
          then PEelem (q1 + q2) (Ppar P1 P2) xs1 f1
          else PEinvalid
        else PEinvalid
    | PEelem q P xs f, PEfree
    | PEfree, PEelem q P xs f => PEelem q P xs f
    | PEfree, PEfree => PEfree
    | PEinvalid, _
    | _, PEinvalid => PEinvalid
  end.

Notation "c1 ⨄ c2" :=
  (pmeUnion c1 c2)
  (only printing, at level 80, right associativity).

(** The [pmeUnion] disjoint union relation is
    associative and commutative with respect to bisimilarity. *)

Lemma pmeUnion_assoc :
  forall c1 c2 c3,
  pmeBisim (pmeUnion (pmeUnion c1 c2) c3) (pmeUnion c1 (pmeUnion c2 c3)).
Proof.
  unfold pmeUnion. ins.
  desf; try congruence.
  unfold pmeBisim. intuition vauto.
  by rewrite Qcplus_assoc.
  by rewrite bisim_par_assoc.
Qed.

Lemma pmeUnion_comm :
  forall c1 c2, pmeBisim (pmeUnion c1 c2) (pmeUnion c2 c1).
Proof.
  unfold pmeUnion. ins.
  repeat desf; try congruence.
  unfold pmeBisim. intuition.
  apply Qcplus_comm.
  rewrite bisim_par_comm. auto.
Qed.

(** The disjoint union of two disjoint entries is always valid. *)

Lemma pmeUnion_valid :
  forall c1 c2, pmeDisj c1 c2 -> pmeValid (pmeUnion c1 c2).
Proof.
  unfold pmeDisj, pmeUnion, pmeValid.
  ins. repeat desf.
  by apply perm_add_valid.
Qed.

(** Free entries are neutral with respect to disjoint union. *)

Lemma pmeUnion_free_l : forall c, pmeUnion c PEfree = c.
Proof. unfold pmeUnion. ins. desf. Qed.
Lemma pmeUnion_free_r : forall c, pmeUnion PEfree c = c.
Proof. unfold pmeUnion. ins. desf. Qed.

Hint Rewrite pmeUnion_free_l pmeUnion_free_r : core.

(** Invalid entries are absorbing with respect to disjoint union. *)

Lemma pmeUnion_invalid_l :
  forall c, pmeUnion c PEinvalid = PEinvalid.
Proof. unfold pmeUnion. intros. desf. Qed.
Lemma pmeUnion_invalid_r :
  forall c, pmeUnion PEinvalid c = PEinvalid.
Proof. unfold pmeUnion. intros. desf. Qed.

(** Bisimilarity of entries is closed under disjoint union. *)

Lemma pmeUnion_bisim_l :
  forall c1 c2 c,
  pmeBisim c1 c2 -> pmeBisim (pmeUnion c1 c) (pmeUnion c2 c).
Proof.
  unfold pmeBisim, pmeUnion. ins.
  repeat desf; intuition try congruence.
  by rewrite H0.
Qed.
Lemma pmeUnion_bisim_r :
  forall c1 c2 c,
  pmeBisim c1 c2 -> pmeBisim (pmeUnion c c1) (pmeUnion c c2).
Proof.
  unfold pmeBisim, pmeUnion. ins.
  repeat desf; intuition try congruence.
  by rewrite H0.
Qed.
Add Parametric Morphism : pmeUnion
  with signature pmeBisim ==> pmeBisim ==> pmeBisim
    as pmeUnion_bisim_mor.
Proof.
  intros c1 c1' H1 c2 c2' H2.
  transitivity (pmeUnion c1' c2).
  - by apply pmeUnion_bisim_l.
  - by apply pmeUnion_bisim_r.
Qed.

Hint Resolve pmeUnion_bisim_l pmeUnion_bisim_r : core.

(** Below are several other useful properties of [pmeUnion]. *)

Lemma pmeUnion_elem :
  forall q1 q2 P1 P2 xs f,
  pmeUnion (PEelem q1 P1 xs f) (PEelem q2 P2 xs f) =
  PEelem (q1 + q2) (Ppar P1 P2) xs f.
Proof.
  intros q1 q2 P1 P2 xs f.
  unfold pmeUnion. desf.
Qed.

Lemma pmeDisj_union_l :
  forall c1 c2 c3,
  pmeDisj c1 c2 -> pmeDisj (pmeUnion c1 c2) c3 -> pmeDisj c2 c3.
Proof.
  unfold pmeUnion, pmeDisj.
  intros c1 c2 c3 H1 H2.
  desf; intuition vauto; des.
  - by apply perm_disj_add_l in H1.
  - congruence.
  - by apply perm_disj_valid_r in H.
  - by apply perm_disj_valid_r in H.
Qed.
Lemma pmeDisj_union_r :
  forall c1 c2 c3,
  pmeDisj c2 c3 -> pmeDisj c1 (pmeUnion c2 c3) -> pmeDisj c1 c2.
Proof.
  intros c1 c2 c3 H1 H2.
  symmetry in H1, H2.
  rewrite pmeUnion_comm in H2; auto.
  apply pmeDisj_union_l in H2; auto.
  by symmetry.
Qed.

Lemma pmeDisj_assoc_l :
  forall c1 c2 c3,
  pmeDisj c1 c2 ->
  pmeDisj (pmeUnion c1 c2) c3 ->
  pmeDisj c1 (pmeUnion c2 c3).
Proof.
  unfold pmeDisj, pmeUnion.
  intros c1 c2 c3 H1 H2.
  desf; intuition vauto; desf.
  - by apply perm_disj_assoc_l.
  - congruence.
  - by apply perm_add_valid.
Qed.
Lemma pmeDisj_assoc_r :
  forall c1 c2 c3,
  pmeDisj c2 c3 ->
  pmeDisj c1 (pmeUnion c2 c3) ->
  pmeDisj (pmeUnion c1 c2) c3.
Proof.
  intros c1 c2 c3 H1 H2.
  symmetry in H1, H2.
  rewrite pmeUnion_comm in H2; auto.
  apply pmeDisj_assoc_l in H2; auto.
  rewrite pmeUnion_comm in H2; auto.
  by symmetry.
Qed.

Lemma pmeDisj_swap_r :
  forall c1 c2 c3,
  pmeDisj c1 c2 ->
  pmeDisj (pmeUnion c1 c2) c3 ->
  pmeDisj (pmeUnion c1 c3) c2.
Proof.
  intros c1 c2 c3 H1 H2.
  assert (H3 : pmeDisj c2 c3). {
    by apply pmeDisj_union_l with c1. }
  rewrite pmeUnion_comm.
  apply pmeDisj_assoc_r; auto.
  by symmetry.
Qed.
Lemma pmeDisj_swap_l :
  forall c1 c2 c3,
  pmeDisj c1 c2 ->
  pmeDisj (pmeUnion c1 c2) c3 ->
  pmeDisj (pmeUnion c2 c3) c1.
Proof.
  intros c1 c2 c3 H1 H2.
  apply pmeDisj_swap_r; auto.
  - by symmetry.
  - by rewrite pmeUnion_comm.
Qed.

Lemma pmeDisj_middle :
  forall c1 c2 c3 c4,
  pmeDisj c1 c2 ->
  pmeDisj c3 c4 ->
  pmeDisj (pmeUnion c1 c2) (pmeUnion c3 c4) ->
  pmeDisj c2 c3.
Proof.
  intros c1 c2 c3 c4 H1 H2 H3.
  apply pmeDisj_union_l with c1; auto.
  by apply pmeDisj_union_r with c4.
Qed.

Lemma pmeDisj_compat :
  forall c1 c2 c3 c4,
  pmeDisj c1 c3 ->
  pmeDisj c2 c4 ->
  pmeDisj (pmeUnion c1 c3) (pmeUnion c2 c4) ->
  pmeDisj (pmeUnion c1 c2) (pmeUnion c3 c4).
Proof.
  intros c1 c2 c3 c4 H1 H2 H3.
  apply pmeDisj_assoc_r.
  - rewrite pmeUnion_comm.
    apply pmeDisj_assoc_l; auto.
    symmetry. by apply pmeDisj_union_l in H3.
  - rewrite pmeUnion_comm.
    rewrite pmeUnion_assoc.
    apply pmeDisj_assoc_l; auto.
    by rewrite pmeUnion_comm with (c1:=c4)(c2:=c2).
Qed.

Lemma pmeUnion_swap_l :
  forall c1 c2 c3,
  pmeBisim
    (pmeUnion c1 (pmeUnion c2 c3))
    (pmeUnion c2 (pmeUnion c1 c3)).
Proof.
  ins. repeat rewrite <- pmeUnion_assoc.
  by apply pmeUnion_bisim_l, pmeUnion_comm.
Qed.
Lemma pmeUnion_swap_r :
  forall c1 c2 c3,
  pmeBisim
    (pmeUnion (pmeUnion c1 c2) c3)
    (pmeUnion (pmeUnion c1 c3) c2).
Proof.
  ins. repeat rewrite pmeUnion_assoc.
  by apply pmeUnion_bisim_r, pmeUnion_comm.
Qed.

Lemma pmeUnion_compat :
  forall c1 c2 c3 c4,
  pmeBisim
    (pmeUnion (pmeUnion c1 c3) (pmeUnion c2 c4))
    (pmeUnion (pmeUnion c1 c2) (pmeUnion c3 c4)).
Proof.
  ins. repeat rewrite pmeUnion_assoc.
  apply pmeUnion_bisim_r.
  repeat rewrite <- pmeUnion_assoc.
  apply pmeUnion_bisim_l, pmeUnion_comm.
Qed.

Lemma pmeUnion_free :
  forall c1 c2,
  pmeUnion c1 c2 = PEfree <-> c1 = PEfree /\ c2 = PEfree.
Proof.
  intros c1 c2.
  unfold pmeUnion.
  intuition desf.
Qed.

Lemma pmeUnion_not_free :
  forall c1 c2,
  pmeUnion c1 c2 <> PEfree <-> c1 <> PEfree \/ c2 <> PEfree.
Proof.
  intros c1 c2. split; intro H.
  - unfold pmeUnion in H. desf; vauto.
  - unfold pmeUnion. desf; vauto.
Qed.


(** *** Entirety *)

(** Any process map entry [c] is _entire_ if [c] is an
    occupied entry with a full fractional permission. *)

Definition pmeEntire (c : ProcMapEntry) : Prop :=
  match c with
    | PEfree
    | PEinvalid => False
    | PEelem q _ _ _ => q = perm_full
  end.

(** Entire entries can always be replaced by bisimilar ones. *)

Lemma pmeEntire_bisim :
  forall c1 c2, pmeBisim c1 c2 -> pmeEntire c1 -> pmeEntire c2.
Proof. unfold pmeBisim, pmeEntire. ins. repeat desf. Qed.
Add Parametric Morphism : pmeEntire
  with signature pmeBisim ==> iff as pmeEntire_bisim_mor.
Proof. ins; split; apply pmeEntire_bisim; auto. by symmetry. Qed.

(** Below are several other useful properties of entirety. *)

Lemma pmeEntire_union :
  forall c1 c2,
  pmeDisj c1 c2 ->
  pmeEntire c1 \/ pmeEntire c2 ->
  pmeEntire (pmeUnion c1 c2).
Proof.
  intros c1 c2 H1 H2. destruct H2 as [H2|H2].
  (* [c1] is full *)
  - unfold pmeDisj in H1.
    unfold pmeEntire, pmeUnion in *.
    repeat desf. by apply perm_disj_full_neg_r in H1.
  (* [c2] is full *)
  - unfold pmeDisj in H1.
    unfold pmeEntire, pmeUnion in *.
    repeat desf. by apply perm_disj_full_neg_l in H1.
Qed.

Lemma pmeDisj_entire_free :
  forall c1 c2, pmeDisj c1 c2 -> pmeEntire c1 -> c2 = PEfree.
Proof.
  intros c1 c2 H1 H2.
  unfold pmeDisj in H1. unfold pmeEntire in H2.
  repeat desf. by apply perm_disj_full_neg_r in H1.
Qed.

Lemma pmeEntire_content :
  forall c,
  pmeEntire c -> exists P xs f, c = PEelem perm_full P xs f.
Proof.
  intros c H. unfold pmeEntire in H.
  desf. exists P, xs, f. auto.
Qed.

Lemma pmeEntire_exp_l :
  forall c1 c2,
  pmeDisj c1 c2 -> pmeEntire c1 -> pmeUnion c1 c2 = c1.
Proof.
  intros c1 c2 H1 H2.
  apply pmeDisj_entire_free in H1; vauto.
  by rewrite pmeUnion_free_l.
Qed.
Lemma pmeEntire_exp_r :
  forall c1 c2,
  pmeDisj c1 c2 -> pmeEntire c2 -> pmeUnion c1 c2 = c2.
Proof.
  intros c1 c2 H1 H2. symmetry in H1.
  apply pmeDisj_entire_free in H1; vauto.
  by rewrite pmeUnion_free_r.
Qed.


(** *** Projection *)

(** The _projection_ of any process map entry is the list of values
    obtained by taking the image of the mappings stored in occupied
    entries (or [nil] if the entry of free or invalid). *)

Definition pmeProj (c : ProcMapEntry) : list Val :=
  match c with
    | PEelem _ _ xs f => map f xs
    | PEfree
    | PEinvalid => nil
  end.

(** Projection is closed under bisimilarity. *)

Lemma pmeProj_bisim :
  forall c1 c2, pmeBisim c1 c2 -> pmeProj c1 = pmeProj c2.
Proof. unfold pmeBisim, pmeProj. ins. desf. desf. Qed.
Add Parametric Morphism : pmeProj
  with signature pmeBisim ==> eq as pmeProj_bisim_mor.
Proof. ins. by apply pmeProj_bisim. Qed.

(** Below are several useful properties for projections. *)

Lemma pmeProj_union :
  forall c1 c2 v,
  pmeDisj c1 c2 ->
  In v (pmeProj c1) ->
  In v (pmeProj (pmeUnion c1 c2)).
Proof.
  intros c1 c2 v H1 H2.
  unfold pmeDisj in H1.
  unfold pmeProj, pmeUnion in *.
  repeat desf.
Qed.

Lemma pmeProj_disj_union :
  forall c1 c2,
  pmeDisj c1 c2 ->
  pmeProj c1 <> nil ->
  pmeProj (pmeUnion c1 c2) = pmeProj c1.
Proof.
  intros c1 c2 H1 H2.
  unfold pmeDisj, pmeProj, pmeUnion in *.
  repeat desf.
Qed.


(** *** Heap coverage *)

(** Any process map entry [c] is said to _fully cover a heap [h]_
    if [h] contains an entry at every location that is
    in the projection of [c]. *)

Definition pmeCovers (c : ProcMapEntry)(h : Heap) : Prop :=
  forall l, In l (pmeProj c) -> exists v, h l = Some v.

(** Heap coverage is closed under bisimilarity. *)

Lemma pmeCovers_bisim :
  forall c1 c2 h,
  pmeBisim c1 c2 -> pmeCovers c1 h -> pmeCovers c2 h.
Proof.
  intros c1 c2 h H1 H2. unfold pmeCovers in *.
  intros l H3. rewrite <- H1 in H3.
  by apply H2 in H3.
Qed.
Add Parametric Morphism : pmeCovers
  with signature pmeBisim ==> eq ==> iff as pmeCovers_bisim_mor.
Proof. ins. split; apply pmeCovers_bisim; auto. by symmetry. Qed.

(** Free entries cover every heap. *)

Lemma pmeCovers_free :
  forall h, pmeCovers PEfree h.
Proof.
  intros h. red. intros l H1. simpl in H1. vauto.
Qed.

(** Below are various other useful properties of coverage. *)

Lemma pmeCovers_union :
  forall c1 c2 h,
  pmeDisj c1 c2 ->
  pmeCovers (pmeUnion c1 c2) h ->
  pmeCovers c1 h.
Proof.
  intros c1 c2 h H1 H2. unfold pmeCovers in *.
  intros l H3. apply H2. by apply pmeProj_union.
Qed.

Lemma pmeCovers_hUpdate :
  forall c h l v,
  ~ In l (pmeProj c) -> pmeCovers c h -> pmeCovers c (hUpdate h l v).
Proof.
  intros c h l v H1 H2. unfold pmeCovers in *.
  intros l' H3.
  assert (H4 : l <> l'). { intro H4. apply H1. vauto. }
  apply H2 in H3. destruct H3 as (v'&H3).
  exists v'. unfold hUpdate, update. desf.
Qed.

Lemma pmeCovers_agrees :
  forall c h1 h2,
    (forall l, In l (pmeProj c) -> h1 l = h2 l) ->
  pmeCovers c h1 ->
  pmeCovers c h2.
Proof.
  intros c h1 h2 H1 H2. unfold pmeCovers in *.
  intros l H3. generalize H3. intro H4.
  apply H2 in H3. destruct H3 as (v&H3).
  exists v. rewrite <- H1; vauto.
Qed.

Lemma pmeCovers_subheap :
  forall c h1 h2,
    (forall l v, h1 l = Some v -> h2 l = Some v) ->
  pmeCovers c h1 ->
  pmeCovers c h2.
Proof.
  intros c h1 h2 H1 H2. unfold pmeCovers in *.
  intros l H3. apply H2 in H3. destruct H3 as (v&H3).
  exists v. by apply H1.
Qed.

Lemma pmeCovers_occ :
  forall c h1 h2,
    (forall l, h1 l <> None -> h2 l <> None) ->
  pmeCovers c h1 ->
  pmeCovers c h2.
Proof.
  intros c h1 h2 H1 H2. unfold pmeCovers in *.
  intros l H3. apply H2 in H3. destruct H3 as (v&H3).
  assert (H4 : h1 l <> None). { intro H4. vauto. }
  apply H1 in H4.
  assert (H5 : exists v' : Val, h2 l = Some v'). {
    by apply option_not_none. }
  destruct H5 as (v'&H5). by exists v'.
Qed.


(** *** Agreement *)

(** The following relation [pmeAgree c1 c2] captures whether
    two process map entries [c1] and [c2] agree on their static
    components (which is everything except processes). *)

Definition pmeAgree (c1 c2 : ProcMapEntry) : Prop :=
  match c1, c2 with
    | PEfree, PEfree
    | PEinvalid, PEinvalid => True
    | PEelem q1 _ xs1 F1, PEelem q2 _ xs2 F2 =>
        q1 = q2 /\ xs1 = xs2 /\ map F1 xs1 = map F2 xs2
    | _, _ => False
  end.

(** The [pmeAgree] relation is an equivalence relation. *)

Global Instance pmeAgree_refl : Reflexive pmeAgree.
Proof. intros c. red. desf. Qed.
Global Instance pmeAgree_symm : Symmetric pmeAgree.
Proof.
  intros c1 c2 H1.
  unfold pmeAgree in *. repeat desf.
Qed.
Global Instance pmeAgree_trans : Transitive pmeAgree.
Proof.
  intros c1 c2 c3 H1 H2.
  unfold pmeAgree in *.
  repeat desf. intuition vauto.
  by rewrite H5, H3.
Qed.
Global Instance pmeAgree_equiv : Equivalence pmeAgree.
Proof. split; intuition. Qed.

Hint Resolve pmeAgree_refl : core.

(** Bisimilarity is a subrelation of agreement. *)

Global Instance pmeAgree_bisim : subrelation pmeBisim pmeAgree.
Proof. red. unfold pmeBisim, pmeAgree. ins. repeat desf. Qed.

Add Parametric Morphism : pmeAgree
  with signature pmeAgree ==> pmeAgree ==> iff
    as pmeAgree_agree_mor.
Proof.
  intros c1 c1' H1 c2 c2' H2. split; intro H3.
  - by rewrite <- H1, <- H2.
  - by rewrite H1, H2.
Qed.

(** Disjointness is closed under agreement. *)

Lemma pmeDisj_agree_l :
  forall c1 c2 c3,
  pmeAgree c1 c2 -> pmeDisj c1 c3 -> pmeDisj c2 c3.
Proof.
  intros c1 c2 c3 H1 H2.
  unfold pmeAgree, pmeDisj in *.
  repeat desf. intuition vauto.
  by rewrite <- H5, H3.
Qed.
Lemma pmeDisj_agree_r :
  forall c1 c2 c3,
  pmeAgree c1 c2 -> pmeDisj c3 c1 -> pmeDisj c3 c2.
Proof.
  intros c1 c2 c3 H1 H2. symmetry.
  apply pmeDisj_agree_l with c1; auto.
  by symmetry.
Qed.
Add Parametric Morphism : pmeDisj
  with signature pmeAgree ==> pmeAgree ==> iff
    as pmeDisj_agree_mor.
Proof.
  intros c1 c2 H1 c3 c4 H2. split; intro H3.
  - apply pmeDisj_agree_l with c1; auto.
    apply pmeDisj_agree_r with c3; auto.
  - apply pmeDisj_agree_l with c2; auto.
    + by symmetry.
    + apply pmeDisj_agree_r with c4; auto.
      by symmetry.
Qed.

(** Disjoint union is closed under agreement *)

Lemma pmeAgree_union_l :
  forall c1 c2 c3,
  pmeAgree c1 c2 -> pmeAgree (pmeUnion c1 c3) (pmeUnion c2 c3).
Proof.
  intros c1 c2 c3 H1.
  unfold pmeAgree, pmeUnion in *. repeat desf.
  - rewrite H2 in e. congruence.
  - rewrite H2 in n. congruence.
Qed.
Lemma pmeAgree_union_r :
  forall c1 c2 c3,
  pmeAgree c1 c2 -> pmeAgree (pmeUnion c3 c1) (pmeUnion c3 c2).
Proof.
  intros c1 c2 c3 H1.
  rewrite pmeUnion_comm with (c2:=c1).
  rewrite pmeUnion_comm with (c2:=c2).
  by apply pmeAgree_union_l.
Qed.
Add Parametric Morphism : pmeUnion
  with signature pmeAgree ==> pmeAgree ==> pmeAgree
    as pmeUnion_agree_mor.
Proof.
  intros c1 c1' H1 c2 c2' H2.
  transitivity (pmeUnion c1 c2').
  - by apply pmeAgree_union_r.
  - by apply pmeAgree_union_l.
Qed.

Hint Resolve pmeAgree_union_l pmeAgree_union_r : core.


(** Below are other useful properties of agreement. *)

Lemma pmeProj_agree :
  forall c1 c2, pmeAgree c1 c2 -> pmeProj c1 = pmeProj c2.
Proof.
  intros c1 c2 H1.
  unfold pmeAgree in H1. repeat desf.
Qed.
Add Parametric Morphism : pmeProj
  with signature pmeAgree ==> eq
    as pmeProj_agree_mor.
Proof.
  intros c1 c2 H1. by apply pmeProj_agree.
Qed.

Lemma pmeCovers_agree :
  forall c1 c2 h,
  pmeAgree c1 c2 ->
  pmeCovers c1 h ->
  pmeCovers c2 h.
Proof.
  intros c1 c2 h H1 H2 l IN1.
  red in H2. specialize H2 with l.
  rewrite pmeProj_agree with c1 c2 in H2; auto.
Qed.
Add Parametric Morphism : pmeCovers
  with signature pmeAgree ==> eq ==> iff
    as pmeCovers_agree_mor.
Proof.
  intros c1 c2 H1 h. split; intro H2.
  - apply pmeCovers_agree with c1; auto.
  - apply pmeCovers_agree with c2; auto.
    by symmetry.
Qed.


(** *** Weak agreement *)

(** Weak agreement between two process map entries is
    essentially the same as ordinary agreement, however
    permission components are not involved in the agreement. *)

Definition pmeWeakAgree (c1 c2 : ProcMapEntry) : Prop :=
  match c1, c2 with
    | PEfree, PEfree
    | PEinvalid, PEinvalid => True
    | PEelem _ _ xs1 F1, PEelem _ _ xs2 F2 =>
        xs1 = xs2 /\ map F1 xs1 = map F2 xs2
    | _, _ => False
  end.

(** Weak agreement is an equivalence relation. *)

Global Instance pmeWeakAgree_refl : Reflexive pmeWeakAgree.
Proof. intros c. red. desf. Qed.
Global Instance pmeWeakAgree_symm : Symmetric pmeWeakAgree.
Proof.
  intros c1 c2 H1.
  unfold pmeWeakAgree in *.
  repeat desf.
Qed.
Global Instance pmeWeakAgree_trans : Transitive pmeWeakAgree.
Proof.
  intros c1 c2 c3 H1 H2.
  unfold pmeWeakAgree in *.
  repeat desf. intuition vauto.
  by rewrite H3, H0.
Qed.
Global Instance pmeWeakAgree_equiv : Equivalence pmeWeakAgree.
Proof. split; intuition. Qed.

Hint Resolve pmeWeakAgree_refl : core.

(** (Ordinary) agreement and bisimilarity are both
    subrelations of weak agreement. *)

Global Instance pmeAgree_weaken : subrelation pmeAgree pmeWeakAgree.
Proof. red. unfold pmeAgree, pmeWeakAgree. ins. repeat desf. Qed.
Global Instance pmeWeakAgree_bisim : subrelation pmeBisim pmeWeakAgree.
Proof. red. unfold pmeBisim, pmeWeakAgree. ins. repeat desf. Qed.

(** Below are several other useful properties of weak agreement. *)

Lemma pmeWeakAgree_union_l :
  forall c1 c2 c3,
  pmeWeakAgree c1 c2 -> pmeWeakAgree (pmeUnion c1 c3) (pmeUnion c2 c3).
Proof.
  intros c1 c2 c3 H1.
  unfold pmeWeakAgree, pmeUnion in *.
  repeat desf.
  - rewrite H0 in e. congruence.
  - rewrite H0 in n. congruence.
Qed.
Lemma pmeWeakAgree_union_r :
  forall c1 c2 c3,
  pmeWeakAgree c1 c2 -> pmeWeakAgree (pmeUnion c3 c1) (pmeUnion c3 c2).
Proof.
  intros c1 c2 c3 H1.
  rewrite pmeUnion_comm with (c2 := c1).
  rewrite pmeUnion_comm with (c2 := c2).
  by apply pmeWeakAgree_union_l.
Qed.

Hint Resolve pmeWeakAgree_union_l pmeWeakAgree_union_r : core.

Lemma pmeWeakAgree_proj :
  forall c1 c2,
  pmeWeakAgree c1 c2 -> pmeProj c1 = pmeProj c2.
Proof.
  intros c1 c2 H1.
  unfold pmeWeakAgree in H1. repeat desf.
Qed.
Add Parametric Morphism : pmeProj
  with signature pmeWeakAgree ==> eq
  as pmeWeakAgree_proj_mor.
Proof.
  intros c1 c2 H1.
  by apply pmeWeakAgree_proj.
Qed.


(** *** Occupation *)

(** The [pmeOcc] predicate determines whether a given process map entry
    is _occupied_, i.e., contains some element. *)

Definition pmeOcc (c : ProcMapEntry) : Prop :=
  match c with
    | PEelem _ _ _ _ => True
    | _ => False
  end.

(** Occupation is closed under bisimilarity. *)

Lemma pmeOcc_bisim :
  forall c1 c2, pmeBisim c1 c2 -> pmeOcc c1 -> pmeOcc c2.
Proof. unfold pmeBisim, pmeOcc. ins. desf. Qed.
Add Parametric Morphism : pmeOcc
  with signature pmeBisim ==> iff as pmeOcc_bisim_mor.
Proof. ins. split; apply pmeOcc_bisim; auto. by symmetry. Qed.

(** Occupation is closed under (ordinary) agreement. *)

Lemma pmeOcc_agree :
  forall c1 c2, pmeAgree c1 c2 -> pmeOcc c1 -> pmeOcc c2.
Proof. unfold pmeAgree, pmeOcc. ins. desf. Qed.
Add Parametric Morphism : pmeOcc
  with signature pmeAgree ==> iff as pmeOcc_agree_mor.
Proof. ins. split; apply pmeOcc_agree; auto. by symmetry. Qed.

(** Below are several more useful properties of occupation. *)

Lemma pmeOcc_union_l :
  forall c1 c2,
  pmeDisj c1 c2 -> pmeOcc c1 -> pmeOcc (pmeUnion c1 c2).
Proof.
  intros c1 c2 H1 H2.
  unfold pmeDisj, pmeOcc, pmeUnion in *.
  repeat desf.
Qed.
Lemma pmeOcc_union_r :
  forall c1 c2,
  pmeDisj c1 c2 -> pmeOcc c2 -> pmeOcc (pmeUnion c1 c2).
Proof.
  intros c1 c2 H1 H2.
  rewrite pmeUnion_comm.
  apply pmeOcc_union_l; auto.
  by symmetry.
Qed.

Lemma pmeOcc_destruct :
  forall c,
  pmeOcc c -> exists q P xs f, c = PEelem q P xs f.
Proof.
  intros c H. unfold pmeOcc in H.
  desf. by exists q, P, xs, f.
Qed.

Lemma pmeWeakAgree_union_occ :
  forall c1 c2,
  pmeDisj c1 c2 -> pmeOcc c1 -> pmeWeakAgree c1 (pmeUnion c1 c2).
Proof.
  intros c1 c2 H1 H2.
  unfold pmeDisj, pmeUnion, pmeOcc, pmeWeakAgree in *.
  repeat desf.
Qed.


(** ** Process maps *)

Definition ProcMap := Val -> ProcMapEntry.

(** The _identity_ process map is free at every entry. *)

Definition pmIden : ProcMap := fun _ => PEfree.

(** An update operation for process maps: *)

Definition pmUpdate (pm : ProcMap)(v : Val)(c : ProcMapEntry) :=
  update val_eq_dec pm v c.


(** *** Bisimilarity *)

(** Two process maps are _bisimilar_ if their entries
    are pointwise bisimilar (with respect to [pmeBisim]). *)

Definition pmBisim : relation ProcMap :=
  pointwise_relation Val pmeBisim.

Notation "pm1 ≃ pm2" := (pmBisim pm1 pm2) (only printing, at level 80).

(** Bisimilarity preserves any free entries. *)

Lemma pmBisim_free :
  forall pm1 pm2 pid,
  pmBisim pm1 pm2 -> pm1 pid = PEfree -> pm2 pid = PEfree.
Proof.
  intros pm1 pm2 pid H1 H2.
  by apply pmeBisim_free with (pm1 pid).
Qed.

(** Bisimilarity is an equivalence relation. *)

Global Instance pmBisim_refl : Reflexive pmBisim.
Proof. red. red. by ins. Qed.
Global Instance pmBisim_symm : Symmetric pmBisim.
Proof. intros ????. by symmetry. Qed.
Global Instance pmBisim_trans : Transitive pmBisim.
Proof. intros ? pm ??? pid. by transitivity (pm pid). Qed.
Global Instance pmBisim_equiv : Equivalence pmBisim.
Proof. split; intuition. Qed.

Hint Resolve pmBisim_refl : core.

(** Process map updates are closed under bisimilarity. *)

Lemma pmUpdate_bisim :
  forall pm1 pm2 pid c1 c2,
  pmBisim pm1 pm2 ->
  pmeBisim c1 c2 ->
  pmBisim (pmUpdate pm1 pid c1) (pmUpdate pm2 pid c2).
Proof.
  intros pm1 pm2 pid c1 c2 H1 H2.
  red. red. intros pid'. red in H1. red in H1.
  specialize H1 with pid'.
  unfold pmUpdate, update.
  case (val_eq_dec pid pid'); ins.
Qed.
Add Parametric Morphism : pmUpdate
  with signature pmBisim ==> eq ==> pmeBisim ==> pmBisim
    as pmUpdate_bisim_mor.
Proof.
  intros pm1 pm2 H1 pid c1 c2 H2.
  apply pmUpdate_bisim; auto.
Qed.

Hint Resolve pmUpdate_bisim : core.


(** *** Validity *)

(** Any process map is defined to be _valid_
    if all its entries are valid. *)

Definition pmValid (pm : ProcMap) : Prop :=
  forall pid, pmeValid (pm pid).

Notation "√ pm" := (pmValid pm) (only printing, at level 80).

(** Validity is closed under bisimilarity. *)

Lemma pmValid_bisim :
  forall pm1 pm2, pmBisim pm1 pm2 -> pmValid pm1 -> pmValid pm2.
Proof.
  intros pm1 pm2 H1 H2 pid.
  unfold pmBisim, pmValid in *.
  red in H1. specialize H1 with pid.
  by rewrite <- H1.
Qed.
Add Parametric Morphism : pmValid
  with signature pmBisim ==> iff as pmValid_bisim_mor.
Proof. ins. split; apply pmValid_bisim; auto. by symmetry. Qed.

(** Below are several other useful properties of validity. *)

Lemma pmValid_iden : pmValid pmIden.
Proof. red. ins. Qed.

Hint Resolve pmValid_iden : core.

Lemma pmValid_update :
  forall c pm pid,
  pmeValid c -> pmValid pm -> pmValid (pmUpdate pm pid c).
Proof.
  intros ??????. unfold pmUpdate, update. desf.
Qed.


(** *** Disjointness *)

(** Two process maps are defined to be _disjoint_
    if their entries are disjoint pairwise. *)

Definition pmDisj : relation ProcMap :=
  pointwise_relation Val pmeDisj.

Notation "pm1 ⟂ pm2" := (pmDisj pm1 pm2) (only printing, at level 80).

(** Process map disjointness is a symmetric relation. *)

Global Instance pmDisj_symm : Symmetric pmDisj.
Proof. intros ????. by symmetry. Qed.

(** Disjointness is closed under bisimilarity. *)

Lemma pmDisj_bisim_l :
  forall pm1 pm2 pm,
  pmBisim pm1 pm2 -> pmDisj pm1 pm -> pmDisj pm2 pm.
Proof.
  unfold pmBisim, pmDisj.
  intros ??? H ??. by rewrite <- H.
Qed.
Lemma pmDisj_bisim_r :
  forall pm1 pm2 pm,
  pmBisim pm1 pm2 -> pmDisj pm pm1 -> pmDisj pm pm2.
Proof.
  unfold pmBisim, pmDisj.
  intros ??? H ??. by rewrite <- H.
Qed.
Add Parametric Morphism : pmDisj
  with signature pmBisim ==> pmBisim ==> iff
    as pmDisj_bisim_mor.
Proof.
  intros pm1 pm1' H1 pm2 pm2' H2. split; intro H.
  - apply pmDisj_bisim_l with pm1; auto.
    apply pmDisj_bisim_r with pm2; auto.
  - apply pmDisj_bisim_l with pm1'; [by symmetry|].
    apply pmDisj_bisim_r with pm2'; auto.
    by symmetry.
Qed.

(** Any two process maps related by disjointness are also valid. *)

Lemma pmDisj_valid_l :
  forall pm1 pm2, pmDisj pm1 pm2 -> pmValid pm1.
Proof.
  intros ? pm ? pid.
  by apply pmeDisj_valid_l with (pm pid).
Qed.
Lemma pmDisj_valid_r :
  forall pm1 pm2, pmDisj pm1 pm2 -> pmValid pm2.
Proof.
  intros pm ?? pid.
  by apply pmeDisj_valid_r with (pm pid).
Qed.
Lemma pmDisj_valid :
  forall pm1 pm2, pmDisj pm1 pm2 -> pmValid pm1 /\ pmValid pm2.
Proof.
  intros pm1 pm2 H. intuition.
  - by apply pmDisj_valid_l with pm2.
  - by apply pmDisj_valid_r with pm1.
Qed.

(** Below are other useful properties of disjointness. *)

Lemma pmDisj_iden_l :
  forall pm, pmValid pm -> pmDisj pm pmIden.
Proof.
  unfold pmValid, pmIden.
  intros ???. by apply pmeDisj_free_l.
Qed.
Lemma pmDisj_iden_r :
  forall pm, pmValid pm -> pmDisj pmIden pm.
Proof.
  unfold pmValid, pmIden.
  intros ???. by apply pmeDisj_free_r.
Qed.

Hint Resolve pmDisj_iden_l pmDisj_iden_r : core.

Lemma pmDisj_upd :
  forall c1 c2 pm1 pm2 pid,
  pmeDisj c1 c2 ->
  pmDisj pm1 pm2 ->
  pmDisj (pmUpdate pm1 pid c1) (pmUpdate pm2 pid c2).
Proof.
  unfold pmDisj, pmUpdate, update.
  intros ????????. desf.
Qed.

Hint Resolve pmDisj_upd : core.


(** *** Disjoint union *)

(** The (disjoint) union of two process maps is defined
    to be the pairwise disjoint union of their entries. *)

Definition pmUnion (pm1 pm2 : ProcMap) : ProcMap :=
  fun pid => pmeUnion (pm1 pid) (pm2 pid).

Notation "pm1 ⨄ pm2" :=
  (pmUnion pm1 pm2)
  (only printing, at level 80, right associativity).

(** Disjoint union is closed under bisimilarity. *)

Lemma pmUnion_bisim :
  forall pm1 pm2 pm1' pm2',
  pmBisim pm1 pm2 -> pmBisim pm1' pm2' ->
  pmBisim (pmUnion pm1 pm1') (pmUnion pm2 pm2').
Proof.
  intros pm1 pm2 pm1' pm2' H1 H2 v.
  red in H1. red in H1. red in H2. red in H2.
  unfold pmUnion. by rewrite <- H1, <- H2.
Qed.
Add Parametric Morphism : pmUnion
  with signature pmBisim ==> pmBisim ==> pmBisim
    as pmUnion_bisim_mor.
Proof. ins. apply pmUnion_bisim; auto; by symmetry. Qed.

(** Identity laws for disjoint union: *)

Lemma pmUnion_iden_l :
  forall pm, pmUnion pm pmIden = pm.
Proof.
  intro pm. extensionality pid.
  unfold pmUnion, pmIden.
  apply pmeUnion_free_l.
Qed.
Lemma pmUnion_iden_r :
  forall pm, pmUnion pmIden pm = pm.
Proof.
  intro pm. extensionality pid.
  unfold pmUnion, pmIden.
  apply pmeUnion_free_r.
Qed.

Hint Rewrite pmUnion_iden_l pmUnion_iden_r : core.

(** Disjoint union is associative and commutative. *)

Lemma pmUnion_assoc :
  forall pm1 pm2 pm3,
  pmBisim
    (pmUnion (pmUnion pm1 pm2) pm3)
    (pmUnion pm1 (pmUnion pm2 pm3)).
Proof.
  intros ????. apply pmeUnion_assoc.
Qed.

Lemma pmUnion_comm :
  forall pm1 pm2,
  pmBisim (pmUnion pm1 pm2) (pmUnion pm2 pm1).
Proof.
  intros ???. by apply pmeUnion_comm.
Qed.

(** Below are various other useful properties of [pmUnion]. *)

Lemma pmUnion_valid :
  forall pm1 pm2,
  pmDisj pm1 pm2 -> pmValid (pmUnion pm1 pm2).
Proof.
  unfold pmUnion. intros ????.
  by apply pmeUnion_valid.
Qed.

Hint Resolve pmUnion_valid : core.

Lemma pmDisj_union_l :
  forall pm1 pm2 pm3,
  pmDisj pm1 pm2 -> pmDisj (pmUnion pm1 pm2) pm3 -> pmDisj pm2 pm3.
Proof.
  intros pm1 pm2 pm3 H1 H2 pid.
  apply pmeDisj_union_l with (pm1 pid); auto.
  by apply H2.
Qed.
Lemma pmDisj_union_r :
  forall pm1 pm2 pm3,
  pmDisj pm2 pm3 -> pmDisj pm1 (pmUnion pm2 pm3) -> pmDisj pm1 pm2.
Proof.
  intros pm1 pm2 pm3 H1 H2 pid.
  apply pmeDisj_union_r with (pm3 pid); auto.
  by apply H2.
Qed.

Lemma pmDisj_assoc_l :
  forall pm1 pm2 pm3,
  pmDisj pm1 pm2 ->
  pmDisj (pmUnion pm1 pm2) pm3 ->
  pmDisj pm1 (pmUnion pm2 pm3).
Proof.
  intros ???? H ?.
  apply pmeDisj_assoc_l. auto. apply H.
Qed.
Lemma pmDisj_assoc_r :
  forall pm1 pm2 pm3,
  pmDisj pm2 pm3 ->
  pmDisj pm1 (pmUnion pm2 pm3) ->
  pmDisj (pmUnion pm1 pm2) pm3.
Proof.
  intros ???? H ?.
  apply pmeDisj_assoc_r. auto. apply H.
Qed.

Lemma pmDisj_swap_r :
  forall pm1 pm2 pm3,
  pmDisj pm1 pm2 ->
  pmDisj (pmUnion pm1 pm2) pm3 ->
  pmDisj (pmUnion pm1 pm3) pm2.
Proof.
  intros pm1 pm2 pm3 H1 H2 pid.
  apply pmeDisj_swap_r; auto.
  by apply H2.
Qed.
Lemma pmDisj_swap_l :
  forall pm1 pm2 pm3,
  pmDisj pm1 pm2 ->
  pmDisj (pmUnion pm1 pm2) pm3 ->
  pmDisj (pmUnion pm2 pm3) pm1.
Proof.
  intros pm1 pm2 pm3 H1 H2 pid.
  apply pmeDisj_swap_l; auto.
  by apply H2.
Qed.

Lemma pmUnion_update :
  forall pm1 pm2 c1 c2 pid,
  pmUpdate (pmUnion pm1 pm2) pid (pmeUnion c1 c2) =
  pmUnion (pmUpdate pm1 pid c1) (pmUpdate pm2 pid c2).
Proof.
  ins. extensionality pid'.
  unfold pmUnion, pmUpdate, update. desf.
Qed.

Hint Rewrite pmUnion_update : core.

Lemma pmUnion_elem :
  forall pm1 pm2 pid,
  pmeUnion (pm1 pid) (pm2 pid) = pmUnion pm1 pm2 pid.
Proof. ins. Qed.

Lemma pmDisj_middle :
  forall pm1 pm2 pm3 pm4,
  pmDisj pm1 pm2 ->
  pmDisj pm3 pm4 ->
  pmDisj (pmUnion pm1 pm2) (pmUnion pm3 pm4) ->
  pmDisj pm2 pm3.
Proof.
  intros pm1 pm2 pm3 pm4 H1 H2 H3.
  apply pmDisj_union_l with pm1; auto.
  by apply pmDisj_union_r with pm4.
Qed.

Lemma pmDisj_compat :
  forall pm1 pm2 pm3 pm4,
  pmDisj pm1 pm3 ->
  pmDisj pm2 pm4 ->
  pmDisj (pmUnion pm1 pm3) (pmUnion pm2 pm4) ->
  pmDisj (pmUnion pm1 pm2) (pmUnion pm3 pm4).
Proof.
  intros pm1 pm2 pm3 pm4 H1 H2 H3.
  apply pmDisj_assoc_r.
  rewrite pmUnion_comm.
  apply pmDisj_assoc_l; auto.
  symmetry. by apply pmDisj_union_l in H3.
  rewrite pmUnion_comm.
  rewrite pmUnion_assoc.
  apply pmDisj_assoc_l; auto.
  by rewrite pmUnion_comm with (pm1:=pm4)(pm2:=pm2).
Qed.

Lemma pmUnion_swap_l :
  forall pm1 pm2 pm3,
  pmBisim
    (pmUnion pm1 (pmUnion pm2 pm3))
    (pmUnion pm2 (pmUnion pm1 pm3)).
Proof.
  intros ????. by apply pmeUnion_swap_l.
Qed.
Lemma pmUnion_swap_r :
  forall pm1 pm2 pm3,
  pmBisim
    (pmUnion (pmUnion pm1 pm2) pm3)
    (pmUnion (pmUnion pm1 pm3) pm2).
Proof.
  intros ????. by apply pmeUnion_swap_r.
Qed.

Hint Resolve pmUnion_swap_l pmUnion_swap_r : core.

Lemma pmUnion_compat :
  forall pm1 pm2 pm3 pm4,
  pmBisim
    (pmUnion (pmUnion pm1 pm3) (pmUnion pm2 pm4))
    (pmUnion (pmUnion pm1 pm2) (pmUnion pm3 pm4)).
Proof.
  intros pm1 pm2 pm3 pm4 pid.
  repeat rewrite <- pmUnion_elem.
  apply pmeUnion_compat.
Qed.

Hint Resolve pmUnion_compat : core.


(** *** Finiteness *)

(** Any process map [pm] is defined to be _finite_
    all occupied entries of [pm] can be mapped to a
    finite structure, in this case a list. *)

Definition pmFinite (pm : ProcMap) : Prop :=
  exists xs : list Val,
    forall pid, pm pid <> PEfree -> In pid xs.

(** Finiteness is closed under bisimilarity. *)

Lemma pmFinite_bisim :
  forall pm1 pm2,
  pmBisim pm1 pm2 -> pmFinite pm1 -> pmFinite pm2.
Proof.
  intros pm1 pm2 EQ (xs&F).
  unfold pmFinite.
  exists xs. intros pid H1.
  apply F. intro H2.
  apply pmBisim_free with (pm2:=pm2) in H2; vauto.
Qed.
Add Parametric Morphism : pmFinite
  with signature pmBisim ==> iff as pmFinite_bisim_mor.
Proof. ins. split; apply pmFinite_bisim; auto. by symmetry. Qed.

(** The identity process map is trivially finite. *)

Lemma pmFinite_iden : pmFinite pmIden.
Proof. red. exists nil. ins. Qed.

Hint Resolve pmFinite_iden : core.

(** The following property is the main property of interest:
    if a process map [pm] is finite, then one is always able
    to find an unoccupied entry in [pm]. *)

Lemma pmFinite_free :
  forall pm, pmFinite pm -> exists pid, pm pid = PEfree.
Proof.
  intros pm (xs&FIN).
  assert (H : exists pid, ~ In pid xs) by apply val_inf.
  destruct H as (pid&H).
  specialize FIN with pid.
  exists pid. tauto.
Qed.

(** Process map updates preserve finiteness. *)

Lemma pmFinite_update :
  forall pm pid c,
  pmFinite pm -> pmFinite (pmUpdate pm pid c).
Proof.
  intros pm pid c (xs&FIN).
  assert (H1 : c = PEfree \/ ~ c = PEfree) by apply classic.
  destruct H1 as [H1|H1].
  (* [c] is free *)
  - exists xs. intros pid' H2. apply FIN.
    unfold pmUpdate, update in H2. desf.
  (* [c] is not free *)
  - exists (pid :: xs). intros pid' H2.
    specialize FIN with pid'. simpls.
    unfold pmUpdate, update in H2.
    destruct (val_eq_dec pid pid') as [|H3]; vauto.
    right. by apply FIN.
Qed.

(** Below are several other interesting properties of finiteness. *)

Lemma pmFinite_union :
  forall pm1 pm2,
  pmFinite (pmUnion pm1 pm2) <-> pmFinite pm1 /\ pmFinite pm2.
Proof.
  intros pm1 pm2. split.
  (* left-to-right *)
  - intros (xs&FIN). unfold pmFinite. split.
    (* [pm1] is finite *)
    + exists xs. intros pid H1.
      apply FIN. intro H2.
      apply pmeUnion_not_free in H2; vauto.
    (* [pm2] is finite *)
    + exists xs. intros pid H1.
      apply FIN. intro H2.
      apply pmeUnion_not_free in H2; vauto.
  (* right-to-left *)
  - intro FIN.
    destruct FIN as ((xs1&FIN1)&(xs2&FIN2)).
    unfold pmFinite.
    exists (xs1 ++ xs2). intros pid H1.
    apply in_or_app. unfold pmUnion in H1.
    apply pmeUnion_not_free in H1.
    destruct H1 as [H1|H1].
    + left. by apply FIN1.
    + right. by apply FIN2.
Qed.


(** *** Projections *)

(** Any value [v] is defined to be _in the projection of [pm]_
    if [v] is in the projection of one of the entries of [pm]. *)

Definition pmProj (pm : ProcMap)(v : Val) : Prop :=
  exists pid, In v (pmeProj (pm pid)).

(** Process map projections are closed under bisimilarity. *)

Lemma pmProj_bisim :
  forall pm1 pm2 l,
  pmBisim pm1 pm2 -> pmProj pm1 l -> pmProj pm2 l.
Proof.
  intros pm1 pm2 v H1 H2. unfold pmProj in *.
  destruct H2 as (pid&H2). exists pid.
  red in H1. red in H1. by rewrite <- H1.
Qed.
Add Parametric Morphism : pmProj
  with signature pmBisim ==> eq ==> iff as pmProj_bisim_mor.
Proof. ins. split; apply pmProj_bisim; auto. by symmetry. Qed.

(** Below are several other useful properties of projections. *)

Lemma pmProj_union :
  forall pm1 pm2 v,
  pmDisj pm1 pm2 -> pmProj pm1 v -> pmProj (pmUnion pm1 pm2) v.
Proof.
  intros pm1 pm2 v H1 H2. unfold pmProj in *.
  destruct H2 as (pid&H2). exists pid.
  rewrite <- pmUnion_elem.
  apply pmeProj_union; auto.
Qed.


(** *** Coverings *)

(** Any process map [pm] is defined to _cover a heap [h]_
    if all entries of [pm] cover [h] (with respect to [pmeCovers]). *)

Definition pmCovers (pm : ProcMap)(h : Heap) : Prop :=
  forall pid, pmeCovers (pm pid) h.

(** Coverage is closed under bisimilarity. *)

Lemma pmCovers_bisim :
  forall pm1 pm2 h,
  pmBisim pm1 pm2 -> pmCovers pm1 h -> pmCovers pm2 h.
Proof.
  intros pm1 pm2 h H1 H2. unfold pmCovers in *.
  intro pid. by apply pmeCovers_bisim with (pm1 pid).
Qed.
Add Parametric Morphism : pmCovers
  with signature pmBisim ==> eq ==> iff
    as pmCovers_bisim_mor.
Proof.
  intros pm1 pm2 H1 h. split; intro H2.
  - apply pmCovers_bisim with pm1; auto.
  - apply pmCovers_bisim with pm2; auto.
    by symmetry.
Qed.

(** The identity process map covers any heap. *)

Lemma pmCovers_iden :
  forall h, pmCovers pmIden h.
Proof.
  intros h. red. intros pid. unfold pmIden.
  by apply pmeCovers_free.
Qed.

(** Below are several other useful properties of coverage. *)

Lemma pmCovers_update :
  forall pm h pid c,
    (forall l, In l (pmeProj c) -> exists v, h l = Some v) ->
  pmCovers pm h ->
  pmCovers (pmUpdate pm pid c) h.
Proof.
  intros pm h pid c H1 H2. unfold pmCovers in *.
  intro pid'. unfold pmUpdate, update. desf.
Qed.

Lemma pmCovers_hUpdate :
  forall pm h l v,
  ~ pmProj pm l -> pmCovers pm h -> pmCovers pm (hUpdate h l v).
Proof.
  intros pm h l v H1 H2.
  unfold pmCovers in *. intro pid.
  apply pmeCovers_hUpdate; vauto. intro H3.
  apply H1. red. exists pid. done.
Qed.

Lemma pmCovers_union :
  forall pm1 pm2 h,
  pmDisj pm1 pm2 ->
  pmCovers (pmUnion pm1 pm2) h ->
  pmCovers pm1 h.
Proof.
  intros pm1 pm2 h H1 H2.
  unfold pmCovers in *. intro pid.
  apply pmeCovers_union with (pm2 pid); vauto.
  specialize H2 with pid.
  by rewrite <- pmUnion_elem in H2.
Qed.

Lemma pmCovers_agrees :
  forall pm h1 h2,
    (forall l, pmProj pm l -> h1 l = h2 l) ->
  pmCovers pm h1 ->
  pmCovers pm h2.
Proof.
  intros pm h1 h2 H1 H2.
  unfold pmCovers in *. intro pid.
  apply pmeCovers_agrees with h1; vauto.
  intros l H3. apply H1. red. exists pid. done.
Qed.

Lemma pmCovers_subheap :
  forall pm h1 h2,
    (forall l v, h1 l = Some v -> h2 l = Some v) ->
  pmCovers pm h1 ->
  pmCovers pm h2.
Proof.
  intros pm h1 h2 H1 H2.
  unfold pmCovers in *. intro pid.
  apply pmeCovers_subheap with h1; vauto.
Qed.

Lemma pmCovers_occ :
  forall pm h1 h2,
    (forall l, h1 l <> None -> h2 l <> None) ->
  pmCovers pm h1 ->
  pmCovers pm h2.
Proof.
  intros pm h1 h2 H1 H2. unfold pmCovers in *.
  intro pid. apply pmeCovers_occ with h1; vauto.
Qed.


(** *** Agreement *)

(** Any two process maps are defined to _agree_
    if their entries agree pairwise with respect to [pmeAgree]. *)

Definition pmAgree : relation ProcMap :=
  pointwise_relation Val pmeAgree.

(** Process map agreement is an equivalence relation. *)

Global Instance pmAgree_refl : Reflexive pmAgree.
Proof. red. intros pm pid. auto. Qed.
Global Instance pmAgree_symm : Symmetric pmAgree.
Proof.
  red. intros pm1 pm2 H1 pid.
  symmetry. apply H1.
Qed.
Global Instance pmAgree_trans : Transitive pmAgree.
Proof.
  red. intros pm1 pm2 pm3 H1 H2 pid.
  transitivity (pm2 pid).
  - apply H1.
  - apply H2.
Qed.
Global Instance pmAgree_equiv : Equivalence pmAgree.
Proof. split; intuition. Qed.

Hint Resolve pmAgree_refl : core.

(** Bisimilarity is a subrelation of agreement. *)

Global Instance pmAgree_bisim : subrelation pmBisim pmAgree.
Proof. red. ins. by rewrite <- H. Qed.

Add Parametric Morphism : pmAgree
  with signature pmAgree ==> pmAgree ==> iff
    as pmAgree_agree_mor.
Proof.
  intros pm1 pm1' H1 pm2 pm2' H2. split; intro H3.
  - by rewrite <- H1, <- H2.
  - by rewrite H1, H2.
Qed.

(** Disjoint maps may always be replaced by agreeing ones. *)

Add Parametric Morphism : pmDisj
  with signature pmAgree ==> pmAgree ==> iff
    as pmDisj_agree_mor.
Proof.
  intros pm1 pm1' H1 pm2 pm2' H2. split; intros H3 p.
  - by rewrite <- H1, <- H2.
  - by rewrite H1, H2.
Qed.

(** Process map finiteness is closed under agreement. *)

Lemma pmFinite_agree :
  forall pm1 pm2,
  pmAgree pm1 pm2 -> pmFinite pm1 -> pmFinite pm2.
Proof.
  intros pm1 pm2 H1 H2.
  red in H2. destruct H2 as (xs&H2).
  exists xs. intros pid H3.
  apply H2. intro H4. apply H3.
  red in H1. red in H1. specialize H1 with pid.
  rewrite H4 in H1. red in H1. desf.
Qed.
Add Parametric Morphism : pmFinite
  with signature pmAgree ==> iff as pmFinite_agree_mor.
Proof. ins. split; apply pmFinite_agree; auto. by symmetry. Qed.

(** Also coverage is closed under agreement. *)

Lemma pmCovers_agree :
  forall pm1 pm2 h,
  pmAgree pm1 pm2 -> pmCovers pm1 h -> pmCovers pm2 h.
Proof. intros ????? pid. by apply pmeCovers_agree with (pm1 pid). Qed.
Add Parametric Morphism : pmCovers
  with signature pmAgree ==> eq ==> iff as pmCovers_agree_mor.
Proof. ins. split; apply pmCovers_agree; auto. by symmetry. Qed.

(** Disjoint union is closed under agreement. *)

Lemma pmAgree_union_l :
  forall pm1 pm2 pm3,
  pmAgree pm1 pm2 -> pmAgree (pmUnion pm1 pm3) (pmUnion pm2 pm3).
Proof.
  intros pm1 pm2 pm3 H1 pid.
  repeat rewrite <- pmUnion_elem.
  by apply pmeAgree_union_l.
Qed.
Lemma pmAgree_union_r :
  forall pm1 pm2 pm3,
  pmAgree pm1 pm2 -> pmAgree (pmUnion pm3 pm1) (pmUnion pm3 pm2).
Proof.
  intros pm1 pm2 pm3 H1 pid.
  repeat rewrite <- pmUnion_elem.
  by apply pmeAgree_union_r.
Qed.
Add Parametric Morphism : pmUnion
  with signature pmAgree ==> pmAgree ==> pmAgree
    as pmUnion_agree_mor.
Proof.
  intros pm1 pm1' H1 pm2 pm2' H2.
  transitivity (pmUnion pm1' pm2).
  - by apply pmAgree_union_l.
  - by apply pmAgree_union_r.
Qed.

Hint Resolve pmAgree_union_l pmAgree_union_r : core.


(** *** Weak agreement *)

(** Two process maps are defined to _agree weakly_
    if their entries pointwise weakly agree with each other,
    with respect to [pmeWeakAgree]. *)

Definition pmWeakAgree : relation ProcMap :=
  pointwise_relation Val pmeWeakAgree.

(** Weak agreement is an equivalence relation. *)

Global Instance pmWeakAgree_refl : Reflexive pmWeakAgree.
Proof. red. intros pm pid. auto. Qed.
Global Instance pmWeakAgree_symm : Symmetric pmWeakAgree.
Proof.
  red. intros pm1 pm2 H1 pid.
  symmetry. apply H1.
Qed.
Global Instance pmWeakAgree_trans : Transitive pmWeakAgree.
Proof.
  red. intros pm1 pm2 pm3 H1 H2 pid.
  transitivity (pm2 pid).
  - apply H1.
  - apply H2.
Qed.
Global Instance pmWeakAgree_equiv : Equivalence pmWeakAgree.
Proof. split; intuition. Qed.

Hint Resolve pmWeakAgree_refl : core.

(** Bisimilarity and agreement are both subrelations of weak agreement. *)

Global Instance pmWeakAgree_bisim : subrelation pmBisim pmWeakAgree.
Proof. red. intros ?? H. by rewrite <- H. Qed.
Global Instance pmWeakAgree_agree : subrelation pmAgree pmWeakAgree.
Proof. red. intros ?? H. by rewrite <- H. Qed.

(** Process map finiteness is closed under weak agreement. *)

Lemma pmFinite_weak_agree :
  forall pm1 pm2,
  pmWeakAgree pm1 pm2 -> pmFinite pm1 -> pmFinite pm2.
Proof.
  intros pm1 pm2 H1 H2.
  red in H2. destruct H2 as (xs&H2).
  exists xs. intros pid H3.
  apply H2. intro H4. apply H3.
  red in H1. red in H1. specialize H1 with pid.
  rewrite H4 in H1. red in H1. desf.
Qed.
Add Parametric Morphism : pmFinite
  with signature pmWeakAgree ==> iff
    as pmFinite_weak_agree_mor.
Proof.
  intros pm1 pm2 H1. split; intro H2.
  - apply pmFinite_weak_agree with pm1; auto.
  - apply pmFinite_weak_agree with pm2; auto.
    by symmetry.
Qed.

(** Below are other useful properties of weak agreement. *)

Lemma pmWeakAgree_union_l :
  forall pm1 pm2 pm3,
  pmWeakAgree pm1 pm2 ->
  pmWeakAgree (pmUnion pm1 pm3) (pmUnion pm2 pm3).
Proof.
  intros pm1 pm2 pm3 H1 pid.
  repeat rewrite <- pmUnion_elem.
  by apply pmeWeakAgree_union_l.
Qed.
Lemma pmWeakAgree_union_r :
  forall pm1 pm2 pm3,
  pmWeakAgree pm1 pm2 ->
  pmWeakAgree (pmUnion pm3 pm1) (pmUnion pm3 pm2).
Proof.
  intros pm1 pm2 pm3 H1 pid.
  repeat rewrite <- pmUnion_elem.
  by apply pmeWeakAgree_union_r.
Qed.

Hint Resolve pmWeakAgree_union_l pmWeakAgree_union_r : core.

End ProcMaps.
