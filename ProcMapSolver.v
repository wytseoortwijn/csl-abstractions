Require Import HahnBase.
Require Import Heaps.
Require Import Permissions.
Require Import Prelude.
Require Import Process.
Require Import ProcMap.


(** * Process map solver *)

Module Type ProcMapSolver
  (dom : Domains)
  (heaps : Heaps dom)
  (procs : Processes dom)
  (procmaps : ProcMaps dom heaps procs).

Export dom heaps procs procmaps.


(** ** Process map entries *)

(** *** Simplifier *)

(** The following tactic, [pmeclarify], is for basic simplification
    of bisimilarities of process map entries. *)

Ltac pmeclarify :=
  clarify; repeat match goal with
    | [H: pmeBisim ?x ?y |- context[?x] ] => rewrite H in *; clear H
    | [H: pmeBisim ?x ?y |- context[?y] ] => rewrite <- H in *; clear H
    | [H1: pmeBisim ?x ?y, H2: context[?x] |- _] => rewrite H1 in *; clear H1
    | [H1: pmeBisim ?x ?y, H2: context[?y] |- _] => rewrite <- H1 in *; clear H1
  end; try done.


(** **** Unit tests *)

(** Below are several unit tests for [pmeclarify]. *)

Goal forall x y z, pmeBisim x y -> pmeBisim x z.
Proof.
  intros. pmeclarify.
  match goal with |- pmeBisim y z => auto end.
Abort.
Goal forall x y z, pmeBisim x y -> pmeBisim z y.
Proof.
  intros. pmeclarify.
  match goal with |- pmeBisim z x => auto end.
Abort.
Goal forall x y z, pmeBisim x y -> pmeBisim x z -> False.
Proof.
  intros ??? H1 H2. pmeclarify.
  match goal with [H2: pmeBisim y z |- _] => auto end.
Abort.
Goal forall x y z, pmeBisim x y -> pmeBisim z y -> False.
Proof.
  intros ??? H1 H2. pmeclarify.
  match goal with [H2: pmeBisim z x |- _] => auto end.
Abort.


(** *** Solver *)

(** The [pmesolve] tactic gives some proof automation for simple
    (but often occuring) properties on validity and disjointness
    of process map entries. *)

(** This tactic is defined simply as a table of patterns,
    and matching proofs for these patterns. *)

Ltac pmesolve :=
  clarify; match goal with
    | [|- pmeValid PEfree] => apply pmeValid_free
    | [|- pmeDisj PEfree PEfree] => by apply pmeDisj_free_l, pmeValid_free
    | [|- pmeDisj ?x PEfree] => apply pmeDisj_free_l; pmesolve
    | [|- pmeDisj PEfree ?x] => apply pmeDisj_free_r; pmesolve
    | [H: pmeDisj ?x ?y |- pmeDisj ?x ?y] => exact H
    | [H: pmeDisj ?x ?y |- pmeDisj ?y ?x] => symmetry; exact H
    | [H: pmDisj ?x ?y |- pmeDisj (?x ?v) (?y ?v)] => by apply H
    | [H: pmDisj ?y ?x |- pmeDisj (?x ?v) (?y ?v)] => symmetry; by apply H
    | [H1: pmeDisj ?x ?y, H2: pmeDisj (pmeUnion ?x ?y) ?z |- pmeDisj ?y ?z] => apply pmeDisj_union_l with x; [exact H1|exact H2]
    | [H1: pmeDisj ?y ?z, H2: pmeDisj ?x (pmeUnion ?y ?z) |- pmeDisj ?x ?y] => apply pmeDisj_union_r with z; [exact H1|exact H2]
    | [H1: pmeDisj ?x ?y, H2: pmeDisj (pmeUnion ?x ?y) ?z |- pmeDisj ?x (pmeUnion ?y ?z)] => apply pmeDisj_assoc_l; [exact H1|exact H2]
    | [H1: pmeDisj ?y ?z, H2: pmeDisj ?x (pmeUnion ?y ?z) |- pmeDisj (pmeUnion ?x ?y) ?z] => apply pmeDisj_assoc_r; [exact H1|exact H2]
    | [H: pmeDisj ?x ?y |- pmeValid (pmeUnion ?x ?y)] => by apply pmeUnion_valid
    | [H: pmeDisj ?y ?x |- pmeValid (pmeUnion ?x ?y)] => symmetry in H; by apply pmeUnion_valid
    | [H: pmeDisj ?x ?y |- pmeValid ?x] => by apply pmeDisj_valid_l with y
    | [H: pmeDisj ?x ?y |- pmeValid ?y] => by apply pmeDisj_valid_r with x
    | [H: pmeDisj ?x ?y |- pmeValid ?x /\ pmeValid ?y] => by apply pmeDisj_valid
    | [H: pmeDisj ?y ?x |- pmeValid ?x /\ pmeValid ?y] => apply pmeDisj_valid; by symmetry
    | [H1: pmeDisj ?y ?x, H2: pmeDisj (pmeUnion ?x ?y) ?z |- pmeDisj ?y ?z] => apply pmeDisj_union_l with x; [symmetry; exact H1|exact H2]
    | [H1: pmeDisj ?x ?y, H2: pmeDisj (pmeUnion ?y ?x) ?z |- pmeDisj ?y ?z] => apply pmeDisj_union_l with x; [exact H1|by rewrite pmeUnion_comm]
    | [H1: pmeDisj ?x ?y, H2: pmeDisj (pmeUnion ?x ?y) ?z |- pmeDisj ?z ?y] => symmetry; apply pmeDisj_union_l with x; [exact H1|exact H2]
    | [H1: pmeDisj ?z ?y, H2: pmeDisj ?x (pmeUnion ?y ?z) |- pmeDisj ?x ?y] => apply pmeDisj_union_r with z; [symmetry; exact H1|exact H2]
    | [H1: pmeDisj ?y ?z, H2: pmeDisj ?x (pmeUnion ?z ?y) |- pmeDisj ?x ?y] => apply pmeDisj_union_r with z; [exact H1|by rewrite pmeUnion_comm]
    | [H1: pmeDisj ?y ?z, H2: pmeDisj ?x (pmeUnion ?y ?z) |- pmeDisj ?y ?x] => symmetry; by apply pmeDisj_union_r with z
    | [H1: pmeDisj ?y ?x, H2: pmeDisj (pmeUnion ?x ?y) ?z |- pmeDisj ?x (pmeUnion ?y ?z)] => apply pmeDisj_assoc_l; [symmetry; exact H1|exact H2]
    | [H1: pmeDisj ?x ?y, H2: pmeDisj (pmeUnion ?y ?x) ?z |- pmeDisj ?x (pmeUnion ?y ?z)] => apply pmeDisj_assoc_l; [exact H1|by rewrite pmeUnion_comm]
    | [H1: pmeDisj ?x ?y, H2: pmeDisj (pmeUnion ?x ?y) ?z |- pmeDisj ?x (pmeUnion ?z ?y)] => rewrite pmeUnion_comm; by apply pmeDisj_assoc_l
    | [H1: pmeDisj ?z ?y, H2: pmeDisj ?x (pmeUnion ?y ?z) |- pmeDisj (pmeUnion ?x ?y) ?z] => apply pmeDisj_assoc_r; [symmetry; exact H1|exact H2]
    | [H1: pmeDisj ?y ?z, H2: pmeDisj ?x (pmeUnion ?z ?y) |- pmeDisj (pmeUnion ?x ?y) ?z] => apply pmeDisj_assoc_r; [exact H1|by rewrite pmeUnion_comm]
    | [H1: pmeDisj ?y ?z, H2: pmeDisj ?x (pmeUnion ?y ?z) |- pmeDisj (pmeUnion ?y ?x) ?z] => rewrite pmeUnion_comm; by apply pmeDisj_assoc_r
    | [H1: pmeDisj ?x ?y, H2: pmeDisj ?z (pmeUnion ?x ?y) |- pmeDisj ?y ?z] => symmetry in H2; by apply pmeDisj_union_l with x
    | [H1: pmeDisj ?y ?x, H2: pmeDisj ?z (pmeUnion ?x ?y) |- pmeDisj ?y ?z] => symmetry in H1; symmetry in H2; by apply pmeDisj_union_l with x
    | [H1: pmeDisj ?x ?y, H2: pmeDisj ?z (pmeUnion ?y ?x) |- pmeDisj ?y ?z] => symmetry in H2; apply pmeDisj_union_l with x; auto; rewrite pmeUnion_comm; auto; fail
    | [H1: pmeDisj ?x ?y, H2: pmeDisj ?z (pmeUnion ?x ?y) |- pmeDisj ?z ?y] => symmetry; symmetry in H2; apply pmeDisj_union_l with x; auto; fail
    | [H1: pmeDisj ?y ?z, H2: pmeDisj (pmeUnion ?y ?z) ?x |- pmeDisj ?x ?y] => symmetry in H2; by apply pmeDisj_union_r with z
    | [H1: pmeDisj ?z ?y, H2: pmeDisj (pmeUnion ?y ?z) ?x |- pmeDisj ?x ?y] => symmetry in H1; symmetry in H2; by apply pmeDisj_union_r with z
    | [H1: pmeDisj ?y ?z, H2: pmeDisj (pmeUnion ?z ?y) ?x |- pmeDisj ?x ?y] => symmetry in H2; apply pmeDisj_union_r with z; auto; by rewrite pmeUnion_comm
    | [H1: pmeDisj ?y ?z, H2: pmeDisj (pmeUnion ?y ?z) ?x |- pmeDisj ?y ?x] => symmetry; symmetry in H2; by apply pmeDisj_union_r with z
    | [H1: pmeDisj ?y ?x, H2: pmeDisj (pmeUnion ?y ?x) ?z |- pmeDisj ?x (pmeUnion ?z ?y)] => rewrite pmeUnion_comm in H2; rewrite pmeUnion_comm; apply pmeDisj_assoc_l; [by symmetry|exact H2]
    | [H1: pmeDisj ?z ?y, H2: pmeDisj ?x (pmeUnion ?z ?y) |- pmeDisj (pmeUnion ?y ?x) ?z] => rewrite pmeUnion_comm in H2; rewrite pmeUnion_comm; apply pmeDisj_assoc_r; [by symmetry|exact H2]
    | [H1: pmeDisj ?x ?y, H2: pmeDisj ?z (pmeUnion ?x ?y) |- pmeDisj ?x (pmeUnion ?y ?z)] => symmetry in H2; by apply pmeDisj_assoc_l
    | [H1: pmeDisj ?y ?x, H2: pmeDisj ?z (pmeUnion ?x ?y) |- pmeDisj ?x (pmeUnion ?y ?z)] => symmetry in H1; symmetry in H2; by apply pmeDisj_assoc_l
    | [H1: pmeDisj ?x ?y, H2: pmeDisj ?z (pmeUnion ?y ?x) |- pmeDisj ?x (pmeUnion ?y ?z)] => apply pmeDisj_assoc_l; [exact H1|symmetry; by rewrite pmeUnion_comm]
    | [H1: pmeDisj ?x ?y, H2: pmeDisj ?z (pmeUnion ?x ?y) |- pmeDisj ?x (pmeUnion ?z ?y)] => rewrite pmeUnion_comm; apply pmeDisj_assoc_l; [exact H1|by symmetry]
    | [H1: pmeDisj ?y ?x, H2: pmeDisj ?z (pmeUnion ?y ?x) |- pmeDisj ?x (pmeUnion ?y ?z)] => apply pmeDisj_assoc_l; [by symmetry|]; symmetry; rewrite pmeUnion_comm; auto; by symmetry
    | [H1: pmeDisj ?y ?x, H2: pmeDisj ?z (pmeUnion ?y ?x) |- pmeDisj ?x (pmeUnion ?z ?y)] => rewrite pmeUnion_comm in H2; rewrite pmeUnion_comm; apply pmeDisj_assoc_l; auto; by symmetry
    | [H1: pmeDisj ?y ?x, H2: pmeDisj ?z (pmeUnion ?x ?y) |- pmeDisj (pmeUnion ?y ?z) ?x] => symmetry; apply pmeDisj_assoc_l; by symmetry
    | [H1: pmeDisj ?x ?y, H2: pmeDisj ?z (pmeUnion ?x ?y) |- pmeDisj (pmeUnion ?z ?y) ?x] => apply pmeDisj_assoc_r; [by symmetry|by rewrite pmeUnion_comm]
    | [|- pmeBisim (pmeUnion (pmeUnion ?x ?y) ?z) (pmeUnion ?x (pmeUnion ?y ?z))] => by apply pmeUnion_assoc
    | [|- pmeBisim (pmeUnion ?x (pmeUnion ?y ?z)) (pmeUnion (pmeUnion ?x ?y) ?z)] => symmetry; by apply pmeUnion_assoc
    | [|- pmeBisim (pmeUnion ?x ?y) (pmeUnion ?y ?x)] => by apply pmeUnion_comm
    | [|- pmeUnion ?x PEfree = ?x] => by apply pmeUnion_free_l
    | [|- pmeUnion PEfree ?x = ?x] => by apply pmeUnion_free_r
    | [|- ?x = pmeUnion ?x PEfree] => symmetry; by apply pmeUnion_free_l
    | [|- ?x = pmeUnion PEfree ?x] => symmetry; by apply pmeUnion_free_r
    | [|- pmeBisim (pmeUnion ?x PEfree) ?x] => by rewrite pmeUnion_free_l
    | [|- pmeBisim (pmeUnion PEfree ?x) ?x] => by rewrite pmeUnion_free_r
    | [|- pmeBisim ?x (pmeUnion ?x PEfree)] => symmetry; by rewrite pmeUnion_free_l
    | [|- pmeBisim ?x (pmeUnion PEfree ?x)] => symmetry; by rewrite pmeUnion_free_r
    | [|- pmeUnion ?x (pmIden _) = ?x] => unfold pmIden; by apply pmeUnion_free_l
    | [|- pmeUnion (pmIden _) ?x = ?x] => unfold pmIden; by apply pmeUnion_free_r
    | [|- ?x = pmeUnion ?x (pmIden _)] => unfold pmIden; symmetry; by apply pmeUnion_free_l
    | [|- ?x = pmeUnion (pmIden _) ?x] => unfold pmIden; symmetry; by apply pmeUnion_free_r
    | [|- pmeBisim (pmeUnion ?x (pmIden _)) ?x] => unfold pmIden; by rewrite pmeUnion_free_l
    | [|- pmeBisim (pmeUnion (pmIden _) ?x) ?x] => unfold pmIden; by rewrite pmeUnion_free_r
    | [|- pmeBisim ?x (pmeUnion ?x (pmIden _))] => unfold pmIden; symmetry; by rewrite pmeUnion_free_l
    | [|- pmeBisim ?x (pmeUnion (pmIden _) ?x)] => unfold pmIden; symmetry; by rewrite pmeUnion_free_r
    | [|- pmeBisim (pmeUnion ?x (pmeUnion ?y ?z)) (pmeUnion ?y (pmeUnion ?x ?z))] => by apply pmeUnion_swap_l
    | [|- pmeBisim (pmeUnion (pmeUnion ?x ?y) ?z) (pmeUnion (pmeUnion ?x ?z) ?y)] => by apply pmeUnion_swap_r
    | [|- pmeBisim (pmeUnion (pmeUnion ?x ?z) (pmeUnion ?y ?w)) (pmeUnion (pmeUnion ?x ?y) (pmeUnion ?z ?w))] => by apply pmeUnion_compat
    | _ => fail
  end.


(** **** Unit tests *)

(** Below several unit tests are given for [pmesolve]. *)

Goal pmeValid PEfree.
Proof. pmesolve. Qed.
Goal pmeDisj PEfree PEfree.
Proof. pmesolve. Qed.
Goal forall x, pmeValid x -> pmeDisj x PEfree.
Proof. intros. pmesolve. Qed.
Goal forall x, pmeValid x -> pmeDisj PEfree x.
Proof. intros. pmesolve. Qed.
Goal forall x y, pmeDisj x y -> pmeDisj x y.
Proof. intros. pmesolve. Qed.
Goal forall x y, pmeDisj x y -> pmeDisj y x.
Proof. intros. pmesolve. Qed.
Goal forall x y z, pmeDisj x y -> pmeDisj (pmeUnion x y) z -> pmeDisj y z.
Proof. intros. pmesolve. Qed.
Goal forall x y z, pmeDisj y z -> pmeDisj x (pmeUnion y z) -> pmeDisj x y.
Proof. intros. pmesolve. Qed.
Goal forall x y z, pmeDisj x y -> pmeDisj (pmeUnion x y) z -> pmeDisj x (pmeUnion y z).
Proof. intros. pmesolve. Qed.
Goal forall x y z, pmeDisj y z -> pmeDisj x (pmeUnion y z) -> pmeDisj (pmeUnion x y) z.
Proof. intros. pmesolve. Qed.
Goal forall x y, pmeDisj x y -> pmeValid (pmeUnion x y).
Proof. intros. pmesolve. Qed.
Goal forall x y, pmeDisj y x -> pmeValid (pmeUnion x y).
Proof. intros. pmesolve. Qed.
Goal forall x y, pmeDisj x y -> pmeValid x.
Proof. intros. pmesolve. Qed.
Goal forall x y, pmeDisj x y -> pmeValid y.
Proof. intros. pmesolve. Qed.
Goal forall x y, pmeDisj x y -> pmeValid x /\ pmeValid y.
Proof. intros. pmesolve. Qed.
Goal forall x y, pmeDisj y x -> pmeValid x /\ pmeValid y.
Proof. intros. pmesolve. Qed.
Goal forall x y z, pmeDisj y x -> pmeDisj (pmeUnion x y) z -> pmeDisj y z.
Proof. intros. pmesolve. Qed.
Goal forall x y z, pmeDisj x y -> pmeDisj (pmeUnion y x) z -> pmeDisj y z.
Proof. intros. pmesolve. Qed.
Goal forall x y z, pmeDisj x y -> pmeDisj (pmeUnion x y) z -> pmeDisj z y.
Proof. intros. pmesolve. Qed.
Goal forall x y z, pmeDisj z y -> pmeDisj x (pmeUnion y z) -> pmeDisj x y.
Proof. intros. pmesolve. Qed.
Goal forall x y z, pmeDisj y z -> pmeDisj x (pmeUnion z y) -> pmeDisj x y.
Proof. intros. pmesolve. Qed.
Goal forall x y z, pmeDisj y z -> pmeDisj x (pmeUnion y z) -> pmeDisj y x.
Proof. intros. pmesolve. Qed.
Goal forall x y z, pmeDisj y x -> pmeDisj (pmeUnion x y) z -> pmeDisj x (pmeUnion y z).
Proof. intros. pmesolve. Qed.
Goal forall x y z, pmeDisj x y -> pmeDisj (pmeUnion y x) z -> pmeDisj x (pmeUnion y z).
Proof. intros. pmesolve. Qed.
Goal forall x y z, pmeDisj x y -> pmeDisj (pmeUnion x y) z -> pmeDisj x (pmeUnion z y).
Proof. intros. pmesolve. Qed.
Goal forall x y z, pmeDisj z y -> pmeDisj x (pmeUnion y z) -> pmeDisj (pmeUnion x y) z.
Proof. intros. pmesolve. Qed.
Goal forall x y z, pmeDisj y z -> pmeDisj x (pmeUnion z y) -> pmeDisj (pmeUnion x y) z.
Proof. intros. pmesolve. Qed.
Goal forall x y z, pmeDisj y z -> pmeDisj x (pmeUnion y z) -> pmeDisj (pmeUnion y x) z.
Proof. intros. pmesolve. Qed.
Goal forall x y z, pmeDisj x y -> pmeDisj z (pmeUnion x y) -> pmeDisj y z.
Proof. intros. pmesolve. Qed.
Goal forall x y z, pmeDisj y x -> pmeDisj z (pmeUnion x y) -> pmeDisj y z.
Proof. intros. pmesolve. Qed.
Goal forall x y z, pmeDisj x y -> pmeDisj z (pmeUnion y x) -> pmeDisj y z.
Proof. intros. pmesolve. Qed.
Goal forall x y z, pmeDisj x y -> pmeDisj z (pmeUnion x y) -> pmeDisj z y.
Proof. intros. pmesolve. Qed.
Goal forall x y z, pmeDisj y z -> pmeDisj (pmeUnion y z) x -> pmeDisj x y.
Proof. intros. pmesolve. Qed.
Goal forall x y z, pmeDisj z y -> pmeDisj (pmeUnion y z) x -> pmeDisj x y.
Proof. intros. pmesolve. Qed.
Goal forall x y z, pmeDisj y z -> pmeDisj (pmeUnion z y) x -> pmeDisj x y.
Proof. intros. pmesolve. Qed.
Goal forall x y z, pmeDisj y z -> pmeDisj (pmeUnion y z) x -> pmeDisj y x.
Proof. intros. pmesolve. Qed.
Goal forall x y z, pmeDisj y x -> pmeDisj (pmeUnion y x) z -> pmeDisj x (pmeUnion z y).
Proof. intros. pmesolve. Qed.
Goal forall x y z, pmeDisj z y -> pmeDisj x (pmeUnion z y) -> pmeDisj (pmeUnion y x) z.
Proof. intros. pmesolve. Qed.
Goal forall x y z, pmeDisj x y -> pmeDisj z (pmeUnion x y) -> pmeDisj x (pmeUnion y z).
Proof. intros. pmesolve. Qed.
Goal forall x y z, pmeDisj z y -> pmeDisj x (pmeUnion z y) -> pmeDisj (pmeUnion y x) z.
Proof. intros. pmesolve. Qed.
Goal forall x y z, pmeDisj y x -> pmeDisj z (pmeUnion x y) -> pmeDisj x (pmeUnion y z).
Proof. intros. pmesolve. Qed.
Goal forall x y z, pmeDisj x y -> pmeDisj z (pmeUnion y x) -> pmeDisj x (pmeUnion y z).
Proof. intros. pmesolve. Qed.
Goal forall x y z, pmeDisj x y -> pmeDisj z (pmeUnion x y) -> pmeDisj x (pmeUnion z y).
Proof. intros. pmesolve. Qed.
Goal forall x y z, pmeDisj y x -> pmeDisj z (pmeUnion y x) -> pmeDisj x (pmeUnion y z).
Proof. intros. pmesolve. Qed.
Goal forall x y z, pmeDisj y x -> pmeDisj z (pmeUnion y x) -> pmeDisj x (pmeUnion z y).
Proof. intros. pmesolve. Qed.
Goal forall x y z, pmeDisj x y -> pmeDisj z (pmeUnion x y) -> pmeDisj (pmeUnion y z) x.
Proof. intros. pmesolve. Qed.
Goal forall x y z, pmeDisj y x -> pmeDisj z (pmeUnion x y) -> pmeDisj (pmeUnion y z) x.
Proof. intros. pmesolve. Qed.
Goal forall x y z, pmeDisj x y -> pmeDisj z (pmeUnion x y) -> pmeDisj (pmeUnion z y) x.
Proof. intros. pmesolve. Qed.
Goal forall x y z, pmeDisj y x -> pmeDisj z (pmeUnion y x) -> pmeDisj (pmeUnion y z) x.
Proof. intros. pmesolve. Qed.
Goal forall x y z, pmeDisj y x -> pmeDisj z (pmeUnion y x) -> pmeDisj (pmeUnion z y) x.
Proof. intros. pmesolve. Qed.
Goal forall x y z, pmeBisim (pmeUnion x (pmeUnion y z)) (pmeUnion (pmeUnion x y) z).
Proof. intros. pmesolve. Qed.
Goal forall x y z, pmeBisim (pmeUnion (pmeUnion x y) z) (pmeUnion x (pmeUnion y z)).
Proof. intros. pmesolve. Qed.
Goal forall x y, pmeBisim (pmeUnion x y) (pmeUnion y x).
Proof. intros. pmesolve. Qed.
Goal forall x, pmeUnion x PEfree = x.
Proof. intros. pmesolve. Qed.
Goal forall x, pmeUnion PEfree x = x.
Proof. intros. pmesolve. Qed.
Goal forall x, pmeBisim (pmeUnion x PEfree) x.
Proof. intros. pmesolve. Qed.
Goal forall x, pmeBisim (pmeUnion PEfree x) x.
Proof. intros. pmesolve. Qed.
Goal forall x, x = pmeUnion x PEfree.
Proof. intros. pmesolve. Qed.
Goal forall x, x = pmeUnion PEfree x.
Proof. intros. pmesolve. Qed.
Goal forall x, pmeBisim x (pmeUnion x PEfree).
Proof. intros. pmesolve. Qed.
Goal forall x, pmeBisim x (pmeUnion PEfree x).
Proof. intros. pmesolve. Qed.
Goal forall x, pmeBisim (pmeUnion x PEfree) x.
Proof. intros. pmesolve. Qed.
Goal forall x, pmeBisim (pmeUnion PEfree x) x.
Proof. intros. pmesolve. Qed.
Goal forall x v, pmeUnion x (pmIden v) = x.
Proof. intros. pmesolve. Qed.
Goal forall x v, pmeUnion (pmIden v) x = x.
Proof. intros. pmesolve. Qed.
Goal forall x v, x = pmeUnion x (pmIden v).
Proof. intros. pmesolve. Qed.
Goal forall x v, x = pmeUnion (pmIden v) x.
Proof. intros. pmesolve. Qed.
Goal forall x v, pmeBisim (pmeUnion x (pmIden v)) x.
Proof. intros. pmesolve. Qed.
Goal forall x v, pmeBisim (pmeUnion (pmIden v) x) x.
Proof. intros. pmesolve. Qed.
Goal forall x v, pmeBisim x (pmeUnion x (pmIden v)).
Proof. intros. pmesolve. Qed.
Goal forall x v, pmeBisim x (pmeUnion (pmIden v) x).
Proof. intros. pmesolve. Qed.
Goal forall x y z, pmeBisim (pmeUnion x (pmeUnion y z)) (pmeUnion y (pmeUnion x z)).
Proof. intros. pmesolve. Qed.
Goal forall x y z, pmeBisim (pmeUnion (pmeUnion x y) z) (pmeUnion (pmeUnion x z) y).
Proof. intros. pmesolve. Qed.
Goal forall x y z w, pmeBisim (pmeUnion (pmeUnion x z) (pmeUnion y w)) (pmeUnion (pmeUnion x y) (pmeUnion z w)).
Proof. intros. pmesolve. Qed.
Goal forall x y z w, pmeBisim (pmeUnion (pmeUnion x y) (pmeUnion z w)) (pmeUnion (pmeUnion x z) (pmeUnion y w)).
Proof. intros. pmesolve. Qed.
Goal forall x y v, pmDisj x y -> pmeDisj (x v) (y v).
Proof. intros. pmesolve. Qed.
Goal forall x y v, pmDisj y x -> pmeDisj (x v) (y v).
Proof. intros. pmesolve. Qed.


(** ** Process maps *)

(** *** Simplifier *)

(** The following tactic, [pmeclarify], is for basic simplification
    of bisimilarities of process maps. *)

Ltac pmclarify :=
  clarify; repeat match goal with
    | [H: pmBisim ?x ?y |- context[?x] ] => rewrite H in *; clear H
    | [H: pmBisim ?x ?y |- context[?y] ] => rewrite <- H in *; clear H
    | [H1: pmBisim ?x ?y, H2: context[?x] |- _] => rewrite H1 in *; clear H1
    | [H1: pmBisim ?x ?y, H2: context[?y] |- _] => rewrite <- H1 in *; clear H1
  end; try done.


(** **** Unit tests *)

(** Below are several unit tests for [pmeclarify]. *)

Goal forall x y z, pmBisim x y -> pmBisim x z.
Proof.
  intros. pmclarify.
  match goal with |- pmBisim y z => auto end.
Abort.
Goal forall x y z, pmBisim x y -> pmBisim z y.
Proof.
  intros. pmclarify.
  match goal with |- pmBisim z x => auto end.
Abort.
Goal forall x y z, pmBisim x y -> pmBisim x z -> False.
Proof.
  intros ??? H1 H2. pmclarify.
  match goal with [H2: pmBisim y z |- _] => auto end.
Abort.
Goal forall x y z, pmBisim x y -> pmBisim z y -> False.
Proof.
  intros ??? H1 H2. pmclarify.
  match goal with [H2: pmBisim z x |- _] => auto end.
Abort.


(** *** Solver *)

(** The [pmsolve] tactic gives some proof automation for simple
    (but often occuring)  properties on validity and disjointness
    of process maps. *)

(** This tactic is defined simply as a table of patterns,
    and matching proofs for these patterns. *)

Ltac pmsolve :=
  clarify; match goal with
    | [|- pmValid pmIden] => apply pmValid_iden
    | [|- pmDisj pmIden pmIden] => by apply pmDisj_iden_l, pmValid_iden
    | [|- pmDisj ?x pmIden] => apply pmDisj_iden_l; pmsolve
    | [|- pmDisj pmIden ?x] => apply pmDisj_iden_r; pmsolve
    | [H: pmDisj ?x ?y |- pmDisj ?x ?y] => exact H
    | [H: pmDisj ?x ?y |- pmDisj ?y ?x] => symmetry; exact H
    | [H1: pmDisj ?x ?y, H2: pmDisj (pmUnion ?x ?y) ?z |- pmDisj ?y ?z] => apply pmDisj_union_l with x; [exact H1|exact H2]
    | [H1: pmDisj ?y ?z, H2: pmDisj ?x (pmUnion ?y ?z) |- pmDisj ?x ?y] => apply pmDisj_union_r with z; [exact H1|exact H2]
    | [H1: pmDisj ?x ?y, H2: pmDisj (pmUnion ?x ?y) ?z |- pmDisj ?x (pmUnion ?y ?z)] => apply pmDisj_assoc_l; [exact H1|exact H2]
    | [H1: pmDisj ?y ?z, H2: pmDisj ?x (pmUnion ?y ?z) |- pmDisj (pmUnion ?x ?y) ?z] => apply pmDisj_assoc_r; [exact H1|exact H2]
    | [H: pmDisj ?x ?y |- pmValid (pmUnion ?x ?y)] => by apply pmUnion_valid
    | [H: pmDisj ?y ?x |- pmValid (pmUnion ?x ?y)] => symmetry in H; by apply pmUnion_valid
    | [H: pmDisj ?x ?y |- pmValid ?x] => by apply pmDisj_valid_l with y
    | [H: pmDisj ?x ?y |- pmValid ?y] => by apply pmDisj_valid_r with x
    | [H: pmDisj ?x ?y |- pmValid ?x /\ pmValid ?y] => by apply pmDisj_valid
    | [H: pmDisj ?y ?x |- pmValid ?x /\ pmValid ?y] => apply pmDisj_valid; by symmetry
    | [H1: pmDisj ?y ?x, H2: pmDisj (pmUnion ?x ?y) ?z |- pmDisj ?y ?z] => apply pmDisj_union_l with x; [symmetry; exact H1|exact H2]
    | [H1: pmDisj ?x ?y, H2: pmDisj (pmUnion ?y ?x) ?z |- pmDisj ?y ?z] => apply pmDisj_union_l with x; [exact H1|by rewrite pmUnion_comm]
    | [H1: pmDisj ?x ?y, H2: pmDisj (pmUnion ?x ?y) ?z |- pmDisj ?z ?y] => symmetry; apply pmDisj_union_l with x; [exact H1|exact H2]
    | [H1: pmDisj ?z ?y, H2: pmDisj ?x (pmUnion ?y ?z) |- pmDisj ?x ?y] => apply pmDisj_union_r with z; [symmetry; exact H1|exact H2]
    | [H1: pmDisj ?y ?z, H2: pmDisj ?x (pmUnion ?z ?y) |- pmDisj ?x ?y] => apply pmDisj_union_r with z; [exact H1|by rewrite pmUnion_comm]
    | [H1: pmDisj ?y ?z, H2: pmDisj ?x (pmUnion ?y ?z) |- pmDisj ?y ?x] => symmetry; by apply pmDisj_union_r with z
    | [H1: pmDisj ?y ?x, H2: pmDisj (pmUnion ?x ?y) ?z |- pmDisj ?x (pmUnion ?y ?z)] => apply pmDisj_assoc_l; [symmetry; exact H1|exact H2]
    | [H1: pmDisj ?x ?y, H2: pmDisj (pmUnion ?y ?x) ?z |- pmDisj ?x (pmUnion ?y ?z)] => apply pmDisj_assoc_l; [exact H1|by rewrite pmUnion_comm]
    | [H1: pmDisj ?x ?y, H2: pmDisj (pmUnion ?x ?y) ?z |- pmDisj ?x (pmUnion ?z ?y)] => rewrite pmUnion_comm; by apply pmDisj_assoc_l
    | [H1: pmDisj ?z ?y, H2: pmDisj ?x (pmUnion ?y ?z) |- pmDisj (pmUnion ?x ?y) ?z] => apply pmDisj_assoc_r; [symmetry; exact H1|exact H2]
    | [H1: pmDisj ?y ?z, H2: pmDisj ?x (pmUnion ?z ?y) |- pmDisj (pmUnion ?x ?y) ?z] => apply pmDisj_assoc_r; [exact H1|by rewrite pmUnion_comm]
    | [H1: pmDisj ?y ?z, H2: pmDisj ?x (pmUnion ?y ?z) |- pmDisj (pmUnion ?y ?x) ?z] => rewrite pmUnion_comm; by apply pmDisj_assoc_r
    | [H1: pmDisj ?x ?y, H2: pmDisj ?z (pmUnion ?x ?y) |- pmDisj ?y ?z] => symmetry in H2; by apply pmDisj_union_l with x
    | [H1: pmDisj ?y ?x, H2: pmDisj ?z (pmUnion ?x ?y) |- pmDisj ?y ?z] => symmetry in H1; symmetry in H2; by apply pmDisj_union_l with x
    | [H1: pmDisj ?x ?y, H2: pmDisj ?z (pmUnion ?y ?x) |- pmDisj ?y ?z] => symmetry in H2; apply pmDisj_union_l with x; auto; rewrite pmUnion_comm; auto; fail
    | [H1: pmDisj ?x ?y, H2: pmDisj ?z (pmUnion ?x ?y) |- pmDisj ?z ?y] => symmetry; symmetry in H2; apply pmDisj_union_l with x; auto; fail
    | [H1: pmDisj ?y ?z, H2: pmDisj (pmUnion ?y ?z) ?x |- pmDisj ?x ?y] => symmetry in H2; by apply pmDisj_union_r with z
    | [H1: pmDisj ?z ?y, H2: pmDisj (pmUnion ?y ?z) ?x |- pmDisj ?x ?y] => symmetry in H1; symmetry in H2; by apply pmDisj_union_r with z
    | [H1: pmDisj ?y ?z, H2: pmDisj (pmUnion ?z ?y) ?x |- pmDisj ?x ?y] => symmetry in H2; apply pmDisj_union_r with z; auto; by rewrite pmUnion_comm
    | [H1: pmDisj ?y ?z, H2: pmDisj (pmUnion ?y ?z) ?x |- pmDisj ?y ?x] => symmetry; symmetry in H2; by apply pmDisj_union_r with z
    | [H1: pmDisj ?y ?x, H2: pmDisj (pmUnion ?y ?x) ?z |- pmDisj ?x (pmUnion ?z ?y)] => rewrite pmUnion_comm in H2; rewrite pmUnion_comm; apply pmDisj_assoc_l; [by symmetry|exact H2]
    | [H1: pmDisj ?z ?y, H2: pmDisj ?x (pmUnion ?z ?y) |- pmDisj (pmUnion ?y ?x) ?z] => rewrite pmUnion_comm in H2; rewrite pmUnion_comm; apply pmDisj_assoc_r; [by symmetry|exact H2]
    | [H1: pmDisj ?x ?y, H2: pmDisj ?z (pmUnion ?x ?y) |- pmDisj ?x (pmUnion ?y ?z)] => symmetry in H2; by apply pmDisj_assoc_l
    | [H1: pmDisj ?y ?x, H2: pmDisj ?z (pmUnion ?x ?y) |- pmDisj ?x (pmUnion ?y ?z)] => symmetry in H1; symmetry in H2; by apply pmDisj_assoc_l
    | [H1: pmDisj ?x ?y, H2: pmDisj ?z (pmUnion ?y ?x) |- pmDisj ?x (pmUnion ?y ?z)] => apply pmDisj_assoc_l; [exact H1|symmetry; by rewrite pmUnion_comm]
    | [H1: pmDisj ?x ?y, H2: pmDisj ?z (pmUnion ?x ?y) |- pmDisj ?x (pmUnion ?z ?y)] => rewrite pmUnion_comm; apply pmDisj_assoc_l; [exact H1|by symmetry]
    | [H1: pmDisj ?y ?x, H2: pmDisj ?z (pmUnion ?y ?x) |- pmDisj ?x (pmUnion ?y ?z)] => apply pmDisj_assoc_l; [by symmetry|]; symmetry; rewrite pmUnion_comm; auto; by symmetry
    | [H1: pmDisj ?y ?x, H2: pmDisj ?z (pmUnion ?y ?x) |- pmDisj ?x (pmUnion ?z ?y)] => rewrite pmUnion_comm in H2; rewrite pmUnion_comm; apply pmDisj_assoc_l; auto; by symmetry
    | [H1: pmDisj ?y ?x, H2: pmDisj ?z (pmUnion ?x ?y) |- pmDisj (pmUnion ?y ?z) ?x] => symmetry; apply pmDisj_assoc_l; by symmetry
    | [H1: pmDisj ?x ?y, H2: pmDisj ?z (pmUnion ?x ?y) |- pmDisj (pmUnion ?z ?y) ?x] => apply pmDisj_assoc_r; [by symmetry|by rewrite pmUnion_comm]
    | [H: pmDisj ?x ?y |- pmeDisj (?x ?v) (?y ?v)] => by apply H
    | [H: pmDisj ?y ?x |- pmeDisj (?x ?v) (?y ?v)] => symmetry; by apply H
    | [|- pmDisj (pmUpdate _ ?l _) (pmUpdate _ ?l _)] => apply pmDisj_upd; [pmesolve|pmsolve]
    | [|- pmBisim (pmUnion (pmUnion ?x ?y) ?z) (pmUnion ?x (pmUnion ?y ?z))] => by apply pmUnion_assoc
    | [|- pmBisim (pmUnion ?x (pmUnion ?y ?z)) (pmUnion (pmUnion ?x ?y) ?z)] => symmetry; by apply pmUnion_assoc
    | [|- pmBisim (pmUnion ?x ?y) (pmUnion ?y ?x)] => by apply pmUnion_comm
    | [|- pmUnion ?x pmIden = ?x] => by apply pmUnion_iden_l
    | [|- pmUnion pmIden ?x = ?x] => by apply pmUnion_iden_r
    | [|- pmBisim (pmUnion ?x pmIden) ?x] => by rewrite pmUnion_iden_l
    | [|- pmBisim (pmUnion pmIden ?x) ?x] => by rewrite pmUnion_iden_r
    | [|- pmBisim (pmUnion ?x (pmUnion ?y ?z)) (pmUnion ?y (pmUnion ?x ?z))] => by apply pmUnion_swap_l
    | [|- pmBisim (pmUnion (pmUnion ?x ?y) ?z) (pmUnion (pmUnion ?x ?z) ?y)] => by apply pmUnion_swap_r
    | [|- pmBisim (pmUnion (pmUnion ?x ?z) (pmUnion ?y ?w)) (pmUnion (pmUnion ?x ?y) (pmUnion ?z ?w))] => by apply pmUnion_compat
    | [|- pmUnion ?x ?y ?v = pmeUnion (?x ?v) (?y ?v)] => by apply pmUnion_elem
    | [|- pmeUnion (?x ?v) (?y ?v) = pmUnion ?x ?y ?v] => by apply pmUnion_elem
    | [|- pmeBisim (pmUnion ?x ?y ?v) (pmeUnion (?x ?v) (?y ?v))] => by rewrite pmUnion_elem
    | [|- pmeBisim (pmeUnion (?x ?v) (?y ?v)) (pmUnion ?x ?y ?v)] => by rewrite pmUnion_elem
    | _ => fail
  end.


(** **** Unit tests *)

(** Below several unit tests are given for [pmesolve]. *)

Goal pmValid pmIden.
Proof. pmsolve. Qed.
Goal pmDisj pmIden pmIden.
Proof. pmsolve. Qed.
Goal forall x, pmValid x -> pmDisj x pmIden.
Proof. intros. pmsolve. Qed.
Goal forall x, pmValid x -> pmDisj pmIden x.
Proof. intros. pmsolve. Qed.
Goal forall x y, pmDisj x y -> pmDisj x y.
Proof. intros. pmsolve. Qed.
Goal forall x y, pmDisj x y -> pmDisj y x.
Proof. intros. pmsolve. Qed.
Goal forall x y z, pmDisj x y -> pmDisj (pmUnion x y) z -> pmDisj y z.
Proof. intros. pmsolve. Qed.
Goal forall x y z, pmDisj y z -> pmDisj x (pmUnion y z) -> pmDisj x y.
Proof. intros. pmsolve. Qed.
Goal forall x y z, pmDisj x y -> pmDisj (pmUnion x y) z -> pmDisj x (pmUnion y z).
Proof. intros. pmsolve. Qed.
Goal forall x y z, pmDisj y z -> pmDisj x (pmUnion y z) -> pmDisj (pmUnion x y) z.
Proof. intros. pmsolve. Qed.
Goal forall x y, pmDisj x y -> pmValid (pmUnion x y).
Proof. intros. pmsolve. Qed.
Goal forall x y, pmDisj y x -> pmValid (pmUnion x y).
Proof. intros. pmsolve. Qed.
Goal forall x y, pmDisj x y -> pmValid x.
Proof. intros. pmsolve. Qed.
Goal forall x y, pmDisj x y -> pmValid y.
Proof. intros. pmsolve. Qed.
Goal forall x y, pmDisj x y -> pmValid x /\ pmValid y.
Proof. intros. pmsolve. Qed.
Goal forall x y, pmDisj y x -> pmValid x /\ pmValid y.
Proof. intros. pmsolve. Qed.
Goal forall x y z, pmDisj y x -> pmDisj (pmUnion x y) z -> pmDisj y z.
Proof. intros. pmsolve. Qed.
Goal forall x y z, pmDisj x y -> pmDisj (pmUnion y x) z -> pmDisj y z.
Proof. intros. pmsolve. Qed.
Goal forall x y z, pmDisj x y -> pmDisj (pmUnion x y) z -> pmDisj z y.
Proof. intros. pmsolve. Qed.
Goal forall x y z, pmDisj z y -> pmDisj x (pmUnion y z) -> pmDisj x y.
Proof. intros. pmsolve. Qed.
Goal forall x y z, pmDisj y z -> pmDisj x (pmUnion z y) -> pmDisj x y.
Proof. intros. pmsolve. Qed.
Goal forall x y z, pmDisj y z -> pmDisj x (pmUnion y z) -> pmDisj y x.
Proof. intros. pmsolve. Qed.
Goal forall x y z, pmDisj y x -> pmDisj (pmUnion x y) z -> pmDisj x (pmUnion y z).
Proof. intros. pmsolve. Qed.
Goal forall x y z, pmDisj x y -> pmDisj (pmUnion y x) z -> pmDisj x (pmUnion y z).
Proof. intros. pmsolve. Qed.
Goal forall x y z, pmDisj x y -> pmDisj (pmUnion x y) z -> pmDisj x (pmUnion z y).
Proof. intros. pmsolve. Qed.
Goal forall x y z, pmDisj z y -> pmDisj x (pmUnion y z) -> pmDisj (pmUnion x y) z.
Proof. intros. pmsolve. Qed.
Goal forall x y z, pmDisj y z -> pmDisj x (pmUnion z y) -> pmDisj (pmUnion x y) z.
Proof. intros. pmsolve. Qed.
Goal forall x y z, pmDisj y z -> pmDisj x (pmUnion y z) -> pmDisj (pmUnion y x) z.
Proof. intros. pmsolve. Qed.
Goal forall x y z, pmDisj x y -> pmDisj z (pmUnion x y) -> pmDisj y z.
Proof. intros. pmsolve. Qed.
Goal forall x y z, pmDisj y x -> pmDisj z (pmUnion x y) -> pmDisj y z.
Proof. intros. pmsolve. Qed.
Goal forall x y z, pmDisj x y -> pmDisj z (pmUnion y x) -> pmDisj y z.
Proof. intros. pmsolve. Qed.
Goal forall x y z, pmDisj x y -> pmDisj z (pmUnion x y) -> pmDisj z y.
Proof. intros. pmsolve. Qed.
Goal forall x y z, pmDisj y z -> pmDisj (pmUnion y z) x -> pmDisj x y.
Proof. intros. pmsolve. Qed.
Goal forall x y z, pmDisj z y -> pmDisj (pmUnion y z) x -> pmDisj x y.
Proof. intros. pmsolve. Qed.
Goal forall x y z, pmDisj y z -> pmDisj (pmUnion z y) x -> pmDisj x y.
Proof. intros. pmsolve. Qed.
Goal forall x y z, pmDisj y z -> pmDisj (pmUnion y z) x -> pmDisj y x.
Proof. intros. pmsolve. Qed.
Goal forall x y z, pmDisj y x -> pmDisj (pmUnion y x) z -> pmDisj x (pmUnion z y).
Proof. intros. pmsolve. Qed.
Goal forall x y z, pmDisj z y -> pmDisj x (pmUnion z y) -> pmDisj (pmUnion y x) z.
Proof. intros. pmsolve. Qed.
Goal forall x y z, pmDisj x y -> pmDisj z (pmUnion x y) -> pmDisj x (pmUnion y z).
Proof. intros. pmsolve. Qed.
Goal forall x y z, pmDisj z y -> pmDisj x (pmUnion z y) -> pmDisj (pmUnion y x) z.
Proof. intros. pmsolve. Qed.
Goal forall x y z, pmDisj y x -> pmDisj z (pmUnion x y) -> pmDisj x (pmUnion y z).
Proof. intros. pmsolve. Qed.
Goal forall x y z, pmDisj x y -> pmDisj z (pmUnion y x) -> pmDisj x (pmUnion y z).
Proof. intros. pmsolve. Qed.
Goal forall x y z, pmDisj x y -> pmDisj z (pmUnion x y) -> pmDisj x (pmUnion z y).
Proof. intros. pmsolve. Qed.
Goal forall x y z, pmDisj y x -> pmDisj z (pmUnion y x) -> pmDisj x (pmUnion y z).
Proof. intros. pmsolve. Qed.
Goal forall x y z, pmDisj y x -> pmDisj z (pmUnion y x) -> pmDisj x (pmUnion z y).
Proof. intros. pmsolve. Qed.
Goal forall x y z, pmDisj x y -> pmDisj z (pmUnion x y) -> pmDisj (pmUnion y z) x.
Proof. intros. pmsolve. Qed.
Goal forall x y z, pmDisj y x -> pmDisj z (pmUnion x y) -> pmDisj (pmUnion y z) x.
Proof. intros. pmsolve. Qed.
Goal forall x y z, pmDisj x y -> pmDisj z (pmUnion x y) -> pmDisj (pmUnion z y) x.
Proof. intros. pmsolve. Qed.
Goal forall x y z, pmDisj y x -> pmDisj z (pmUnion y x) -> pmDisj (pmUnion y z) x.
Proof. intros. pmsolve. Qed.
Goal forall x y z, pmDisj y x -> pmDisj z (pmUnion y x) -> pmDisj (pmUnion z y) x.
Proof. intros. pmsolve. Qed.
Goal forall x y v, pmDisj x y -> pmeDisj (x v) (y v).
Proof. intros. pmsolve. Qed.
Goal forall x y v, pmDisj y x -> pmeDisj (x v) (y v).
Proof. intros. pmsolve. Qed.
Goal forall x y l v w, pmDisj x y -> pmeDisj v w -> pmDisj (pmUpdate x l v) (pmUpdate y l w).
Proof. intros. pmsolve. Qed.
Goal forall x y z, pmBisim (pmUnion x (pmUnion y z)) (pmUnion (pmUnion x y) z).
Proof. intros. pmsolve. Qed.
Goal forall x y z, pmBisim (pmUnion (pmUnion x y) z) (pmUnion x (pmUnion y z)).
Proof. intros. pmsolve. Qed.
Goal forall x y, pmBisim (pmUnion x y) (pmUnion y x).
Proof. intros. pmsolve. Qed.
Goal forall x, pmUnion x pmIden = x.
Proof. intros. pmsolve. Qed.
Goal forall x, pmUnion pmIden x = x.
Proof. intros. pmsolve. Qed.
Goal forall x, pmBisim (pmUnion x pmIden) x.
Proof. intros. pmsolve. Qed.
Goal forall x, pmBisim (pmUnion pmIden x) x.
Proof. intros. pmsolve. Qed.
Goal forall x y z, pmBisim (pmUnion x (pmUnion y z)) (pmUnion y (pmUnion x z)).
Proof. intros. pmsolve. Qed.
Goal forall x y z, pmBisim (pmUnion (pmUnion x y) z) (pmUnion (pmUnion x z) y).
Proof. intros. pmsolve. Qed.
Goal forall x y z w, pmBisim (pmUnion (pmUnion x z) (pmUnion y w)) (pmUnion (pmUnion x y) (pmUnion z w)).
Proof. intros. pmsolve. Qed.
Goal forall x y z w, pmBisim (pmUnion (pmUnion x y) (pmUnion z w)) (pmUnion (pmUnion x z) (pmUnion y w)).
Proof. intros. pmsolve. Qed.
Goal forall x y v, pmUnion x y v = pmeUnion (x v) (y v).
Proof. intros. pmsolve. Qed.
Goal forall x y v, pmeUnion (x v) (y v) = pmUnion x y v.
Proof. intros. pmsolve. Qed.
Goal forall x y v, pmeBisim (pmUnion x y v) (pmeUnion (x v) (y v)).
Proof. intros. pmsolve. Qed.
Goal forall x y v, pmeBisim (pmeUnion (x v) (y v)) (pmUnion x y v).
Proof. intros. pmsolve. Qed.

End ProcMapSolver.
