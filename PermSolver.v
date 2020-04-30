Require Import HahnBase.
Require Import Permissions.
Require Import QArith.
Require Import Qcanon.

Open Scope Qc_scope.


(** * Permission solver *)

(** The following tactic gives some proof automation for simple
    (but often occuring) properties on validity and disjointness
    of fractional permissions. *)

(** This tactic is defined simply as a table of patterns
    and matching proofs for these patterns. *)

Ltac permsolve :=
  match goal with
    | [H: perm_disj ?x ?y |- perm_disj ?x ?y] => exact H
    | [H: perm_disj ?x ?y |- perm_disj ?y ?x] => symmetry; exact H
    | [H: perm_valid ?x |- 0 < ?x] => by apply perm_valid_pos
    | [H: perm_valid ?x |- ?y < ?x + ?y] => by apply perm_valid_mono
    | [H: perm_valid ?x |- ?y < ?y + ?x] => rewrite Qcplus_comm with y x; by apply perm_valid_mono
    | [H: perm_disj ?x perm_full |- _] => by apply perm_disj_full_neg_l in H
    | [H: perm_disj perm_full ?x |- _] => by apply perm_disj_full_neg_r in H
    | [H1: perm_disj ?x ?y, H2: perm_disj (?x + ?y) ?z |- perm_disj ?y ?z] => apply perm_disj_add_l with x; [exact H1|exact H2]
    | [H1: perm_disj ?y ?z, H2: perm_disj ?x (?y + ?z) |- perm_disj ?x ?y] => apply perm_disj_add_r with z; [exact H1|exact H2]
    | [H1: perm_disj ?x ?y, H2: perm_disj (?x + ?y) ?z |- perm_disj ?x (?y + ?z)] => apply perm_disj_assoc_l; [exact H1|exact H2]
    | [H1: perm_disj ?y ?z, H2: perm_disj ?x (?y + ?z) |- perm_disj (?x + ?y) ?z] => apply perm_disj_assoc_r; [exact H1|exact H2]
    | [H: perm_disj ?x ?y |- perm_valid (?x + ?y)] => by apply perm_add_valid
    | [H: perm_disj ?y ?x |- perm_valid (?x + ?y)] => symmetry in H; by apply perm_add_valid
    | [H: perm_disj ?x ?y |- perm_valid ?x] => by apply perm_disj_valid_l with y
    | [H: perm_disj ?x ?y |- perm_valid ?y] => by apply perm_disj_valid_r with x
    | [H1: perm_disj ?y ?x, H2: perm_disj (?x + ?y) ?z |- perm_disj ?y ?z] => apply perm_disj_add_l with x; [symmetry; exact H1|exact H2]
    | [H1: perm_disj ?x ?y, H2: perm_disj (?y + ?x) ?z |- perm_disj ?y ?z] => apply perm_disj_add_l with x; [exact H1|by rewrite Qcplus_comm]
    | [H1: perm_disj ?x ?y, H2: perm_disj (?x + ?y) ?z |- perm_disj ?z ?y] => symmetry; apply perm_disj_add_l with x; [exact H1|exact H2]
    | [H1: perm_disj ?z ?y, H2: perm_disj ?x (?y + ?z) |- perm_disj ?x ?y] => apply perm_disj_add_r with z; [symmetry; exact H1|exact H2]
    | [H1: perm_disj ?y ?z, H2: perm_disj ?x (?z + ?y) |- perm_disj ?x ?y] => apply perm_disj_add_r with z; [exact H1|by rewrite Qcplus_comm]
    | [H1: perm_disj ?y ?z, H2: perm_disj ?x (?y + ?z) |- perm_disj ?y ?x] => symmetry; by apply perm_disj_add_r with z
    | [H1: perm_disj ?y ?x, H2: perm_disj (?x + ?y) ?z |- perm_disj ?x (?y + ?z)] => apply perm_disj_assoc_l; [symmetry; exact H1|exact H2]
    | [H1: perm_disj ?x ?y, H2: perm_disj (?y + ?x) ?z |- perm_disj ?x (?y + ?z)] => apply perm_disj_assoc_l; [exact H1|by rewrite Qcplus_comm with x y]
    | [H1: perm_disj ?x ?y, H2: perm_disj (?x + ?y) ?z |- perm_disj ?x (?z + ?y)] => rewrite Qcplus_comm with z y; by apply perm_disj_assoc_l
    | [H1: perm_disj ?z ?y, H2: perm_disj ?x (?y + ?z) |- perm_disj (?x + ?y) ?z] => apply perm_disj_assoc_r; [symmetry; exact H1|exact H2]
    | [H1: perm_disj ?y ?z, H2: perm_disj ?x (?z + ?y) |- perm_disj (?x + ?y) ?z] => apply perm_disj_assoc_r; [exact H1|by rewrite Qcplus_comm with y z]
    | [H1: perm_disj ?y ?z, H2: perm_disj ?x (?y + ?z) |- perm_disj (?y + ?x) ?z] => rewrite Qcplus_comm with y x; by apply perm_disj_assoc_r
    | [H1: perm_disj ?x ?y, H2: perm_disj ?z (?x + ?y) |- perm_disj ?y ?z] => symmetry in H2; by apply perm_disj_add_l with x
    | [H1: perm_disj ?y ?x, H2: perm_disj ?z (?x + ?y) |- perm_disj ?y ?z] => symmetry in H1; symmetry in H2; by apply perm_disj_add_l with x
    | [H1: perm_disj ?x ?y, H2: perm_disj ?z (?y + ?x) |- perm_disj ?y ?z] => symmetry in H2; apply perm_disj_add_l with x; auto; rewrite Qcplus_comm; auto; fail
    | [H1: perm_disj ?x ?y, H2: perm_disj ?z (?x + ?y) |- perm_disj ?z ?y] => symmetry; symmetry in H2; apply perm_disj_add_l with x; auto; fail
    | [H1: perm_disj ?y ?z, H2: perm_disj (?y + ?z) ?x |- perm_disj ?x ?y] => symmetry in H2; by apply perm_disj_add_r with z
    | [H1: perm_disj ?z ?y, H2: perm_disj (?y + ?z) ?x |- perm_disj ?x ?y] => symmetry in H1; symmetry in H2; by apply perm_disj_add_r with z
    | [H1: perm_disj ?y ?z, H2: perm_disj (?z + ?y) ?x |- perm_disj ?x ?y] => symmetry in H2; apply perm_disj_add_r with z; auto; by rewrite Qcplus_comm
    | [H1: perm_disj ?y ?z, H2: perm_disj (?y + ?z) ?x |- perm_disj ?y ?x] => symmetry; symmetry in H2; by apply perm_disj_add_r with z
    | [H1: perm_disj ?y ?x, H2: perm_disj (?y + ?x) ?z |- perm_disj ?x (?z + ?y)] => rewrite Qcplus_comm in H2; rewrite Qcplus_comm; apply perm_disj_assoc_l; [by symmetry|exact H2]
    | [H1: perm_disj ?z ?y, H2: perm_disj ?x (?z + ?y) |- perm_disj (?y + ?x) ?z] => rewrite Qcplus_comm in H2; rewrite Qcplus_comm; apply perm_disj_assoc_r; [by symmetry|exact H2]
    | [H1: perm_disj ?x ?y, H2: perm_disj ?z (?x + ?y) |- perm_disj ?x (?y + ?z)] => symmetry in H2; by apply perm_disj_assoc_l
    | [H1: perm_disj ?y ?x, H2: perm_disj ?z (?x + ?y) |- perm_disj ?x (?y + ?z)] => symmetry in H1; symmetry in H2; by apply perm_disj_assoc_l
    | [H1: perm_disj ?x ?y, H2: perm_disj ?z (?y + ?x) |- perm_disj ?x (?y + ?z)] => apply perm_disj_assoc_l; [exact H1|symmetry; by rewrite Qcplus_comm]
    | [H1: perm_disj ?x ?y, H2: perm_disj ?z (?x + ?y) |- perm_disj ?x (?z + ?y)] => rewrite Qcplus_comm; apply perm_disj_assoc_l; [exact H1|by symmetry]
    | [H1: perm_disj ?y ?x, H2: perm_disj ?z (?y + ?x) |- perm_disj ?x (?y + ?z)] => apply perm_disj_assoc_l; [by symmetry|]; symmetry; rewrite Qcplus_comm; auto; by symmetry
    | [H1: perm_disj ?y ?x, H2: perm_disj ?z (?y + ?x) |- perm_disj ?x (?z + ?y)] => rewrite Qcplus_comm in H2; rewrite Qcplus_comm; apply perm_disj_assoc_l; auto; by symmetry
    | [H1: perm_disj ?y ?x, H2: perm_disj ?z (?x + ?y) |- perm_disj (?y + ?z) ?x] => symmetry; apply perm_disj_assoc_l; by symmetry
    | [H1: perm_disj ?x ?y, H2: perm_disj ?z (?x + ?y) |- perm_disj (?z + ?y) ?x] => apply perm_disj_assoc_r; [by symmetry|by rewrite Qcplus_comm]
    | [H1: perm_disj ?x ?y |- ?x < ?x + ?y] => apply Qclt_mono_pos; apply perm_disj_valid_r in H1; by auto
    | [H1: perm_disj ?y ?x |- ?x < ?x + ?y] => symmetry in H1; apply Qclt_mono_pos; apply perm_disj_valid_r in H1; by auto
    | [H1: perm_valid ?x, H2: perm_full < ?x |- _] => by apply perm_valid_full_neg in H2
    | [H1: perm_disj ?x ?y, H2: perm_full < ?x |- _] => apply perm_disj_valid_l in H1; by apply perm_valid_full_neg in H2
    | [H1: perm_disj ?x ?y, H2: perm_full < ?y |- _] => apply perm_disj_valid_r in H1; by apply perm_valid_full_neg in H2
    | _ => fail
  end.


(** ** Unit tests *)

(** Below several unit tests are given for [permsolve]. *)

Goal forall x y, perm_disj x y -> perm_disj x y.
Proof. intros. permsolve. Qed.
Goal forall x y, perm_disj x y -> perm_disj y x.
Proof. intros. permsolve. Qed.
Goal forall x, perm_valid x -> 0 < x.
Proof. intros. permsolve. Qed.
Goal forall x y, perm_valid x -> y < x + y.
Proof. intros. permsolve. Qed.
Goal forall x y, perm_valid x -> y < y + x.
Proof. intros. permsolve. Qed.
Goal forall x, perm_disj x perm_full -> False.
Proof. intros. permsolve. Qed.
Goal forall x, perm_disj perm_full x -> False.
Proof. intros. permsolve. Qed.
Goal forall x y z, perm_disj x y -> perm_disj (x + y) z -> perm_disj y z.
Proof. intros. permsolve. Qed.
Goal forall x y z, perm_disj y z -> perm_disj x (y + z) -> perm_disj x y.
Proof. intros. permsolve. Qed.
Goal forall x y z, perm_disj x y -> perm_disj (x + y) z -> perm_disj x (y + z).
Proof. intros. permsolve. Qed.
Goal forall x y z, perm_disj y z -> perm_disj x (y + z) -> perm_disj (x + y) z.
Proof. intros. permsolve. Qed.
Goal forall x y, perm_disj x y -> perm_valid (x + y).
Proof. intros. permsolve. Qed.
Goal forall x y, perm_disj y x -> perm_valid (x + y).
Proof. intros. permsolve. Qed.
Goal forall x y, perm_disj x y -> perm_valid x.
Proof. intros. permsolve. Qed.
Goal forall x y, perm_disj x y -> perm_valid y.
Proof. intros. permsolve. Qed.
Goal forall x y z, perm_disj y x -> perm_disj (x + y) z -> perm_disj y z.
Proof. intros. permsolve. Qed.
Goal forall x y z, perm_disj x y -> perm_disj (y + x) z -> perm_disj y z.
Proof. intros. permsolve. Qed.
Goal forall x y z, perm_disj x y -> perm_disj (x + y) z -> perm_disj z y.
Proof. intros. permsolve. Qed.
Goal forall x y z, perm_disj z y -> perm_disj x (y + z) -> perm_disj x y.
Proof. intros. permsolve. Qed.
Goal forall x y z, perm_disj y z -> perm_disj x (z + y) -> perm_disj x y.
Proof. intros. permsolve. Qed.
Goal forall x y z, perm_disj y z -> perm_disj x (y + z) -> perm_disj y x.
Proof. intros. permsolve. Qed.
Goal forall x y z, perm_disj y x -> perm_disj (x + y) z -> perm_disj x (y + z).
Proof. intros. permsolve. Qed.
Goal forall x y z, perm_disj x y -> perm_disj (y + x) z -> perm_disj x (y + z).
Proof. intros. permsolve. Qed.
Goal forall x y z, perm_disj x y -> perm_disj (x + y) z -> perm_disj x (z + y).
Proof. intros. permsolve. Qed.
Goal forall x y z, perm_disj z y -> perm_disj x (y + z) -> perm_disj (x + y) z.
Proof. intros. permsolve. Qed.
Goal forall x y z, perm_disj y z -> perm_disj x (z + y) -> perm_disj (x + y) z.
Proof. intros. permsolve. Qed.
Goal forall x y z, perm_disj y z -> perm_disj x (y + z) -> perm_disj (y + x) z.
Proof. intros. permsolve. Qed.
Goal forall x y z, perm_disj x y -> perm_disj z (x + y) -> perm_disj y z.
Proof. intros. permsolve. Qed.
Goal forall x y z, perm_disj y x -> perm_disj z (x + y) -> perm_disj y z.
Proof. intros. permsolve. Qed.
Goal forall x y z, perm_disj x y -> perm_disj z (y + x) -> perm_disj y z.
Proof. intros. permsolve. Qed.
Goal forall x y z, perm_disj x y -> perm_disj z (x + y) -> perm_disj z y.
Proof. intros. permsolve. Qed.
Goal forall x y z, perm_disj y z -> perm_disj (y + z) x -> perm_disj x y.
Proof. intros. permsolve. Qed.
Goal forall x y z, perm_disj z y -> perm_disj (y + z) x -> perm_disj x y.
Proof. intros. permsolve. Qed.
Goal forall x y z, perm_disj y z -> perm_disj (z + y) x -> perm_disj x y.
Proof. intros. permsolve. Qed.
Goal forall x y z, perm_disj y z -> perm_disj (y + z) x -> perm_disj y x.
Proof. intros. permsolve. Qed.
Goal forall x y z, perm_disj z y -> perm_disj x (z + y) -> perm_disj (y + x) z.
Proof. intros. permsolve. Qed.
Goal forall x y z, perm_disj y x -> perm_disj (y + x) z -> perm_disj x (z + y).
Proof. intros. permsolve. Qed.
Goal forall x y z, perm_disj z y -> perm_disj x (z + y) -> perm_disj (y + x) z.
Proof. intros. permsolve. Qed.
Goal forall x y z, perm_disj x y -> perm_disj z (x + y) -> perm_disj x (y + z).
Proof. intros. permsolve. Qed.
Goal forall x y z, perm_disj y x -> perm_disj z (x + y) -> perm_disj x (y + z).
Proof. intros. permsolve. Qed.
Goal forall x y z, perm_disj x y -> perm_disj z (y + x) -> perm_disj x (y + z).
Proof. intros. permsolve. Qed.
Goal forall x y z, perm_disj x y -> perm_disj z (x + y) -> perm_disj x (z + y).
Proof. intros. permsolve. Qed.
Goal forall x y z, perm_disj y x -> perm_disj z (y + x) -> perm_disj x (y + z).
Proof. intros. permsolve. Qed.
Goal forall x y z, perm_disj y x -> perm_disj z (y + x) -> perm_disj x (z + y).
Proof. intros. permsolve. Qed.
Goal forall x y z, perm_disj x y -> perm_disj z (x + y) -> perm_disj (y + z) x.
Proof. intros. permsolve. Qed.
Goal forall x y z, perm_disj y x -> perm_disj z (x + y) -> perm_disj (y + z) x.
Proof. intros. permsolve. Qed.
Goal forall x y z, perm_disj x y -> perm_disj z (x + y) -> perm_disj (z + y) x.
Proof. intros. permsolve. Qed.
Goal forall x y z, perm_disj y x -> perm_disj z (y + x) -> perm_disj (y + z) x.
Proof. intros. permsolve. Qed.
Goal forall x y z, perm_disj y x -> perm_disj z (y + x) -> perm_disj (z + y) x.
Proof. intros. permsolve. Qed.
Goal forall x y, perm_disj x y -> x < x + y.
Proof. intros. permsolve. Qed.
Goal forall x y, perm_disj x y -> y < y + x.
Proof. intros. permsolve. Qed.
Goal forall x, perm_valid x -> perm_full < x -> False.
Proof. intros. permsolve. Qed.
Goal forall x y, perm_disj x y -> perm_full < x -> False.
Proof. intros. permsolve. Qed.
Goal forall x y, perm_disj x y -> perm_full < y -> False.
Proof. intros. permsolve. Qed.
