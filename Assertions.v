Require Import HahnBase.
Require Import Heaps.
Require Import HeapSolver.
Require Import List.
Require Import Permissions.
Require Import PermSolver.
Require Import Permutation.
Require Import PermutationTactic.
Require Import Prelude.
Require Import Process.
Require Import ProcMap.
Require Import ProcMapSolver.
Require Import Programs.
Require Import QArith Qcanon.

Import ListNotations.

Set Implicit Arguments.


(** * Assertions *)

Module Type Assertions
  (domains : Domains)
  (heaps : Heaps domains)
  (hsolver : HeapSolver domains heaps)
  (procs : Processes domains)
  (procmaps : ProcMaps domains heaps procs)
  (progs : Programs domains heaps procs procmaps)
  (pmsolver : ProcMapSolver domains heaps procs procmaps).

Export domains heaps hsolver procs procmaps pmsolver progs.


(** ** Statics *)

(** Below is the syntax of assertions of the program logic. *)

Inductive Assn :=
  | Aplain(B : Cond)
  | Aex(A : Val -> Assn)
  | Adisj(A1 A2 : Assn)
  | Astar(A1 A2 : Assn)
  | Awand(A1 A2 : Assn)
  | Apointsto(t : PointsToType)(q : Qc)(E1 E2 : Expr)
  | Aproc(x : Var)(q : Qc)(P : HProc)(xs : list ProcVar)(f : ProcVar -> Expr)
  | Abisim(P Q : HProc)
  | Aterm(P : HProc)
with
  PointsToType := PTTstd | PTTproc | PTTact.

Add Search Blacklist "Assn_rect".
Add Search Blacklist "Assn_ind".
Add Search Blacklist "Assn_rec".
Add Search Blacklist "Assn_sind".
Add Search Blacklist "PointsToType_rect".
Add Search Blacklist "PointsToType_ind".
Add Search Blacklist "PointsToType_rec".
Add Search Blacklist "PointsToType_sind".

(** Below is a helper tactic for doing induction
    on the structure of assertions. *)

Ltac assn_induction A :=
  induction A as [
    (* plain *)
    B|
    (* quantifiers *)
    A IH|
    (* disjunction *)
    A1 IH1 A2 IH2|
    (* separating conjunction *)
    A1 IH1 A2 IH2|
    (* magic wands *)
    A1 IH1 A2 IH2|
    (* heap ownership *)
    t q E1 E2|
    (* process ownership *)
    x q P xs f|
    (* bisimilarity *)
    P Q|
    (* termination *)
    P
  ].

(** Some sugar. *)

Definition Atrue : Assn := Aplain (Bconst true).
Definition Afalse : Assn := Aplain (Bconst false).

Definition Apointsto_procact (q : Qc)(E1 E2 : Expr) : Assn :=
  if Qc_eq_dec q 1
  then Apointsto PTTact q E1 E2
  else Apointsto PTTproc q E1 E2.


(** *** Iterated separating conjunction *)

(** The iterated separating conjunction is derived from the syntax. *)

Fixpoint Aiter (xs : list Assn) : Assn :=
  match xs with
    | nil => Atrue
    | A :: xs' => Astar A (Aiter xs')
  end.

(** Two helper definitions for iterated separating conjunctions
    over points-to ownership predicates: *)

Definition ApointstoIter {T} (xs : list T)(F : T -> Qc)(f1 f2 : T -> Expr)(t : PointsToType) : list Assn :=
  map (fun x : T => Apointsto t (F x) (f1 x) (f2 x)) xs.

Definition ApointstoIter_procact {T} (xs : list T)(F : T -> Qc)(f1 f2 : T -> Expr) : list Assn :=
  map (fun x : T => Apointsto_procact (F x) (f1 x) (f2 x)) xs.

(** Below are several properties of iterated separating conjunctions. *)

Lemma ApointstoIter_cons {T} :
  forall (xs : list T)(x : T) F f1 f2 t,
  ApointstoIter (x :: xs) F f1 f2 t =
  Apointsto t (F x) (f1 x) (f2 x) :: ApointstoIter xs F f1 f2 t.
Proof. ins. Qed.

Lemma ApointstoIter_app {T} :
  forall (xs ys : list T)(fq : T -> Qc)(f1 f2 : T -> Expr)(t : PointsToType),
  ApointstoIter xs fq f1 f2 t ++ ApointstoIter ys fq f1 f2 t =
  ApointstoIter (xs ++ ys) fq f1 f2 t.
Proof.
  intros xs ys fq f1 f2 t. unfold ApointstoIter.
  by rewrite map_app.
Qed.

Lemma ApointstoIter_procact_app {T} :
  forall (xs ys : list T)(fq : T -> Qc)(f1 f2 : T -> Expr),
  ApointstoIter_procact xs fq f1 f2 ++ ApointstoIter_procact ys fq f1 f2 =
  ApointstoIter_procact (xs ++ ys) fq f1 f2.
Proof.
  intros xs ys fq f1 f2. unfold ApointstoIter_procact.
  by rewrite map_app.
Qed.

Lemma ApointstoIter_ext_in {T} :
  forall (xs : list T)(fq fq' : T -> Qc)(f1 f1' f2 f2' : T -> Expr) t,
    (forall x : T, In x xs -> fq x = fq' x) ->
    (forall x : T, In x xs -> f1 x = f1' x) ->
    (forall x : T, In x xs -> f2 x = f2' x) ->
  ApointstoIter xs fq f1 f2 t = ApointstoIter xs fq' f1' f2' t.
Proof.
  intros xs fq fq' f1 f1' f2 f2' t H1 H2 H3.
  unfold ApointstoIter. apply map_ext_in.
  intros x H4. rewrite H1, H2, H3; vauto.
Qed.

Lemma ApointstoIter_procact_ext_in {T} :
  forall (xs : list T)(fq fq' : T -> Qc)(f1 f1' f2 f2' : T -> Expr),
    (forall x : T, In x xs -> fq x = fq' x) ->
    (forall x : T, In x xs -> f1 x = f1' x) ->
    (forall x : T, In x xs -> f2 x = f2' x) ->
  ApointstoIter_procact xs fq f1 f2 = ApointstoIter_procact xs fq' f1' f2'.
Proof.
  intros xs fq fq' f1 f1' f2 f2' H1 H2 H3.
  unfold ApointstoIter_procact. apply map_ext_in.
  intros x H4. rewrite H1, H2, H3; vauto.
Qed.


(** *** Free variables *)

(** The predicate [assn_fv A x] determines whether the
    _program_ variable [x] occurs freely in [A].
    The definition of [assn_fv] is as expected. *)

Fixpoint assn_fv (A : Assn)(x : Var) : Prop :=
  match A with
    | Aplain B => In x (cond_fv B)
    | Aex A => exists v, assn_fv (A v) x
    | Adisj A1 A2
    | Astar A1 A2
    | Awand A1 A2 => assn_fv A1 x \/ assn_fv A2 x
    | Apointsto _ _ E1 E2 => In x (expr_fv E1) \/ In x (expr_fv E2)
    | Aproc y _ P _ f => x = y \/ hproc_fv P x \/ expr_map_fv f x
    | Abisim P Q => hproc_fv P x \/ hproc_fv Q x
    | Aterm P => hproc_fv P x
  end.

(** Several useful properties related to free variables: *)

Lemma assn_fv_iter :
  forall xs x,
  assn_fv (Aiter xs) x <-> exists A, In A xs /\ assn_fv A x.
Proof.
  induction xs as [|A xs IH]; intro x.
  - split; intro H; desf.
  - split; intro H.
    + simpl in H. destruct H as [H | H].
      * exists A. split; vauto.
      * rewrite IH in H. destruct H as (A'&H1&H2).
        exists A'. split; auto. by apply in_cons.
    + destruct H as (A'&H1&H2).
      simpls. destruct H1 as [H1|H1]; vauto.
      right. rewrite IH. exists A'. split; vauto.
Qed.

Lemma assn_fv_ApointstoIter {T} :
  forall (xs : list T) F f1 f2 t x,
  assn_fv (Aiter (ApointstoIter xs F f1 f2 t)) x <->
  exists e : T, In e xs /\ (In x (expr_fv (f1 e)) \/ In x (expr_fv (f2 e))).
Proof.
  intros xs F f1 f2 t x. split; intro H.
  - rewrite assn_fv_iter in H.
    destruct H as (A&H1&H2).
    unfold ApointstoIter in H1.
    rewrite in_map_iff in H1.
    destruct H1 as (e&H1&H3). clarify.
    simpl in H2. exists e. intuition.
  - destruct H as (e&H1&H2).
    rewrite assn_fv_iter.
    exists (Apointsto t (F e) (f1 e) (f2 e)). split; vauto.
    unfold ApointstoIter. rewrite in_map_iff.
    exists e. intuition.
Qed.


(** *** Substitution *)

(** The operation [assn_subst x E A] substitutes every
    occurence of the _program_ variable [x] by [E]
    in the assertion [A]. The definition of [assn_subst]
    is as expected. *)

Fixpoint assn_subst (x : Var)(E : Expr)(A : Assn) : Assn :=
  match A with
    | Aplain B => Aplain (cond_subst x E B)
    | Aex A => Aex (fun v => assn_subst x E (A v))
    | Adisj A1 A2 => Adisj (assn_subst x E A1) (assn_subst x E A2)
    | Astar A1 A2 => Astar (assn_subst x E A1) (assn_subst x E A2)
    | Awand A1 A2 => Awand (assn_subst x E A1) (assn_subst x E A2)
    | Apointsto t q E1 E2 => Apointsto t q (expr_subst x E E1) (expr_subst x E E2)
    | Aproc y q P xs f => Aproc y q (hproc_subst x E P) xs (expr_subst_map x E f)
    | Abisim P Q => Abisim (hproc_subst x E P) (hproc_subst x E Q)
    | Aterm P => Aterm (hproc_subst x E P)
  end.

(** Existential quantification as is written in the paper
    (with a variable instead of a mapping) can be defined
    using the definition of substitution. *)

Definition Aexists (x : Var)(A : Assn) : Assn :=
  Aex (fun v => assn_subst x (Econst v) A).

(** The substitution of any variable not occuring in the
    targetted assertion does not change the assertion. *)

Lemma assn_subst_pres :
  forall A x E, ~ assn_fv A x -> assn_subst x E A = A.
Proof.
  assn_induction A; intros y E H1; simpls; vauto.
  (* plain *)
  - rewrite cond_subst_pres; auto.
  (* quantifiers *)
  - cut (A = fun v => assn_subst y E (A v)).
    + intro H2. by rewrite <- H2.
    + extensionality v. symmetry. apply IH.
      intro H2. apply H1. by exists v.
  (* disjunction *)
  - apply not_or_and in H1. destruct H1 as (H1&H2).
    by rewrite IH1, IH2.
  (* separating conjunction *)
  - apply not_or_and in H1. destruct H1 as (H1&H2).
    by rewrite IH1, IH2.
  (* magic wand *)
  - apply not_or_and in H1. destruct H1 as (H1&H2).
    by rewrite IH1, IH2.
  (* heap ownership *)
  - repeat rewrite expr_subst_pres; auto; intro; apply H.
  (* process ownership *)
  - apply not_or_and in H1. destruct H1 as (H1&H2).
    apply not_or_and in H2. destruct H2 as (H2&H3).
    rewrite hproc_subst_pres; auto.
    by rewrite expr_subst_pres_map.
  (* bisimilarity *)
  - apply not_or_and in H1. destruct H1 as (H1&H2).
    by repeat rewrite hproc_subst_pres; auto.
  (* termination *)
  - rewrite hproc_subst_pres; auto.
Qed.


(** ** Dynamics *)

(** The following satisfaction relation, [sat], defines
    the semantic meaning of assertions. *)

Fixpoint sat (ph : PermHeap)(pm : ProcMap)(s g : Store)(A : Assn) : Prop :=
  match A with
    (* plain *)
    | Aplain B => cond_eval B s = true
    (* quantifiers *)
    | Aex A => exists v, sat ph pm s g (A v)
    (* disjunction *)
    | Adisj A1 A2 =>
        sat ph pm s g A1 \/ sat ph pm s g A2
    (* separating conjunction *)
    | Astar A1 A2 =>
        exists ph1 ph2,
          phDisj ph1 ph2 /\
          phUnion ph1 ph2 = ph /\
        exists pm1 pm2,
          pmDisj pm1 pm2 /\
          pmBisim (pmUnion pm1 pm2) pm /\
          sat ph1 pm1 s g A1 /\
          sat ph2 pm2 s g A2
    (* magic wand *)
    | Awand A1 A2 =>
        forall ph' pm',
        phDisj ph ph' ->
        pmDisj pm pm' ->
        sat ph' pm' s g A1 ->
        sat (phUnion ph ph') (pmUnion pm pm') s g A2
    (* standard heap ownership *)
    | Apointsto PTTstd q E1 E2 =>
        let l := expr_eval E1 s in
        let v := expr_eval E2 s in
        perm_valid q /\ phcLe (PHCstd q v) (ph l)
    (* process heap ownership *)
    | Apointsto PTTproc q E1 E2 =>
        let l := expr_eval E1 s in
        let v := expr_eval E2 s in
        perm_valid q /\ phcLe (PHCproc q v) (ph l)
    (* action heap ownership *)
    | Apointsto PTTact q E1 E2 =>
        let l := expr_eval E1 s in
        let v := expr_eval E2 s in
        perm_valid q /\ exists v', phcLe (PHCact q v v') (ph l)
    (* process ownership *)
    | Aproc x q HP xs f =>
        let P := pDehybridise HP s in
        let F := expr_eval_map f s in
        let c := PEelem q P xs F in
        exists c',
          pmeDisj c c' /\
          pmeBisim (pm (g x)) (pmeUnion c c')
    (* bisimilarity *)
    | Abisim P Q =>
        bisim (pDehybridise P s) (pDehybridise Q s)
    (* termination *)
    | Aterm P => pterm (pDehybridise P s)
  end.

(** Process maps can always be replaced by bisimilar ones
    (and therefore also by equal ones, since process map equality
    is a subrelation of bisimilarity). *)

Lemma sat_procmap_bisim :
  forall A ph pm1 pm2 s g,
  pmBisim pm1 pm2 -> sat ph pm1 s g A -> sat ph pm2 s g A.
Proof.
  assn_induction A; intros ph pm1 pm2 s g H1 H2; vauto.
  (* quantifiers *)
  - simpl in H2. destruct H2 as (v&H2).
    exists v. by apply IH with pm1.
  (* disjunction *)
  - simpls. destruct H2 as [H2|H2].
    + left. by apply IH1 with pm1.
    + right. by apply IH2 with pm1.
  (* separating conjunction *)
  - simpls.
    destruct H2 as (ph1&ph2&D1&D2&pm3&pm4&D3&D4&D5&D6).
    exists ph1, ph2. intuition.
    exists pm3, pm4. intuition.
    by rewrite <- H1.
  (* magic wand *)
  - simpls. intros ph' pm' H3 H4 H5.
    apply IH2 with (pmUnion pm1 pm'); clear IH2.
    + by rewrite H1.
    + apply H2; auto. by rewrite H1.
  (* process ownership *)
  - unfold sat in *.
    destruct H2 as (c&H2&H3).
    exists c. intuition.
    rewrite <- H3. by rewrite H1.
Qed.
Add Parametric Morphism : sat
  with signature eq ==> pmBisim ==> eq ==> eq ==> eq ==> iff
    as sat_bisim_mor.
Proof.
  intros ph pm1 pm2 H1 s g A. split; intro H2.
  - by apply sat_procmap_bisim with pm1; auto.
  - apply sat_procmap_bisim with pm2; auto.
    by symmetry.
Qed.

(** The following lemma relates substitution in assertions
    with the satisfiability of that assertion. *)

Lemma sat_subst :
  forall A ph pm s g x E,
  sat ph pm s g (assn_subst x E A) <->
  sat ph pm (sUpdate s x (expr_eval E s)) g A.
Proof.
  assn_induction A; intros ph pm s g y E'; auto; split; intro H1.
  (* plain *)
  - simpl. by rewrite <- cond_eval_subst.
  - simpl. by rewrite cond_eval_subst.
  (* quantifiers *)
  - simpl in H1. destruct H1 as (v&H1).
    simpl. exists v. by apply IH.
  - simpl in H1. destruct H1 as (v&H1).
    simpl. exists v. by apply IH.
  (* disjunction *)
  - simpl in H1. destruct H1 as [H1|H1].
    + left. by rewrite <- IH1.
    + right. by rewrite <- IH2.
  - simpl in H1. destruct H1 as [H1|H1].
    + left. by rewrite IH1.
    + right. by rewrite IH2.
  (* separating conjunction *)
  - simpl in H1.
    destruct H1 as (ph1&ph2&D1&D2&pm1&pm2&D3&D4&D5&D6).
    exists ph1, ph2. intuition.
    exists pm1, pm2. intuition.
    + by apply IH1.
    + by apply IH2.
  - simpl in H1.
    destruct H1 as (ph1&ph2&D1&D2&pm1&pm2&D3&D4&D5&D6).
    exists ph1, ph2. intuition.
    exists pm1, pm2. intuition.
    + by apply <- IH1.
    + by apply <- IH2.
  (* magic wands *)
  - intros ph' pm' D1 D2 D3.
    apply IH2, H1; auto. by apply IH1.
  - intros ph' pm' D1 D2 D3.
    apply IH2, H1; auto. by apply IH1.
  (* heap ownership *)
  - simpl. repeat rewrite <- expr_eval_subst in *. vauto.
  - simpl. repeat rewrite expr_eval_subst in *. vauto.
  (* process ownership *)
  - destruct H1 as (c&H1&H2). exists c.
    rewrite <- expr_eval_subst_map in *.
    split; auto. by rewrite <- pDehybridise_subst.
  - destruct H1 as (c&H1&H2). exists c.
    rewrite expr_eval_subst_map in *.
    split; auto. by rewrite pDehybridise_subst.
  (* bisimilarity *)
  - simpl in H1. simpl.
    by repeat rewrite <- pDehybridise_subst.
  - simpl in H1. simpl.
    by repeat rewrite pDehybridise_subst.
  (* termination *)
  - simpl in H1. simpl.
    by repeat rewrite <- pDehybridise_subst.
  - simpl in H1. simpl.
    by repeat rewrite pDehybridise_subst.
Qed.

(** The satisfiability of any assertion [A] only depends
    on the variables occuring freely in [A]. *)

Lemma sat_agree :
  forall A ph pm s1 s2 g,
  sAgree (assn_fv A) s1 s2 -> sat ph pm s1 g A <-> sat ph pm s2 g A.
Proof.
  assn_induction A; intros ph pm s1 s2 g H1; split; intro H2.
  (* plain *)
  - simpls. rewrite <- cond_agree with (s1:=s1); vauto.
  - simpls. rewrite cond_agree with (s2:=s2); vauto.
  (* quantifiers *)
  - simpls. destruct H2 as (v&H2).
    exists v. rewrite <- IH with (s1:=s1); auto.
    intros x H3. apply H1. by exists v.
  - simpls. destruct H2 as (v&H2).
    exists v. rewrite IH with (s2:=s2); auto.
    intros x H3. apply H1. by exists v.
  (* disjunction *)
  - simpls. destruct H2 as [H2|H2].
    + left. rewrite <- IH1 with (s1:=s1); auto.
      intros x H3. apply H1. by left.
    + right. rewrite <- IH2 with (s1:=s1); auto.
      intros x H3. apply H1. by right.
  - simpls. destruct H2 as [H2|H2].
    + left. rewrite IH1 with (s2:=s2); auto.
      intros x H3. apply H1. by left.
    + right. rewrite IH2 with (s2:=s2); auto.
      intros x H3. apply H1. by right.
  (* separating conjunction *)
  - simpls. destruct H2 as (ph1&ph2&D1&D2&pm1&pm2&D3&D4&D5&D6).
    exists ph1, ph2. intuition.
    exists pm1, pm2. intuition.
    + rewrite <- IH1 with (s1:=s1); auto.
      intros x H3. apply H1. by left.
    + rewrite <- IH2 with (s1:=s1); auto.
      intros x H3. apply H1. by right.
  - simpls. destruct H2 as (ph1&ph2&D1&D2&pm1&pm2&D3&D4&D5&D6).
    exists ph1, ph2. intuition.
    exists pm1, pm2. intuition.
    + rewrite IH1 with (s2:=s2); auto.
      intros x H3. apply H1. by left.
    + rewrite IH2 with (s2:=s2); auto.
      intros x H3. apply H1. by right.
  (* magic wand *)
  - simpls. intros ph' pm' H3 H4 H5.
    rewrite <- IH2 with (s1:=s1); auto.
    + apply H2; auto. clear H2.
      rewrite IH1 with (s2:=s2); auto.
      intros x H2. apply H1. by left.
    + intros x H6. apply H1. by right.
  - simpls. intros ph' pm' H3 H4 H5.
    rewrite IH2 with (s1:=s1); auto.
    + apply H2; auto. clear H2.
      rewrite <- IH1 with (s1:=s1); auto.
      intros x H2. apply H1. by left.
    + intros x H6. apply H1. by right.
  (* heap ownership *)
  - unfold sat in H2.
    rewrite expr_agree with (s2:=s2) in H2; auto.
    2:{ intros x H3. apply H1. simpl. by right. }
    unfold sat. destruct t.
    + rewrite <- expr_agree with (E:=E1)(s1:=s1); auto.
      red. intros x H3. apply H1. simpl. by left.
    + rewrite <- expr_agree with (E:=E1)(s1:=s1); auto.
      red. intros x H3. apply H1. simpl. by left.
    + rewrite <- expr_agree with (E:=E1)(s1:=s1); auto.
      red. intros x H3. apply H1. simpl. by left.
  - unfold sat in H2.
    rewrite <- expr_agree with (s1:=s1) in H2; auto.
    2:{ intros x H3. apply H1. simpl. by right. }
    unfold sat. destruct t.
    + rewrite expr_agree with (E:=E1)(s2:=s2); auto.
      red. intros x H3. apply H1. simpl. by left.
    + rewrite expr_agree with (E:=E1)(s2:=s2); auto.
      red. intros x H3. apply H1. simpl. by left.
    + rewrite expr_agree with (E:=E1)(s2:=s2); auto.
      red. intros x H3. apply H1. simpl. by left.
  (* process ownership *)
  - destruct H2 as (c&H2&H3). unfold sat.
    rewrite <- expr_map_agree with (s3:=s1); vauto.
    + exists c. intuition.
      rewrite <- pDehybridise_agree with (s1:=s1); auto.
      intros y H4. apply H1. simpl. right. by left.
    + intros y H4. apply H1. simpl. by repeat right.
  - destruct H2 as (c&H2&H3). unfold sat.
    rewrite expr_map_agree with (s4:=s2); vauto.
    + exists c. intuition.
      rewrite pDehybridise_agree with (s2:=s2); auto.
      intros y H4. apply H1. simpl. right. by left.
    + intros y H4. apply H1. simpl. by repeat right.
  (* bisimilarity *)
  - simpl in H2. simpl.
    rewrite <- pDehybridise_agree with (s1:=s1)(P:=P).
    2:{ intros x H3. apply H1. simpl. by left. }
    rewrite <- pDehybridise_agree with (s1:=s1)(P:=Q); auto.
    intros x H3. apply H1. simpl. by right.
  - simpl in H2. simpl.
    rewrite pDehybridise_agree with (s2:=s2)(P:=P).
    2:{ intros x H3. apply H1. simpl. by left. }
    rewrite pDehybridise_agree with (s2:=s2)(P:=Q); auto.
    intros x H3. apply H1. simpl. by right.
  (* termination *)
  - simpl in H2. simpl.
    rewrite <- pDehybridise_agree with (s1:=s1)(P:=P); auto.
  - simpl in H2. simpl.
    rewrite pDehybridise_agree with (s2:=s2)(P:=P); auto.
Qed.
Lemma sat_agree_ghost :
  forall A ph pm s g1 g2,
  sAgree (assn_fv A) g1 g2 -> sat ph pm s g1 A <-> sat ph pm s g2 A.
Proof.
  assn_induction A; intros ph pm s g1 g2 H1; split; intro H2; vauto.
  (* quantifiers *)
  - simpls. destruct H2 as (v&H2).
    exists v. rewrite <- IH with (g1:=g1); auto.
    intros x H3. apply H1. by exists v.
  - simpls. destruct H2 as (v&H2).
    exists v. rewrite IH with (g2:=g2); auto.
    intros x H3. apply H1. by exists v.
  (* disjunction *)
  - simpls. destruct H2 as [H2|H2].
    + left. rewrite <- IH1 with (g1:=g1); auto.
      intros x H3. apply H1. by left.
    + right. rewrite <- IH2 with (g1:=g1); auto.
      intros x H3. apply H1. by right.
  - simpls. destruct H2 as [H2|H2].
    + left. rewrite IH1 with (g2:=g2); auto.
      intros x H3. apply H1. by left.
    + right. rewrite IH2 with (g2:=g2); auto.
      intros x H3. apply H1. by right.
  (* separating conjunction *)
  - simpls. destruct H2 as (ph1&ph2&D1&D2&pm1&pm2&D3&D4&D5&D6).
    exists ph1, ph2. intuition.
    exists pm1, pm2. intuition.
    + rewrite <- IH1 with (g1:=g1); auto.
      intros x H3. apply H1. by left.
    + rewrite <- IH2 with (g1:=g1); auto.
      intros x H3. apply H1. by right.
  - simpls. destruct H2 as (ph1&ph2&D1&D2&pm1&pm2&D3&D4&D5&D6).
    exists ph1, ph2. intuition.
    exists pm1, pm2. intuition.
    + rewrite IH1 with (g2:=g2); auto.
      intros x H3. apply H1. by left.
    + rewrite IH2 with (g2:=g2); auto.
      intros x H3. apply H1. by right.
  (* magic wand *)
  - simpls. intros ph' pm' H3 H4 H5.
    rewrite <- IH2 with (g1:=g1); auto.
    + apply H2; auto. clear H2.
      rewrite IH1 with (g2:=g2); auto.
      intros x H2. apply H1. by left.
    + intros x H6. apply H1. by right.
  - simpls. intros ph' pm' H3 H4 H5.
    rewrite IH2 with (g1:=g1); auto.
    + apply H2; auto. clear H2.
      rewrite <- IH1 with (g1:=g1); auto.
      intros x H2. apply H1. by left.
    + intros x H6. apply H1. by right.
  (* process ownership *)
  - destruct H2 as (c&H2&H3). unfold sat.
    exists c. intuition. rewrite <- H1; [done|].
    simpl. by left.
  - destruct H2 as (c&H2&H3). unfold sat.
    exists c. intuition. rewrite H1; [done|].
    simpl. by left.
Qed.

(** Satisfiability of any assertion [A] is insensitive to
    updating variables not occuring freely in [A]. *)

Lemma sat_update :
  forall A ph pm s g x v,
  ~ assn_fv A x -> sat ph pm (sUpdate s x v) g A <-> sat ph pm s g A.
Proof.
  intros A ph pm s g x v H1. split; intro H2.
  - rewrite sat_agree with (s2:=sUpdate s x v); auto.
    intros y H3. unfold sUpdate, update.
    destruct (var_eq_dec x y); vauto.
  - rewrite <- sat_agree with (s1:=s); auto.
    intros y H3. unfold sUpdate, update.
    destruct (var_eq_dec x y); vauto.
Qed.
Lemma sat_update_ghost :
  forall A ph pm s g x v,
  ~ assn_fv A x -> sat ph pm s (sUpdate g x v) A <-> sat ph pm s g A.
Proof.
  intros A ph pm s g x v H1. split; intro H2.
  - rewrite sat_agree_ghost with (g2:=sUpdate g x v); auto.
    intros y H3. unfold sUpdate, update.
    destruct (var_eq_dec x y); vauto.
  - rewrite <- sat_agree_ghost with (g1:=g); auto.
    intros y H3. unfold sUpdate, update.
    destruct (var_eq_dec x y); vauto.
Qed.

(** Satisfiability of assertions is monotonic with respect
    to permission heaps and process maps. *)

Lemma sat_weaken :
  forall A ph1 ph2 pm1 pm2 s g,
  phDisj ph1 ph2 ->
  pmDisj pm1 pm2 ->
  sat ph1 pm1 s g A ->
  sat (phUnion ph1 ph2) (pmUnion pm1 pm2) s g A.
Proof.
  assn_induction A; intros ph1 ph2 pm1 pm2 s g H1 H2 H3; auto.
  (* quantifiers *)
  - simpls. destruct H3 as (v&H3).
    exists v. by apply IH.
  (* disjunction *)
  - simpls. destruct H3 as [H3|H3].
    + left. by apply IH1.
    + right. by apply IH2.
  (* separating conjunction *)
  - simpl in H3.
    destruct H3 as (ph3&ph4&D1&D2&pm3&pm4&D3&D4&D5&D6).
    simpl. clarify. exists ph3, (phUnion ph4 ph2).
    intuition; [phsolve|phsolve|].
    exists pm3, (pmUnion pm4 pm2).
    rewrite <- D4 in *. clear D4.
    intuition; [pmsolve|pmsolve|].
    apply IH2; [phsolve|pmsolve|done].
  (* magic wand *)
  - simpls. intros ph' pm' H4 H5 H6.
    rewrite phUnion_assoc, pmUnion_assoc.
    apply H3; clear H3; [phsolve|pmsolve|].
    rewrite phUnion_comm, pmUnion_comm.
    apply IH1; [phsolve|pmsolve|done].
  (* heap ownership *)
  - unfold sat in *. destruct t.
    + destruct H3 as (H3&H4). split; [done|].
      rewrite <- phUnion_cell.
      apply phcLe_weaken; vauto.
    + destruct H3 as (H3&H4). split; [done|].
      rewrite <- phUnion_cell.
      apply phcLe_weaken; vauto.
    + destruct H3 as (H3&v&H4). split; [done|].
      exists v. rewrite <- phUnion_cell.
      apply phcLe_weaken; vauto.
  (* process ownership *)
  - unfold sat in *.
    destruct H3 as (pmv&H3&H4).
    exists (pmeUnion pmv (pm2 (g x))). split.
    + apply pmeDisj_assoc_l; auto. pmeclarify.
    + rewrite <- pmeUnion_assoc. by pmeclarify.
Qed.

(** The satisfiability of iterated separating conjunctions
    is insensitive to permutations. *)

Lemma sat_iter_permut :
  forall xs ys,
  Permutation xs ys ->
  forall ph pm s g,
  sat ph pm s g (Aiter xs) ->
  sat ph pm s g (Aiter ys).
Proof.
  intros xs ys PERM.
  permut_induction PERM; intros ph pm s g SAT; simpls.
  (* skip *)
  - destruct SAT as (ph1&ph2&D1&D2&pm1&pm2&D3&D4&SAT1&SAT2).
    exists ph1, ph2. intuition.
    exists pm1, pm2. intuition.
  (* swap *)
  - destruct SAT as (ph1&ph2&D1&H1&pm1&pm2&D2&H2&SAT1&SAT).
    destruct SAT as (ph3&ph4&D3&H3&pm3&pm4&D4&H4&SAT3&SAT4).
    clarify. exists ph3, (phUnion ph1 ph4).
    intuition; [phsolve|phsolve|].
    exists pm3, (pmUnion pm1 pm4).
    intuition; [pmclarify; pmsolve|pmclarify; pmsolve|].
    exists ph1, ph4. intuition; [phsolve|].
    exists pm1, pm4. intuition. pmclarify. pmsolve.
  (* transitive *)
  - by apply IH2, IH1.
Qed.

(** The satisfiability of points-to predicates is independent of the process map. *)

Lemma sat_pointsto_indep :
  forall ph pm1 pm2 s g t q E1 E2,
  sat ph pm1 s g (Apointsto t q E1 E2) ->
  sat ph pm2 s g (Apointsto t q E1 E2).
Proof.
  intros ph pm1 pm2 s g t q E1 E2 SAT.
  unfold sat in *. desf.
Qed.


(** ** Logical consequence *)

(** The relation [entails] defines _semantic consequence_
    of two assertions. That is, [A] is a logical consequence of [A']
    if there is no model that distinguishes [A] from [A']. *)

(** Logical equivalence [aEquiv] of any two assertions
    is defined to be a logical entailment in both directions. *)

Definition aEntails (A1 A2 : Assn) : Prop :=
  forall ph pm s g,
    phValid ph -> pmValid pm -> sat ph pm s g A1 -> sat ph pm s g A2.
Definition aEntails_rev (A1 A2 : Assn) : Prop :=
  aEntails A2 A1.
Definition aEquiv (A1 A2 : Assn) : Prop :=
  aEntails A1 A2 /\ aEntails A2 A1.

Notation "A1 ⊢ A2":=(aEntails A1 A2) (only printing, at level 80).
Notation "A1 ⊣ A2":=(aEntails_rev A1 A2) (only printing, at level 80).
Notation "A1 ⊣⊢ A2":=(aEquiv A1 A2) (only printing, at level 80).

Lemma aEntails_flip :
  forall A1 A2, aEntails A1 A2 <-> aEntails_rev A2 A1.
Proof. ins. Qed.

(** Logical consequence is a consequence relation. *)

Instance aEntails_refl : Reflexive aEntails.
Proof. intro. red. intuition. Qed.
Instance aEntails_trans : Transitive aEntails.
Proof. unfold aEntails. intuition. Qed.
Instance aEntails_preorder : PreOrder aEntails.
Proof. split; intuition. Qed.

Instance aEntails_rev_refl : Reflexive aEntails_rev.
Proof. intro. red. intuition. Qed.
Instance aEntails_rev_trans : Transitive aEntails_rev.
Proof. unfold aEntails_rev. intros ?????. by transitivity y. Qed.
Instance aEntails_rev_preorder : PreOrder aEntails_rev.
Proof. split; intuition. Qed.

Hint Resolve aEntails_refl aEntails_rev_refl : core.

(** Logical equivalence is an equivalence relation. *)

Instance aEquiv_refl : Reflexive aEquiv.
Proof. red. ins. Qed.
Instance aEquiv_symm : Symmetric aEquiv.
Proof. red. intros A1 A2 (H1&H2). split; auto. Qed.
Instance aEquiv_trans : Transitive aEquiv.
Proof. red. intros A1 A2 A3 (H1&H2) (H3&H4). split; by transitivity A2. Qed.
Instance aEquiv_eq : Equivalence aEquiv.
Proof. split; intuition. Qed.

Hint Resolve aEquiv_refl : core.

(** Logical equivalence is a subrelation of entailment. *)

Instance aEntails_subrel : subrelation aEquiv aEntails.
Proof. red. ins. red in H. desf. Qed.
Instance aEntails_rev_subrel : subrelation aEquiv aEntails_rev.
Proof. red. ins. red in H. desf. Qed.

(** Logical consequence is a congruence for all
    connectives of the program logic. *)

Add Parametric Morphism : Adisj
  with signature aEntails ==> aEntails ==> aEntails
    as Adisj_entails_mor.
Proof.
  intros A1 A1' ENT1 A2 A2' ENT2.
  red. intros ph pm s g Vph Vpm SAT. simpls.
  destruct SAT as [SAT|SAT].
  - left. apply ENT1; auto.
  - right. apply ENT2; auto.
Qed.
Add Parametric Morphism : Astar
  with signature aEntails ==> aEntails ==> aEntails
    as Astar_entails_mor.
Proof.
  intros A1 A1' ENT1 A2 A2' ENT2.
  red. intros ph pm s g Vph Vpm SAT. simpls.
  destruct SAT as (ph1&ph2&D1&H1&pm1&pm2&D2&H2&SAT1&SAT2).
  exists ph1, ph2. intuition.
  exists pm1, pm2. intuition.
  - apply ENT1; [phsolve|pmsolve|done].
  - apply ENT2; [phsolve|pmsolve|done].
Qed.
Add Parametric Morphism : Awand
  with signature aEntails_rev ==> aEntails ==> aEntails
    as Awand_entails_mor.
Proof.
  intros A1 A1' ENT1 A2 A2' ENT2.
  red. intros ph pm s g Vph Vpm WAND. simpls.
  intros ph' pm' D1 D2 SAT1.
  apply ENT2; auto.
  apply WAND; auto.
  apply ENT1; [phsolve|pmsolve|done].
Qed.

Add Parametric Morphism : Adisj
  with signature aEquiv ==> aEquiv ==> aEquiv
    as Adisj_equiv_mor.
Proof.
  intros A1 A2 (H1&H2) A3 A4 (H3&H4). split.
  - by rewrite H1, H3.
  - by rewrite H2, H4.
Qed.
Add Parametric Morphism : Astar
  with signature aEquiv ==> aEquiv ==> aEquiv
    as Astar_equiv_mor.
Proof.
  intros A1 A2 (H1&H2) A3 A4 (H3&H4). split.
  - by rewrite H1, H3.
  - by rewrite H2, H4.
Qed.
Add Parametric Morphism : Awand
  with signature aEquiv ==> aEquiv ==> aEquiv
    as Awand_equiv_mor.
Proof.
  intros A1 A2 (H1&H2) A3 A4 (H3&H4). split.
  - rewrite aEntails_flip in H2. by rewrite H2, H3.
  - rewrite aEntails_flip in H1. by rewrite H1, H4.
Qed.


(** *** Weakening rule *)

Lemma sat_star_combine :
  forall ph1 ph2 pm1 pm2 s g A1 A2,
  phDisj ph1 ph2 ->
  pmDisj pm1 pm2 ->
  sat ph1 pm1 s g A1 ->
  sat ph2 pm2 s g A2 ->
  sat (phUnion ph1 ph2) (pmUnion pm1 pm2) s g (Astar A1 A2).
Proof.
  intros ph1 ph2 pm1 pm2 s g A1 A2 D1 D2 H1 H2.
  exists ph1, ph2. repeat split; auto.
  exists pm1, pm2. repeat split; auto.
Qed.

Lemma sat_star_weaken :
  forall ph pm s g A1 A2,
  sat ph pm s g (Astar A1 A2) ->
  sat ph pm s g A1.
Proof.
  intros ph pm s g A1 A2 SAT.
  destruct SAT as (ph1&ph2&D1&H1&pm1&pm2&D2&H2&SAT1&SAT2).
  rewrite <- H1, <- H2. by apply sat_weaken.
Qed.

(** The following rule shows that our separation logic is _intuitionistic_. *)

Theorem assn_weaken :
  forall A1 A2, aEntails (Astar A1 A2) A1.
Proof.
  intros A1 A2 ph pm s g H1 H2 H3.
  by apply sat_star_weaken with A2.
Qed.


(** *** Separating conjunction *)

(** Soundness of the axioms of associativity and commutativity. *)

Lemma sat_star_assoc_l :
  forall ph pm s g A1 A2 A3,
  sat ph pm s g (Astar A1 (Astar A2 A3)) ->
  sat ph pm s g (Astar (Astar A1 A2) A3).
Proof.
  intros ph pm s g A1 A2 A3 SAT.
  destruct SAT as (ph1&ph1'&D1&H1&pm1&pm1'&D2&H2&SAT1&SAT2).
  destruct SAT2 as (ph2&ph3&D3&H3&pm2&pm3&D4&H4&SAT2&SAT3).
  exists (phUnion ph1 ph2), ph3.
  repeat split; [phsolve|phsolve|].
  exists (pmUnion pm1 pm2), pm3.
  repeat split; [pmclarify; pmsolve|pmclarify; pmsolve| |done].
  exists ph1, ph2. repeat split; [phsolve|].
  exists pm1, pm2. repeat split; auto.
  pmclarify. pmsolve.
Qed.
Theorem Astar_assoc_l :
  forall A1 A2 A3,
  aEntails (Astar A1 (Astar A2 A3)) (Astar (Astar A1 A2) A3).
Proof.
  intros A1 A2 A3 ph pm s g H1 H2 H3.
  by apply sat_star_assoc_l.
Qed.
Lemma sat_star_assoc_r :
  forall ph pm s g A1 A2 A3,
  sat ph pm s g (Astar (Astar A1 A2) A3) ->
  sat ph pm s g (Astar A1 (Astar A2 A3)).
Proof.
  intros ph pm s g A1 A2 A3 SAT.
  destruct SAT as (ph1'&ph3&D1&H1&pm1'&pm3&D2&H2&SAT1&SAT2).
  destruct SAT1 as (ph1&ph2&D3&H3&pm1&pm2&D4&H4&SAT1&SAT3).
  exists ph1, (phUnion ph2 ph3). repeat split; [phsolve|phsolve|].
  exists pm1, (pmUnion pm2 pm3).
  repeat split; [pmclarify; pmsolve|pmclarify; pmsolve|done|].
  exists ph2, ph3. repeat split; [phsolve|].
  exists pm2, pm3. repeat split; auto.
  pmclarify. pmsolve.
Qed.
Theorem Astar_assoc_r :
  forall A1 A2 A3,
  aEntails (Astar (Astar A1 A2) A3) (Astar A1 (Astar A2 A3)).
Proof.
  intros A1 A2 A3 ph pm s g H1 H2 H3.
  by apply sat_star_assoc_r.
Qed.
Theorem Astar_assoc :
  forall A1 A2 A3,
  aEquiv (Astar (Astar A1 A2) A3) (Astar A1 (Astar A2 A3)).
Proof.
  ins. split; [apply Astar_assoc_r|apply Astar_assoc_l].
Qed.

Lemma sat_star_comm :
  forall ph pm s g A1 A2,
  sat ph pm s g (Astar A1 A2) ->
  sat ph pm s g (Astar A2 A1).
Proof.
  intros ph pm s g A1 A2 SAT.
  destruct SAT as (ph1&ph2&D1&H1&pm1&pm2&D2&H2&SAT1&SAT2).
  exists ph2, ph1. repeat split; [phsolve|phsolve|].
  exists pm2, pm1.
  repeat split; auto; [pmclarify; pmsolve|pmclarify; pmsolve].
Qed.
Theorem Astar_comm :
  forall A1 A2, aEntails (Astar A1 A2) (Astar A2 A1).
Proof.
  intros A1 A2 ph pm s g H1 H2 H3.
  by apply sat_star_comm.
Qed.
Theorem Astar_comm_equiv :
  forall A1 A2, aEquiv (Astar A1 A2) (Astar A2 A1).
Proof. ins. split; by apply Astar_comm. Qed.

(** One can always forget about resources. *)

Corollary assn_weaken_r :
  forall A1 A2, aEntails (Astar A1 A2) A2.
Proof.
  intros A1 A2. transitivity (Astar A2 A1).
  apply Astar_comm. apply assn_weaken.
Qed.
Corollary assn_weaken_l :
  forall A1 A2, aEntails (Astar A1 A2) A1.
Proof.
  intros A1 A2. rewrite Astar_comm. by apply assn_weaken_r.
Qed.

(** One can always introduce a [Atrue]. *)

Lemma sat_star_true :
  forall ph pm s g A,
  phValid ph -> pmValid pm ->
  sat ph pm s g A -> sat ph pm s g (Astar A Atrue).
Proof.
  intros ph pm s g A V1 V2 SAT.
  exists ph, phIden. repeat split; auto; [phsolve|].
  exists pm, pmIden. repeat split; auto. pmsolve.
Qed.
Theorem Astar_true :
  forall A, aEntails A (Astar A Atrue).
Proof.
  intros A ph pm s g V1 V2 SAT.
  by apply sat_star_true.
Qed.

(** The following properties allow "swapping" separate resources. *)

Lemma sat_star_swap_l :
  forall ph pm s g A1 A2 A3,
  sat ph pm s g (Astar A1 (Astar A2 A3)) ->
  sat ph pm s g (Astar A2 (Astar A1 A3)).
Proof.
  intros ph pm s g A1 A2 A3 SAT.
  apply sat_star_assoc_r.
  apply sat_star_assoc_l in SAT.
  destruct SAT as (ph1&ph2&D1&H1&pm1&pm2&D2&H2&SAT1&SAT2).
  exists ph1, ph2. repeat split; vauto.
  exists pm1, pm2. repeat split; vauto.
  by apply sat_star_comm.
Qed.
Lemma Astar_swap_l :
  forall A1 A2 A3,
  aEntails (Astar A1 (Astar A2 A3)) (Astar A2 (Astar A1 A3)).
Proof.
  intros A1 A2 A3. rewrite Astar_assoc_l.
  rewrite Astar_comm with (A1:=A1)(A2:=A2).
  by rewrite Astar_assoc_r.
Qed.
Lemma sat_star_swap_r :
  forall ph pm s g A1 A2 A3,
  sat ph pm s g (Astar (Astar A1 A2) A3) ->
  sat ph pm s g (Astar (Astar A1 A3) A2).
Proof.
  intros ph pm s g A1 A2 A3 SAT.
  apply sat_star_assoc_l.
  apply sat_star_assoc_r in SAT.
  destruct SAT as (ph1&ph2&D1&H1&pm1&pm2&D2&H2&SAT1&SAT2).
  exists ph1, ph2. repeat split; vauto.
  exists pm1, pm2. repeat split; vauto.
  by apply sat_star_comm.
Qed.
Lemma Astar_swap_r :
  forall A1 A2 A3,
  aEntails (Astar (Astar A1 A2) A3) (Astar (Astar A1 A3) A2).
Proof.
  intros A1 A2 A3. rewrite Astar_assoc_r.
  rewrite Astar_comm with (A1:=A2)(A2:=A3).
  by rewrite Astar_assoc_l.
Qed.

(** A property that combines logical entailment with
    separating conjunction. *)

Corollary Astar_add_l :
  forall A1 A2 A3,
  aEntails A2 A3 -> aEntails (Astar A1 A2) (Astar A1 A3).
Proof. intros ??? ENT. by rewrite ENT. Qed.
Corollary Astar_add_r :
  forall A1 A2 A3,
  aEntails A2 A3 -> aEntails (Astar A2 A1) (Astar A3 A1).
Proof. intros ??? ENT. by rewrite ENT. Qed.

(** Separating conjunction distributes over disjunction. *)

Lemma Astar_disj_l :
  forall A1 A2 A3,
  aEntails (Astar A1 (Adisj A2 A3)) (Adisj (Astar A1 A2) (Astar A1 A3)).
Proof.
  intros A1 A2 A3 ph pm s g V1 V2.
  intros (ph1&ph2&D1&EQ1&pm1&pm2&D2&EQ2&SAT1&SAT2).
  destruct SAT2 as [SAT2|SAT2].
  - left. exists ph1, ph2. intuition.
    exists pm1, pm2. intuition.
  - right. exists ph1, ph2. intuition.
    exists pm1, pm2. intuition.
Qed.
Lemma Astar_disj_r :
  forall A1 A2 A3,
  aEntails (Adisj (Astar A1 A2) (Astar A1 A3)) (Astar A1 (Adisj A2 A3)).
Proof.
  intros A1 A2 A3 ph pm s g V1 V2 [SAT|SAT];
    destruct SAT as (ph1&ph2&D1&EQ1&pm1&pm2&D2&EQ2&SAT1&SAT2).
  - exists ph1, ph2. intuition.
    exists pm1, pm2. intuition. by left.
  - exists ph1, ph2. intuition.
    exists pm1, pm2. intuition. by right.
Qed.
Lemma Astar_disj :
  forall A1 A2 A3,
  aEquiv (Astar A1 (Adisj A2 A3)) (Adisj (Astar A1 A2) (Astar A1 A3)).
Proof.
  ins. split; [by apply Astar_disj_l|by apply Astar_disj_r].
Qed.


(** *** Iterated separating conjunction *)

(** The following properties cover entailment rules
    with iterated separating conjunctions. *)

(** First, iterated separating conjunctions are insensitive
    to permutation. *)

Theorem Aiter_permut :
  forall xs ys, Permutation xs ys -> aEntails (Aiter xs) (Aiter ys).
Proof.
  intros xs ys H. red. intros ph pm s g Vph Vpm SAT.
  by apply sat_iter_permut with xs.
Qed.
Add Parametric Morphism : Aiter
  with signature @Permutation Assn ==> aEntails
    as Aiter_permut_mor.
Proof. ins. by apply Aiter_permut. Qed.

(** Iterated separating conjunction allows
    "pulling out" the head resource (or unfolding once). *)

Lemma sat_iter_cons_l :
  forall ph pm s g A xs,
  sat ph pm s g (Astar A (Aiter xs)) ->
  sat ph pm s g (Aiter (A :: xs)).
Proof. intuition vauto. Qed.
Theorem Aiter_cons_l :
  forall A xs, aEntails (Astar A (Aiter xs)) (Aiter (A :: xs)).
Proof. intuition vauto. Qed.
Lemma sat_iter_cons_r :
  forall ph pm s g A xs,
  sat ph pm s g (Aiter (A :: xs)) ->
  sat ph pm s g (Astar A (Aiter xs)).
Proof. intuition vauto. Qed.
Theorem Aiter_cons_r :
  forall A xs, aEntails (Aiter (A :: xs)) (Astar A (Aiter xs)).
Proof. intuition vauto. Qed.

(** Two iterated separating conjunctions can be combined
    into a single one. *)

Lemma sat_iter_add_l :
  forall (xs ys : list Assn) ph pm s g,
  sat ph pm s g (Astar (Aiter xs) (Aiter ys)) ->
  sat ph pm s g (Aiter (xs ++ ys)).
Proof.
  induction xs as [|A xs IH]; intros ys ph pm s g SAT.
  - simpl (Aiter []) in SAT. rewrite app_nil_l.
    by apply sat_star_comm, sat_star_weaken in SAT.
  - simpl (Aiter (A :: xs)) in SAT.
    replace ((A :: xs) ++ ys) with (A :: (xs ++ ys)); auto.
    apply sat_iter_cons_l. apply sat_star_assoc_r in SAT.
    destruct SAT as (ph1&ph2&D1&H1&pm1&pm2&D2&H2&SAT1&SAT2).
    exists ph1, ph2. repeat split; vauto.
    exists pm1, pm2. repeat split; vauto.
    by apply IH.
Qed.
Theorem Aiter_add_l :
  forall xs ys,
  aEntails (Astar (Aiter xs) (Aiter ys)) (Aiter (xs ++ ys)).
Proof.
  intros xs ys ph pm s g V1 V2 SAT.
  by apply sat_iter_add_l.
Qed.
Lemma sat_iter_add_r :
  forall (xs ys : list Assn) ph pm s g,
  phValid ph -> pmValid pm ->
  sat ph pm s g (Aiter (xs ++ ys)) ->
  sat ph pm s g (Astar (Aiter xs) (Aiter ys)).
Proof.
  induction xs as [|A xs IH]; intros ys ph pm s g V1 V2 SAT.
  - simpl (Aiter []). rewrite app_nil_l in SAT.
    apply sat_star_comm. by apply sat_star_true.
  - simpl (Aiter (A :: xs)).
    replace ((A :: xs) ++ ys) with (A :: (xs ++ ys)) in SAT; auto.
    apply sat_iter_cons_r in SAT. apply sat_star_assoc_l.
    destruct SAT as (ph1&ph2&D1&H1&pm1&pm2&D2&H2&SAT1&SAT2).
    exists ph1, ph2. repeat split; vauto.
    exists pm1, pm2. repeat split; vauto.
    apply IH; [phsolve|pmsolve|done].
Qed.
Theorem Aiter_add_r :
  forall xs ys,
  aEntails (Aiter (xs ++ ys)) (Astar (Aiter xs) (Aiter ys)).
Proof.
  induction xs as [|A xs IH]; intro ys; simpls.
  rewrite <- Astar_comm.
  by rewrite <- Astar_true.
  rewrite <- Astar_assoc_l.
  by rewrite <- IH.
Qed.

(** Binary separating conjunctions that occur inside
    iterated separating conjuncations can always
    be eliminated (and also introduced). *)

Lemma sat_iter_star_l :
  forall ph pm s g A1 A2 (xs : list Assn),
  sat ph pm s g (Aiter (Astar A1 A2 :: xs)) ->
  sat ph pm s g (Aiter (A1 :: A2 :: xs)).
Proof.
  intros ph pm s g A1 A2 xs SAT.
  simpl (Aiter (A1 :: A2 :: xs)).
  by apply sat_star_assoc_r.
Qed.
Theorem Aiter_star_l :
  forall A1 A2 xs,
  aEntails (Aiter (Astar A1 A2 :: xs)) (Aiter (A1 :: A2 :: xs)).
Proof.
  intros A1 A2 xs. simpls.
  by rewrite Astar_assoc_r.
Qed.
Lemma sat_iter_star_r :
  forall ph pm s g A1 A2 (xs : list Assn),
  sat ph pm s g (Aiter (A1 :: A2 :: xs)) ->
  sat ph pm s g (Aiter (Astar A1 A2 :: xs)).
Proof.
  intros ph pm s g A1 A2 xs SAT.
  simpl (Aiter (A1 :: A2 :: xs)) in SAT.
  by apply sat_star_assoc_l.
Qed.
Theorem Aiter_star_r :
  forall A1 A2 xs,
  aEntails (Aiter (A1 :: A2 :: xs)) (Aiter (Astar A1 A2 :: xs)).
Proof.
  intros A1 A2 xs. simpls.
  by rewrite Astar_assoc_l.
Qed.

(** Iterated resources can always be forgotten. *)

Lemma sat_iter_weaken :
  forall ph pm s g A (xs : list Assn),
  sat ph pm s g (Aiter (A :: xs)) ->
  sat ph pm s g (Aiter xs).
Proof.
  intros ph pm s g A xs SAT.
  simpl (Aiter (A :: xs)) in SAT.
  apply sat_star_weaken with A.
  by apply sat_star_comm.
Qed.
Corollary Aiter_weaken :
  forall A xs,
  aEntails (Aiter (A :: xs)) (Aiter xs).
Proof.
  intros A xs.
  rewrite Aiter_cons_r.
  rewrite Astar_comm.
  by rewrite assn_weaken.
Qed.

(** Iterated heap ownership assertions
    (i.e., [ApointstoIter] and [ApointstoIter_procact])
    are insensitive to permutations, likewise to
    ordinary iterated separating conjunctions. *)

(** Note, some helper lemmas are needed in order to prove this. *)

Lemma sat_iter_In_l {T} (eq_dec : forall x y : T, { x = y } + { x <> y }) :
  forall (xs : list T) ph pm s g (f : T -> Assn)(x : T),
  In x xs ->
  sat ph pm s g (Aiter (map f xs)) ->
  sat ph pm s g (Astar (f x) (Aiter (map f (removeFirst eq_dec x xs)))).
Proof.
  intros xs ph pm s g f x H1 SAT.
  apply Permutation_moveleft with (eq_dec:=eq_dec) in H1.
  apply sat_iter_permut with (ys:=map f (x :: removeFirst eq_dec x xs)) in SAT; auto.
  by apply Permutation_map.
Qed.

Lemma Aiter_In_l {T} (eq_dec : forall x y : T, { x = y } + { x <> y }) :
  forall (xs : list T)(f : T -> Assn)(x : T),
  In x xs ->
  aEntails (Aiter (map f xs)) (Astar (f x) (Aiter (map f (removeFirst eq_dec x xs)))).
Proof.
  intros xs f x H1 ph pm s g V1 V2 SAT.
  by apply sat_iter_In_l.
Qed.

Lemma sat_iter_In_r {T} (eq_dec : forall x y : T, { x = y } + { x <> y }) :
  forall (xs : list T) ph pm s g (f : T -> Assn)(x : T),
  In x xs ->
  sat ph pm s g (Astar (f x) (Aiter (map f (removeFirst eq_dec x xs)))) ->
  sat ph pm s g (Aiter (map f xs)).
Proof.
  intros xs ph pm s g f x H1 SAT.
  apply Permutation_moveleft with (eq_dec:=eq_dec) in H1.
  apply sat_iter_cons_l in SAT.
  apply sat_iter_permut with (ys:=map f xs) in SAT; auto.
  rewrite <- map_cons. apply Permutation_map. by symmetry.
Qed.

Lemma Aiter_In_r {T} (eq_dec : forall x y : T, { x = y } + { x <> y }) :
  forall (xs : list T)(f : T -> Assn)(x : T),
  In x xs ->
  aEntails (Astar (f x) (Aiter (map f (removeFirst eq_dec x xs)))) (Aiter (map f xs)).
Proof.
  intros xs f x H1 ph pm s g V1 V2 SAT.
  by apply sat_iter_In_r in SAT.
Qed.

Lemma sat_ApointstoIter_permut {T} :
  forall (xs ys : list T) ph pm s g (fq : T -> Qc)(f1 f2 : T -> Expr) t,
  Permutation xs ys ->
  sat ph pm s g (Aiter (ApointstoIter xs fq f1 f2 t)) ->
  sat ph pm s g (Aiter (ApointstoIter ys fq f1 f2 t)).
Proof.
  intros xs ys ph pm s g fq f1 f2 t H1 SAT.
  apply sat_iter_permut with (ApointstoIter xs fq f1 f2 t); auto.
  apply map_permut_mor; auto.
Qed.

Lemma sat_procact_iter_permut {T} :
  forall (xs ys : list T) ph pm s g (fq : T -> Qc)(f1 f2 : T -> Expr),
  Permutation xs ys ->
  sat ph pm s g (Aiter (ApointstoIter_procact xs fq f1 f2)) ->
  sat ph pm s g (Aiter (ApointstoIter_procact ys fq f1 f2)).
Proof.
  intros xs ys ph pm s g fq f1 f2 H1 SAT.
  apply sat_iter_permut with (ApointstoIter_procact xs fq f1 f2); auto.
  apply map_permut_mor; auto.
Qed.


(** *** Plain assertions *)

(** _Introduction_ and _elimination_ rules for plain assertions. *)

Theorem Atrue_intro :
  forall A, aEntails A Atrue.
Proof.
  red. simpls.
Qed.

Theorem Afalse_elim :
  forall A1 A2, aEntails A1 Afalse -> aEntails A1 A2.
Proof.
  unfold aEntails.
  intros A1 A2 H1 ph pm s g H2 H3 H4.
  apply H1 in H4; vauto.
Qed.

Lemma assn_plain_tauto :
  forall E,
  aEntails (Aplain (Beq E E)) Atrue /\
  aEntails Atrue (Aplain (Beq E E)).
Proof.
  intros E. split.
  - red. ins.
  - red. ins. desf.
Qed.

Lemma Aplain_equiv :
  forall B1 B2,
  aEquiv (Aplain B1) (Aplain B2) <->
  forall s, cond_eval B1 s = cond_eval B2 s.
Proof.
  intros B1 B2. split; intro H1.
  (* left-to-right *)
  - intro s. red in H1.
    destruct H1 as (H1&H2).
    red in H1. red in H2.
    specialize H1 with phIden pmIden s s.
    specialize H2 with phIden pmIden s s. simpls.
    assert (H3 : cond_eval B1 s = true \/ cond_eval B1 s = false)
      by apply cond_eval_excl.
    destruct H3 as [H3|H3]; vauto.
    (* case [cond_eval B1 s = true] *)
    + symmetry. apply H1; vauto.
    (* case [cond_eval B1 s = false] *)
    + assert (H4 : cond_eval B2 s = true \/ cond_eval B2 s = false)
        by apply cond_eval_excl.
      destruct H4 as [H4|H4]; vauto.
      by apply H2.
  (* right-to-left *)
  - split.
    (* [Aplain B1] entails [Aplain B2] *)
    + intros ph pm s g H2 H3 H4. simpls.
      by rewrite <- H1.
    (* [Aplain B2] entails [Aplain B1] *)
    + intros ph pm s g H2 H3 H4. simpls.
      by rewrite H1.
Qed.


(** *** Existential quantifiers *)

(** Introduction rule for existential quantification. *)

Theorem Aexists_intro :
  forall A1 A2 x v,
  aEntails A1 (assn_subst x (Econst v) A2) ->
  aEntails A1 (Aexists x A2).
Proof.
  intros A1 A2 x v H ph pm s g H1 H2 H3.
  exists v. by apply H.
Qed.


(** *** Disjunction *)

(** Standard elimination rules for disjunction. *)

Lemma sat_elim_l :
  forall ph pm s g A1 A2,
  sat ph pm s g A1 ->
  sat ph pm s g (Adisj A1 A2).
Proof.
  intros ph pm s g A1 A2 SAT. simpl. by left.
Qed.
Lemma sat_elim_r :
  forall ph pm s g A1 A2,
  sat ph pm s g A2 ->
  sat ph pm s g (Adisj A1 A2).
Proof.
  intros ph pm s g A1 A2 SAT. simpl. by right.
Qed.

Theorem Adisj_elim_l :
  forall A A1 A2,
  aEntails A A1 ->
  aEntails A (Adisj A1 A2).
Proof.
  intros A A1 A2 H ph pm s g V1 V2 SAT.
  by apply sat_elim_l, H.
Qed.
Theorem Adisj_elim_r :
  forall A A1 A2,
  aEntails A A2 ->
  aEntails A (Adisj A1 A2).
Proof.
  intros A A1 A2 H ph pm s g V1 V2 SAT.
  by apply sat_elim_r, H.
Qed.

(** Disjunction is idempotent. *)

Lemma Adisj_idemp :
  forall A,
  aEntails A (Adisj A A) /\ aEntails (Adisj A A) A.
Proof.
  intro A. split; ins; vauto. red. ins. desf.
Qed.


(** *** Magic wand *)

(** Introduction and elimination rules for magic wands. *)

Theorem Awand_intro :
  forall A1 A2 A3,
  aEntails (Astar A1 A2) A3 -> aEntails A1 (Awand A2 A3).
Proof.
  intros A1 A2 A3 H1 ph pm s g H2 H3 H4 ph' pm' H5 H6 H7.
  apply H1; auto.
  exists ph, ph'. intuition.
  exists pm, pm'. intuition.
Qed.

Theorem Awand_elim :
  forall A1 A2 A A',
  aEntails A1 (Awand A A') ->
  aEntails A2 A ->
  aEntails (Astar A1 A2) A'.
Proof.
  intros A1 A2 A A' H1 H2 ph pm s g H3 H4 H5.
  simpl in H5.
  destruct H5 as (ph1&ph2&D1&D2&pm1&pm2&D3&D4&D5&D6).
  clarify. pmclarify.
  apply H1; auto; [phsolve|pmsolve|].
  apply H2; auto; [phsolve|pmsolve].
Qed.


(** *** Heap ownership predicates *)

(** The following rules cover points-to assertions. *)

(** Heap ownership predicates with invalid
    fractional permissions are meaningless. *)


Theorem Apointsto_valid :
  forall t q E1 E2,
  ~ perm_valid q -> aEntails (Apointsto t q E1 E2) Afalse.
Proof.
  intros t q E1 E2 H1 ph pm s g H2 H3 H4.
  simpl. simpl in H4. repeat desf.
Qed.

Lemma Apointsto_entire :
  forall ph pm s g t E1 E2,
  phValid ph ->
  sat ph pm s g (Apointsto t 1 E1 E2) ->
  phcEntire (ph (expr_eval E1 s)).
Proof.
  intros ph pm s g t E1 E2 H1 SAT.
  destruct t.
  (* standard points-to predicate *)
  - unfold sat in SAT. destruct SAT as (_&SAT).
    apply phcLe_entire_eq in SAT; vauto.
    rewrite <- SAT. vauto.
  (* process points-to predicate *)
  - unfold sat in SAT. destruct SAT as (_&SAT).
    apply phcLe_entire_eq in SAT; vauto.
    rewrite <- SAT. vauto.
  (* standard points-to predicate *)
  - unfold sat in SAT. destruct SAT as (_&SAT).
    destruct SAT as (v'&SAT).
    apply phcLe_entire_eq in SAT; vauto.
    rewrite <- SAT. vauto.
Qed.

Lemma ApointstoIter_perm_full {T} :
  forall (xs : list T)(fq : T -> Qc)(f1 f2 : T -> Expr)(l : Val) ph pm s g t,
    (forall x : T, In x xs -> fq x = 1) ->
  sat ph pm s g (Aiter (ApointstoIter xs fq f1 f2 t)) ->
  In l (map (expr_eval_map f1 s) xs) ->
  phcEntire (ph l).
Proof.
  induction xs as [|x xs IH]. vauto.
  intros fq f1 f2 l ph pm s g t H1 SAT H2.
  destruct SAT as (ph1&ph2&D1&H3&pm1&pm2&D2&H4&SAT1&SAT2).
  rewrite map_cons in H2. simpl in H2. destruct H2 as [H2|H2].
  - rewrite H1 in SAT1; vauto.
    apply Apointsto_entire in SAT1; [phsolve|phsolve].
  - apply IH with (l:=l) in SAT2; auto; [phcsolve|].
    intros y H5. apply H1. vauto.
Qed.

(** Heap ownership predicates of different types cannot coexist
    if they target the same heap location. *)

Lemma Apointsto_diff :
  forall q1 q2 E1 E2 t1 t2,
  t1 <> t2 ->
  aEntails (Astar (Apointsto t1 q1 E1 E2) (Apointsto t2 q2 E1 E2)) Afalse.
Proof.
  intros q1 q2 E1 E2 t1 t2 H1 ph pm s g V1 V2 SAT.
  destruct SAT as (ph1&ph2&D1&EQ1&pm1&pm2&D2&EQ2&SAT1&SAT2).
  clarify. red in D1. red in D1.
  specialize D1 with (expr_eval E1 s).
  simpls. desf; intuition desf.
Qed.

(** Heap ownership predicates may be _split_. *)

Lemma Apointsto_split_std :
  forall q1 q2 E1 E2,
  perm_disj q1 q2 ->
  aEntails
    (Apointsto PTTstd (q1 + q2) E1 E2)
    (Astar (Apointsto PTTstd q1 E1 E2) (Apointsto PTTstd q2 E1 E2)).
Proof.
  intros q1 q2 E1 E2 H1 ph pm s g H2 H3 H4.
  unfold sat in *. destruct H4 as (H4'&H4).
  pose (v:=expr_eval E2 s).
  assert (H5 : phcUnion (PHCstd q1 v) (PHCstd q2 v) = PHCstd (q1 + q2) v). {
    unfold phcUnion. desf. }
  assert (H6 : phcDisj (PHCstd q1 v) (PHCstd q2 v)). {
    red. intuition. }
  subst v. rewrite <- H5 in H4. clear H5.
  apply phcLe_diff in H4; vauto; [|phcsolve].
  destruct H4 as (phc&H4&H5).
  pose (l:=expr_eval E1 s).
  pose (v:=expr_eval E2 s).
  exists (phUpdate ph l (PHCstd q1 v)).
  exists (phUpdate phIden l (phcUnion (PHCstd q2 v) phc)).
  repeat split; auto; [phsolve| |].
  - extensionality l'. unfold phUnion, phUpdate, update.
    desf; [|phcsolve]. by rewrite phcUnion_assoc.
  - exists pmIden, pm. split; [pmsolve|].
    split; [by rewrite pmUnion_iden_r|]. split.
    + split; [permsolve|].
      unfold phUpdate, update. desf.
    + split; [permsolve|].
      unfold phUpdate, update, phIden. desf.
      apply phcLe_mono_pos.
      by apply phcDisj_union_l with (PHCstd q1 v).
Qed.

Lemma Apointsto_split_proc :
  forall q1 q2 E1 E2,
  perm_disj q1 q2 ->
  aEntails
    (Apointsto PTTproc (q1 + q2) E1 E2)
    (Astar (Apointsto PTTproc q1 E1 E2) (Apointsto PTTproc q2 E1 E2)).
Proof.
  intros q1 q2 E1 E2 H1 ph pm s g H2 H3 H4.
  unfold sat in *. destruct H4 as (H4'&H4).
  pose (v:=expr_eval E2 s).
  assert (H5 : phcUnion (PHCproc q1 v) (PHCproc q2 v) = PHCproc (q1 + q2) v). {
    unfold phcUnion. desf. }
  assert (H6 : phcDisj (PHCproc q1 v) (PHCproc q2 v)). {
    red. intuition. }
  subst v. rewrite <- H5 in H4. clear H5.
  apply phcLe_diff in H4; vauto; [|phcsolve].
  destruct H4 as (phc&H4&H5).
  pose (l:=expr_eval E1 s).
  pose (v:=expr_eval E2 s).
  exists (phUpdate ph l (PHCproc q1 v)).
  exists (phUpdate phIden l (phcUnion (PHCproc q2 v) phc)).
  repeat split; vauto; [phsolve| |].
  - extensionality l'. unfold phUnion, phUpdate, update.
    desf; [|phcsolve]. by rewrite phcUnion_assoc.
  - exists pmIden, pm.
    split; [phsolve|].
    split; [by rewrite pmUnion_iden_r|]. split.
    + split; [permsolve|].
      unfold phUpdate, update. desf.
    + split; [permsolve|].
      unfold phUpdate, update, phIden. desf.
      apply phcLe_mono_pos.
      by apply phcDisj_union_l with (PHCproc q1 v).
Qed.

Lemma Apointsto_split_act :
  forall q1 q2 E1 E2,
  perm_disj q1 q2 ->
  aEntails
    (Apointsto PTTact (q1 + q2) E1 E2)
    (Astar (Apointsto PTTact q1 E1 E2) (Apointsto PTTact q2 E1 E2)).
Proof.
  intros q1 q2 E1 E2 H1 ph pm s g H2 H3 H4.
  unfold sat in *. destruct H4 as (H4'&H4).
  destruct H4 as (v'&H4).
  pose (v:=expr_eval E2 s).
  assert (H5 : phcUnion (PHCact q1 v v') (PHCact q2 v v') = PHCact (q1 + q2) v v'). {
    unfold phcUnion. desf. }
  assert (H6 : phcDisj (PHCact q1 v v') (PHCact q2 v v')). {
    red. intuition. }
  subst v. rewrite <- H5 in H4. clear H5.
  apply phcLe_diff in H4; vauto; [|phcsolve].
  destruct H4 as (phc&H4&H5).
  pose (l:=expr_eval E1 s).
  pose (v:=expr_eval E2 s).
  exists (phUpdate ph l (PHCact q1 v v')).
  exists (phUpdate phIden l (phcUnion (PHCact q2 v v') phc)).
  repeat split; vauto; [phsolve| |].
  - extensionality l'.
    unfold phUnion, phUpdate, update.
    desf; [|phcsolve]. by rewrite phcUnion_assoc.
  - exists pmIden, pm.
    split; [pmsolve|].
    split; [by rewrite pmUnion_iden_r|]. split.
    + split; [permsolve|].
      exists v'. unfold phUpdate, update. desf.
    + split; [permsolve|].
      exists v'. unfold phUpdate, update, phIden.
      desf. apply phcLe_mono_pos.
      by apply phcDisj_union_l with (PHCact q1 v v').
Qed.

Theorem Apointsto_split :
  forall q1 q2 E1 E2 t,
  perm_disj q1 q2 ->
  aEntails
    (Apointsto t (q1 + q2) E1 E2)
    (Astar (Apointsto t q1 E1 E2) (Apointsto t q2 E1 E2)).
Proof.
  intros q1 q2 E1 E2 t H. destruct t.
  - by apply Apointsto_split_std.
  - by apply Apointsto_split_proc.
  - by apply Apointsto_split_act.
Qed.

(** Heap ownership predicates may be merged. *)

Lemma Apointsto_merge_std :
  forall q1 q2 E1 E2,
  perm_disj q1 q2 ->
  aEntails
    (Astar (Apointsto PTTstd q1 E1 E2) (Apointsto PTTstd q2 E1 E2))
    (Apointsto PTTstd (q1 + q2) E1 E2).
Proof.
  unfold aEntails.
  intros q1 q2 E1 E2 D1 ph pm s g V1 V2 SAT.
  unfold sat in *.
  destruct SAT as (ph1&ph2&D2&H1&pm1&pm2&D3&H2&(V3&LE1)&(V4&LE2)).
  clarify. rewrite <- phUnion_cell.
  pose (v:=expr_eval E2 s).
  assert (H6 : PHCstd (q1 + q2) v = phcUnion (PHCstd q1 v) (PHCstd q2 v)). {
    unfold phcUnion. desf. }
  subst v. rewrite H6. split; [permsolve|].
  apply phcLe_compat; vauto.
  apply phcLe_diff in LE1; auto.
  - destruct LE1 as (phc&D4&H3).
    apply phcDisj_union_l with phc; auto; [phcsolve|].
    rewrite phcUnion_comm. by rewrite H3.
  - by apply phDisj_valid_l in D2.
Qed.

Lemma Apointsto_merge_proc :
  forall q1 q2 E1 E2,
  perm_disj q1 q2 ->
  aEntails
    (Astar (Apointsto PTTproc q1 E1 E2) (Apointsto PTTproc q2 E1 E2))
    (Apointsto PTTproc (q1 + q2) E1 E2).
Proof.
  unfold aEntails.
  intros q1 q2 E1 E2 D1 ph pm s g V1 V2 SAT.
  unfold sat in *.
  destruct SAT as (ph1&ph2&D2&H1&pm1&pm2&D3&H2&(V3&LE1)&(V4&LE2)).
  clarify. rewrite <- phUnion_cell.
  pose (v:=expr_eval E2 s).
  assert (H6 : PHCproc (q1 + q2) v = phcUnion (PHCproc q1 v) (PHCproc q2 v)). {
    unfold phcUnion. desf. }
  subst v. rewrite H6. split; [permsolve|].
  apply phcLe_compat; vauto.
  apply phcLe_diff in LE1; auto.
  - destruct LE1 as (phc&D4&H3).
    apply phcDisj_union_l with phc; auto; [phcsolve|].
    rewrite phcUnion_comm. by rewrite H3.
  - by apply phDisj_valid_l in D2.
Qed.

Lemma Apointsto_merge_act :
  forall q1 q2 E1 E2,
  perm_disj q1 q2 ->
  aEntails
    (Astar (Apointsto PTTact q1 E1 E2) (Apointsto PTTact q2 E1 E2))
    (Apointsto PTTact (q1 + q2) E1 E2).
Proof.
  unfold aEntails.
  intros q1 q2 E1 E2 D1 ph pm s g V1 V2 SAT.
  unfold sat in *.
  destruct SAT as (ph1&ph2&D2&H1&pm1&pm2&D3&H2&(V3&LE1)&(V4&LE2)).
  clarify. rewrite <- phUnion_cell.
  destruct LE1 as (v1&LE1).
  destruct LE2 as (v2&LE2).
  assert (H3 : v1 = v2). {
  red in D2. red in D2. unfold phcDisj in D2.
  specialize D2 with (expr_eval E1 s).
  unfold phcLe in LE1, LE2. repeat desf. }
  split; [permsolve|]. clarify. exists v2.
  pose (v:=expr_eval E2 s).
  assert (H6 : PHCact (q1 + q2) v v2 = phcUnion (PHCact q1 v v2) (PHCact q2 v v2)). {
    unfold phcUnion. desf. }
  subst v. rewrite H6.
  apply phcLe_compat; vauto.
  apply phcLe_diff in LE1; auto.
  - destruct LE1 as (phc&D4&H3).
    apply phcDisj_union_l with phc; auto; [phcsolve|].
    rewrite phcUnion_comm. by rewrite H3.
  - by apply phDisj_valid_l in D2.
Qed.

Theorem Apointsto_merge :
  forall q1 q2 E1 E2 t,
  perm_disj q1 q2 ->
  aEntails
    (Astar (Apointsto t q1 E1 E2) (Apointsto t q2 E1 E2))
    (Apointsto t (q1 + q2) E1 E2).
Proof.
  intros q1 q2 E1 E2 t H1. destruct t.
  - by apply Apointsto_merge_std.
  - by apply Apointsto_merge_proc.
  - by apply Apointsto_merge_act.
Qed.

(** Below are the rules for 'process-action' ownership predicates,
    which allow using such predicates as abbreviations
    for process- and action ownership predicates *)

Lemma assn_proc_procact_l :
  forall q E1 E2,
  q <> 1 ->
  aEntails (Apointsto_procact q E1 E2) (Apointsto PTTproc q E1 E2).
Proof.
  intros q E1 E2 H1 ph pm s g V1 V2 SAT.
  unfold Apointsto_procact in SAT. desf.
Qed.
Lemma assn_proc_procact_r :
  forall q E1 E2,
  q <> 1 ->
  aEntails (Apointsto PTTproc q E1 E2) (Apointsto_procact q E1 E2).
Proof.
  intros q E1 E2 H1 ph pm s g V1 V2 SAT.
  unfold Apointsto_procact. desf.
Qed.
Lemma assn_act_procact_l :
  forall E1 E2,
  aEntails (Apointsto_procact 1 E1 E2) (Apointsto PTTact 1 E1 E2).
Proof.
  intros E1 E2 ph pm s g V1 V2 SAT.
  unfold Apointsto_procact in SAT. desf.
Qed.
Lemma assn_act_procact_r :
  forall E1 E2,
  aEntails (Apointsto PTTact 1 E1 E2) (Apointsto_procact 1 E1 E2).
Proof.
  intros E1 E2 ph pm s g V1 V2 SAT.
  unfold Apointsto_procact. desf.
Qed.

Lemma Aiter_proc_procact_l {T} :
  forall (xs : list T)(f1 f2 : T -> Expr)(fq : T -> Qc),
    (forall x : T, In x xs -> fq x <> 1) ->
  aEntails (Aiter (ApointstoIter_procact xs fq f1 f2)) (Aiter (ApointstoIter xs fq f1 f2 PTTproc)).
Proof.
  induction xs as [|x xs IH]. vauto.
  intros f1 f2 fq H1 ph pm s g V1 V2 SAT.
  destruct SAT as (ph1&ph2&D1&H2&pm1&pm2&D2&H3&SAT1&SAT2). vauto.
  exists ph1, ph2. intuition vauto.
  exists pm1, pm2. intuition vauto.
  - apply assn_proc_procact_l; auto; [|phsolve|pmsolve].
    intro H2. apply H1 with x; vauto.
  - apply IH; vauto; [|phsolve|pmsolve].
    intros y H2 H4. apply H1 with y; vauto.
Qed.
Lemma Aiter_proc_procact_r {T} :
  forall (xs : list T)(f1 f2 : T -> Expr)(fq : T -> Qc),
    (forall x : T, In x xs -> fq x <> 1) ->
  aEntails (Aiter (ApointstoIter xs fq f1 f2 PTTproc)) (Aiter (ApointstoIter_procact xs fq f1 f2)).
Proof.
  induction xs as [|x xs IH]. vauto.
  intros f1 f2 fq H1 ph pm s g V1 V2 SAT.
  destruct SAT as (ph1&ph2&D1&H2&pm1&pm2&D2&H3&SAT1&SAT2). vauto.
  exists ph1, ph2. intuition vauto.
  exists pm1, pm2. intuition vauto.
  - apply assn_proc_procact_r; auto; [|phsolve|pmsolve].
    intro H2. apply H1 with x; vauto.
  - apply IH; vauto; [|phsolve|pmsolve].
    intros y H2 H4. apply H1 with y; vauto.
Qed.
Lemma Aiter_act_procact_l {T} :
  forall (xs : list T)(f1 f2 : T -> Expr)(fq : T -> Qc),
    (forall x : T, In x xs -> fq x = 1) ->
  aEntails (Aiter (ApointstoIter_procact xs fq f1 f2)) (Aiter (ApointstoIter xs fq f1 f2 PTTact)).
Proof.
  induction xs as [|x xs IH]. vauto.
  intros f1 f2 fq H1 ph pm s g V1 V2 SAT.
  destruct SAT as (ph1&ph2&D1&H2&pm1&pm2&D2&H3&SAT1&SAT2). vauto.
  exists ph1, ph2. intuition vauto.
  exists pm1, pm2. intuition vauto.
  - rewrite H1; vauto. apply assn_act_procact_l; auto.
    + phsolve.
    + pmsolve.
    + rewrite <- H1 with x; vauto.
  - apply IH; vauto.
    + intros y H2. apply H1. vauto.
    + phsolve.
    + pmsolve.
Qed.
Lemma Aiter_act_procact_r {T} :
  forall (xs : list T)(f1 f2 : T -> Expr)(fq : T -> Qc),
    (forall x : T, In x xs -> fq x = 1) ->
  aEntails (Aiter (ApointstoIter xs fq f1 f2 PTTact)) (Aiter (ApointstoIter_procact xs fq f1 f2)).
Proof.
  induction xs as [|x xs IH]. vauto.
  intros f1 f2 fq H1 ph pm s g V1 V2 SAT.
  destruct SAT as (ph1&ph2&D1&H2&pm1&pm2&D2&H3&SAT1&SAT2). vauto.
  exists ph1, ph2. intuition vauto.
  exists pm1, pm2. intuition vauto.
  - rewrite H1; vauto. apply assn_act_procact_r; auto.
    + phsolve.
    + pmsolve.
    + rewrite <- H1 with x; vauto.
  - apply IH; vauto.
    + intros y H2. apply H1. vauto.
    + phsolve.
    + pmsolve.
Qed.

Theorem ApointstoIter_procact_split {T} :
  forall (xs ys : list T)(f1 f2 : T -> Expr)(fq : T -> Qc),
    (forall x : T, In x xs -> fq x <> 1) ->
    (forall x : T, In x ys -> fq x = 1) ->
  aEntails
    (Aiter (ApointstoIter_procact (xs ++ ys) fq f1 f2))
    (Astar (Aiter (ApointstoIter xs fq f1 f2 PTTproc)) (Aiter (ApointstoIter ys fq f1 f2 PTTact))).
Proof.
  intros xs ys f1 f2 q1 H1 H2 ph pm s g V1 V2 SAT.
  rewrite <- ApointstoIter_procact_app in SAT.
  apply Aiter_add_r in SAT; auto.
  destruct SAT as (ph1&ph2&D1&H3&pm1&pm2&D2&H4&SAT1&SAT2).
  exists ph1, ph2. intuition vauto.
  exists pm1, pm2. intuition vauto.
  - apply Aiter_proc_procact_l; auto.
    + phsolve.
    + pmsolve.
  - apply Aiter_act_procact_l; auto.
    + phsolve.
    + pmsolve.
Qed.

Theorem ApointstoIter_procact_merge {T} :
  forall (xs ys : list T)(f1 f2 : T -> Expr)(fq : T -> Qc),
    (forall x : T, In x xs -> fq x <> 1) ->
    (forall x : T, In x ys -> fq x = 1) ->
  aEntails
    (Astar (Aiter (ApointstoIter xs fq f1 f2 PTTproc)) (Aiter (ApointstoIter ys fq f1 f2 PTTact)))
    (Aiter (ApointstoIter_procact (xs ++ ys) fq f1 f2)).
Proof.
  intros xs ys f1 f2 q1 H1 H2 ph pm s g V1 V2 SAT.
  destruct SAT as (ph1&ph2&D1&H3&pm1&pm2&D2&H4&SAT1&SAT2).
  rewrite <- ApointstoIter_procact_app.
  apply Aiter_add_l; auto.
  exists ph1, ph2. intuition vauto.
  exists pm1, pm2. intuition vauto.
  - apply Aiter_proc_procact_r; auto.
    + phsolve.
    + pmsolve.
  - apply Aiter_act_procact_r; auto.
    + phsolve.
    + pmsolve.
Qed.

Corollary ApointstoIter_procact_partition {T} :
  forall (xs ys1 ys2 : list T)(f1 f2 : T -> Expr)(fq : T -> Qc),
  let f := fun x : T => if Qc_eq_dec (fq x) 1 then false else true in
  partition f xs = (ys1, ys2) ->
  aEntails
    (Aiter (ApointstoIter_procact xs fq f1 f2))
    (Astar (Aiter (ApointstoIter ys1 fq f1 f2 PTTproc)) (Aiter (ApointstoIter ys2 fq f1 f2 PTTact))).
Proof.
  intros xs ys1 ys2 f1 f2 fq f H1 ph pm s g V1 V2 SAT.
  assert (H2 : Permutation xs (ys1 ++ ys2)). {
    by apply partition_permut with f. }
  apply sat_procact_iter_permut with (ys:=ys1 ++ ys2) in SAT; vauto.
  apply ApointstoIter_procact_split; vauto.
  - intros x H3. apply partition_f_left with (x0:=x) in H1; auto.
    subst f. simpl in H1. desf.
  - intros x H3. apply partition_f_right with (x0:=x) in H1; auto.
    subst f. simpl in H1. desf.
Qed.


(** *** Process ownership predicates *)

(** Process ownership predicates with invalid
    fractional permissions are meaningless. *)

Theorem assn_proc_valid :
  forall x q P xs f,
  ~ perm_valid q -> aEntails (Aproc x q P xs f) Afalse.
Proof.
  intros x q P xs f H1 ph pm s g H2 H3 H4.
  unfold sat in H4.
  destruct H4 as (c'&H4&H5).
  apply pmeDisj_valid_l in H4.
  simpl in H4. contradiction.
Qed.

(** Processes may always be replaced by bisimilar ones. *)

Theorem assn_proc :
  forall P1 P2 x q xs f,
  hbisim P1 P2 ->
  aEntails (Aproc x q P1 xs f) (Aproc x q P2 xs f).
Proof.
  intros P1 P2 x q xs f H ph pm s g H2 H3 H4.
  unfold sat in *.
  destruct H4 as (pmv&H4&H5).
  exists pmv. intuition.
  pose (F:=expr_eval_map f s).
  pose (P':=pDehybridise P1 s).
  transitivity (pmeUnion (PEelem q P' xs F) pmv); auto.
  subst F P'. by rewrite <- H5, <- H.
Qed.

(** Processes ownership may always be split. *)

Theorem assn_proc_split :
  forall q1 q2 x P1 P2 xs f,
  perm_disj q1 q2 ->
  aEntails
    (Aproc x (q1 + q2) (HPpar P1 P2) xs f)
    (Astar (Aproc x q1 P1 xs f) (Aproc x q2 P2 xs f)).
Proof.
  intros q1 q2 x P1 P2 xs f H1 ph pm s g H2 H3 H4.
  unfold sat in H4.
  destruct H4 as (pmv&H4&H5).
  exists phIden, ph. intuition; [phsolve|].
  exists (pmUpdate pmIden (g x) (PEelem q1 (pDehybridise P1 s) xs (expr_eval_map f s))).
  exists (pmUpdate pm (g x) (pmeUnion (PEelem q2 (pDehybridise P2 s) xs (expr_eval_map f s)) pmv)).
  intuition vauto. 
  - apply pmDisj_upd; auto. 
    apply pmeDisj_assoc_l; auto.
    + pmsolve.
    + unfold pmeUnion. desf.
  - intro pid.
    unfold pmUnion, pmUpdate, update.
    destruct (val_eq_dec (g x) pid); vauto.
    + rewrite H5. rewrite <- pmeUnion_assoc.
      unfold pmeUnion. desf.
    + pmesolve.
  - exists PEfree. intuition clarify.
    + apply pmeDisj_free_l.
      unfold pmeValid.
      by apply perm_disj_valid_l in H1.
    + unfold pmUpdate, update. desf.
  - exists pmv. intuition clarify.
    apply pmeDisj_union_l with (PEelem q1 (pDehybridise P1 s) xs (expr_eval_map f s)).
    + unfold pmeDisj. intuition vauto.
    + unfold pmeUnion. desf.
    + unfold pmUpdate, update. desf.
Qed.

(** Processes ownership may always be merged. *)

Theorem assn_proc_merge :
  forall q1 q2 x P1 P2 xs f,
  perm_disj q1 q2 ->
  aEntails
    (Astar (Aproc x q1 P1 xs f) (Aproc x q2 P2 xs f))
    (Aproc x (q1 + q2) (HPpar P1 P2) xs f).
Proof.
  intros q1 q2 x P1 P2 xs f H1 ph pm s g H2 H3 H4.
  unfold sat in H4.
  destruct H4 as (ph1&ph2&D1&H4&pm1&pm2&D2&H5&SAT1&SAT2).
  destruct SAT1 as (pmv1&S1&S2).
  destruct SAT2 as (pmv2&S3&S4).
  exists (pmeUnion pmv1 pmv2).
  intuition clarify.
  - simpl (pDehybridise (HPpar P1 P2) s).
    rewrite <- pmeUnion_elem.
    apply pmeDisj_compat; vauto.
    rewrite <- S2, <- S4.
    by apply D2.
  - simpl (pDehybridise (HPpar P1 P2) s).
    rewrite <- pmeUnion_elem.
    rewrite pmeUnion_compat.
    rewrite <- S2, <- S4.
    rewrite pmUnion_elem.
    by rewrite <- H5.
Qed.

(** One can always dispose of parts of an abstraction. *)

Theorem assn_proc_weaken :
  forall q1 q2 x P1 P2 xs f,
  perm_disj q1 q2 ->
  aEntails
    (Aproc x (q1 + q2) (HPpar P1 P2) xs f)
    (Aproc x q1 P1 xs f).
Proof.
  intros q1 q2 x P1 P2 xs f H.
  transitivity (Astar (Aproc x q1 P1 xs f) (Aproc x q2 P2 xs f)).
  by apply assn_proc_split.
  apply assn_weaken.
Qed.


(** *** Bisimilarity *)

(** Any bisimilarity from [hbisim] can be introduced via [Abisim]. *)

Theorem aBisim_hbisim :
  forall P Q, hbisim P Q -> aEntails Atrue (Abisim P Q).
Proof. intros P Q H1 ph pm s g H2 H3 H4. vauto. Qed.

(** Bisimilarity is an equivalence relation
    with respect to separating conjunction and entailment. *)

Theorem aBisim_refl :
  forall P, aEntails Atrue (Abisim P P).
Proof. intros. by apply aBisim_hbisim. Qed.
Theorem aBisim_symm :
  forall P Q, aEntails (Abisim P Q) (Abisim Q P).
Proof. intros. red. intros. simpls. by symmetry. Qed.
Theorem aBisim_trans :
  forall P Q R, aEntails (Astar (Abisim P Q) (Abisim Q R)) (Abisim P R).
Proof.
  intros P Q R. red. intros ph pm s g H1 H2 H3. simpls.
  destruct H3 as (ph1&ph2&D1&D2&pm1&pm2&D3&D4&D5&D6).
  clarify. by transitivity (pDehybridise Q s).
Qed.

(** Bisimilarity is a congruence for all connectives. *)

Theorem aBisim_seq :
  forall P1 P2 Q1 Q2,
  aEntails (Astar (Abisim P1 P2) (Abisim Q1 Q2)) (Abisim (HPseq P1 Q1) (HPseq P2 Q2)).
Proof.
  intros P1 P2 Q1 Q2. red.
  intros ph pm s g H1 H2 H3. simpl in H3.
  destruct H3 as (ph1&ph2&D1&D2&pm1&pm2&D3&D4&D5&D6).
  clarify. simpl. apply bisim_seq; auto.
Qed.

Theorem aBisim_alt :
  forall P1 P2 Q1 Q2,
  aEntails (Astar (Abisim P1 P2) (Abisim Q1 Q2)) (Abisim (HPalt P1 Q1) (HPalt P2 Q2)).
Proof.
  intros P1 P2 Q1 Q2. red.
  intros ph pm s g H1 H2 H3. simpl in H3.
  destruct H3 as (ph1&ph2&D1&D2&pm1&pm2&D3&D4&D5&D6).
  clarify. simpl. apply bisim_alt; auto.
Qed.

Theorem aBisim_par :
  forall P1 P2 Q1 Q2,
  aEntails (Astar (Abisim P1 P2) (Abisim Q1 Q2)) (Abisim (HPpar P1 Q1) (HPpar P2 Q2)).
Proof.
  intros P1 P2 Q1 Q2. red.
  intros ph pm s g H1 H2 H3. simpl in H3.
  destruct H3 as (ph1&ph2&D1&D2&pm1&pm2&D3&D4&D5&D6).
  clarify. simpl. apply bisim_par; auto.
Qed.

Theorem aBisim_lmerge :
  forall P1 P2 Q1 Q2,
  aEntails (Astar (Abisim P1 P2) (Abisim Q1 Q2)) (Abisim (HPlmerge P1 Q1) (HPlmerge P2 Q2)).
Proof.
  intros P1 P2 Q1 Q2. red.
  intros ph pm s g H1 H2 H3. simpl in H3.
  destruct H3 as (ph1&ph2&D1&D2&pm1&pm2&D3&D4&D5&D6).
  clarify. simpl. apply bisim_lmerge; auto.
Qed.

Theorem aBisim_sum :
  forall P Q x,
  ~ hproc_fv P x ->
  ~ hproc_fv Q x ->
  aEntails (Abisim P Q) (Abisim (HPsigma x P) (HPsigma x Q)).
Proof.
  intros P Q x H1 H2. red. intros ph pm s g H3 H4 H5.
  simpl in H5. simpl. apply bisim_sum.
  red. red. intro v. by repeat rewrite hproc_subst_pres.
Qed.

Corollary aBisim_sum_alt :
  forall x E P,
  aEntails Atrue (Abisim (HPsigma x P) (HPalt (hproc_subst x E P) (HPsigma x P))).
Proof.
  intros x E P. apply aBisim_hbisim.
  by apply hbisim_sigma_alt.
Qed.

Theorem aBisim_cond :
  forall P Q B1 B2,
  aEquiv (Aplain B1) (Aplain B2) ->
  aEntails (Abisim P Q) (Abisim (HPcond B1 P) (HPcond B2 Q)).
Proof.
  intros P Q B1 B2 H1 ph pm s g H2 H3 H4.
  simpls. rewrite H4. clear H4.
  rewrite Aplain_equiv in H1.
  by rewrite H1.
Qed.

Theorem aBisim_cond_true :
  forall B1 B2 P,
  aEntails (Aplain B1) (Aplain B2) ->
  aEntails (Aplain B1) (Abisim (HPcond B2 P) P).
Proof.
  intros B1 B2 P H1 ph pm s g H2 H3 H4.
  simpls. red in H1.
  apply H1 with ph pm s g in H4; vauto.
  clear H1. simpl in H4. rewrite H4.
  clear H4. by apply bisim_cond_true.
Qed.

Theorem aBisim_cond_false :
  forall B1 B2 P,
  aEntails (Aplain B1) (Aplain B2) ->
  aEntails (Aplain B1) (Abisim (HPcond (Bnot B2) P) HPdelta).
Proof.
  intros B1 B2 P H1 ph pm s g H2 H3 H4.
  simpls. red in H1.
  apply H1 with ph pm s g in H4; vauto.
  clear H1. simpl in H4. rewrite H4.
  clear H4. simpl. by apply bisim_cond_false.
Qed.

Theorem aBisim_iter :
  forall P Q,
  aEntails (Abisim P Q) (Abisim (HPiter P) (HPiter Q)).
Proof.
  intros P Q. red. intros ph pm s g H1 H2 H3.
  simpls. by rewrite H3.
Qed.

Theorem aBisim_term :
  forall P, aEntails (Aterm P) (Abisim P (HPalt P HPepsilon)).
Proof.
  intros P ph pm s g H1 H2 H3.
  simpl in H3. simpl.
  rewrite bisim_alt_comm.
  by apply bisim_term_intuit.
Qed.

(** Bisimilarity assertions are duplicable. *)

Theorem aBisim_dupl :
  forall P Q,
  aEntails (Abisim P Q) (Astar (Abisim P Q) (Abisim P Q)).
Proof.
  intros P Q ph pm s g H1 H2 H3. simpls.
  exists phIden, ph. intuition; [phsolve|].
  exists pmIden, pm. intuition. pmsolve.
Qed.


(** *** Termination *)

(** Termination according to [pterm] can be lifted to [Aterm]. *)

Theorem aTerm_intro :
  forall P, pterm P -> aEntails Atrue (Aterm (pHybridise P)).
Proof.
  intros P H1 ph pm s g H2 H3 _.
  simpl. by rewrite <- pDehybridise_hybridise.
Qed.

(** Terminating processes can always be replaced by bisimilar ones. *)

Theorem aTerm_bisim :
  forall P Q,
  aEntails (Astar (Aterm P) (Abisim P Q)) (Aterm Q).
Proof.
  intros P Q ph pm s g H1 H2 H3. simpl in H3.
  destruct H3 as (ph1&ph2&D1&D2&pm1&pm2&D3&D4&D5&D6).
  clarify. simpl. by rewrite <- D6.
Qed.

(** Termination assertions are duplicable. *)

Theorem aTerm_dupl :
  forall P, aEntails (Aterm P) (Astar (Aterm P) (Aterm P)).
Proof.
  intros P ph pm s g H1 H2 H3. simpls.
  exists phIden, ph. intuition; [phsolve|].
  exists pmIden, pm. intuition. pmsolve.
Qed.


(** ** Iterated points-to predicates *)

(** The properties below are for iterated heap ownership assertions. *)

(** First, the evaluation of heap ownership assertions
    in independent of any process maps: *)

Lemma sat_ApointstoIter_indep {T} :
  forall (xs : list T)(fq : T -> Qc)(f1 f2 : T -> Expr) ph pm1 pm2 s g t,
  pmValid pm2 ->
  sat ph pm1 s g (Aiter (ApointstoIter xs fq f1 f2 t)) ->
  sat ph pm2 s g (Aiter (ApointstoIter xs fq f1 f2 t)).
Proof.
  induction xs as [|l xs IH]. vauto.
  intros fq f1 f2 ph pm1 pm2 s g t V1 SAT.
  destruct SAT as (ph1&ph2&D1&H1&pm1'&pm2'&D2&H2&SAT1&SAT2).
  exists ph1, ph2. intuition vauto.
  exists pmIden, pm2. intuition vauto.
  - pmsolve.
  - apply IH with pm2'; auto.
Qed.

(** The satisfiability of iterated points-to predicates
    implies the satisfiability of a single points-to predicate. *)

Lemma ApointstoIter_sat_single_std {T} :
  forall (xs : list T)(x : T) ph pm s g F f1 f2,
  In x xs ->
  sat ph pm s g (Aiter (ApointstoIter xs F f1 f2 PTTstd)) ->
  let q := F x in
  let l := expr_eval (f1 x) s in
  let v := expr_eval (f2 x) s in
  phcLe (PHCstd q v) (ph l).
Proof.
  induction xs as [|x xs IH]. vauto.
  intros y ph pm s g F f1 f2 H1 SAT q l v.
  destruct SAT as (ph1&ph2&D1&H2&pm1&pm2&D2&H3&SAT1&SAT2).
  simpl in H1. destruct H1 as [H1|H1].
  - clarify. unfold sat in SAT1.
    destruct SAT1 as (V1&SAT1).
    transitivity (ph1 l); vauto.
    rewrite <- phUnion_cell.
    by apply phcLe_mono_pos.
  - apply IH with (x:=y) in SAT2; vauto.
    transitivity (ph2 l); vauto. rewrite <- phUnion_cell.
    rewrite phcUnion_comm. apply phcLe_mono_pos. by symmetry.
Qed.
Lemma ApointstoIter_sat_single_proc {T} :
  forall (xs : list T)(x : T) ph pm s g F f1 f2,
  In x xs ->
  sat ph pm s g (Aiter (ApointstoIter xs F f1 f2 PTTproc)) ->
  let q := F x in
  let l := expr_eval (f1 x) s in
  let v := expr_eval (f2 x) s in
  phcLe (PHCproc q v) (ph l).
Proof.
  induction xs as [|x xs IH]. vauto.
  intros y ph pm s g F f1 f2 H1 SAT q l v.
  destruct SAT as (ph1&ph2&D1&H2&pm1&pm2&D2&H3&SAT1&SAT2).
  simpl in H1. destruct H1 as [H1|H1].
  - clarify. unfold sat in SAT1.
    destruct SAT1 as (V1&SAT1).
    transitivity (ph1 l); vauto.
    rewrite <- phUnion_cell.
    by apply phcLe_mono_pos.
  - apply IH with (x:=y) in SAT2; vauto.
    transitivity (ph2 l); vauto. rewrite <- phUnion_cell.
    rewrite phcUnion_comm. apply phcLe_mono_pos. by symmetry.
Qed.
Lemma ApointstoIter_sat_single_act {T} :
  forall (xs : list T)(x : T) ph pm s g F f1 f2,
  In x xs ->
  sat ph pm s g (Aiter (ApointstoIter xs F f1 f2 PTTact)) ->
  let q := F x in
  let l := expr_eval (f1 x) s in
  let v := expr_eval (f2 x) s in
  exists v', phcLe (PHCact q v v') (ph l).
Proof.
  induction xs as [|x xs IH]. vauto.
  intros y ph pm s g F f1 f2 H1 SAT q l v.
  destruct SAT as (ph1&ph2&D1&H2&pm1&pm2&D2&H3&SAT1&SAT2).
  simpl in H1. destruct H1 as [H1|H1].
  - clarify. unfold sat in SAT1.
    destruct SAT1 as (V1&SAT1).
    destruct SAT1 as (v'&SAT1). exists v'.
    transitivity (ph1 l); vauto.
    rewrite <- phUnion_cell.
    by apply phcLe_mono_pos.
  - apply IH with (x:=y) in SAT2; vauto.
    destruct SAT2 as (v'&SAT2). exists v'.
    transitivity (ph2 l); vauto. rewrite <- phUnion_cell.
    rewrite phcUnion_comm. apply phcLe_mono_pos. by symmetry.
Qed.

(** Relations between the satisfiability of assertions
    and converted heap cells: *)

(* note: the other direction of the rightmost implication does not hold *)
Lemma sat_pointsto_conv_std :
  forall ph pm s g q E1 E2 l,
  phValid ph ->
  sat ph pm s g (Apointsto PTTstd q E1 E2) ->
  sat (phConvStd ph l) pm s g (Apointsto PTTstd q E1 E2).
Proof.
  intros ph pm s g q E1 E2 l V1 SAT.
  unfold sat, phConvStd, phUpdate, update in *. desf.
  split; [done|]. rewrite phc_std_conv.
  by apply phcConvStd_le.
Qed.
(* note: the other direction of the rightmost implication does not hold *)
Lemma sat_pointsto_conv_proc :
  forall ph pm s g q E1 E2 l,
  phValid ph ->
  sat ph pm s g (Apointsto PTTproc q E1 E2) ->
  sat (phConvProc ph l) pm s g (Apointsto PTTproc q E1 E2).
Proof.
  intros ph pm s g q E1 E2 l V1 SAT.
  unfold sat, phConvProc, phUpdate, update in *. desf.
  split; [done|]. rewrite phc_proc_conv.
  by apply phcConvProc_le.
Qed.
(* note: the other direction of the rightmost implication does not hold *)
Lemma sat_pointsto_conv_act :
  forall ph pm s g q E1 E2 l,
  phValid ph ->
  sat ph pm s g (Apointsto PTTact q E1 E2) ->
  sat (phConvAct ph l) pm s g (Apointsto PTTact q E1 E2).
Proof.
  intros ph pm s g q E1 E2 l V1 SAT.
  unfold sat in *. destruct SAT as (V2&(v'&SAT)).
  split; [done|]. exists v'.
  unfold phConvAct, phUpdate, update in *. desf.
  rewrite phc_act_conv. by apply phcConvAct_le.
Qed.

(* note: the other direction of the rightmost implication does not hold *)
Lemma sat_pointsto_conv_std_mult :
  forall (ls : list Val) ph pm s g q E1 E2,
  phValid ph ->
  sat ph pm s g (Apointsto PTTstd q E1 E2) ->
  sat (phConvStdMult ph ls) pm s g (Apointsto PTTstd q E1 E2).
Proof.
  induction ls as [|l ls IH]. vauto.
  intros ph pm s g q E1 E2 V1 SAT.
  simpl (phConvStdMult ph (l :: ls)).
  apply sat_pointsto_conv_std; auto.
  by apply phConvStdMult_valid.
Qed.
(* note: the other direction of the rightmost implication does not hold *)
Lemma sat_pointsto_conv_proc_mult :
  forall (ls : list Val) ph pm s g q E1 E2,
  phValid ph ->
  sat ph pm s g (Apointsto PTTproc q E1 E2) ->
  sat (phConvProcMult ph ls) pm s g (Apointsto PTTproc q E1 E2).
Proof.
  induction ls as [|l ls IH]. vauto.
  intros ph pm s g q E1 E2 V1 SAT.
  simpl (phConvProcMult ph (l :: ls)).
  apply sat_pointsto_conv_proc; auto.
  by apply phConvProcMult_valid.
Qed.
(* note: the other direction of the rightmost implication does not hold *)
Lemma sat_pointsto_conv_act_mult :
  forall (ls : list Val) ph pm s g q E1 E2,
  phValid ph ->
  sat ph pm s g (Apointsto PTTact q E1 E2) ->
  sat (phConvActMult ph ls) pm s g (Apointsto PTTact q E1 E2).
Proof.
  induction ls as [|l ls IH]. vauto.
  intros ph pm s g q E1 E2 V1 SAT.
  simpl (phConvActMult ph (l :: ls)).
  apply sat_pointsto_conv_act; auto.
  by apply phConvActMult_valid.
Qed.

(* note: the other direction of the rightmost implication does not hold *)
Lemma sat_iter_conv_std {T} :
  forall (xs : list T)(l : Val) ph pm s g (f1 f2 : T -> Expr)(fq : T -> Qc),
  sat ph pm s g (Aiter (ApointstoIter xs fq f1 f2 PTTstd)) ->
  sat (phConvStd ph l) pm s g (Aiter (ApointstoIter xs fq f1 f2 PTTstd)).
Proof.
  induction xs as [|x xs IH]. vauto. intros l ph pm s g f1 f2 fq SAT.
  destruct SAT as (ph1&ph2&D1&H2&pm1&pm2&D2&H3&SAT1&SAT2).
  exists (phConvStd ph1 l), (phConvStd ph2 l).
  repeat split; vauto.
  - by apply phConvStd_disj.
  - by rewrite  phConvStd_union.
  - exists pm1, pm2. split; [done|].
    split; [done|]. split.
    + apply sat_pointsto_conv_std; vauto.
      by apply phDisj_valid_l in D1.
    + apply IH; vauto.
Qed.
(* note: the other direction of the rightmost implication does not hold *)
Lemma sat_iter_conv_proc {T} :
  forall (xs : list T)(l : Val) ph pm s g (f1 f2 : T -> Expr)(fq : T -> Qc),
  sat ph pm s g (Aiter (ApointstoIter xs fq f1 f2 PTTproc)) ->
  sat (phConvProc ph l) pm s g (Aiter (ApointstoIter xs fq f1 f2 PTTproc)).
Proof.
  induction xs as [|x xs IH]. vauto. intros l ph pm s g f1 f2 fq SAT.
  destruct SAT as (ph1&ph2&D1&H2&pm1&pm2&D2&H3&SAT1&SAT2).
  exists (phConvProc ph1 l), (phConvProc ph2 l).
  repeat split; vauto.
  - by apply phConvProc_disj.
  - by rewrite  phConvProc_union.
  - exists pm1, pm2. split; [done|].
    split; [done|]. split.
    + apply sat_pointsto_conv_proc; vauto.
      by apply phDisj_valid_l in D1.
    + apply IH; vauto.
Qed.
(* note: the other direction of the rightmost implication does not hold *)
Lemma sat_iter_conv_act {T} :
  forall (xs : list T)(l : Val) ph pm s g (f1 f2 : T -> Expr)(fq : T -> Qc),
  sat ph pm s g (Aiter (ApointstoIter xs fq f1 f2 PTTact)) ->
  sat (phConvAct ph l) pm s g (Aiter (ApointstoIter xs fq f1 f2 PTTact)).
Proof.
  induction xs as [|x xs IH]. vauto. intros l ph pm s g f1 f2 fq SAT.
  destruct SAT as (ph1&ph2&D1&H2&pm1&pm2&D2&H3&SAT1&SAT2).
  exists (phConvAct ph1 l), (phConvAct ph2 l).
  repeat split; vauto.
  - by apply phConvAct_disj.
  - by rewrite  phConvAct_union.
  - exists pm1, pm2. split; [done|].
    split; [done|]. split.
    + apply sat_pointsto_conv_act; vauto.
      by apply phDisj_valid_l in D1.
    + apply IH; vauto.
Qed.

(* note: the other direction of the rightmost implication does not hold *)
Lemma sat_iter_conv_std_mult {T} :
  forall (ls : list Val)(xs : list T) ph pm s g (f1 f2 : T -> Expr)(fq : T -> Qc),
  sat ph pm s g (Aiter (ApointstoIter xs fq f1 f2 PTTstd)) ->
  sat (phConvStdMult ph ls) pm s g (Aiter (ApointstoIter xs fq f1 f2 PTTstd)).
Proof.
  induction ls as [|l ls IH]. vauto.
  intros xs ph pm s g f1 f2 fq SAT. simpl.
  by apply sat_iter_conv_std, IH.
Qed.
(* note: the other direction of the rightmost implication does not hold *)
Lemma sat_iter_conv_proc_mult {T} :
  forall (ls : list Val)(xs : list T) ph pm s g (f1 f2 : T -> Expr)(fq : T -> Qc),
  sat ph pm s g (Aiter (ApointstoIter xs fq f1 f2 PTTproc)) ->
  sat (phConvProcMult ph ls) pm s g (Aiter (ApointstoIter xs fq f1 f2 PTTproc)).
Proof.
  induction ls as [|l ls IH]. vauto.
  intros xs ph pm s g f1 f2 fq SAT. simpl.
  by apply sat_iter_conv_proc, IH.
Qed.
(* note: the other direction of the rightmost implication does not hold *)
Lemma sat_iter_conv_act_mult {T} :
  forall (ls : list Val)(xs : list T) ph pm s g (f1 f2 : T -> Expr)(fq : T -> Qc),
  sat ph pm s g (Aiter (ApointstoIter xs fq f1 f2 PTTact)) ->
  sat (phConvActMult ph ls) pm s g (Aiter (ApointstoIter xs fq f1 f2 PTTact)).
Proof.
  induction ls as [|l ls IH]. vauto.
  intros xs ph pm s g f1 f2 fq SAT. simpl.
  by apply sat_iter_conv_act, IH.
Qed.

Lemma pointsto_conv_std :
  forall ph pm s g E1 E2 q t,
  phValid ph ->
  sat ph pm s g (Apointsto t q E1 E2) ->
  let ph' := phConvStd ph (expr_eval E1 s) in
  sat ph' pm s g (Apointsto PTTstd q E1 E2).
Proof.
  intros ph pm s g E1 E2 q [ | | ] H1 (V1&SAT) ph'.
  - unfold sat in *. subst ph'.
    unfold phConvStd, phUpdate, update. desf.
    replace (PHCstd q (expr_eval E2 s)) with (phcConvStd (PHCstd q (expr_eval E2 s))); vauto.
    split; [done|]. apply phcConvStd_le; vauto.
  - unfold sat in *. subst ph'.
    unfold phConvStd, phUpdate, update. desf.
    replace (PHCstd q (expr_eval E2 s)) with (phcConvStd (PHCproc q (expr_eval E2 s))); vauto.
    split; [done|]. apply phcConvStd_le; vauto.
  - unfold sat in *. subst ph'.
    destruct SAT as (v'&SAT).
    unfold phConvStd, phUpdate, update. desf.
    replace (PHCstd q (expr_eval E2 s)) with (phcConvStd (PHCact q (expr_eval E2 s) v')); vauto.
    split; [done|]. apply phcConvStd_le; vauto.
Qed.
Lemma pointsto_conv_std_proc :
  forall ph pm s g E1 E2 q,
  phValid ph ->
  sat ph pm s g (Apointsto PTTstd q E1 E2) ->
  let ph' := phConvProc ph (expr_eval E1 s) in
  sat ph' pm s g (Apointsto PTTproc q E1 E2).
Proof.
  intros ph pm s g E1 E2 q H1 (V1&SAT) ph'.
  unfold sat in *. subst ph'.
  unfold phConvProc, phUpdate, update. desf.
  replace (PHCproc q (expr_eval E2 s)) with (phcConvProc (PHCstd q (expr_eval E2 s))); vauto.
  split; [done|]. apply phcConvProc_le; vauto.
Qed.
Lemma pointsto_conv_proc_act :
  forall ph pm s g E1 E2 q,
  phValid ph ->
  sat ph pm s g (Apointsto PTTproc q E1 E2) ->
  let ph' := phConvAct ph (expr_eval E1 s) in
  sat ph' pm s g (Apointsto PTTact q E1 E2).
Proof.
  intros ph pm s g E1 E2 q V1 (V2&SAT) ph'.
  unfold sat in *. subst ph'.
  unfold phConvAct, phUpdate, update. desf.
  split; [done|]. exists (expr_eval E2 s).
  replace (PHCact q (expr_eval E2 s) (expr_eval E2 s)) with (phcConvAct (PHCproc q (expr_eval E2 s))); vauto.
  apply phcConvAct_le; vauto.
Qed.

Lemma pointsto_conv_act_proc :
  forall ph pm s g E1 E2 q,
  phValid ph ->
  sat ph pm s g (Apointsto PTTact q E1 E2) ->
  let ph' := phConvProc ph (expr_eval E1 s) in
  sat ph' pm s g (Apointsto PTTproc q E1 E2).
Proof.
  intros ph pm s g E1 E2 q V1 (V2&SAT) ph'.
  unfold sat in *. subst ph'.
  unfold phConvProc, phUpdate, update. desf.
  replace (PHCproc q (expr_eval E2 s)) with (phcConvProc (PHCact q (expr_eval E2 s) v')); vauto.
  split; [done|]. apply phcConvProc_le; vauto.
Qed.

Lemma ApointstoIter_conv_std_proc {T} :
  forall (xs : list T) ph pm s g (f1 f2 : T -> Expr),
  let F := fun _ : T => 1 in
  sat ph pm s g (Aiter (ApointstoIter xs F f1 f2 PTTstd)) ->
  let xs' := map (expr_eval_map f1 s) xs in
  let ph' := phConvProcMult ph xs' in
  sat ph' pm s g (Aiter (ApointstoIter xs F f1 f2 PTTproc)).
Proof.
  induction xs as [|x xs IH]. vauto.
  intros ph pm s g f1 f2 F SAT xs' ph'.
  destruct SAT as (ph1&ph2&D1&H1&pm1&pm2&D2&H2&SAT1&SAT2).
  assert (V3 : phValid ph1). { by apply phDisj_valid_l in D1. }
  apply pointsto_conv_std_proc in SAT1; auto.
  apply IH in SAT2; clear IH.
  exists (phConvProcMult ph1 (map (expr_eval_map f1 s) (x :: xs))).
  exists (phConvProcMult ph2 (map (expr_eval_map f1 s) (x :: xs))).
  repeat split; vauto.
  - by apply phConvProcMult_disj.
  - rewrite <- phConvProcMult_union; vauto.
  - exists pm1, pm2. intuition.
    + rewrite map_cons.
      rewrite phConvProcMult_app with (xs:=[expr_eval_map f1 s x])(ys:=map (expr_eval_map f1 s) xs).
      rewrite phConvProcMult_free with (xs:=map (expr_eval_map f1 s) xs); [by vauto|].
      intros l H1. apply ApointstoIter_perm_full with (l0:=l) in SAT2; auto.
      rewrite phConvProcMult_entire in SAT2.
      red in D1. red in D1. specialize D1 with l.
      symmetry in D1. by apply phcDisj_entire_free in D1.
    + rewrite map_cons.
      rewrite phConvProcMult_app with (xs:=[expr_eval_map f1 s x])(ys:=map (expr_eval_map f1 s) xs).
      rewrite phConvProcMult_free with (xs:=[expr_eval_map f1 s x]); [by vauto|].
      intros l H1. simpl in H1.
      destruct H1 as [H1|H1]; vauto.
      subst F. simpl ((fun _ => 1) x) in SAT1.
      apply Apointsto_entire in SAT1.
      * rewrite phConvProcMult_free2.
        rewrite phConvProc_entire in SAT1.
        replace (expr_eval_map f1 s x) with (expr_eval (f1 x) s); vauto.
        red in D1. red in D1.
        specialize D1 with (expr_eval (f1 x) s).
        by apply phcDisj_entire_free in D1.
      * apply phConvProc_valid.
        by apply phDisj_valid_l in D1.
Qed.

Lemma ApointstoIter_conv_proc_std {T} :
  forall (xs : list T) ph pm s g (f1 f2 : T -> Expr),
  let F := fun _ : T => 1 in
  sat ph pm s g (Aiter (ApointstoIter xs F f1 f2 PTTproc)) ->
  let xs' := map (expr_eval_map f1 s) xs in
  let ph' := phConvStdMult ph xs' in
  sat ph' pm s g (Aiter (ApointstoIter xs F f1 f2 PTTstd)).
Proof.
  induction xs as [|x xs IH]. vauto.
  intros ph pm s g f1 f2 F SAT xs' ph'.
  destruct SAT as (ph1&ph2&D1&H1&pm1&pm2&D2&H2&SAT1&SAT2).
  assert (V2 : phValid ph1). { by apply phDisj_valid_l in D1. }
  apply pointsto_conv_std in SAT1; auto.
  apply IH in SAT2; clear IH.
  exists (phConvStdMult ph1 (map (expr_eval_map f1 s) (x :: xs))).
  exists (phConvStdMult ph2 (map (expr_eval_map f1 s) (x :: xs))).
  repeat split; vauto.
  - by apply phConvStdMult_disj.
  - rewrite <- phConvStdMult_union; vauto.
  - exists pm1, pm2. intuition.
    + rewrite map_cons.
      rewrite phConvStdMult_app with (xs:=[expr_eval_map f1 s x])(ys:=map (expr_eval_map f1 s) xs).
      rewrite phConvStdMult_free with (xs:=map (expr_eval_map f1 s) xs); [by vauto|].
      intros l H1. apply ApointstoIter_perm_full with (l0:=l) in SAT2; auto.
      rewrite phConvStdMult_entire in SAT2.
      red in D1. red in D1. specialize D1 with l.
      symmetry in D1. by apply phcDisj_entire_free in D1.
    + rewrite map_cons.
      rewrite phConvStdMult_app with (xs:=[expr_eval_map f1 s x])(ys:=map (expr_eval_map f1 s) xs).
      rewrite phConvStdMult_free with (xs:=[expr_eval_map f1 s x]); [by vauto|].
      intros l H1. simpl in H1.
      destruct H1 as [H1|H1]; vauto.
      subst F. simpl ((fun _ => 1) x) in SAT1.
      apply Apointsto_entire in SAT1.
      * rewrite phConvStdMult_free2.
        rewrite phConvStd_entire in SAT1.
        replace (expr_eval_map f1 s x) with (expr_eval (f1 x) s); vauto.
        red in D1. red in D1.
        specialize D1 with (expr_eval (f1 x) s).
        by apply phcDisj_entire_free in D1.
      * apply phConvStd_valid.
        by apply phDisj_valid_l in D1.
Qed.

Lemma ApointstoIter_conv_proc_act {T} :
  forall (xs : list T) ph pm s g (f1 f2 : T -> Expr)(F : T -> Qc),
  sat ph pm s g (Aiter (ApointstoIter xs F f1 f2 PTTproc)) ->
  let xs' := map (expr_eval_map f1 s) xs in
  let ph' := phConvActMult ph xs' in
  sat ph' pm s g (Aiter (ApointstoIter xs F f1 f2 PTTact)).
Proof.
  induction xs as [|x xs IH]. vauto.
  intros ph pm s g f1 f2 F SAT1 xs' ph'.
  destruct SAT1 as (ph1&ph2&D1&H1&pm1&pm2&D2&H2&SAT1&SAT2).
  assert (V1 : phValid ph1) by by apply phDisj_valid_l in D1.
  apply pointsto_conv_proc_act in SAT1; auto. apply IH in SAT2; clear IH.
  exists (phConvActMult ph1 (map (expr_eval_map f1 s) (x :: xs))).
  exists (phConvActMult ph2 (map (expr_eval_map f1 s) (x :: xs))).
  repeat split; vauto.
  - by apply phConvActMult_disj.
  - rewrite <- phConvActMult_union; vauto.
  - exists pm1, pm2. intuition.
    + unfold sat in SAT1. desf.
      unfold sat. split; [done|].
      exists v'. rewrite map_cons.
      unfold expr_eval_map at 1.
      rewrite phConvActMult_apply; vauto.
      by rewrite phConvAct_apply in SAT0.
    + replace (x :: xs) with ([x] ++ xs); auto.
      rewrite map_app, phConvActMult_app.
      by apply sat_iter_conv_act_mult.
Qed.

Lemma ApointstoIter_conv_act_proc {T} :
  forall (xs : list T) ph pm s g (f1 f2 : T -> Expr)(F : T -> Qc),
  sat ph pm s g (Aiter (ApointstoIter xs F f1 f2 PTTact)) ->
  let xs' := map (expr_eval_map f1 s) xs in
  let ph' := phConvProcMult ph xs' in
  sat ph' pm s g (Aiter (ApointstoIter xs F f1 f2 PTTproc)).
Proof.
  induction xs as [|x xs IH]. vauto.
  intros ph pm s g f1 f2 F SAT1 xs' ph'.
  destruct SAT1 as (ph1&ph2&D1&H1&pm1&pm2&D2&H2&SAT1&SAT2).
  assert (V1 : phValid ph1) by (by apply phDisj_valid_l in D1).
  apply pointsto_conv_act_proc in SAT1; auto. apply IH in SAT2; clear IH.
  exists (phConvProcMult ph1 (map (expr_eval_map f1 s) (x :: xs))).
  exists (phConvProcMult ph2 (map (expr_eval_map f1 s) (x :: xs))).
  repeat split; vauto.
  - by apply phConvProcMult_disj.
  - rewrite <- phConvProcMult_union; vauto.
  - exists pm1, pm2. intuition.
    + unfold sat in SAT1. desf.
      unfold sat. split; [done|].
      rewrite map_cons.
      unfold expr_eval_map at 1.
      rewrite phConvProcMult_apply; vauto.
      by rewrite phConvProc_apply in SAT0.
    + replace (x :: xs) with ([x] ++ xs); auto.
      rewrite map_app, phConvProcMult_app.
      by apply sat_iter_conv_proc_mult.
Qed.

(** Relations between assertion satisfiability and heap disjointness,
    in combination with heap conversions. *)

Lemma Adisj_sat_conv_std :
  forall ph1 ph2 pm s g E1 E2 q,
  phValid ph1 ->
  sat ph1 pm s g (Apointsto PTTstd q E1 E2) ->
  phDisj (phConvStd ph1 (expr_eval E1 s)) ph2 <->
  phDisj ph1 ph2.
Proof.
  intros ph1 ph2 pm s g E1 E2 q V1 SAT. split; intro D1.
  - unfold sat in SAT.
    intro l. unfold phConvStd in D1.
    red in D1. red in D1. specialize D1 with l.
    unfold phUpdate, update in D1. desf.
    rewrite <- phcLe_conv_std_disj with q (expr_eval E2 s); auto.
  - unfold sat in SAT.
    intro l. unfold phConvStd, phUpdate, update. desf.
    rewrite phcLe_conv_std_disj with q (expr_eval E2 s); auto.
Qed.
Lemma Adisj_sat_conv_proc :
  forall ph1 ph2 pm s g E1 E2 q,
  phValid ph1 ->
  sat ph1 pm s g (Apointsto PTTproc q E1 E2) ->
  phDisj (phConvProc ph1 (expr_eval E1 s)) ph2 <->
  phDisj ph1 ph2.
Proof.
  intros ph1 ph2 pm s g E1 E2 q V1 SAT. split; intro D1.
  - unfold sat in SAT.
    intro l. unfold phConvProc in D1.
    red in D1. red in D1. specialize D1 with l.
    unfold phUpdate, update in D1. desf.
    rewrite <- phcLe_conv_proc_disj with q (expr_eval E2 s); auto.
  - unfold sat in SAT.
    intro l. unfold phConvProc, phUpdate, update. desf.
    rewrite phcLe_conv_proc_disj with q (expr_eval E2 s); auto.
Qed.
Lemma Adisj_sat_conv_act :
  forall ph1 ph2 pm s g E1 E2 q,
  phValid ph1 ->
  sat ph1 pm s g (Apointsto PTTact q E1 E2) ->
  phDisj (phConvAct ph1 (expr_eval E1 s)) ph2 <->
  phDisj ph1 ph2.
Proof.
  intros ph1 ph2 pm s g E1 E2 q V1 SAT. split; intro D1.
  - unfold sat in SAT. destruct SAT as (V2&(v'&H1)).
    intro l. unfold phConvAct in D1.
    red in D1. red in D1. specialize D1 with l.
    unfold phUpdate, update in D1. desf.
    rewrite <- phcLe_conv_act_disj with q (expr_eval E2 s) v'; auto.
  - unfold sat in SAT. destruct SAT as (V2&(v'&H1)).
    intro l. unfold phConvAct, phUpdate, update. desf.
    rewrite phcLe_conv_act_disj with q (expr_eval E2 s) v'; auto.
Qed.

Lemma Adisj_sat_conv_std_In {T} :
  forall (xs : list T)(l : Val)(fq : T -> Qc)(f1 f2 : T -> Expr) ph1 ph2 pm s g,
  sat ph1 pm s g (Aiter (ApointstoIter xs fq f1 f2 PTTstd)) ->
  let ls := map (expr_eval_map f1 s) xs in
  In l ls ->
  phDisj (phConvStd ph1 l) ph2 <->
  phDisj ph1 ph2.
Proof.
  induction xs as [|x xs IH]. vauto.
  intros l fq f1 f2 ph1 ph2 pm s g SAT ls H1.
  destruct SAT as (ph3&ph4&D2&H2&pm1&pm2&D3&H3&SAT1&SAT2).
  split; intro D1.
  - subst ls. simpl in H1. destruct H1 as [H1|H1]; vauto.
    + unfold expr_eval_map in D1.
      rewrite Adisj_sat_conv_std with (pm:=pm)(g:=g)(q:=fq x)(E1:=f1 x)(E2:=f2 x) in D1; auto.
      rewrite <- H3. by apply sat_weaken.
    + rewrite IH with fq f1 f2 pm s g in D1; auto.
      rewrite <- H3. rewrite phUnion_comm, pmUnion_comm.
      apply sat_weaken; auto; [phsolve|pmsolve].
  - subst ls. simpl in H1. destruct H1 as [H1|H1]; vauto.
    + unfold expr_eval_map.
      rewrite Adisj_sat_conv_std with (pm:=pm)(g:=g)(q:=fq x)(E1:=f1 x)(E2:=f2 x); auto.
      clarify. rewrite <- H3. apply sat_weaken; auto.
    + apply IH with fq f1 f2 pm s g; auto.
      rewrite <- H3. rewrite phUnion_comm, pmUnion_comm.
      apply sat_weaken; auto; [phsolve|pmsolve].
Qed.
Lemma Adisj_sat_conv_proc_In {T} :
  forall (xs : list T)(l : Val)(fq : T -> Qc)(f1 f2 : T -> Expr) ph1 ph2 pm s g,
  sat ph1 pm s g (Aiter (ApointstoIter xs fq f1 f2 PTTproc)) ->
  let ls := map (expr_eval_map f1 s) xs in
  In l ls ->
  phDisj (phConvProc ph1 l) ph2 <-> phDisj ph1 ph2.
Proof.
  induction xs as [|x xs IH]. vauto.
  intros l fq f1 f2 ph1 ph2 pm s g SAT ls H1.
  destruct SAT as (ph3&ph4&D2&H2&pm1&pm2&D3&H3&SAT1&SAT2).
  split; intro D1.
  - subst ls. simpl in H1. destruct H1 as [H1|H1]; vauto.
    + unfold expr_eval_map in D1.
      rewrite Adisj_sat_conv_proc with (pm:=pm)(g:=g)(q:=fq x)(E1:=f1 x)(E2:=f2 x) in D1; auto.
      rewrite <- H3. by apply sat_weaken.
    + rewrite IH with fq f1 f2 pm s g in D1; auto.
      rewrite <- H3. rewrite phUnion_comm, pmUnion_comm.
      apply sat_weaken; auto; [phsolve|pmsolve].
  - subst ls. simpl in H1. destruct H1 as [H1|H1]; vauto.
    + unfold expr_eval_map.
      rewrite Adisj_sat_conv_proc with (pm:=pm)(g:=g)(q:=fq x)(E1:=f1 x)(E2:=f2 x); auto.
      clarify. rewrite <- H3. apply sat_weaken; auto.
    + apply IH with fq f1 f2 pm s g; auto.
      rewrite <- H3. rewrite phUnion_comm, pmUnion_comm.
      apply sat_weaken; auto; [phsolve|pmsolve].
Qed.
Lemma Adisj_sat_conv_act_In {T} :
  forall (xs : list T)(l : Val)(fq : T -> Qc)(f1 f2 : T -> Expr) ph1 ph2 pm s g,
  sat ph1 pm s g (Aiter (ApointstoIter xs fq f1 f2 PTTact)) ->
  let ls := map (expr_eval_map f1 s) xs in
  In l ls ->
  phDisj (phConvAct ph1 l) ph2 <->
  phDisj ph1 ph2.
Proof.
  induction xs as [|x xs IH]. vauto.
  intros l fq f1 f2 ph1 ph2 pm s g SAT ls H1.
  destruct SAT as (ph3&ph4&D2&H2&pm1&pm2&D3&H3&SAT1&SAT2).
  split; intro D1.
  - subst ls. simpl in H1. destruct H1 as [H1|H1]; vauto.
    + unfold expr_eval_map in D1.
      rewrite Adisj_sat_conv_act with (pm:=pm)(g:=g)(q:=fq x)(E1:=f1 x)(E2:=f2 x) in D1; auto.
      rewrite <- H3. by apply sat_weaken.
    + rewrite IH with fq f1 f2 pm s g in D1; auto.
      rewrite <- H3. rewrite phUnion_comm, pmUnion_comm.
      apply sat_weaken; auto; [phsolve|pmsolve].
  - subst ls. simpl in H1. destruct H1 as [H1|H1]; vauto.
    + unfold expr_eval_map.
      rewrite Adisj_sat_conv_act with (pm:=pm)(g:=g)(q:=fq x)(E1:=f1 x)(E2:=f2 x); auto.
      clarify. rewrite <- H3. apply sat_weaken; auto.
    + apply IH with fq f1 f2 pm s g; auto.
      rewrite <- H3. rewrite phUnion_comm, pmUnion_comm.
      apply sat_weaken; auto; [phsolve|pmsolve].
Qed.

Lemma Adisj_sat_conv_std_mult {T} :
  forall (xs : list T)(fq : T -> Qc)(f1 f2 : T -> Expr) ph1 ph2 pm s g,
  sat ph1 pm s g (Aiter (ApointstoIter xs fq f1 f2 PTTstd)) ->
  let ls := map (expr_eval_map f1 s) xs in
  phDisj (phConvStdMult ph1 ls) ph2 <->
  phDisj ph1 ph2.
Proof.
  induction xs as [|x xs IH]. vauto.
  intros fq f1 f2 ph1 ph2 pm s g SAT ls.
  destruct SAT as (ph3&ph4&D1&H1&pm1&pm2&D2&H2&SAT1&SAT2).
  clarify. split; intro D3.
  - subst ls. simpl in D3.
    rewrite <- IH with (pm:=pm)(s:=s)(g:=g)(fq:=fq)(f1:=f1)(f2:=f2).
    + rewrite <- Adisj_sat_conv_std with (pm:=pm)(s:=s)(g:=g)(q:=fq x)(E1:=f1 x)(E2:=f2 x); auto.
      * by apply phConvStdMult_valid, phUnion_valid.
      * apply sat_pointsto_conv_std_mult; auto.
        rewrite <- H2. by apply sat_weaken.
    + rewrite <- H2. rewrite phUnion_comm, pmUnion_comm.
      apply sat_weaken; auto; [phsolve|pmsolve].
  - subst ls. simpl. unfold expr_eval_map at 2.
    rewrite Adisj_sat_conv_std with (pm:=pm)(g:=g)(q:=fq x)(E1:=f1 x)(E2:=f2 x); auto.
    + apply IH with fq f2 pm g; auto. rewrite <- H2.
      rewrite phUnion_comm, pmUnion_comm.
      apply sat_weaken; auto; [phsolve|pmsolve].
    + apply phConvStdMult_valid.
      by apply phUnion_valid.
    + apply sat_pointsto_conv_std_mult; auto.
      rewrite <- H2. by apply sat_weaken.
Qed.
Lemma Adisj_sat_conv_proc_mult {T} :
  forall (xs : list T)(fq : T -> Qc)(f1 f2 : T -> Expr) ph1 ph2 pm s g,
  sat ph1 pm s g (Aiter (ApointstoIter xs fq f1 f2 PTTproc)) ->
  let ls := map (expr_eval_map f1 s) xs in
  phDisj (phConvProcMult ph1 ls) ph2 <->
  phDisj ph1 ph2.
Proof.
  induction xs as [|x xs IH]. vauto.
  intros fq f1 f2 ph1 ph2 pm s g SAT ls.
  destruct SAT as (ph3&ph4&D1&H1&pm1&pm2&D2&H2&SAT1&SAT2).
  clarify. split; intro D3.
  - subst ls. simpl in D3.
    rewrite <- IH with (pm:=pm)(s:=s)(g:=g)(fq:=fq)(f1:=f1)(f2:=f2).
    + rewrite <- Adisj_sat_conv_proc with (pm:=pm)(s:=s)(g:=g)(q:=fq x)(E1:=f1 x)(E2:=f2 x); auto.
      * by apply phConvProcMult_valid, phUnion_valid.
      * apply sat_pointsto_conv_proc_mult; auto.
        rewrite <- H2. by apply sat_weaken.
    + rewrite <- H2. rewrite phUnion_comm, pmUnion_comm.
      apply sat_weaken; auto; [phsolve|pmsolve].
  - subst ls. simpl. unfold expr_eval_map at 2.
    rewrite Adisj_sat_conv_proc with (pm:=pm)(g:=g)(q:=fq x)(E1:=f1 x)(E2:=f2 x); auto.
    + apply IH with fq f2 pm g; auto. rewrite <- H2.
      rewrite phUnion_comm, pmUnion_comm.
      apply sat_weaken; auto; [phsolve|pmsolve].
    + apply phConvProcMult_valid.
      by apply phUnion_valid.
    + apply sat_pointsto_conv_proc_mult; auto.
      rewrite <- H2. by apply sat_weaken.
Qed.
Lemma Adisj_sat_conv_act_mult {T} :
  forall (xs : list T)(fq : T -> Qc)(f1 f2 : T -> Expr) ph1 ph2 pm s g,
  sat ph1 pm s g (Aiter (ApointstoIter xs fq f1 f2 PTTact)) ->
  let ls := map (expr_eval_map f1 s) xs in
  phDisj (phConvActMult ph1 ls) ph2 <->
  phDisj ph1 ph2.
Proof.
  induction xs as [|x xs IH]. vauto.
  intros fq f1 f2 ph1 ph2 pm s g SAT ls.
  destruct SAT as (ph3&ph4&D1&H1&pm1&pm2&D2&H2&SAT1&SAT2).
  clarify. split; intro D3.
  - subst ls. simpl in D3.
    rewrite <- IH with (pm:=pm)(s:=s)(g:=g)(fq:=fq)(f1:=f1)(f2:=f2).
    + rewrite <- Adisj_sat_conv_act with (pm:=pm)(s:=s)(g:=g)(q:=fq x)(E1:=f1 x)(E2:=f2 x); auto.
      * by apply phConvActMult_valid, phUnion_valid.
      * apply sat_pointsto_conv_act_mult; auto.
        rewrite <- H2. by apply sat_weaken.
    + rewrite <- H2. rewrite phUnion_comm, pmUnion_comm.
      apply sat_weaken; auto; [phsolve|pmsolve].
  - subst ls. simpl. unfold expr_eval_map at 2.
    rewrite Adisj_sat_conv_act with (pm:=pm)(g:=g)(q:=fq x)(E1:=f1 x)(E2:=f2 x); auto.
    + apply IH with fq f2 pm g; auto. rewrite <- H2.
      rewrite phUnion_comm, pmUnion_comm.
      apply sat_weaken; auto; [phsolve|pmsolve].
    + apply phConvActMult_valid.
      by apply phUnion_valid.
    + apply sat_pointsto_conv_act_mult; auto.
      rewrite <- H2. by apply sat_weaken.
Qed.

End Assertions.
