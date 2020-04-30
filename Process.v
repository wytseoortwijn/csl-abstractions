Require Import HahnBase.
Require Import List.
Require Import Morphisms.
Require Import Prelude.
Require Import Setoid.
Require Import Utf8.

Import ListNotations.


(** * Process Algebra Theory *)

Module Type Processes(dom : Domains).
  Export dom.


(** ** Statics *)

(** *** Expressions *)

Inductive ProcExpr :=
  | PEconst(v : Val)
  | PEvar(x : ProcVar)
  | PEop(e1 e2 : ProcExpr).

Add Search Blacklist "ProcExpr_rect".
Add Search Blacklist "ProcExpr_ind".
Add Search Blacklist "ProcExpr_rec".
Add Search Blacklist "ProcExpr_sind".

(** **** Free variables *)

Fixpoint pexpr_fv (e : ProcExpr) : list ProcVar :=
  match e with
    | PEconst _ => []
    | PEvar x => [x]
    | PEop e1 e2 => pexpr_fv e1 ++ pexpr_fv e2
  end.


(** *** Conditions *)

Inductive ProcCond :=
  | PBconst(b : bool)
  | PBnot(b : ProcCond)
  | PBand(b1 b2 : ProcCond)
  | PBeq(e1 e2 : ProcExpr).

Add Search Blacklist "ProcCond_rect".
Add Search Blacklist "ProcCond_ind".
Add Search Blacklist "ProcCond_rec".
Add Search Blacklist "ProcCond_sind".

(** **** Free variables *)

Fixpoint pcond_fv (b : ProcCond) : list ProcVar :=
  match b with
    | PBconst _ => []
    | PBnot b' => pcond_fv b'
    | PBand b1 b2 => pcond_fv b1 ++ pcond_fv b2
    | PBeq e1 e2 => pexpr_fv e1 ++ pexpr_fv e2
  end.


(** *** Processes *)

(** All actions have an associated _guard_ and _effect_.
    Rather than giving syntax for defining such guards and
    effects, we simply assume the following two functions: *)

Parameter guard : Act -> Val -> ProcCond.
Parameter effect : Act -> Val -> ProcCond.

(** Processs maintain the well-formedness condition that any
    action argument (in [Pact]) and condition (in [Pcond])
    is closed (i.e., does not have any free variables).
    This condition is enforced already here, by letting
    action arguments be values and conditions be Booleans.
    Note that summations can be used in combination with these
    (Boolean) values, to make them useful. *)

Inductive Proc :=
  | Pepsilon
  | Pdelta
  | Pact(a : Act)(v : Val)
  | Passert(b : ProcCond)
  | Pseq(P1 P2 : Proc)
  | Palt(P1 P2 : Proc)
  | Ppar(P1 P2 : Proc)
  | Plmerge(P1 P2 : Proc)
  | Psum(f : Val -> Proc)
  | Pcond(b : bool)(P : Proc)
  | Piter(P : Proc).

Add Search Blacklist "Proc_rect".
Add Search Blacklist "Proc_ind".
Add Search Blacklist "Proc_rec".
Add Search Blacklist "Proc_sind".

Lemma proc_sum_ext :
  forall f f', f = f' -> Psum f = Psum f'.
Proof.
  intuition vauto.
Qed.

(** Below is a shorthand tactic for doing induction
    on the inductive structure of processes. *)

Ltac proc_induction P :=
  induction P as [
    (* epsilon *)
    |
    (* delta *)
    |
    (* actions *)
    a E|
    (* assertions *)
    B|
    (* sequential *)
    P1 IH1 P2 IH2|
    (* choice *)
    P1 IH1 P2 IH2|
    (* parallel *)
    P1 IH1 P2 IH2|
    (* left-merge *)
    P1 IH1 P2 IH2|
    (* summation *)
    f IH|
    (* conditionals *)
    B P' IH |
    (* iteration *)
    P IH
  ].


(** **** Free variables *)

(** The set of free variables in processes is defined in terms of a
    predicate instead of a fixpoint. This is needed, since processes
    are coinductively defined. *)

Definition act_fv (a : Act)(v : Val) : list ProcVar :=
  pcond_fv (guard a v) ++ pcond_fv (effect a v).

Fixpoint proc_fv (P : Proc)(x : ProcVar) : Prop :=
  match P with
    | Pepsilon => False
    | Pdelta => False
    | Pact a v => In x (act_fv a v)
    | Passert b => In x (pcond_fv b)
    | Pseq Q R => proc_fv Q x \/ proc_fv R x
    | Palt Q R => proc_fv Q x \/ proc_fv R x
    | Ppar Q R => proc_fv Q x \/ proc_fv R x
    | Plmerge Q R => proc_fv Q x \/ proc_fv R x
    | Psum f => exists v, proc_fv (f v) x
    | Pcond _ Q => proc_fv Q x
    | Piter Q => proc_fv Q x
  end.


(** *** Successful termination *)

(** An explicit notion [pterm P] of termination of process [P]
    is defined to define the reduction rules for sequential
    composition [Pseq]. *)

(** Intuitively [proc_term P] means that [P] has the choice to
    have no further behaviour and behave like [Pepsilon].
    In other words, [proc_term P] means that [P] is bisimilar to
    [Palt P Pepsilon] (which we prove later, after defining bisimilarity). *)

Inductive pterm : Proc -> Prop :=
  (* epsilon *)
  | pterm_epsilon : pterm Pepsilon
  (* sequential *)
  | pterm_seq P Q : pterm P -> pterm Q -> pterm (Pseq P Q)
  (* choice *)
  | pterm_alt_l P Q : pterm P -> pterm (Palt P Q)
  | pterm_alt_r P Q : pterm Q -> pterm (Palt P Q)
  (* parallel *)
  | pterm_par P Q : pterm P -> pterm Q -> pterm (Ppar P Q)
  (* left-merge *)
  | pterm_lmerge P Q : pterm P -> pterm Q -> pterm (Plmerge P Q)
  (* summation *)
  | pterm_sum f v : pterm (f v) -> pterm (Psum f)
  (* conditionals *)
  | pterm_cond P : pterm P -> pterm (Pcond true P)
  (* iteration *)
  | pterm_iter P : pterm (Piter P).

Add Search Blacklist "pterm_ind".
Add Search Blacklist "pterm_sind".


(** ** Dynamics *)

(** *** Process stores *)

(** Process stores are used on the denotational and operational
    semantics of processes to give an interpretation to
    process-algebraic variables. *)

Definition ProcStore := ProcVar -> Val.

(** The following definition captures two stores _agreeing_ on a
    given predicate [phi] over process variables. *)

Definition pstore_agree (phi : ProcVar -> Prop)(s1 s2 : ProcStore) : Prop :=
  forall x, phi x -> s1 x = s2 x.

Global Instance pstore_agree_symm :
  forall phi, Symmetric (pstore_agree phi).
Proof.
  intros phi s1 s2 H1 x H2. symmetry. by apply H1.
Qed.

Lemma pstore_agree_split :
  forall phi1 phi2 s1 s2,
  pstore_agree (fun x => phi1 x \/ phi2 x) s1 s2 <->
  pstore_agree phi1 s1 s2 /\ pstore_agree phi2 s1 s2.
Proof.
  intros phi1 phi2 s1 s2. split; intro H1; [split|].
  - red. intros x H2. apply H1. by left.
  - red. intros x H2. apply H1. by right.
  - destruct H1 as (H1&H2). red. intros x [H3|H3].
    + by apply H1.
    + by apply H2.
Qed.

Lemma pstore_agree_app :
  forall xs1 xs2 s1 s2,
  pstore_agree (fun x => In x (xs1 ++ xs2)) s1 s2 <->
  pstore_agree (fun x => In x xs1) s1 s2 /\
  pstore_agree (fun x => In x xs2) s1 s2.
Proof.
  intros xs1 xs2 s1 s2. split; intro H1; [split|].
  - red. intros x H2. apply H1.
    apply in_or_app. by left.
  - red. intros x H2. apply H1.
    apply in_or_app. by right.
  - destruct H1 as (H1&H2). red. intros x H3.
    apply in_app_or in H3. destruct H3 as [H3|H3].
    + by apply H1.
    + by apply H2.
Qed.

Lemma pstore_agree_weaken :
  forall (phi1 phi2 : ProcVar -> Prop)(s1 s2 : ProcStore),
    (forall x, phi1 x -> phi2 x) ->
  pstore_agree phi2 s1 s2 ->
  pstore_agree phi1 s1 s2.
Proof.
  intros phi1 phi2 s1 s2 H1 H2 s H3.
  by apply H2, H1.
Qed.


(** *** Expressions *)

(** The denotational semantics [pexpr_eval e s] of expressions
    [e] with respect to a process store [s] is defined
    in the standard way. *)

Fixpoint pexpr_eval (e : ProcExpr)(s : ProcStore) : Val :=
  match e with
    | PEconst v => v
    | PEvar x => s x
    | PEop e1 e2 => val_op (pexpr_eval e1 s) (pexpr_eval e2 s)
  end.

(** The evaluation of process-algebraic expressions [e]
    only depends on the variables occuring freely in [e]. *)

Lemma pexpr_agree :
  forall e s1 s2,
  pstore_agree (fun x => In x (pexpr_fv e)) s1 s2 ->
  pexpr_eval e s1 = pexpr_eval e s2.
Proof.
  induction e as [v|x|e1 IH1 e2 IH2]; intros s1 s2 H; simpls.
  - apply H. vauto.
  - apply pstore_agree_app in H.
    destruct H as (H1&H2).
    by rewrite IH1 with s1 s2, IH2 with s1 s2.
Qed.

(** Standard property relating expression evaluation to store updates. *)

Lemma pexpr_eval_upd :
  forall e s x v,
  ~ In x (pexpr_fv e) ->
  pexpr_eval e (update procvar_eq_dec s x v) = pexpr_eval e s.
Proof.
  intros e s x v H1.
  rewrite pexpr_agree with e s (update procvar_eq_dec s x v); vauto.
  intros y H2. unfold update. desf.
Qed.


(** *** Conditions *)

(** The denotational semantics [pcond_eval b s] of conditions
    [b] with respect to a process store [s] is defined
    in the standard way. *)

Fixpoint pcond_eval (b : ProcCond)(s : ProcStore) : bool :=
  match b with
    | PBconst b' => b'
    | PBnot b' => negb (pcond_eval b' s)
    | PBand b1 b2 => pcond_eval b1 s && pcond_eval b2 s
    | PBeq e1 e2 => if val_eq_dec (pexpr_eval e1 s) (pexpr_eval e2 s) then true else false
  end.

Lemma pcond_eval_excl :
  forall b s, pcond_eval b s = true \/ pcond_eval b s = false.
Proof.
  intros b s. rewrite <- Bool.not_true_iff_false.
  apply classic.
Qed.

(** The evaluation of process-algebraic conditions [b]
    only depends on the variables occuring freely in [b]. *)

Lemma pcond_agree :
  forall b s1 s2,
  pstore_agree (fun x => In x (pcond_fv b)) s1 s2 ->
  pcond_eval b s1 = pcond_eval b s2.
Proof.
  induction b as [b'|b' IH|b1 IH1 b2 IH2|e1 e2]; intros s1 s2 H; simpls.
  - by rewrite IH with s1 s2.
  - apply pstore_agree_app in H.
    destruct H as (H1&H2).
    by rewrite IH1 with s1 s2, IH2 with s1 s2.
  - apply pstore_agree_app in H.
    destruct H as (H1&H2).
    by rewrite pexpr_agree with e1 s1 s2, pexpr_agree with e2 s1 s2.
Qed.

Lemma pcond_eval_upd :
  forall b s x v,
  ~ In x (pcond_fv b) ->
  pcond_eval b (update procvar_eq_dec s x v) = pcond_eval b s.
Proof.
  intros b s x v H1.
  rewrite pcond_agree with b s (update procvar_eq_dec s x v); vauto.
  intros y H2. unfold update. desf.
Qed.


(** *** Processes *)

(** The labelled small-step reduction rules of processes
    are defined below, as [pstep]. *)

Inductive ProcLabel :=
  | PLact(a : Act)(v : Val)
  | PLassert.

Add Search Blacklist "ProcLabel_rect".
Add Search Blacklist "ProcLabel_ind".
Add Search Blacklist "ProcLabel_rec".
Add Search Blacklist "ProcLabel_sind".

Inductive pstep : Proc -> ProcStore -> ProcLabel -> Proc -> ProcStore -> Prop :=
  (* action *)
  | pstep_act s a v s' :
    pcond_eval (guard a v) s = true ->
    pcond_eval (effect a v) s' = true ->
    pstep (Pact a v) s (PLact a v) Pepsilon s'
  (* assertions *)
  | pstep_assert b s :
    pcond_eval b s -> pstep (Passert b) s PLassert Pepsilon s
  (* sequential *)
  | pstep_seq_l P Q l s P' s' :
    pstep P s l P' s' ->
    pstep (Pseq P Q) s l (Pseq P' Q) s'
  | pstep_seq_r P Q l s Q' s' :
    pterm P -> pstep Q s l Q' s' -> pstep (Pseq P Q) s l Q' s'
  (* choice *)
  | pstep_alt_l P Q l s P' s' :
    pstep P s l P' s' -> pstep (Palt P Q) s l P' s'
  | pstep_alt_r P Q l s Q' s' :
    pstep Q s l Q' s' -> pstep (Palt P Q) s l Q' s'
  (* parallel *)
  | pstep_par_l P Q l s P' s' :
    pstep P s l P' s' ->
    pstep (Ppar P Q) s l (Ppar P' Q) s'
  | pstep_par_r P Q l s Q' s' :
    pstep Q s l Q' s' ->
    pstep (Ppar P Q) s l (Ppar P Q') s'
  (* left-merge *)
  | pstep_lmerge P Q l s P' s' :
    pstep P s l P' s' ->
    pstep (Plmerge P Q) s l (Ppar P' Q) s'
  (* summation *)
  | pstep_sum f l v P s s' :
    pstep (f v) s l P s' -> pstep (Psum f) s l P s'
  (* conditionals *)
  | pstep_cond P l s P' s' :
    pstep P s l P' s' -> pstep (Pcond true P) s l P' s'
  (* iteration *)
  | pstep_iter P s a P' s' :
    pstep P s a P' s' -> pstep (Piter P) s a (Pseq P' (Piter P)) s'.

Add Search Blacklist "pstep_ind".
Add Search Blacklist "pstep_ind".

(** Standard properties of the reduction rules. *)

Lemma pstep_par_frame_l :
  forall P s l P' s' Q,
  pstep P s l P' s' ->
  pstep (Ppar P Q) s l (Ppar P' Q) s'.
Proof.
  intros. by apply pstep_par_l.
Qed.
Lemma pstep_par_frame_r :
  forall P s l P' s' Q,
  pstep P s l P' s' ->
  pstep (Ppar Q P) s l (Ppar Q P') s'.
Proof.
  intros. by apply pstep_par_r.
Qed.

Lemma pstep_act_agree :
  forall P s a v Q s1 s2,
  pstore_agree (fun x => In x (act_fv a v)) s1 s2 ->
  pstep P s (PLact a v) Q s1 ->
  pstep P s (PLact a v) Q s2.
Proof.
  proc_induction P; intros s a' v' Q s1 s2 H1 H2; inv H2; clear H2.
  (* action *)
  - rewrite pcond_agree with (s1:=s1)(s2:=s2) in H9.
    + constructor; auto.
    + red in H1. red. intros x H3. apply H1.
      unfold act_fv. apply in_or_app. by right.
  (* sequential *)
  - apply pstep_seq_l; auto.
    apply IH1 with s1; auto.
  - apply pstep_seq_r; auto.
    apply IH2 with s1; auto.
  (* choice *)
  - apply pstep_alt_l. by apply IH1 with s1.
  - apply pstep_alt_r. by apply IH2 with s1.
  (* parallel *)
  - apply pstep_par_l; auto.
    by apply IH1 with s1.
  - apply pstep_par_r; auto.
    by apply IH2 with s1.
  (* left-merge *)
  - apply pstep_lmerge; auto.
    by apply IH1 with s1.
  (* summation *)
  - apply pstep_sum with v.
    apply IH with s1; auto.
  (* conditionals *)
  - constructor; auto.
    apply IH with s1; auto.
  (* iteration *)
  - constructor. by apply IH with s1.
Qed.

Lemma pstep_assert_store :
  forall P s P' s',
  pstep P s PLassert P' s' -> s = s'.
Proof.
  proc_induction P; intros p Q s' H1; inv H1; clear H1; vauto.
  (* sequential *)
  - by apply IH1 in H6.
  - by apply IH2 in H7.
  (* choice *)
  - by apply IH1 in H6.
  - by apply IH2 in H6.
  (* parallel *)
  - by apply IH1 in H6.
  - by apply IH2 in H6.
  (* left-merge *)
  - by apply IH1 in H6.
  (* summation *)
  - by apply IH in H0.
  (* conditionals *)
  - by apply IH in H6.
  (* iteration *)
  - by apply IH in H0.
Qed.

Lemma pstep_assert_agree :
  forall P s1 s2 P',
  pstore_agree (proc_fv P) s1 s2 ->
  pstep P s1 PLassert P' s1 ->
  pstep P s2 PLassert P' s2.
Proof.
  proc_induction P; intros s1 s2 Q H1 H2;
    inv H2; clear H2; vauto.
  (* assertions *)
  - constructor.
    rewrite <- pcond_agree with (s1:=s1); vauto.
  (* sequential *)
  - apply pstep_seq_l. apply IH1 with s1; vauto.
    intros x H2. apply H1. vauto.
  - apply pstep_seq_r; vauto.
    apply IH2 with s1; vauto.
    intros x H2. apply H1. vauto.
  (* choice *)
  - apply pstep_alt_l.
    apply IH1 with s1; vauto.
    intros x H2. apply H1. vauto.
  - apply pstep_alt_r.
    apply IH2 with s1; vauto.
    intros x H2. apply H1. vauto.
  (* parallel *)
  - apply pstep_par_l.
    apply IH1 with s1; vauto.
    intros x H2. apply H1. vauto.
  - apply pstep_par_r.
    apply IH2 with s1; vauto.
    intros x H2. apply H1. vauto.
  (* left-merge *)
  - apply pstep_lmerge.
    apply IH1 with s1; vauto.
    intros x H2. apply H1. vauto.
  (* summation *)
  - apply pstep_sum with v.
    apply IH with s1; vauto.
    intros x H2. apply H1. vauto.
  (* conditionals *)
  - apply pstep_cond.
    apply IH with s1; vauto.
  (* iteration *)
  - apply pstep_iter.
    apply IH with s1; vauto.
Qed.


(** *** Fault semantics *)

(** A process [P] _exhibits a fault_ with respect to a store [s],
    written [pfault P s], if [P] can violate an assertional process
    [Passn] in a single reduction step, from the configuration [(P, s)]. *)

Inductive pfault : Proc -> ProcStore -> Prop :=
  (* assertions *)
  | pfault_assert b s : pcond_eval b s = false -> pfault (Passert b) s
  (* sequential *)
  | pfault_seq_l P Q s : pfault P s -> pfault (Pseq P Q) s
  | pfault_seq_r P Q s : pterm P -> pfault Q s -> pfault (Pseq P Q) s
  (* choice *)
  | pfault_alt_l P Q s : pfault P s -> pfault (Palt P Q) s
  | pfault_alt_r P Q s : pfault Q s -> pfault (Palt P Q) s
  (* parallel *)
  | pfault_par_l P Q s : pfault P s -> pfault (Ppar P Q) s
  | pfault_par_r P Q s : pfault Q s -> pfault (Ppar P Q) s
  (* left-merge *)
  | pfault_lmerge P Q s : pfault P s -> pfault (Plmerge P Q) s
  (* summation *)
  | pfault_sum f v s : pfault (f v) s -> pfault (Psum f) s
  (* conditionals *)
  | pfault_cond P s : pfault P s -> pfault (Pcond true P) s
  (* iteration *)
  | pfault_iter P s : pfault P s -> pfault (Piter P) s.

Add Search Blacklist "pfault_ind".
Add Search Blacklist "pfault_ind".

(** Standard properties of process faults. *)

Lemma passn_nfault :
  forall b s, ~ pfault (Passert b) s -> pcond_eval b s = true.
Proof.
  intros b s H1. apply Bool.not_false_is_true.
  intro H2. apply H1. by constructor.
Qed.

Lemma pfault_agree :
  forall P s1 s2,
  pstore_agree (proc_fv P) s1 s2 -> pfault P s1 -> pfault P s2.
Proof.
  proc_induction P; intros s1 s2 H1 H2; inv H2; clear H2.
  (* assertions *)
  - constructor.
    rewrite <- pcond_agree with (s1:=s1); auto.
  (* sequential *)
  - apply pfault_seq_l.
    apply IH1 with s1; auto. intros ??.
    apply H1. vauto.
  - apply pfault_seq_r; auto.
    apply IH2 with s1; auto. intros ??.
    apply H1. vauto.
  (* choice *)
  - apply pfault_alt_l.
    apply IH1 with s1; auto. intros ??.
    apply H1. vauto.
  - apply pfault_alt_r.
    apply IH2 with s1; auto. intros ??.
    apply H1. vauto.
  (* parallel *)
  - apply pfault_par_l.
    apply IH1 with s1; auto. intros ??.
    apply H1. vauto.
  - apply pfault_par_r.
    apply IH2 with s1; auto. intros ??.
    apply H1. vauto.
  (* left-merge *)
  - constructor. apply IH1 with s1; auto.
    intros ??. apply H1. vauto.
  (* summation *)
  - apply pfault_sum with v.
    apply IH with s1; auto.
    intros ??. apply H1. by exists v.
  (* conditionals *)
  - constructor. apply IH with s1; auto.
  (* iteration *)
  - constructor. apply IH with s1; auto.
Qed.


(** ** Bisimulation *)

(** Bisimilarity is defined in the standard way. *)

CoInductive bisim : relation Proc :=
  | bisim_proc P Q :
      (* termination is preserved *)
      (pterm P <-> pterm Q) /\
      (* faults are preserved *)
      (forall s, pfault P s <-> pfault Q s) /\
      (* left-to-right simulation *)
      (forall s l P' s', pstep P s l P' s' -> exists Q', pstep Q s l Q' s' /\ bisim P' Q') /\
      (* right-to-left simulation *)
      (forall s l Q' s', pstep Q s l Q' s' -> exists P', pstep P s l P' s' /\ bisim P' Q') ->
    bisim P Q.

Definition bisim_f : relation (Val -> Proc) :=
  pointwise_relation Val bisim.

Notation "P ≃ Q" := (bisim P Q) (only printing, at level 80).
Notation "f ≃ g" := (bisim_f f g) (only printing, at level 80).

(** Bisimilarity is an equivalence relation. *)

Global Instance bisim_refl : Reflexive bisim.
Proof.
  cofix CH. intro P. constructor. intuition vauto.
Qed.
Global Instance bisim_symm : Symmetric bisim.
Proof.
  cofix CH. intros P Q H. inv H. clear H.
  destruct H0 as (H1&H2&H3&H4). constructor.
  repeat split.
  (* termination *)
  - intro H5. by apply H1.
  - intro H5. by apply H1.
  (* faults *)
  - intro H5. by apply H2.
  - intro H5. by apply H2.
  (* simulation *)
  - intros s l Q' s' H5. apply H4 in H5.
    destruct H5 as (P'&H5&H6).
    exists P'. intuition vauto. by apply CH.
  - intros s l P' s' H5. apply H3 in H5.
    destruct H5 as (Q'&H5&H6).
    exists Q'. intuition vauto. by apply CH.
Qed.
Global Instance bisim_trans : Transitive bisim.
Proof.
  cofix CH. intros P Q R H1 H2.
  inv H1. clear H1. destruct H as (K1&K2&K3&K4).
  inv H2. clear H2. destruct H as (K5&K6&K7&K8).
  constructor. repeat split.
  (* termination *)
  - intro H1. by apply K5, K1.
  - intro H1. by apply K1, K5.
  (* faults *)
  - intro H1. by apply K6, K2.
  - intro H1. by apply K2, K6.
  (* simulation *)
  - intros s l P' s' H1.
    apply K3 in H1. destruct H1 as (Q'&H1&H2).
    apply K7 in H1. destruct H1 as (R'&H1&H3).
    exists R'. split; auto. by apply CH with Q'.
  - intros s l R' s' H1.
    apply K8 in H1. destruct H1 as (Q'&H1&H2).
    apply K4 in H1. destruct H1 as (P'&H1&H3).
    exists P'. split; auto. by apply CH with Q'.
Qed.
Global Instance bisim_equiv : Equivalence bisim.
Proof. split; intuition. Qed.

Hint Resolve bisim_refl : core.

Global Instance bisim_f_refl : Reflexive bisim_f.
Proof. intros f v. auto. Qed.
Global Instance bisim_f_symm : Symmetric bisim_f.
Proof. intros f1 f2 H v. symmetry. by apply H. Qed.
Global Instance bisim_f_trans : Transitive bisim_f.
Proof. intros f1 f2 f3 H1 H2 v. transitivity (f2 v); auto. Qed.
Global Instance bisim_f_equiv : Equivalence bisim_f.
Proof. split; intuition. Qed.

Hint Resolve bisim_f_refl : core.

(** Terminating processes can always be replaced by bisimilar ones. *)

Lemma bisim_term :
  forall P Q, bisim P Q -> pterm P -> pterm Q.
Proof.
  intros P Q H1 H2. inv H1. destruct H as (T&_). by apply T.
Qed.
Add Parametric Morphism : pterm
  with signature bisim ==> iff as pterm_mor.
Proof.
  intros P Q ?. split; ins;
    [apply bisim_term with P|apply bisim_term with Q]; auto.
  by symmetry.
Qed.

(** Faulting processes can always be replaced by bisimilar ones. *)

Lemma bisim_fault :
  forall P Q s, bisim P Q -> pfault P s -> pfault Q s.
Proof.
  intros P Q s H1 H2. inv H1. destruct H as (_&T&_). by apply T.
Qed.
Add Parametric Morphism : pfault
  with signature bisim ==> eq ==> iff as pfault_mor.
Proof.
  intros P Q H1 s.
  split; ins;
    [apply bisim_fault with P|apply bisim_fault with Q]; auto.
  by symmetry.
Qed.

(** The following theorem makes explicit the intuitive meaning
    of successful termination. *)

Theorem bisim_term_intuit :
  forall P, pterm P -> bisim P (Palt Pepsilon P).
Proof.
  cofix CH. intros P H1. constructor. repeat split.
  (* termination *)
  - intros _. vauto.
  - intros _. vauto.
  (* faults *)
  - intros H2. by apply pfault_alt_r.
  - intros H2. inv H2. inv H4.
  (* reduction *)
  - intros s l P' s' H2. exists P'. intuition vauto.
  - intros s l P' s' H2.
    inv H2; clear H2; vauto. inv H7.
Qed.


(** *** Congruence *)

(** Bisimilarity is a congruence for all connectives. *)

Add Parametric Morphism : Pseq
  with signature bisim ==> bisim ==> bisim
    as bisim_seq.
Proof.
  cofix CH. intros P1 P2 H1 Q1 Q2 H2.
  constructor. repeat split.
  (* termination *)
  - intro H3. inv H3. constructor; [by rewrite <- H1|by rewrite <- H2].
  - intro H3. inv H3. constructor; [by rewrite H1|by rewrite H2].
  (* faults *)
  - intro H3. inv H3; clear H3.
    + apply pfault_seq_l. by rewrite <- H1.
    + apply pfault_seq_r; [by rewrite <- H1|by rewrite <- H2].
  - intro H3. inv H3; clear H3.
    + apply pfault_seq_l. by rewrite H1.
    + apply pfault_seq_r; [by rewrite H1|by rewrite H2].
  (* simulations *)
  - intros s l P' s' STEP. inv STEP; clear STEP.
    + rename P'0 into P1'.
      inv H1. clear H1. destruct H as (_&_&H1&_).
      apply H1 in H7. clear H1. destruct H7 as (P2'&H5&H6).
      exists (Pseq P2' Q2). intuition vauto.
      apply CH; auto.
    + rename P' into Q1'. inv H2. clear H2.
      destruct H as (_&_&H2&_). apply H2 in H8.
      clear H2. destruct H8 as (Q2'&H6&H7).
      exists Q2'. intuition.
      apply pstep_seq_r; auto. by rewrite <- H1.
  - intros s l P' s' STEP. inv STEP; clear STEP.
    + rename P'0 into P2'. inv H1. clear H1.
      destruct H as (_&_&_&H1). apply H1 in H7.
      clear H1. destruct H7 as (P1'&H3&H4).
      exists (Pseq P1' Q1). intuition vauto.
      apply CH; auto.
    + rename P' into Q2'. inv H2. clear H2.
      destruct H as (_&_&_&H2). apply H2 in H8.
      clear H2. destruct H8 as (Q1'&H2&H4).
      exists Q1'. intuition.
      apply pstep_seq_r; auto. by rewrite H1.
Qed.

Add Parametric Morphism : Palt
  with signature bisim ==> bisim ==> bisim
    as bisim_alt.
Proof.
  intros P1 P2 H1 Q1 Q2 H2.
  constructor. repeat split.
  (* termination *)
  - intro H3. inv H3; clear H3.
    + apply pterm_alt_l. by rewrite <- H1.
    + apply pterm_alt_r. by rewrite <- H2.
  - intro H3. inv H3; clear H3.
    + apply pterm_alt_l. by rewrite H1.
    + apply pterm_alt_r. by rewrite H2.
  (* faults *)
  - intro H3. inv H3; clear H3.
    + apply pfault_alt_l. by rewrite <- H1.
    + apply pfault_alt_r. by rewrite <- H2.
  - intro H3. inv H3; clear H3.
    + apply pfault_alt_l. by rewrite H1.
    + apply pfault_alt_r. by rewrite H2.
  (* simulations *)
  - intros s l P' s' H3. inv H3; clear H3.
    + rename P' into P1'. inv H1. clear H1.
      destruct H as (_&_&H1&_).
      apply H1 in H8. clear H1.
      destruct H8 as (P2'&H6&H7).
      exists P2'. intuition. vauto.
    + rename P' into Q1'. inv H2. clear H2.
      destruct H as (_&_&H2&_).
      apply H2 in H8. clear H2.
      destruct H8 as (Q2'&H6&H7).
      exists Q2'. intuition. vauto.
  - intros s l P' s' H3. inv H3; clear H3.
    + rename P' into P2'. inv H1. clear H1.
      destruct H as (_&_&_&H1).
      apply H1 in H8. clear H1.
      destruct H8 as (P1'&H6&H7).
      exists P1'. intuition. vauto.
    + rename P' into Q2'. inv H2. clear H2.
      destruct H as (_&_&_&H2).
      apply H2 in H8. clear H2.
      destruct H8 as (Q1'&H6&H7).
      exists Q1'. intuition. vauto.
Qed.

Add Parametric Morphism : Ppar
  with signature bisim ==> bisim ==> bisim
    as bisim_par.
Proof.
  cofix CH. intros P1 P2 H1 Q1 Q2 H2.
  constructor. repeat split.
  (* termination *)
  - intro H3. inv H3. constructor; [by rewrite <- H1|by rewrite <- H2].
  - intro H3. inv H3. constructor; [by rewrite H1|by rewrite H2].
  (* faults *)
  - intro H3. inv H3; clear H3.
    + apply pfault_par_l. by rewrite <- H1.
    + apply pfault_par_r. by rewrite <- H2.
  - intro H3. inv H3; clear H3.
    + apply pfault_par_l. by rewrite H1.
    + apply pfault_par_r. by rewrite H2.
  (* simulations *)
  - intros s l P' s' H3. inv H3; clear H3.
    + rename P'0 into P1'.
      inv H1. clear H1. destruct H as (_&_&H1&_).
      apply H1 in H8. clear H1.
      destruct H8 as (P2'&H4&H5).
      exists (Ppar P2' Q2). intuition vauto.
      apply CH; auto.
    + rename Q' into Q1'.
      inv H2. clear H2. destruct H as (_&_&H2&_).
      apply H2 in H8. clear H2.
      destruct H8 as (Q2'&H4&H5).
      exists (Ppar P2 Q2'). intuition vauto.
      apply CH; auto.
  - intros s l P' s' H3. inv H3; clear H3.
    + rename P'0 into P2'.
      inv H1. clear H1. destruct H as (_&_&_&H1).
      apply H1 in H8. clear H1.
      destruct H8 as (P1'&H4&H5).
      exists (Ppar P1' Q1). intuition vauto.
      apply CH; auto.
    + rename Q' into Q2'.
      inv H2. clear H2. destruct H as (_&_&_&H2).
      apply H2 in H8. clear H2.
      destruct H8 as (Q1'&H4&H5).
      exists (Ppar P1 Q1'). intuition vauto.
      apply CH; auto.
Qed.

Add Parametric Morphism : Plmerge
  with signature bisim ==> bisim ==> bisim
    as bisim_lmerge.
Proof.
  cofix CH. intros P1 P2 H1 Q1 Q2 H2.
  constructor. repeat split.
  (* termination *)
  - intro H3. inv H3. constructor; [by rewrite <- H1|by rewrite <- H2].
  - intro H3. inv H3. constructor; [by rewrite H1|by rewrite H2].
  (* faults *)
  - intro H3. inv H3; clear H3. constructor. by rewrite <- H1.
  - intro H3. inv H3; clear H3. constructor. by rewrite H1.
  (* simulations *)
  - intros s l P' s' STEP. inv STEP; clear STEP.
    rename P'0 into P1'.
    inv H1. clear H1. destruct H as (_&_&H1&_).
    apply H1 in H7. clear H1. destruct H7 as (P2'&H3&H4).
    exists (Ppar P2' Q2). intuition vauto.
    apply bisim_par; auto.
  - intros s l P' s' STEP. inv STEP; clear STEP.
    rename P'0 into P2'.
    inv H1. clear H1. destruct H as (_&_&_&H1).
    apply H1 in H7. clear H1. destruct H7 as (P1'&H3&H4).
    exists (Ppar P1' Q1). intuition vauto.
    apply bisim_par; auto.
Qed.

Add Parametric Morphism : Psum
  with signature bisim_f ==> bisim
    as bisim_sum.
Proof.
  intros f1 f2 H1. constructor. repeat split.
  (* termination *)
  - intro H2. inv H2. clear H2.
    apply pterm_sum with v. red in H1. by rewrite <- H1.
  - intro H2. inv H2. clear H2.
    apply pterm_sum with v. red in H1. by rewrite H1.
  (* faults *)
  - intro H2. inv H2. clear H2.
    apply pfault_sum with v. red in H1. by rewrite <- H1.
  - intro H2. inv H2. clear H2.
    apply pfault_sum with v. red in H1. by rewrite H1.
  (* simulations *)
  - intros s l P' s' H2. inv H2. clear H2. red in H1.
    red in H1. specialize H1 with v. inv H1. clear H1.
    destruct H as (_&_&H1&_). apply H1 in H0. clear H1.
    destruct H0 as (P&H1&H2). exists P. intuition. vauto.
  - intros s l P' s' H2. inv H2. clear H2. red in H1.
    red in H1. specialize H1 with v. inv H1. clear H1.
    destruct H as (_&_&_&H1). apply H1 in H0. clear H1.
    destruct H0 as (P&H1&H2). exists P. intuition. vauto.
Qed.

Add Parametric Morphism : Pcond
  with signature eq ==> bisim ==> bisim
    as bisim_cond.
Proof.
  intros b P Q H1. constructor. repeat split.
  (* termination *)
  - intro H2. inv H2. clear H2. constructor; vauto. by rewrite <- H1.
  - intro H2. inv H2. clear H2. constructor; vauto. by rewrite H1.
  (* faults *)
  - intro H2. inv H2. clear H2. constructor; vauto. by rewrite <- H1.
  - intro H2. inv H2. clear H2. constructor; vauto. by rewrite H1.
  (* simulations *)
  - intros s l P' s' H2. inv H2. clear H2.
    inv H1. clear H1. destruct H as (_&_&H1&_).
    apply H1 in H7. clear H1. destruct H7 as (Q'&H1&H2).
    exists Q'. intuition. constructor; vauto.
  - intros s l Q' s' H2. inv H2. clear H2.
    inv H1. clear H1. destruct H as (_&_&_&H1).
    apply H1 in H7. clear H1. destruct H7 as (P'&H1&H2).
    exists P'. intuition. constructor; vauto.
Qed.

Lemma bisim_iter_seq_cong :
  forall P1 P2 Q1 Q2,
  bisim P1 P2 ->
  bisim Q1 Q2 ->
  bisim (Pseq P1 (Piter Q1)) (Pseq P2 (Piter Q2)).
Proof.
  cofix CH.
  intros P1 P2 Q1 Q2 H1 H2.
  constructor. repeat split.
  (* termination *)
  - intros H3. inv H3. clear H3.
    inv H5. clear H5. repeat constructor.
    by rewrite <- H1.
  - intros H3. inv H3. clear H3.
    inv H5. clear H5. repeat constructor.
    by rewrite H1.
  (* faults *)
  - intros H3. inv H3; clear H3.
    + apply pfault_seq_l. by rewrite <- H1.
    + inv H6. clear H6. apply pfault_seq_r.
      * by rewrite <- H1.
      * constructor. by rewrite <- H2.
  - intros H3. inv H3; clear H3.
    + apply pfault_seq_l. by rewrite H1.
    + inv H6. clear H6. apply pfault_seq_r.
      * by rewrite H1.
      * constructor. by rewrite H2.
  (* reductions *)
  - intros s a P' s' STEP.
    inv STEP; clear STEP.
    + rename P'0 into P1'.
      inv H1. clear H1. destruct H as (K1&K2&K3&K4).
      apply K3 in H7. destruct H7 as (P2'&H7&H8).
      exists (Pseq P2' (Piter Q2)).
      split; auto. by constructor.
    + inv H8. clear H8. rename P'0 into Q1'.
      inv H2. destruct H as (K1&K2&K3&K4).
      apply K3 in H0. destruct H0 as (Q2'&H0&H0').
      exists (Pseq Q2' (Piter Q2)).
      split; auto. apply pstep_seq_r; vauto.
      inv H1. clear H1. destruct H as (J1&J2&J3&J4).
      by apply J1.
  - intros ps a P' ps' STEP.
    inv STEP; clear STEP.
    + rename P'0 into P2'.
      inv H1. clear H1. destruct H as (K1&K2&K3&K4).
      apply K4 in H7. destruct H7 as (P1'&H7&H8).
      exists (Pseq P1' (Piter Q1)).
      split; auto. by constructor.
    + inv H8. clear H8. rename P'0 into Q2'.
      inv H2. destruct H as (K1&K2&K3&K4).
      apply K4 in H0. destruct H0 as (Q1'&H4&H5).
      exists (Pseq Q1' (Piter Q1)).
      split; auto. apply pstep_seq_r; vauto.
      inv H1. clear H1. destruct H as (J1&J2&J3&J4).
      by apply J1.
Qed.

Add Parametric Morphism : Piter
  with signature bisim ==> bisim as bisim_iter.
Proof.
  intros P Q H1.
  constructor. repeat split; vauto.
  (* faults *)
  - intro H2. inv H2. clear H2.
    constructor. by rewrite <- H1.
  - intro H2. inv H2. clear H2.
    constructor. by rewrite H1.
  (* reductions *)
  - intros s a P' s' STEP.
    inv STEP; clear STEP.
    rename H0 into STEP, P'0 into P'.
    inv H1. clear H1. destruct H as (K1&K2&K3&K4).
    apply K3 in STEP. destruct STEP as (Q'&H1&H2).
    exists (Pseq Q' (Piter Q)). split; vauto.
    by apply bisim_iter_seq_cong.
  - intros s a P' s' STEP.
    inv STEP; clear STEP.
    rename H0 into STEP, P'0 into Q'.
    inv H1. clear H1. destruct H as (K1&K2&K3&K4).
    apply K4 in STEP. destruct STEP as (P'&H1&H2).
    exists (Pseq P' (Piter P)). split; vauto.
    by apply bisim_iter_seq_cong.
Qed.


(** ** Axiomatisation *)

(** Below are several bisimulation equivalences
    for the above language of processes. *)

(** Usually these equation are given or presented as an
    axiomatisation that is proven sound (and sometimes complete)
    with respect to bisimilarity. However, here they
    are given directly as bisimulation equivalences. *)

Theorem bisim_seq_epsilon_l :
  forall P, bisim (Pseq P Pepsilon) P.
Proof.
  cofix CH. intros P. constructor. repeat split.
  (* termination *)
  - intros H1. inv H1.
  - intros H1. apply pterm_seq; vauto.
  (* faults *)
  - intros H1. inv H1. clear H1. inv H4.
  - intros H1. by constructor.
  (* simulations *)
  - intros s l P' s' H1. inv H1; vauto. inv H7.
  - intros s l P' s' H1. exists (Pseq P' Pepsilon).
    intuition. by apply pstep_seq_l.
Qed.

Theorem bisim_seq_epsilon_r :
  forall P, bisim (Pseq Pepsilon P) P.
Proof.
  cofix CH. intros P. constructor. repeat split.
  (* termination *)
  - intros H1. inv H1.
  - intros H1. apply pterm_seq; vauto.
  (* faults *)
  - intros H1. inv H1. clear H1. inv H3.
  - intros H1. apply pfault_seq_r; vauto.
  (* simulations *)
  - intros s l P' s' H1. inv H1; vauto.
    inv H6.
  - intros s l P' s' H1. exists P'.
    intuition. apply pstep_seq_r; vauto.
Qed.

Theorem bisim_seq_delta :
  forall P, bisim (Pseq Pdelta P) Pdelta.
Proof.
  intro P. constructor. repeat split.
  (* termination *)
  - intro H1. inv H1.
  - intro H1. inv H1.
  (* faults *)
  - intro H1. inv H1. inv H2.
  - intro H1. inv H1.
  (* simulations *)
  - intros s l P' s' H1. inv H1; clear H1.
    + inv H6.
    + inv H2.
  - intros s l P' s' H1. inv H1.
Qed.

Theorem bisim_seq_assoc :
  forall P Q R, bisim (Pseq P (Pseq Q R)) (Pseq (Pseq P Q) R).
Proof.
  cofix CH. intros P Q R.
  constructor. repeat split.
  (* termination *)
  - intro H1. inv H1. clear H1.
    inv H3. clear H3. vauto.
  - intro H1. inv H1. clear H1.
    inv H2. clear H2. vauto.
  (* faults *)
  - intro H1. inv H1; clear H1.
    + by repeat apply pfault_seq_l.
    + inv H4; clear H4; vauto.
  - intro H1. inv H1; clear H1.
    + inv H3; clear H3; vauto.
    + inv H2. clear H2. vauto.
  (* simulations *)
  - intros s l P' s' STEP. inv STEP; clear STEP.
    + rename P'0 into P'.
      exists (Pseq (Pseq P' Q) R). split; vauto.
    + inv H6; clear H6.
      * rename P'0 into Q''.
        exists (Pseq Q'' R). split; vauto.
      * rename P' into R'.
        exists R'. split; vauto.
  - intros s l Q' s' STEP. inv STEP; clear STEP.
    + inv H5; clear H5.
      * rename P'0 into P'.
        exists (Pseq P' (Pseq Q R)). split; vauto.
      * rename P' into Q'.
        exists (Pseq Q' R). split; vauto.
    + rename Q' into R'. inv H1. clear H1.
      exists R'. split; vauto.
Qed.

Theorem bisim_alt_comm :
  forall P Q, bisim (Palt P Q) (Palt Q P).
Proof.
  cofix CH. intros P Q. constructor. repeat split.
  (* termination *)
  - intro H1. inv H1; clear H1; vauto.
  - intro H1. inv H1; clear H1; vauto.
  (* faults *)
  - intro H1. inv H1; clear H1; vauto.
  - intro H1. inv H1; clear H1; vauto.
  (* simulations *)
  - intros s l P' s' STEP. inv STEP; clear STEP.
    + exists P'. split; vauto.
    + rename P' into Q'. exists Q'. split; vauto.
  - intros s l Q' s' STEP. inv STEP; clear STEP.
    + exists Q'. split; vauto.
    + rename Q' into P'. exists P'. split; vauto.
Qed.

Theorem bisim_alt_assoc :
  forall P Q R, bisim (Palt P (Palt Q R)) (Palt (Palt P Q) R).
Proof.
  cofix CH. intros P Q R. constructor. repeat split.
  (* termination *)
  - intro H1. inv H1; clear H1; vauto.
    inv H0; clear H0; vauto.
  - intro H1. inv H1; clear H1; vauto.
    inv H0; clear H0; vauto.
  (* faults *)
  - intro H1. inv H1; clear H1; vauto.
    inv H3; clear H3; vauto.
  - intro H1. inv H1; clear H1; vauto.
    inv H3; clear H3; vauto.
  (* simulations *)
  - intros s l P' s' STEP. inv STEP; clear STEP.
    + exists P'. split; vauto.
    + inv H5; clear H5.
      * rename P' into Q'. exists Q'. split; vauto.
      * rename P' into R'. exists R'. split; vauto.
  - intros s l Q' s' STEP. inv STEP; clear STEP.
    + inv H5; clear H5.
      * rename Q' into P'. exists P'. split; vauto.
      * exists Q'. split; vauto.
    + rename Q' into R'. exists R'. split; vauto.
Qed.

Theorem bisim_alt_dupl :
  forall P, bisim (Palt P P) P.
Proof.
  cofix CH. intros P. constructor. repeat split.
  (* termination *)
  - intro H1. inv H1.
  - intro H1. vauto.
  (* faulting *)
  - intro H1. inv H1.
  - intro H1. vauto.
  (* simulations *)
  - intros s l P' s' STEP. inv STEP; clear STEP.
    + exists P'. split; vauto.
    + exists P'. split; vauto.
  - intros s l P' s' STEP. exists P'. split; vauto.
Qed.

Theorem bisim_alt_delta :
  forall P, bisim (Palt P Pdelta) P.
Proof.
  cofix CH. intros P. constructor. repeat split.
  (* termination *)
  - intro H1. inv H1. inv H0.
  - intro H1. vauto.
  (* faulting *)
  - intro H1. inv H1. inv H3.
  - intro H1. vauto.
  (* simulations *)
  - intros s l P' s' STEP. inv STEP; vauto. inv H5.
  - intros s l P' s' STEP. exists P'. split; vauto.
Qed.

Theorem bisim_alt_distr :
  forall P Q R,
  bisim (Pseq (Palt P Q) R) (Palt (Pseq P R) (Pseq Q R)).
Proof.
  cofix CH. intros P Q R.
  constructor. repeat split.
  (* termination *)
  - intro H1. inv H1; clear H1.
    inv H2; clear H2; vauto.
  - intro H1. inv H1; clear H1.
    + inv H0. clear H0. vauto.
    + inv H0. clear H0. vauto.
  (* faulting *)
  - intro H1. inv H1; clear H1.
    + inv H3; clear H3; vauto.
    + inv H2; clear H2; vauto.
  - intro H1. inv H1; clear H1.
    + inv H3; clear H3; vauto.
    + inv H3; clear H3; vauto.
  (* simulations *)
  - intros s l P' s' STEP. inv STEP; clear STEP.
    + inv H5; clear H5.
      * rename P'0 into P'. exists (Pseq P' R). split; vauto.
      * rename P'0 into Q'.
        exists (Pseq Q' R). split; vauto.
    + rename P' into R'. inv H1; clear H1.
      * exists R'. split; vauto.
      * exists R'. split; vauto.
  - intros s l Q' s' STEP. inv STEP; clear STEP.
    + inv H5; clear H5.
      * exists (Pseq P' R). split; vauto.
      * rename Q' into R'. exists R'. split; vauto.
    + inv H5; clear H5.
      * rename P into Q'.
        exists (Pseq P' R). split; vauto.
      * rename Q' into R'. exists R'.
        split; vauto.
Qed.

Theorem bisim_par_comm :
  forall P Q, bisim (Ppar P Q) (Ppar Q P).
Proof.
  cofix CH. intros P Q. constructor. repeat split.
  (* termination *)
  - intro H. inv H. vauto.
  - intro H. inv H. vauto.
  (* faults *)
  - intro H. inv H; clear H.
    + by apply pfault_par_r.
    + by apply pfault_par_l.
  - intro H. inv H; clear H.
    + by apply pfault_par_r.
    + by apply pfault_par_l.
  (* simulations *)
  - intros s l P' s' H1. inv H1; clear H1.
    + rename P'0 into P'. exists (Ppar Q P').
      intuition vauto.
    + exists (Ppar Q' P). intuition vauto.
  - intros s l P' s' H1. inv H1; clear H1.
    + rename P'0 into Q'.
      exists (Ppar P Q'). intuition vauto.
    + rename Q' into P'.
      exists (Ppar P' Q). intuition vauto.
Qed.

Theorem bisim_par_assoc :
  forall P Q R, bisim (Ppar P (Ppar Q R)) (Ppar (Ppar P Q) R).
Proof.
  cofix CH. intros P Q R. constructor. repeat split.
  (* termination *)
  - intro H. inv H. clear H. inv H3. vauto.
  - intro H. inv H. clear H. inv H2. vauto.
  (* faults *)
  - intro H. inv H; clear H.
    + by repeat apply pfault_par_l.
    + inv H3; clear H3.
      * apply pfault_par_l. by apply pfault_par_r.
      * by repeat apply pfault_par_r.
  - intro H. inv H; clear H.
    + inv H3; clear H3.
      * by repeat apply pfault_par_l.
      * apply pfault_par_r. by apply pfault_par_l.
    + by repeat apply pfault_par_r.
  (* simulations *)
  - intros s l S s' H1. inv H1; clear H1.
    + exists (Ppar (Ppar P' Q) R). split; vauto.
    + inv H6; clear H6.
      * rename P' into Q'.
        exists (Ppar (Ppar P Q') R).
        split; vauto.
      * rename Q'0 into R'.
        exists (Ppar (Ppar P Q) R').
        split; vauto.
  - intros s l S s' H1. inv H1; clear H1.
    + inv H6; clear H6.
      * rename P'0 into P'.
        exists (Ppar P' (Ppar Q R)). intuition vauto.
      * exists (Ppar P (Ppar Q' R)). intuition vauto.
    + rename Q' into R'.
      exists (Ppar P (Ppar Q R')). intuition vauto.
Qed.

Theorem bisim_par_epsilon_l :
  forall P, bisim (Ppar Pepsilon P) P.
Proof.
  cofix CP. intros P. constructor. repeat split.
  (* termination *)
  - intro H. inv H.
  - intro H. apply pterm_par; auto.
    apply pterm_epsilon.
  (* faults *)
  - intro H. inv H. inv H3.
  - intro H. by apply pfault_par_r.
  (* simulations *)
  - intros s l P' s' H. inv H; clear H.
    + by inv H6.
    + rename Q' into P'. exists P'. split; vauto.
  - intros s l P' s' H.
    exists (Ppar Pepsilon P'). split; vauto.
Qed.

Theorem bisim_par_epsilon_r :
  forall P, bisim (Ppar P Pepsilon) P.
Proof.
  intro P. rewrite bisim_par_comm.
  by apply bisim_par_epsilon_l.
Qed.

Theorem bisim_par_delta :
  forall P, bisim (Ppar P Pdelta) (Pseq P Pdelta).
Proof.
  cofix CH. intros P. constructor. repeat split.
  (* termination *)
  - intro H1. inv H1. inv H3.
  - intro H1. inv H1. inv H3.
  (* faulting *)
  - intro H1. inv H1; vauto. inv H3.
  - intro H1. inv H1; vauto.
  (* simulations *)
  - intros s l P' s' STEP. inv STEP; clear STEP.
    + rename P'0 into P'.
      exists (Pseq P' Pdelta). intuition vauto.
    + inv H5.
  - intros s l Q' s' STEP. inv STEP; clear STEP.
    + exists (Ppar P' Pdelta). intuition vauto.
    + inv H6.
Qed.

Theorem bisim_lmerge_unfold :
  forall P Q, bisim (Ppar P Q) (Palt (Plmerge P Q) (Plmerge Q P)).
Proof.
  intros P Q. constructor. repeat split.
  (* termination *)
  - intros H1. inv H1. clear H1.
    apply pterm_alt_l. vauto.
  - intros H1. inv H1; clear H1.
    + inv H0. vauto.
    + inv H0. vauto.
  (* faults *)
  - intros H1. inv H1; clear H1.
    + apply pfault_alt_l. vauto.
    + apply pfault_alt_r. vauto.
  - intros H1. inv H1; clear H1.
    + inv H3. clear H3. vauto.
    + inv H3. clear H3. vauto.
  (* simulations *)
  - intros s l R s' H1. inv H1; clear H1.
    + exists (Ppar P' Q). intuition vauto.
    + exists (Ppar Q' P). intuition vauto.
      apply bisim_par_comm.
  - intros s l R s' H1. inv H1; clear H1.
    + inv H6. clear H6.
      exists (Ppar P' Q). intuition vauto.
    + inv H6; clear H6. rename P' into Q'.
      exists (Ppar P Q'). intuition vauto.
      apply bisim_par_comm.
Qed.

Theorem bisim_lmerge_delta :
  forall P, bisim (Plmerge Pdelta P) Pdelta.
Proof.
  intros P. constructor. repeat split.
  (* termination *)
  - intros H1. inv H1.
  - intros H1. inv H1.
  (* faults *)
  - intros H1. inv H1.
  - intros H1. inv H1.
  (* simulation *)
  - intros s l P' s' H1. inv H1. clear H1.
    rename P'0 into P'. inv H6.
  - intros s l P' s' H1. inv H1.
Qed.

Theorem bisim_lmerge_epsilon_delta :
  bisim (Plmerge Pepsilon Pdelta) Pdelta.
Proof.
  constructor. repeat split.
  (* termination *)
  - intros H1. inv H1.
  - intros H1. inv H1.
  (* faults *)
  - intros H1. inv H1. inv H3.
  - intros H1. inv H1.
  (* simulations *)
  - intros s l P' s' H1. inv H1. inv H6.
  - intros s l P' s' H1. inv H1.
Qed.

Theorem bisim_lmerge_epsilon_act :
  forall a v P, bisim (Plmerge Pepsilon (Pseq (Pact a v) P)) Pdelta.
Proof.
  intros a v P. constructor. repeat split.
  (* termination *)
  - intros H1. inv H1. inv H3. inv H4.
  - intros H1. inv H1.
  (* faults *)
  - intros H1. inv H1. inv H3.
  - intros H1. inv H1.
  (* simulations *)
  - intros s l P' s' H1. inv H1. clear H1.
    rename P'0 into P'. inv H6.
  - intros s l P' s' H1. inv H1.
Qed.

Theorem bisim_lmerge_act :
  forall a v P, bisim (Plmerge (Pact a v) P) (Pseq (Pact a v) P).
Proof.
  intros a v P. constructor. repeat split.
  (* termination *)
  - intros H1. inv H1. inv H2.
  - intros H1. inv H1. inv H2.
  (* faults *)
  - intros H1. inv H1. inv H3.
  - intros H1. inv H1.
    + inv H3.
    + inv H2.
  (* simulations *)
  - intros s l P' s' H1. inv H1. clear H1.
    rename P'0 into R. inv H6. clear H6.
    exists (Pseq Pepsilon P). intuition vauto.
    rewrite bisim_par_epsilon_l.
    by rewrite bisim_seq_epsilon_r.
  - intros s l P' s' H1. inv H1; clear H1.
    + rename P'0 into R. inv H6. clear H6.
      exists (Ppar Pepsilon P). intuition vauto.
      rewrite bisim_par_epsilon_l.
      by rewrite bisim_seq_epsilon_r.
    + inv H2.
Qed.

Theorem bisim_lmerge_epsilon :
  bisim (Plmerge Pepsilon Pepsilon) Pepsilon.
Proof.
  constructor. repeat split.
  (* termination *)
  - intros H1. inv H1.
  - intros H1. vauto.
  (* faults *)
  - intros H1. inv H1.
  - intros H1. vauto.
  (* simulations *)
  - intros s l P' s' H1. inv H1. inv H6.
  - intros s l P' s' H1. inv H1.
Qed.

Theorem bisim_lmerge_epsilon_alt :
  forall P Q,
  bisim (Plmerge Pepsilon (Palt P Q)) (Palt (Plmerge Pepsilon P) (Plmerge Pepsilon Q)).
Proof.
  intros P Q. constructor. repeat split.
  (* termination *)
  - intros H1. inv H1. clear H1. inv H3; clear H3.
    + apply pterm_alt_l. vauto.
    + apply pterm_alt_r. vauto.
  - intros H1. inv H1; clear H1.
    + inv H0. vauto.
    + inv H0. vauto.
  (* faults *)
  - intros H1. inv H1. inv H3.
  - intros H1. inv H1; clear H1.
    + inv H3. inv H2.
    + inv H3. inv H2.
  (* simulations *)
  - intros s l P' s' H1.
    inv H1. clear H1. inv H6.
  - intros s l Q' s' H1. inv H1; clear H1.
    + inv H6. inv H5.
    + inv H6. inv H5.
Qed.

Theorem bisim_lmerge_alt :
  forall P Q R,
  bisim (Plmerge (Palt P Q) R) (Palt (Plmerge P R) (Plmerge Q R)).
Proof.
  intros P Q R. constructor. repeat split.
  (* termination *)
  - intros H1. inv H1. clear H1. inv H2; clear H2.
    + apply pterm_alt_l. vauto.
    + apply pterm_alt_r. vauto.
  - intros H1. inv H1; clear H1.
    + inv H0. vauto.
    + inv H0. vauto.
  (* faults *)
  - intros H1. inv H1. clear H1. inv H3; clear H3.
    + apply pfault_alt_l. vauto.
    + apply pfault_alt_r. vauto.
  - intros H1. inv H1; clear H1.
    + inv H3. clear H3. vauto.
    + inv H3. clear H3. vauto.
  (* simulations *)
  - intros s l P' s' H1. inv H1. clear H1.
    rename P'0 into P'. inv H6; clear H6.
    + exists (Ppar P' R). intuition vauto.
    + rename P' into Q'. exists (Ppar Q' R).
      intuition vauto.
  - intros s l Q' s' H1. inv H1; clear H1.
    + inv H6. clear H6.
      exists (Ppar P' R). intuition vauto.
    + inv H6. clear H6.
      rename P' into Q'.
      exists (Ppar Q' R).
      intuition vauto.
Qed.

Theorem bisim_lmerge_assoc :
  forall P Q R,
  bisim (Plmerge (Plmerge P Q) R) (Plmerge P (Ppar Q R)).
Proof.
  intros P Q R. constructor. repeat split.
  (* termination *)
  - intros H1. inv H1. inv H2. vauto.
  - intros H1. inv H1. inv H3. vauto.
  (* faults *)
  - intros H1. inv H1. inv H3. vauto.
  - intros H1. inv H1. inv H1. vauto.
  (* simulations *)
  - intros s l P' s' H1. inv H1. clear H1.
    inv H6. clear H6. exists (Ppar P' (Ppar Q R)).
    intuition vauto. by rewrite bisim_par_assoc.
  - intros s l P' s' H1. inv H1. clear H1.
    rename P'0 into P'. exists (Ppar (Ppar P' Q) R).
    intuition vauto. by rewrite bisim_par_assoc.
Qed.

Theorem bisim_lmerge_seq_delta :
  forall P, bisim (Plmerge P Pdelta) (Pseq P Pdelta).
Proof.
  intros P. constructor. repeat split.
  (* termination *)
  - intros H1. inv H1. inv H3.
  - intros H1. inv H1. inv H3.
  (* faults *)
  - intros H1. inv H1. vauto.
  - intros H1. inv H1; clear H1; vauto. inv H4.
  (* simulations *)
  - intros s l P' s' H1. inv H1. clear H1.
    rename P'0 into P'. exists (Pseq P' Pdelta).
    intuition vauto. by rewrite bisim_par_delta.
  - intros s l P' s' H1. inv H1; clear H1.
    + rename P'0 into P'.
      exists (Ppar P' Pdelta). intuition vauto.
      by rewrite bisim_par_delta.
    + inv H7.
Qed.

Theorem bisim_lmerge_act_seq :
  forall a v P Q,
  bisim (Plmerge (Pseq (Pact a v) P) Q) (Pseq (Pact a v) (Ppar P Q)).
Proof.
  intros a v P Q. constructor. repeat split.
  (* termination *)
  - intros H1. inv H1. clear H1. inv H2. inv H1.
  - intros H1. inv H1. inv H2.
  (* faults *)
  - intros H1. inv H1. clear H1. inv H3; clear H3.
    + inv H2.
    + inv H1.
  - intros H1. inv H1; clear H1.
    + inv H3.
    + inv H2.
  (* simulations *)
  - intros s l P' s' H1.
    inv H1. clear H1. inv H6; clear H6.
    + inv H5. clear H5. exists (Pseq Pepsilon (Ppar P Q)).
      intuition vauto. by repeat rewrite bisim_seq_epsilon_r.
    + rename P'0 into P'. inv H1.
  - intros s l P' s' H1. inv H1; clear H1.
    + rename P'0 into P'. inv H6. clear H6.
      inv H7. clear H7.
      exists (Ppar (Pseq Pepsilon P) Q).
      intuition vauto.
      * apply pstep_lmerge; auto.
        apply pstep_seq_l; vauto.
      * by repeat rewrite bisim_seq_epsilon_r.
    + inv H2.
Qed.

Theorem bisim_assert :
  forall b1 b2,
  pcond_eval b1 = pcond_eval b2 ->
  bisim (Passert b1) (Passert b2).
Proof.
  intros b1 b2 H1. constructor. repeat split.
  (* termination *)
  - intros H2. inv H2.
  - intros H2. inv H2.
  (* faults *)
  - intros H2. inv H2. clear H2.
    constructor. rewrite <- H0. clear H0.
    symmetry. by apply equal_f.
  - intros H2. inv H2. clear H2.
    constructor. rewrite <- H0. clear H0.
    by apply equal_f.
  (* reductions *)
  - intros s l P' s' H2. inv H2. clear H2.
    exists Pepsilon. intuition.
    apply pstep_assert. by rewrite <- H1.
  - intros s l P' s' H2. inv H2. clear H2.
    exists Pepsilon. intuition.
    apply pstep_assert. by rewrite H1.
Qed.

Theorem bisim_cond_true :
  forall P, bisim (Pcond true P) P.
Proof.
  intro P. constructor. repeat split.
  (* termination *)
  - intro H1. inv H1.
  - intro H1. constructor; auto.
  (* faults *)
  - intro H1. inv H1.
  - intro H1. vauto.
  (* simulation *)
  - intros s l P' s' H1. inv H1. clear H1.
    exists P'. vauto.
  - intros s l P' s' H1. exists P'.
    intuition. constructor; vauto.
Qed.

Theorem bisim_cond_false :
  forall P, bisim (Pcond false P) Pdelta.
Proof.
  intros P. constructor. repeat split.
  (* termination *)
  - intro H1. inv H1.
  - intro H1. inv H1.
  (* faults *)
  - intro H1. inv H1.
  - intro H1. inv H1.
  (* simulations *)
  - intros s l P' s' H1. inv H1.
  - intros s l P' s' H1. inv H1.
Qed.

Theorem bisim_cond_conj :
  forall b1 b2 P, bisim (Pcond b1 (Pcond b2 P)) (Pcond (b1 && b2) P).
Proof.
  intros b1 b2 P. constructor. repeat split.
  (* termination *)
  - intros H1. inv H1.
  - intros H1. inv H1. symmetry in H. apply andb_prop in H.
    destruct H as (H2&H4). clarify. vauto.
  (* faults *)
  - intros H1. inv H1.
  - intros H1. inv H1. symmetry in H. apply andb_prop in H.
    destruct H as (H2&H4). clarify. vauto.
  (* simulations *)
  - intros s l P' s' H1. inv H1. clear H1. inv H6. clear H6.
    exists P'. simpl. intuition vauto.
  - intros s l P' s' H1. inv H1. clear H1.
    symmetry in H. apply andb_prop in H.
    destruct H as (H2&H4). clarify.
    exists P'. intuition vauto.
Qed.

Theorem bisim_sum_alt :
  forall f v, bisim (Psum f) (Palt (f v) (Psum f)).
Proof.
  intros f v. constructor. repeat split.
  (* termination *)
  - intro H1. inv H1. clear H1. rename v0 into v'.
    apply pterm_alt_r. by apply pterm_sum with v'.
  - intro H1. inv H1. clear H1. vauto.
  (* faulting *)
  - intro H1. inv H1. clear H1. rename v0 into v'.
    apply pfault_alt_r. vauto.
  - intro H1. inv H1. clear H1. vauto.
  (* simulations *)
  - intros s l P' s' STEP. inv STEP. clear STEP.
    rename v0 into v'. exists P'.
    intuition vauto.
  - intros s l P' s' STEP. inv STEP; clear STEP.
    + exists P'. intuition vauto.
    + inv H5. clear H5. rename v0 into v'.
      exists P'. intuition vauto.
Qed.

Theorem bisim_sum_alt_distr :
  forall f g,
  bisim (Psum (fun v => Palt (f v) (g v))) (Palt (Psum f) (Psum g)).
Proof.
  intros f g. constructor. repeat split.
  (* termination *)
  - intro H1. inv H1. clear H1. inv H0; clear H0; vauto.
  - intro H1. inv H1; clear H1.
    + inv H0. vauto.
    + inv H0. vauto.
  (* faulting *)
  - intros H1. inv H1. clear H1. inv H0; clear H0; vauto.
  - intros H1. inv H1; clear H1.
    + inv H3. clear H3. vauto.
    + inv H3. clear H3. vauto.
  (* simulations *)
  - intros s l P' s' STEP. inv STEP. clear STEP.
    inv H0; clear H0.
    + exists P'. intuition vauto.
    + exists P'. intuition vauto.
  - intros s l P' s' STEP. inv STEP; clear STEP.
    + inv H5. clear H5. exists P'. intuition vauto.
    + inv H5. clear H5. exists P'. intuition vauto.
Qed.

Theorem bisim_sum_seq :
  forall f P, bisim (Pseq (Psum f) P) (Psum (fun v => Pseq (f v) P)).
Proof.
  intros f P. constructor. repeat split.
  (* termination *)
  - intros H1. inv H1. clear H1. inv H2. clear H2. vauto.
  - intros H1. inv H1. clear H1. inv H0. clear H0. vauto.
  (* faulting *)
  - intros H1. inv H1; clear H1.
    + inv H3. clear H3. vauto.
    + inv H2. clear H2. vauto.
  - intros H1. inv H1. clear H1.
    inv H0; clear H0; vauto.
  (* simulations *)
  - intros s l P' s' STEP. inv STEP; clear STEP.
    + rename P'0 into R.
      inv H5. clear H5. exists (Pseq R P).
      intuition vauto.
    + inv H1. clear H1. exists P'.
      intuition vauto.
  - intros s l P' s' STEP. inv STEP. clear STEP.
    inv H0; clear H0.
    + rename P'0 into R.
      exists (Pseq R P). intuition vauto.
    + exists P'. intuition vauto.
Qed.

Theorem bisim_sum_indep :
  forall P, bisim (Psum (fun v => P)) P.
Proof.
  intros P. constructor. repeat split.
  (* termination *)
  - intros H1. inv H1.
  - intros H1. by apply pterm_sum with val_unit.
  (* reduction *)
  - intros H1. inv H1.
  - intros H1. by apply pfault_sum with val_unit.
  (* reduction *)
  - intros s l P' s' STEP. inv STEP. clear STEP.
    exists P'. intuition.
  - intros s l P' s' STEP. exists P'. intuition vauto.
    by apply pstep_sum with val_unit.
Qed.

Theorem bisim_sum_cond :
  forall b (f: Val -> Proc),
  bisim (Psum (fun v => Pcond b (f v))) (Pcond b (Psum f)).
Proof.
  intros b f. constructor. repeat split; vauto.
  (* termination *)
  - intro H1. inv H1. clear H1. inv H0. clear H0.
    constructor; vauto.
  - intro H1. inv H1. clear H1. inv H0. clear H0.
    apply pterm_sum with v. constructor; vauto.
  (* faults *)
  - intro H1. inv H1. clear H1. inv H0. clear H0.
    constructor; vauto.
  - intro H1. inv H1. clear H1. inv H3. clear H3.
    apply pfault_sum with v. constructor; vauto.
  (* reduction *)
  - intros s l P' s' H1. inv H1. clear H1. inv H0. clear H0.
    exists P'. intuition. constructor; vauto.
  - intros s l P' s' H1. inv H1. clear H1. inv H6. clear H6.
    exists P'. intuition. apply pstep_sum with v. vauto.
Qed.

Theorem bisim_iter_unroll :
  forall P, bisim (Piter P) (Palt (Pseq P (Piter P)) Pepsilon).
Proof.
  intro P. constructor. repeat split; vauto.
  (* faults *)
  - intros H1. apply pfault_alt_l.
    apply pfault_seq_l. inv H1.
  - intros H1. inv H1; clear H1.
    + inv H3. clear H3. vauto.
    + inv H3.
  (* reductions *)
  - intros s a P' s' H. inv H. clear H.
    rename P'0 into P'.
    exists (Pseq P' (Piter P)). split; vauto.
  - intros s a P' s' H. inv H; clear H.
    + inv H6; clear H6.
      * rename P'0 into P'.
        exists (Pseq P' (Piter P)). split; vauto.
      * inv H7. clear H7. rename P'0 into P'.
        exists (Pseq P' (Piter P)). split; vauto.
    + by inv H6.
Qed.

Lemma bisim_iter_seq_helper :
  forall P Q R,
  bisim (Pseq P (Piter (Palt Q R))) (Pseq (Pseq P (Piter Q)) (Piter (Pseq R (Piter Q)))).
Proof.
  cofix CH.
  intros P Q R. repeat split; vauto.
  (* termination *)
  - intros TERM. inv TERM.
    clear H2. constructor; vauto.
  - intros TERM. inv TERM.
    clear H2. inv H1. clear H3.
    constructor; vauto.
  (* faults *)
  - intros H1. inv H1; clear H1.
    + by repeat apply pfault_seq_l.
    + inv H4. clear H4. inv H0; clear H0.
      * apply pfault_seq_l. vauto.
      * apply pfault_seq_r; vauto.
  - intros H1. inv H1; clear H1.
    + inv H3; clear H3; vauto.
      inv H4. clear H4.
      apply pfault_seq_r; vauto.
    + inv H4. clear H4. inv H2. clear H2 H4.
      inv H0; clear H0.
      * apply pfault_seq_r; vauto.
      * inv H5. clear H5.
        apply pfault_seq_r; vauto.
  (* reductions *)
  - intros s a P' s' STEP. inv STEP; clear STEP.
    + rename P'0 into P'.
      exists (Pseq (Pseq P' (Piter Q)) (Piter (Pseq R (Piter Q)))).
      split; vauto.
    + inv H6. clear H6. inv H0; clear H0.
      * rename P'0 into Q'.
        exists (Pseq (Pseq Q' (Piter Q)) (Piter (Pseq R (Piter Q)))).
        split; vauto. constructor. apply pstep_seq_r; auto.
        by constructor.
      * rename P'0 into R'.
        exists (Pseq (Pseq R' (Piter Q)) (Piter (Pseq R (Piter Q)))).
        split; vauto. apply pstep_seq_r; vauto.
  - intros s a P' s' STEP. inv STEP; clear STEP.
    + inv H5; clear H5.
      * exists (Pseq P' (Piter (Palt Q R))). split; vauto.
      * inv H7; clear H7. rename P' into Q'.
        exists (Pseq Q' (Piter (Palt Q R))). split; vauto.
        apply pstep_seq_r; auto. apply pstep_iter.
        by apply pstep_alt_l.
    + inv H1. clear H1 H3. inv H6; clear H6; vauto.
      inv H0; clear H0.
      * rename P' into R'. exists (Pseq R' (Piter (Palt Q R))).
        split; vauto. apply pstep_seq_r; auto.
        by apply pstep_iter, pstep_alt_r.
      * inv H8; clear H8. rename P' into Q'.
        exists (Pseq Q' (Piter (Palt Q R))). split; vauto.
        apply pstep_seq_r; auto.
        by apply pstep_iter, pstep_alt_l.
Qed.

Theorem bisim_iter_seq :
  forall P Q,
  bisim (Piter (Palt P Q)) (Pseq (Piter P) (Piter (Pseq Q (Piter P)))).
Proof.
  intros P Q. repeat split; vauto.
  (* faults *)
  - intros H1. inv H1. clear H1.
    inv H0; clear H0.
    + apply pfault_seq_l; vauto.
    + apply pfault_seq_r; vauto.
  - intros H1. inv H1; clear H1.
    + inv H3. clear H3. constructor.
      by apply pfault_alt_l.
    + clear H2. inv H4. clear H4.
      inv H0; clear H0; vauto.
      inv H4. clear H4. vauto.
  (* reductions *)
  - intros s a P' s' H. inv H. clear H.
    inv H1; clear H1; rename P'0 into P'.
    + exists (Pseq (Pseq P' (Piter P)) (Piter (Pseq Q (Piter P)))).
      split; vauto. apply bisim_iter_seq_helper.
    + rename P' into Q'.
      exists (Pseq (Pseq Q' (Piter P)) (Piter (Pseq Q (Piter P)))).
      split; vauto.
      * apply pstep_seq_r; vauto.
      * apply bisim_iter_seq_helper.
  - intros s a P' s' STEP. inv STEP; clear STEP.
    + inv H5; vauto. clear H5.
      exists (Pseq P' (Piter (Palt P Q))). split; vauto.
      apply bisim_iter_seq_helper.
    + clear H1. inv H6. clear H6. inv H0; clear H0.
      * rename P' into Q'. exists (Pseq Q' (Piter (Palt P Q))).
        split; vauto. by apply bisim_iter_seq_helper.
      * inv H7; clear H7. exists (Pseq P' (Piter (Palt P Q))).
        split; vauto. by apply bisim_iter_seq_helper.
Qed.

Theorem bisim_iter_delta :
  bisim (Piter Pdelta) Pepsilon.
Proof.
  constructor. repeat split; vauto.
  (* faults *)
  - intro H1. inv H1. inv H0.
  - intro H1. inv H1.
  (* reductions *)
  - intros s a P' s' H. inv H. inv H1.
  - intros s a P' s' H. inv H.
Qed.

Theorem bisim_iter_epsilon :
  bisim (Piter Pepsilon) Pepsilon.
Proof.
  constructor. repeat split; vauto.
  (* faults *)
  - intro H1. inv H1.
  (* reductions *)
  - intros s a P' s' H. inv H. inv H1.
  - intros s a P' s' H. inv H.
Qed.


(** ** Process safety *)

(** Any process [P] is defined to be _safe_ with respect to
    any process store [s], written [psafe P s], if no
    fault can ever be reached from that configuration. *)

CoInductive psafe : Proc -> ProcStore -> Prop :=
  | proc_safe P s :
      (* no faults *)
      (~ pfault P s) /\
      (* reductions *)
      (forall l P' s', pstep P s l P' s' -> psafe P' s') ->
    psafe P s.

(** Process safety is closed under bisimilarity. *)

Lemma psafe_bisim :
  forall P Q s, bisim P Q -> psafe P s -> psafe Q s.
Proof.
  cofix CH. intros P Q s H1 H2. inv H2. clear H2.
  destruct H as (H2&H3). constructor. split.
  (* no faults *)
  - intro H4. apply H2. by rewrite H1.
  (* reductions *)
  - intros l P' s' H4. rename P' into Q'.
    inv H1. clear H1. destruct H as (_&_&_&H1).
    apply H1 in H4. clear H1. destruct H4 as (P'&H1&H4).
    apply CH with P'; auto. by apply H3 with l.
Qed.
Add Parametric Morphism : psafe
  with signature bisim ==> eq ==> iff
    as psafe_eq_mor.
Proof.
  intros P Q H s. split; intros.
  - apply psafe_bisim with P; auto.
  - apply psafe_bisim with Q; auto. by symmetry.
Qed.

(** Other properties of process safety. *)

Lemma psafe_seq_l :
  forall P1 P2 s, psafe (Pseq P1 P2) s -> psafe P1 s.
Proof.
  cofix CH. intros P1 P2 s H1. constructor. split.
  (* faults *)
  - intro H2. inv H1. clear H1.
    destruct H as (H&_). apply H. vauto.
  (* reductions *)
  - intros l P1' s' H2. inv H1. clear H1.
    destruct H as (_&H).
    assert (H1: pstep (Pseq P1 P2) s l (Pseq P1' P2) s') by vauto.
    apply H in H1. by apply CH in H1.
Qed.
Lemma psafe_seq_r :
  forall P1 P2 s, pterm P1 -> psafe (Pseq P1 P2) s -> psafe P2 s.
Proof.
  cofix CH. intros P1 P2 s H1 H2. constructor. split.
  (* faults *)
  - intro H3. inv H2. clear H2.
    destruct H as (H&_). apply H. apply pfault_seq_r; auto.
  (* reductions *)
  - intros l P2' s' H3. inv H2. clear H2.
    destruct H as (_&H).
    assert (H2: pstep (Pseq P1 P2) s l P2' s') by vauto.
    by apply H in H2.
Qed.

Lemma psafe_alt :
  forall P1 P2 s, psafe P1 s -> psafe P2 s -> psafe (Palt P1 P2) s.
Proof.
  cofix CH. intros P1 P2 s H1 H2.
  constructor. intuition.
  (* faults *)
  - inv H.
    + inv H1. clear H1. destruct H0 as (H1&_).
      by apply H1.
    + inv H2. clear H2. destruct H0 as (H2&_).
      by apply H2.
  (* reductions *)
  - inv H.
    + rename P' into P1'. inv H1. clear H1.
      destruct H0 as (_&H1). by apply H1 in H8.
    + rename P' into P2'. inv H2. clear H2.
      destruct H0 as (_&H2). by apply H2 in H8.
Qed.

Lemma psafe_alt_rev :
  forall P1 P2 s, psafe (Palt P1 P2) s -> psafe P1 s /\ psafe P2 s.
Proof.
  intros P1 P2 s H1. split.
  (* [P1] is safe *)
  - constructor. split.
    + intro H2. inv H1. clear H1.
      destruct H as (H&_). apply H.
      by apply pfault_alt_l.
    + intros l P1' s' H2. inv H1. clear H1.
      destruct H as (_&H).
      assert (H1: pstep (Palt P1 P2) s l P1' s') by vauto.
      by apply H in H1.
  (* [P2] is safe *)
  - constructor. split.
    + intro H2. inv H1. clear H1.
      destruct H as (H&_). apply H.
      by apply pfault_alt_r.
    + intros l P2' s' H2. inv H1. clear H1.
      destruct H as (_&H).
      assert (H1: pstep (Palt P1 P2) s l P2' s') by vauto.
      by apply H in H1.
Qed.

Lemma psafe_alt_l :
  forall P Q s, psafe (Palt P Q) s -> psafe P s.
Proof.
  intros P Q s H1.
  inv H1. destruct H as (H2&H3).
  constructor. split.
  (* faults *)
  - intro H4. apply H2. vauto.
  (* reductions *)
  - intros l P' s' H4.
    apply H3 with l. vauto.
Qed.
Lemma psafe_alt_r :
  forall P Q s, psafe (Palt P Q) s -> psafe Q s.
Proof.
  intros P Q s H1. rewrite bisim_alt_comm in H1.
  by apply psafe_alt_l in H1.
Qed.

Lemma psafe_delta :
  forall s, psafe Pdelta s.
Proof.
  intros s. constructor. intuition inv H.
Qed.

Lemma psafe_epsilon :
  forall s, psafe Pepsilon s.
Proof.
  intros s. constructor. intuition inv H.
Qed.

Lemma psafe_par_l :
  forall P1 P2 s, psafe (Ppar P1 P2) s -> psafe P1 s.
Proof.
  cofix CH. intros P1 P2 s H1. constructor. split.
  (* faults *)
  - intro H2. inv H1. clear H1.
    destruct H as (H&_). apply H.
    by apply pfault_par_l.
  (* reductions *)
  - intros l P1' s' H2. inv H1. clear H1.
    destruct H as (_&H).
    assert (H1: pstep (Ppar P1 P2) s l (Ppar P1' P2) s') by vauto.
    apply H in H1. by apply CH in H1.
Qed.
Lemma psafe_par_r :
  forall P1 P2 s, psafe (Ppar P1 P2) s -> psafe P2 s.
Proof.
  intros P1 P2 s H1. rewrite bisim_par_comm in H1.
  by apply psafe_par_l in H1.
Qed.

Lemma psafe_sum :
  forall f s,
    (forall v, psafe (f v) s) <->
  psafe (Psum f) s.
Proof.
  intros f s. split; intro H1.
  (* left-to-right *)
  - constructor. intuition.
    (* faults *)
    + inv H. specialize H1 with v.
      inv H1. clear H1. destruct H0 as (H1&_). done.
    (* reductions *)
    + inv H. clear H. specialize H1 with v.
      inv H1. clear H1. destruct H as (_&H1).
      by apply H1 in H2.
  (* right-to-left *)
  - intro v. constructor. split.
    (* faults *)
    + intro H2. inv H1. clear H1.
      destruct H as (H1&_). apply H1.
      by apply pfault_sum with v.
    (* reductions *)
    + intros l P' s' H2. inv H1. clear H1.
      destruct H as (_&H1).
      assert (H3 : pstep (Psum f) s l P' s') by vauto.
      clear H2. by apply H1 in H3.
Qed.

Lemma psafe_cond :
  forall P s, psafe (Pcond true P) s <-> psafe P s.
Proof.
  intros P s. split; intros H1.
  (* left-to-right *)
  - inv H1. clear H1. destruct H as (H1&H2).
    constructor. split.
    (* faults *)
    + intros H3. apply H1. vauto.
    (* reductions *)
    + intros l P' s' H3.
      assert (H4 : pstep (Pcond true P) s l P' s') by vauto.
      clear H3. by apply H2 in H4.
  (* right-to-left *)
  - constructor. split.
    (* faults *)
    + intros H2. inv H1. clear H1.
      destruct H as (H1&_). apply H1. inv H2.
    (* reductions *)
    + intros l P' s' H2. inv H2. clear H2. inv H1.
      clear H1. destruct H as (_&H2).
      by apply H2 in H0.
Qed.

End Processes.
