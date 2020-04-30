Require Import Assertions.
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


(** * Soundness *)

Module Type Soundness
  (domains : Domains)
  (heaps : Heaps domains)
  (hsolver : HeapSolver domains heaps)
  (procs : Processes domains)
  (procmaps : ProcMaps domains heaps procs)
  (progs : Programs domains heaps procs procmaps)
  (pmsolver : ProcMapSolver domains heaps procs procmaps)
  (assns : Assertions domains heaps hsolver procs procmaps progs pmsolver).

Export domains heaps hsolver procs procmaps pmsolver progs assns.


(** ** Process environments *)

(** The remaining theory assumes an _environment of process definitions_,
    which assigns to each (defined) process its precondition. *)

(** Note that processes do not have postconditions (any longer).
    Instead, processes have the [Passert] (or [HPassert]) constructors
    to specify that a certain property should hold at that point. *)

(** So we define process environments simply as a total function
    [precondition] that maps any process to its precondition. *)

Parameter precondition : HProc -> HCond.

(** Moreover, the remaining theory requires that all defined processes
    are _safe_ (with respect to [psafe]).  *)

Parameter precondition_safe :
  forall P s ps,
    pcond_eval (cDehybridise (precondition P) s) ps = true ->
    psafe (pDehybridise P s) ps.


(** ** Adequacy of process maps *)

(** The following definition captures what it means
    for a process map entry [c] to be _safe_
    (with respect to some heap [h]). *)

(** In particular this means that, if [c] is occupied,
    then the underlying process in [c] is safe with respect
    to any process store that corresponds with [h]. This
    correspondence is needed to connect process-algebraic
    state to shared program state. *)

Definition pmeSafe (h : Heap)(c : ProcMapEntry) : Prop :=
  match c with
    | PEelem _ P xs f =>
        forall ps,
          (forall x, In x xs -> h (f x) = Some (ps x)) ->
        psafe P ps
    | PEfree => True
    | PEinvalid => False
  end.

(** Safety of process map entries is preserved by bisimilarity. *)

Lemma pmeSafe_bisim :
  forall h c1 c2,
  pmeBisim c1 c2 -> pmeSafe h c1 -> pmeSafe h c2.
Proof.
  intros h c1 c2 H1 H2.
  unfold pmeSafe in *. destruct c1, c2; vauto.
  unfold pmeBisim in H1. destruct H1 as (F1&F2&F3&F4).
  clarify. intros ps IN1. rewrite <- F2.
  apply H2. intros y IN2.
  assert (IN3 : f y = f0 y). { apply map_eq_In with xs0; vauto. }
  rewrite IN3. by apply IN1.
Qed.
Add Parametric Morphism : pmeSafe
  with signature eq ==> pmeBisim ==> iff
    as pmeSafe_bisim_mor.
Proof.
  intros h c1 c2 H1. split; intros H2.
  - apply pmeSafe_bisim with c1; auto.
  - apply pmeSafe_bisim with c2; auto.
    by symmetry.
Qed.

(** Free entries are trivially safe. *)

Lemma pmeSafe_iden :
  forall h, pmeSafe h PEfree.
Proof. ins. Qed.

(** Safety of process map entries [c] is stable under replacing
    heaps that agree on all locations covered by [c]. *)

Lemma pmeSafe_heap_acc :
  forall h1 h2 c,
    (forall l, In l (pmeProj c) -> h1 l = h2 l) ->
  pmeSafe h1 c ->
  pmeSafe h2 c.
Proof.
  intros h1 h2 c H1 H2.
  unfold pmeSafe in *. desf.
  intros ps IN1. apply H2; vauto.
  intros y IN2. rewrite H1; [|by apply in_map].
  by apply IN1.
Qed.

(** Safety of process map entries is stable
    under extending (snapshot) heaps. *)

Lemma pmeSafe_subheap :
  forall h1 h2 c,
  (forall l v, h2 l = Some v -> h1 l = Some v) ->
  pmeSafe h1 c ->
  pmeSafe h2 c.
Proof.
  intros h1 h2 pme H1 H2.
  unfold pmeSafe in *. desf.
  intros ps IN1. apply H2. intros y IN2.
  by apply H1, IN1.
Qed.

Lemma pmeSafe_weaken_snapshot_l :
  forall ph1 ph2 c,
  phDisj ph1 ph2 ->
  pmeSafe (phSnapshot (phUnion ph1 ph2)) c ->
  pmeSafe (phSnapshot ph1) c.
Proof.
  intros ph1 ph2 c H1 H2. unfold pmeSafe in *.
  desf. intros ps H3. apply H2. clear H2.
  intros x H4. apply H3 in H4. clear H3.
  unfold phSnapshot in *.
  by apply phcSnapshot_union.
Qed.

Lemma pmeSafe_weaken_snapshot_r :
  forall ph1 ph2 c,
  phDisj ph1 ph2 ->
  pmeSafe (phSnapshot (phUnion ph1 ph2)) c ->
  pmeSafe (phSnapshot ph2) c.
Proof.
  intros ph1 ph2 c H1 H2.
  rewrite phUnion_comm in H2.
  apply pmeSafe_weaken_snapshot_l in H2; auto.
  by symmetry.
Qed.

(** Removing entry information does not invalidate safety. *)

Lemma pmeSafe_weaken_l :
  forall h c1 c2,
  pmeSafe h (pmeUnion c1 c2) ->
  pmeSafe h c1.
Proof.
  intros h c1 c2 H1. red in H1.
  red. unfold pmeUnion in H1.
  repeat desf. intros ps H2.
  apply psafe_par_l with P1. by apply H1.
Qed.

Lemma pmeSafe_weaken_r :
  forall h c1 c2,
  pmeSafe h (pmeUnion c1 c2) ->
  pmeSafe h c2.
Proof.
  intros h c1 c2 H1.
  rewrite pmeUnion_comm in H1.
  by apply pmeSafe_weaken_l in H1.
Qed.

(** Any process map is defined to be _safe_ (with respect to some heap)
    if all its entries are safe with respect to [pmeSafe]. *)

Definition pmSafe (h : Heap)(pm : ProcMap) : Prop :=
  forall pid, pmeSafe h (pm pid).

(** The identity process map is trivially safe. *)

Lemma pmSafe_iden :
  forall h, pmSafe h pmIden.
Proof.
  intros h pid. by apply pmeSafe_iden.
Qed.

(** Bisimilarity preserves safety. *)

Lemma pmSafe_bisim :
  forall h pm1 pm2,
  pmBisim pm1 pm2 -> pmSafe h pm1 -> pmSafe h pm2.
Proof.
  intros h pm1 pm2 H1 H2 pid.
  unfold pmSafe in H2.
  specialize H2 with pid.
  by rewrite <- H1.
Qed.
Add Parametric Morphism : pmSafe
  with signature eq ==> pmBisim ==> iff
    as pmSafe_bisim_mor.
Proof.
  intros h pm1 pm2 H1. split; intros H2.
  - apply pmSafe_bisim with pm1; auto.
  - apply pmSafe_bisim with pm2; auto.
    by symmetry.
Qed.

(** Process map safety is stable under extensions
    of the (snapshot) heap. *)

Lemma pmSafe_subheap :
  forall h1 h2 pm,
    (forall l v, h2 l = Some v -> h1 l = Some v) ->
  pmSafe h1 pm ->
  pmSafe h2 pm.
Proof.
  intros h1 h2 pm H1 H2. unfold pmSafe in *.
  intro pid. apply pmeSafe_subheap with h1; vauto.
Qed.

Lemma pmSafe_weaken_snapshot_l :
  forall ph1 ph2 pm,
  phDisj ph1 ph2 ->
  pmSafe (phSnapshot (phUnion ph1 ph2)) pm ->
  pmSafe (phSnapshot ph1) pm.
Proof.
  intros ph1 ph2 pm H1 H2.
  unfold pmSafe in *. intro pid.
  apply pmeSafe_weaken_snapshot_l with ph2; auto.
Qed.

Lemma pmSafe_weaken_snapshot_r :
  forall ph1 ph2 pm,
  phDisj ph1 ph2 ->
  pmSafe (phSnapshot (phUnion ph1 ph2)) pm ->
  pmSafe (phSnapshot ph2) pm.
Proof.
  intros ph1 ph2 pm H1 H2.
  rewrite phUnion_comm in H2.
  apply pmSafe_weaken_snapshot_l with ph1; auto.
  by symmetry.
Qed.

(** Removing process map information does not invalidate safety. *)

Lemma pmSafe_weaken_l :
  forall h pm1 pm2,
  pmSafe h (pmUnion pm1 pm2) ->
  pmSafe h pm1.
Proof.
  intros h pm1 pm2 H1. red in H1.
  red. intro pid.
  apply pmeSafe_weaken_l with (pm2 pid).
  apply H1.
Qed.

Lemma pmSafe_weaken_r :
  forall h pm1 pm2,
  pmSafe h (pmUnion pm1 pm2) ->
  pmSafe h pm2.
Proof.
  intros h pm1 pm2 H1.
  rewrite pmUnion_comm in H1.
  by apply pmSafe_weaken_l in H1.
Qed.


(** ** Well-structured process maps *)

(** A process map [pm] is defined to be _well-structured_
    if every heap location [l] is accessed by at most one entry of [pm].
    This definition therefore implies that all the entries of [pm]
    access different heap locations (i.e., disjoint parts of the heap). *)

(** This definition is important in the soundness argument,
    since every heap location can be subject to at most one
    "active process", and we need to make this fact explicit,
    which we do via [pmWs]. *)

Definition pmWs (pm : ProcMap) : Prop :=
  forall p1 p2 l,
    In l (pmeProj (pm p1)) -> In l (pmeProj (pm p2)) -> p1 = p2.

(** Bisimilarity preserves well-structuredness of process maps. *)

Lemma pmWs_bisim :
  forall pm1 pm2,
  pmBisim pm1 pm2 -> pmWs pm1 -> pmWs pm2.
Proof.
  intros pm1 pm2 H1 H2.
  unfold pmWs in *. intros p1 p2 l H3 H4.
  apply H2 with l; by rewrite H1.
Qed.
Add Parametric Morphism : pmWs
  with signature pmBisim ==> iff as pmWs_mor.
Proof.
  intros pm1 pm2 H1. split; intro H2.
  - apply pmWs_bisim with pm1; auto.
  - apply pmWs_bisim with pm2; auto.
    by symmetry.
Qed.

(** The identity process map is trivially well-structured. *)

Lemma pmWs_iden : pmWs pmIden.
Proof. red. ins. Qed.

(** Process map agreement preserves well-structuredness. *)

Lemma pmWs_agree :
  forall pm1 pm2,
  pmAgree pm1 pm2 -> pmWs pm1 -> pmWs pm2.
Proof.
  intros pm1 pm2 H1 H2 p1 p2 l H3 H4.
  red in H2. apply H2 with l; by rewrite H1.
Qed.
Add Parametric Morphism : pmWs
  with signature pmAgree ==> iff as pmWs_agree_mor.
Proof.
  intros pm1 pm2 H1. split; intro H2.
  - apply pmWs_agree with pm1; auto.
  - apply pmWs_agree with pm2; auto.
    by symmetry.
Qed.

(** Below are several other useful properties
    of well-structuredness. *)

Lemma pmWs_update :
  forall pm p c,
    (forall p' l, p <> p' -> In l (pmeProj c) -> ~ In l (pmeProj (pm p'))) ->
  pmWs pm ->
  pmWs (pmUpdate pm p c).
Proof.
  intros pm p c H1 H2. unfold pmWs in *.
  intros p1 p2 l H3 H4.
  unfold pmUpdate, update in H3, H4. desf.
  - apply H1 in H3; vauto.
  - apply H1 in H4; vauto.
  - by apply H2 with l.
Qed.


(** ** Adequacy *)

(** The auxiliary predicate [invariant_sat] determines
    whether a resource invariant [J] is satisfied by the given model
    in the context of the given program [C]. If the program is locked,
    we allow the resource invariant to be arbitrary
    (as in the proof system the resource invariant then becomes [Atrue]),
    but otherwise the model should hold with respect to [J]. *)

Definition invariant_sat (ph : PermHeap)(pm : ProcMap)(s g : Store)(C : GhostCmd)(J : Assn) : Prop :=
  ~ cmd_locked C -> sat ph pm s g J.

Fixpoint safe (n : nat)(basic : Prop)(C : GhostCmd)(ph : PermHeap)(pm : ProcMap)(s g : Store)(J A : Assn) : Prop :=
  match n with
    | O => True
    | S m =>
      (* (1) terminal programs satisfy their postcondition *)
        (C = Cskip -> sat ph pm s g A) /\
      (* (2) the program does not fault (which includes the absence of data-races) *)
      (forall phF pmF,
        phDisj ph phF ->
        pmDisj pm pmF ->
      let h := phConcr (phUnion ph phF) in
      let pm' := pmUnion pm pmF in
        hFinite h ->
        pmFinite pm' ->
        ~ gfault h pm' s g C) /\
      (* (3) all heap accesses are in the footprint (i.e. memory safety) *)
      (forall l, cmd_acc C s l -> phcLt PHCfree (ph l)) /\
      (* (4) all heap writes are in the footprint (i.e. memory safety) *)
      (forall l, cmd_writes C s l -> phcEntire (ph l)) /\
      (* (5) after performing a computation step the program remains safe for another [m] steps *)
      (forall phJ phF pmJ pmF pmC h' s' C',
        phDisj ph phJ ->
        phDisj (phUnion ph phJ) phF ->
        pmDisj pm pmJ ->
        pmDisj (pmUnion pm pmJ) pmF ->
        pmBisim (pmUnion (pmUnion pm pmJ) pmF) pmC ->
        pmFinite pmC ->
        pmWs pmC ->
        invariant_sat phJ pmJ s g C J ->
      let h := phConcr (phUnion (phUnion ph phJ) phF) in
      let hs := phSnapshot (phUnion (phUnion ph phJ) phF) in
        hFinite h ->
        pmCovers pmC hs ->
        pmSafe hs pmC ->
        step h s (plain C) h' s' C' ->
      exists ph' phJ',
        phDisj ph' phJ' /\
        phDisj (phUnion ph' phJ') phF /\
        phConcr (phUnion (phUnion ph' phJ') phF) = h' /\
        hFinite h' /\
        (basic -> phJ = phJ' /\ phSnapshot ph = phSnapshot ph') /\
      exists pm' pmJ' pmC',
        pmDisj pm' pmJ' /\
        pmDisj (pmUnion pm' pmJ') pmF /\
        pmBisim (pmUnion (pmUnion pm' pmJ') pmF) pmC' /\
        pmFinite pmC' /\
        pmWs pmC' /\
        (basic -> pmBisim pm pm' /\ pmBisim pmJ pmJ') /\
      let hs' := phSnapshot (phUnion (phUnion ph' phJ') phF) in
        pmCovers pmC' hs' /\
        pmSafe hs' pmC' /\
      exists g' C'',
        plain C'' = C' /\
        gstep h pmC s g C h' pmC' s' g' C'' /\
        invariant_sat phJ' pmJ' s' g' C'' J /\
        safe m basic C'' ph' pm' s' g' J A)
  end.

(** Safety is stable under replacing process maps by bisimilar ones. *)

Lemma safe_pmBisim :
  forall n basic C ph pm1 pm2 s g J A,
  pmBisim pm1 pm2 ->
  safe n basic C ph pm1 s g J A ->
  safe n basic C ph pm2 s g J A.
Proof.
  intros [|n] basic C ph pm1 pm2 s g J A EQ SAFE. vauto.
  destruct SAFE as (TERM&ABORT&ACC&WRITE&SAFE).
  repeat split; vauto.
  (* (1) terminal programs *)
  - intro H. rewrite <- EQ.
    by apply TERM.
  (* (2) absence of faults *)
  - red. intros phF pmF D1 D2 FIN1 FIN2 ABORT1.
    rewrite <- EQ in ABORT1.
    apply ABORT in ABORT1; vauto; by rewrite EQ.
  (* (5) program step *)
  - simpl.
    intros phJ phF pmJ pmF pmC h' s' C' D1 D2 D3 D4 H1 FIN1 WS INV FIN2 COV1 PSAFE STEP.
    apply SAFE with (pmJ := pmJ)(pmF := pmF)(pmC := pmC) in STEP; vauto; try by rewrite EQ.
    destruct STEP as (ph'&phJ'&D5&D6&H2&FIN3&BASIC1&STEP).
    destruct STEP as (pm'&pmJ'&pmC'&D7&D8&H3&FIN4&WS2&BASIC2&COV2&PSAFE1&STEP).
    destruct STEP as (g'&C''&H4&GSTEP&INV1&SAFE1). clarify.
    exists ph', phJ'. intuition vauto.
    exists pm', pmJ', pmC'. intuition vauto.
    by rewrite <- EQ.
Qed.

(** Safety is stable under replacing resource invariants
    by equivalent ones. *)

Lemma safe_aEquiv_inv :
  forall n basic C ph pm s g R1 R2 A,
  aEquiv R1 R2 ->
  safe n basic C ph pm s g R1 A ->
  safe n basic C ph pm s g R2 A.
Proof.
  induction n as [|n IH]. vauto.
  intros basic C ph pm s g R1 R2 A (AEQ1&AEQ2) SAFE. vauto.
  destruct SAFE as (TERM&ABORT&ACC&WRITE&SAFE).
  repeat split; vauto. simpl.
  intros phJ phF pmJ pmF pmC h' s' C' D1 D2 D3 D4 H2 FIN1 WS INV FIN2 COV1 PSAFE STEP.
  apply SAFE with (pmJ := pmJ)(pmF := pmF)(pmC := pmC) in STEP; vauto.
  - destruct STEP as (ph'&phJ'&D5&D6&H3&FIN3&BASIC1&STEP).
    destruct STEP as (pm'&pmJ'&pmC'&D7&D8&H4&FIN4&WS2&BASIC2&COV2&PSAFE1&STEP).
    destruct STEP as (g'&C''&H5&GSTEP&INV1&SAFE1). clarify.
    exists ph', phJ'. intuition vauto.
    exists pm', pmJ', pmC'. intuition vauto.
    exists g',C''. intuition vauto.
    + red. ins. apply AEQ1; auto; [phsolve|pmsolve].
    + by apply IH with R1.
  - red. ins. apply AEQ2; auto; [phsolve|pmsolve].
Qed.

(** Safety is stable under replacing postconditions by equivalent ones. *)

Lemma safe_aEquiv_post :
  forall n basic C ph pm s g R A1 A2,
  phValid ph ->
  pmValid pm ->
  aEquiv A1 A2 ->
  safe n basic C ph pm s g R A1 ->
  safe n basic C ph pm s g R A2.
Proof.
  induction n as [|n IH]. vauto.
  intros basic C ph pm s g R A1 A2 V1 V2 (AEQ1&AEQ2) SAFE. vauto.
  destruct SAFE as (TERM&ABORT&ACC&WRITE&SAFE).
  repeat split; vauto.
  - ins. apply AEQ1; auto.
  - simpl. intros phJ phF pmJ pmF pmC h' s' C' D1 D2 D3 D4 H2 FIN1 WS INV FIN2 COV1 PSAFE STEP.
    apply SAFE with (pmJ := pmJ)(pmF := pmF)(pmC := pmC) in STEP; vauto.
    destruct STEP as (ph'&phJ'&D5&D6&H3&FIN3&BASIC1&STEP).
    destruct STEP as (pm'&pmJ'&pmC'&D7&D8&H4&FIN4&WS2&BASIC2&COV2&PSAFE1&STEP).
    destruct STEP as (g'&C''&H5&GSTEP&INV1&SAFE1). clarify.
    exists ph', phJ'. intuition vauto.
    exists pm', pmJ', pmC'. intuition vauto.
    exists g',C''. intuition vauto.
    apply IH with A1; auto; [phsolve|pmsolve|by intuition].
Qed.

Add Parametric Morphism : safe
  with signature eq ==> eq ==> eq ==> eq ==> pmBisim ==> eq ==> eq ==> aEquiv ==> eq ==> iff
    as safe_bisim_mor.
Proof.
  intros n basic C ph pm1 pm2 H1 s g R1 R2 (H2&H3) A.
  split; intro H4.
  - apply safe_pmBisim with pm1; auto.
    by apply safe_aEquiv_inv with R1; auto.
  - apply safe_pmBisim with pm2; [pmclarify; pmsolve|].
    apply safe_aEquiv_inv with R2; auto.
    by symmetry.
Qed.

(** Adequacy is monotonic in the number of computation steps. *)

(** That is, if any configuration is safe for [n] steps, it
    must also be safe for less than [n] steps. *)

Open Scope nat_scope.

Lemma safe_mono :
  forall m n basic C ph pm s g J A,
  m <= n ->
  safe n basic C ph pm s g J A ->
  safe m basic C ph pm s g J A.
Proof.
  induction m as [|m IH]; intros n basic C ph pm a g J A LE SAFE.
  vauto. repeat split.
  (* (1) terminating programs *)
  - intro H. clarify. destruct n.
    by apply Nat.nle_succ_0 in LE.
    simpls. intuition.
  (* (2) absence of faults *)
  - red. intros phF pmF D1 D2 FIN1 FIN2 ABORT.
    destruct n. by apply Nat.nle_succ_0 in LE.
    destruct SAFE as (_&ABORT1&_).
    by apply ABORT1 with phF pmF.
  (* (3) heap accesses are in footprint *)
  - intros l H1.
    destruct n. by apply Nat.nle_succ_0 in LE.
    destruct SAFE as (_&_&LOC&_).
    by apply LOC in H1.
  (* (4) heap writes are in footprint *)
  - intros l H1.
    destruct n. by apply Nat.nle_succ_0 in LE.
    destruct SAFE as (_&_&_&WRITES&_).
    by apply WRITES in H1.
  (* (5) program step *)
  - simpl. intros phJ phF pmJ pmF pmC h' s' C' D1 D2 D3 D4 H1 FIN1 WS1 INV FIN2 COV1 PSAFE STEP.
    destruct n. by apply Nat.nle_succ_0 in LE.
    destruct SAFE as (TERM&ABORT'&LOCr&LOCw&SAFE).
    apply SAFE with (pmJ := pmJ)(pmF := pmF)(pmC := pmC) in STEP; vauto.
    destruct STEP as (ph'&phJ'&D5&D6&H2&FIN3&BASIC1&STEP).
    destruct STEP as (pm'&pmJ'&pmC'&D7&D8&H3&FIN4&WS2&BASIC2&COV2&PSAFE1&STEP).
    destruct STEP as (g'&C''&H4&GSTEP&INV1&SAFE1). clarify.
    exists ph', phJ'. intuition.
    exists pm', pmJ', pmC'. intuition.
    exists g', C''. intuition.
    apply IH with n; auto.
    by apply le_S_n.
Qed.

Close Scope nat_scope.

(** The [Cskip] program being safe in a certain state
    means that the postcondition holds in that state. *)

Lemma safe_skip :
  forall n basic ph pm s g J A,
  safe (S n) basic Cskip ph pm s g J A ->
  sat ph pm s g A.
Proof.
  intros n basic ph pm s g J A H.
  simpls. des. by apply H.
Qed.

Lemma safe_done :
  forall n basic ph pm s g J A,
  sat ph pm s g A ->
  safe n basic Cskip ph pm s g J A.
Proof.
  intros [|n] basic ph pm s g J A H. vauto.
  repeat split; vauto.
  (* (2) absence of faults *)
  - red. intros phF pmF D1 D2 FIN1 FIN2 ABORT.
    inv ABORT.
  (* (5) program step *)
  - simpl. intros phJ phF pmJ pmF pmC h' s' C' D1 D2 D3 D4 H1 FIN1 WS INV FIN2 COV1 PSAFE STEP.
    inv STEP.
Qed.

(** Any (ghost) store can be replaced by one that agrees on
    the values of all free variables in the program, resource invariant,
    and the postcondition. *)

Lemma safe_agree :
  forall n basic C ph pm s1 s2 g J A,
  sAgree (assn_fv A) s1 s2 ->
  sAgree (assn_fv J) s1 s2 ->
  sAgree (cmd_fv C) s1 s2 ->
  safe n basic C ph pm s1 g J A ->
  safe n basic C ph pm s2 g J A.
Proof.
  induction n as [|n IH]; auto.
  intros basic C ph pm s1 s2 g J A F1 F2 F3 SAFE.
  repeat split.
  (* (1) terminal programs *)
  - intro H. destruct SAFE as (TERM&_).
    rewrite <- sat_agree with (s1:=s1); auto.
  (* (2) absence of faults *)
  - red. intros phF pmF D1 D2 FIN1 FIN2 ABORT1.
    apply gfault_agree with (s2 := s1) in ABORT1; auto.
    destruct SAFE as (_&ABORT&_).
    apply ABORT with phF pmF; auto.
    intros x H1. symmetry. by apply F3.
  (* (3) heap reads are in footprint *)
  - intros l S1. destruct SAFE as (_&_&LOC&_).
    rewrite <- cmd_acc_agree with (s3 := s1) in S1; auto.
  (* (4) heap writes are in footprint *)
  - intros l S1. destruct SAFE as (_&_&_&WRITES&_).
    rewrite <- cmd_writes_agree with (s3 := s1) in S1; auto.
  (* (5) program step *)
  - simpl. intros phJ phF pmJ pmF pmC h' s2' C' D1 D2 D3 D4 H1 FIN1 WS1 SAT FIN2 COV1 PSAFE1 STEP.
    generalize STEP. intro STEP'.
    apply step_agree with (s2 := s1)(phi := fun x => cmd_fv C x \/ assn_fv J x \/ assn_fv A x) in STEP.
    destruct STEP as (s1'&H2 &STEP).
    apply SAFE with (pmJ := pmJ)(pmF := pmF)(pmC := pmC) in STEP; intuition vauto. clear SAFE.
    destruct STEP as (ph'&phJ'&D5&D6&H3&FIN3&BASIC1&STEP).
    destruct STEP as (pm'&pmJ'&pmC'&D7&D8&H4&FIN4&WS2&BASIC2&COV2&PSAFE2&STEP).
    destruct STEP as (g'&C''&H5&GSTEP&INV1&SAFE1). clarify.
    exists ph', phJ'. intuition.
    exists pm', pmJ', pmC'. intuition.
    exists g', C''. intuition vauto.
    1:{ (* ghost semantics can make a matching step *)
      apply gstep_agree_sim with s1 s1'; vauto.
      - intros x H3. symmetry. by apply F3.
      - intros x H3. apply H2. by left. }
    1:{ (* the resource invariant still holds after the program step *)
      red. unfold invariant_sat in INV1.
      intro H. apply sat_agree with (s1 := s1').
      - intros x F4. symmetry. apply H2. right. by left.
      - by apply INV1. }
    1:{ (* program is safe for [n] more steps *)
      apply IH with s1'; auto.
      - intros x H. symmetry. apply H2. by repeat right.
      - intros x H. symmetry. apply H2. right. by left.
      - intros x H3. symmetry. apply H2. left.
        apply gstep_fv_mod in GSTEP.
        destruct GSTEP as (G1&_). by apply G1. }
    1:{ (* resource invariant holds before program step *)
      red. unfold invariant_sat in SAT.
      intros H'. apply sat_agree with (s1 := s2).
      - intros x F4. symmetry. by apply F2.
      - by apply SAT. }
    1:{ (* all free variables of [C] are contained *)
      intros x H. left. by rewrite cmd_fv_plain. }
    1:{ (* program stores agree on all free variables *)
      intros x [F|[F|F]]; symmetry.
      - by apply F3.
      - by apply F2.
      - by apply F1. }
Qed.

Lemma safe_agree_ghost :
  forall n basic C ph pm s g1 g2 J A,
  sAgree (assn_fv A) g1 g2 ->
  sAgree (assn_fv J) g1 g2 ->
  sAgree (cmd_fv C) g1 g2 ->
  safe n basic C ph pm s g1 J A ->
  safe n basic C ph pm s g2 J A.
Proof.
  induction n; vauto.
  intros basic C ph pm s g1 g2 J A FV1 FV2 FV3 SAFE.
  repeat split.
  (* (1) terminal programs *)
  - intro H. destruct SAFE as (TERM&_).
    rewrite <- sat_agree_ghost with (g1 := g1); auto.
  (* (2) absence of faults *)
  - red. intros phF pmF D1 D2 FIN1 FIN2 ABORT'.
    apply gfault_agree_g with (g2 := g1) in ABORT'; auto.
    destruct SAFE as (_&ABORT&_).
    apply ABORT with phF pmF; auto.
    unfold sAgree in *.
    intros x FV4. symmetry. by apply FV3.
  (* (3) all heap reads are in the footprint *)
  - destruct SAFE as (_&_&ACC&_). vauto.
  (* (4) heap writes are in the footprint *)
  - destruct SAFE as (_&_&_&WRITES&_). vauto.
  (* (5) program step *)
  - simpl. intros phJ phF pmJ pmF pmC h' s' C' D1 D2 D3 D4 H1 FIN1 WS1 INV FIN2 COV1 PSAFE1 STEP.
    apply SAFE with (pmJ := pmJ)(pmF := pmF)(pmC := pmC) in STEP; auto.
    destruct STEP as (ph'&phJ'&D5&D6&H2&FIN3&BASIC1&STEP).
    destruct STEP as (pm'&pmJ'&pmC'&D7&D8&H3&FIN4&WS2&BASIC2&COV2&PSAFE&STEP).
    destruct STEP as (g'&C''&H4&GSTEP&INV1&SAFE1). clarify.
    exists ph', phJ'. intuition.
    exists pm', pmJ', pmC'. intuition.
    apply gstep_agree_g with (g2 := g2)(phi := fun x => cmd_fv C x \/ assn_fv J x \/ assn_fv A x) in GSTEP; auto.
    destruct GSTEP as (g2'&F4&GSTEP).
    exists g2', C''. intuition vauto.
    1:{ (* resource invariant still holds after program step *)
      red. unfold invariant_sat in INV1.
      intro H4. apply sat_agree_ghost with g'.
      - intros x F5. symmetry. apply F4. right. by left.
      - by apply INV1. }
    1:{ (* program is safe for [n] more steps *)
      apply IHn with g'; vauto.
      - intros x F9. apply F4. by vauto.
      - intros x F9. apply F4. by vauto.
      - apply gstep_fv_mod in GSTEP.
        destruct GSTEP as (F5&F6&F7&F8).
        intros x F9. apply F4. left. by apply F5. }
    1:{ (* The ghost stores [g1] and [g2] agree on all free variables in [C], [J], and [A] *)
      intros x [F5|[F5|F5]].
      - by apply FV3.
      - by apply FV2.
      - by apply FV1. }
    1:{ (* resource invariant holds before program step *)
      red. unfold invariant_sat in INV.
      intros H'. apply sat_agree_ghost with g2.
      - intros x F4. by apply FV2.
      - by apply INV. }
Qed.

(** Disjuncts in postconditions can always be introduced. *)

Lemma safe_disj_weaken :
  forall n basic C ph pm s g R A1 A2,
  safe n basic C ph pm s g R A1 ->
  safe n basic C ph pm s g R (Adisj A1 A2).
Proof.
  induction n as [|n IH]. vauto.
  intros basic C ph pm s g R A1 A2 SAFE.
  destruct SAFE as (TERM&ABORT&ACC&WRITE&SAFE).
  repeat split; vauto.
  - ins. left. by apply TERM.
  - simpl. intros phJ phF pmJ pmF pmC h' s' C' D1 D2 D3 D4 H2 FIN1 WS INV FIN2 COV1 PSAFE STEP.
    apply SAFE with (pmJ := pmJ)(pmF := pmF)(pmC := pmC) in STEP; vauto.
    destruct STEP as (ph'&phJ'&D5&D6&H3&FIN3&BASIC1&STEP).
    destruct STEP as (pm'&pmJ'&pmC'&D7&D8&H4&FIN4&WS2&BASIC2&COV2&PSAFE1&STEP).
    destruct STEP as (g'&C''&H5&GSTEP&INV1&SAFE1). clarify.
    exists ph', phJ'. intuition vauto.
    exists pm', pmJ', pmC'. intuition vauto.
    exists g',C''. intuition vauto. by apply IH.
Qed.


(** ** Soundness of the proof rules *)

(** The meaning of Hoare triples is given by 
    the following definition. *)

(** Intuitively [csl b J A C A'] holds if [C] is a user program,
    and moreover that [C] is safe for any number of reduction steps. *)

(** The extra [basic] parameter is purely for technical reasons.
    Recall that basic programs exclude certain language features
    such as specification-only commands. It later helps if we explicitly
    administer whether a [csl] judgement is used in the context of a
    basic program. The extra [basic] parameter is used for just that. *)

Definition csl (basic : Prop)(J : Assn)(A1 : Assn)(C : GhostCmd)(A2 : Assn) : Prop :=
  cmd_user C /\
  forall n ph pm s g,
    phValid ph ->
    pmValid pm ->
    pmSafe (phSnapshot ph) pm ->
    cmd_wf C ->
    sat ph pm s g A1 ->
    safe n basic C ph pm s g J A2.

(** Any assertion (pre- or postcondition, or resource invariant)
    can always be replaced by an equivalent one. *)

Add Parametric Morphism : csl
  with signature eq ==> aEquiv ==> aEquiv ==> eq ==> aEquiv ==> iff
    as csl_aEquiv_mor.
Proof.
  intros basic R1 R2 H1 A1 A2 H2 C A3 A4 H3.
  split; intros (H4&H5).
  - red. split; vauto. intros n ph pm s g V1 V2 SAFE1 WF1 SAT1.
    rewrite <- H1. apply safe_aEquiv_post with A3; auto.
    apply H5; vauto. destruct H2 as (_&H2). by apply H2.
  - red. split; vauto. intros n ph pm s g V1 V2 SAFE1 WF1 SAT1.
    rewrite H1. apply safe_aEquiv_post with A4; auto.
    + by symmetry.
    + apply H5; vauto. destruct H2 as (H2&_). by apply H2.
Qed.

(** Any program judgement with an unsatisfiable precondition
    trivially holds. *)

Lemma csl_trivial  :
  forall basic J C A,
  cmd_user C -> csl basic J Afalse C A.
Proof.
  intros basic J C A USER. red. split; vauto.
Qed.


(** *** Skip rule *)

Theorem rule_skip :
  forall basic J A,
  csl basic J A Cskip A.
Proof.
  intros basic J A. red. split. vauto.
  intros n ph pm s g V1 V2 SAFE1 WF SAT.
  by apply safe_done.
Qed.


(** *** Sequential composition *)

Open Scope nat_scope.

Lemma safe_seq :
  forall n basic C1 C2 J A1 A2 ph pm s g,
  phValid ph ->
  pmValid pm ->
  pmSafe (phSnapshot ph) pm ->
  safe n basic C1 ph pm s g J A1 ->
  (forall m ph' pm' s' g',
    m <= n ->
    phValid ph' ->
    pmValid pm' ->
    pmSafe (phSnapshot ph') pm' ->
    sat ph' pm' s' g' A1 ->
    safe m basic C2 ph' pm' s' g' J A2) ->
  safe n basic (Cseq C1 C2) ph pm s g J A2.
Proof.
  induction n as [|n IH]; vauto.
  intros basic C1 C2 J A1 A2 ph pm s g V1 V2 S1 SAFE1 SAFE2.
  repeat split; vauto.
  (* (2) absence of faults *)
  - red. intros phF pmF D1 D2 FIN1 FIN2 ABORT.
    destruct SAFE1 as (_&ABORT2&_).
    inv ABORT. by apply ABORT2 in H4.
  (* (3) all heap accesses are in footprint *)
  - simpls. intuition vauto.
  (* (4) all heap writes are in footprint *)
  - simpls. intuition vauto.
  (* (5) program step *)
  - destruct SAFE1 as (TERM&ABORT&ACC&WRITE&SAFE1). simpl.
    intros phJ phF pmJ pmF pmC h' s' C' D1 D2 D3 D4
      H1 FIN1 WS1 INV FIN2 COV1 PSAFE1 STEP.
    inv STEP; clear STEP.
    (* left program [C1] is not empty *)
    + apply SAFE1 with (pmJ := pmJ)(pmF := pmF)(pmC := pmC) in H7; auto.
      destruct H7 as (ph'&phJ'&D5&D6&H2&FIN3&BASIC1&H7).
      destruct H7 as (pm'&pmJ'&pmC'&D7&D8&H3&FIN4&WS2&BASIC2&COV2&PSAFE&H7).
      destruct H7 as (g'&C''&H4&GSTEP&INV1&SAFE3). clarify.
      exists ph', phJ'. intuition.
      exists pm', pmJ', pmC'. intuition.
      exists g', (Cseq C'' C2). intuition vauto.
      apply IH with A1; auto; [phsolve|pmsolve|].
      apply pmSafe_weaken_l with pmJ'.
      apply pmSafe_weaken_l with pmF.
      rewrite H3.
      apply pmSafe_weaken_snapshot_l with phJ'; [done|].
      by apply pmSafe_weaken_snapshot_l with phF.
    (* left program [C1] is empty *)
    + rename s' into s.
      symmetry in H3.
      apply plain_skip in H3. clarify.
      exists ph, phJ. intuition.
      exists pm, pmJ, pmC. intuition.
      exists g, C2. intuition auto; vauto.
      unfold invariant_sat in INV.
      intuition. red. done.
Qed.

Close Scope nat_scope.

Theorem rule_seq :
  forall basic J A1 A2 A3 C1 C2,
  csl basic J A1 C1 A2 ->
  csl basic J A2 C2 A3 ->
  csl basic J A1 (Cseq C1 C2) A3.
Proof.
  intros basic J A1 A2 A3 C1 C2 CSL1 CSL2.
  red. split; vauto.
  (* the program [C1; C2] is a _user program_ *)
  - constructor.
    + by destruct CSL1 as (?&_).
    + by destruct CSL2 as (?&_).
  (* the program [C1; C2] is safe for any number of steps *)
  - intros n ph pm s g V1 V2 S1 WF SAT.
    apply safe_seq with A2; auto.
    (* [C1] is safe for any number of steps *)
    + destruct CSL1 as (_&SAFE1).
      apply SAFE1; auto. inv WF.
    (* [C2] is safe for any number of steps *)
    + destruct CSL2 as (_&SAFE2).
      intros m ph' pm' s' g' LE V3 V4 SAT'.
      apply SAFE2; auto. inv WF.
Qed.


(** *** If-then-else rule *)

Lemma safe_ite :
  forall n basic J A1 A2 B C1 C2 ph pm s g,
  sat ph pm s g A1 ->
    (sat ph pm s g (Astar A1 (Aplain B)) -> safe n basic C1 ph pm s g J A2) ->
    (sat ph pm s g (Astar A1 (Aplain (Bnot B))) -> safe n basic C2 ph pm s g J A2) ->
  safe n basic (Cite B C1 C2) ph pm s g J A2.
Proof.
  induction n as [|n IH]; vauto.
  intros basic J A1 A2 B C1 C2 ph pm s g SAT1 SAFE1 SAFE2.
  repeat split; vauto.
  (* (2) absence of faults *)
  - red. intros phF pmF D1 D2 FIN1 FIN2 ABORT.
    inv ABORT.
  (* (5) program step *)
  - simpl. intros phJ phF pmJ pmF pmC h' s' C' D1 D2 D3 D4 H1 FIN1 WS1 INV FIN2 COV1 PSAFE1 STEP.
    inv STEP; clear STEP.
    (* computation step in [C1] *)
    + rename s' into s.
      exists ph, phJ. intuition.
      exists pm, pmJ, pmC. intuition.
      exists g, C1. intuition vauto.
      (* the resource invariant is still maintained after the step *)
      * unfold invariant_sat. intro H. by apply INV.
      (* the program is safe for [n] more steps *)
      * apply safe_mono with (S n); auto.
        apply SAFE1. simpl. exists ph, phIden.
        repeat split; [phsolve|phsolve|].
        exists pm, pmIden.
        repeat split; [pmsolve|pmsolve|by vauto|by vauto].
    (* computation step in [C2] *)
    + rename s' into s.
      exists ph, phJ. intuition.
      exists pm, pmJ, pmC. intuition.
      exists g, C2. intuition vauto.
      (* the resource invariant is still maintained after the step *)
      * unfold invariant_sat.
        intro H. by apply INV.
      (* the program is safe for [n] more steps *)
      * apply safe_mono with (S n). auto.
        apply SAFE2. simpl. exists ph, phIden. 
        repeat split; [phsolve|phsolve|].
        exists pm, pmIden.
        repeat split; [pmsolve|pmsolve|by vauto|by vauto].
Qed.

Theorem rule_ite :
  forall basic J A1 A2 B C1 C2,
  csl basic J (Astar A1 (Aplain B)) C1 A2 ->
  csl basic J (Astar A1 (Aplain (Bnot B))) C2 A2 ->
  csl basic J A1 (Cite B C1 C2) A2.
Proof.
  intros basic J A1 A2 B C1 C2 CSL1 CSL2. red. split.
  (* the program [Cite B C1 C2] is a user program *)
  - constructor.
    + by destruct CSL1 as (?&_).
    + by destruct CSL2 as (?&_).
  (* the program [Cite B C1 C2] is safe for any number of steps *)
  - intros n ph pm s g V1 V2 S1 WF SAT.
    apply safe_ite with A1; auto.
    (* [C1] is safe for any number of steps *)
    + intro SAT'. destruct CSL1 as (_&SAFE1).
      apply SAFE1; auto. inv WF.
    (* [C2] is safe for any number of steps *)
    + intro SAT'. destruct CSL2 as (_&SAFE2).
      apply SAFE2; auto. inv WF.
Qed.


(** *** While rule *)

Lemma safe_while :
  forall n basic B C ph pm s g J A,
  csl basic J (Astar A (Aplain B)) C A ->
  sat ph pm s g A ->
  cmd_wf C ->
  safe n basic (Cwhile B C) ph pm s g J (Astar A (Aplain (Bnot B))).
Proof.
  induction n as [|n IH]; vauto.
  intros basic B C ph pm s g J A CSL SAT1 WF.
  repeat split; vauto.
  (* (2) absence of faults *)
  - red. intros phF pmF D1 D2 FIN1 FIN2 ABORT. inv ABORT.
  (* (5) program step *)
  - simpl. intros phJ phF pmJ pmF pmC h' s' C' D1 D2 D3 D4 H1 FIN1 WS1 INV FIN2 COV1 PSAFE STEP.
    inv STEP. clear STEP.

    (* [pm] is safe with [ph]'s snapshot heap *)
    assert (S2 : pmSafe (phSnapshot ph) pm). {
      apply pmSafe_weaken_l with pmJ.
      apply pmSafe_weaken_l with pmF.
      rewrite H1.
      apply pmSafe_weaken_snapshot_l with phJ; [done|].
      by apply pmSafe_weaken_snapshot_l with phF. }

    exists ph, phJ. intuition.
    exists pm, pmJ, pmC. intuition.
    exists g, (Cite B (Cseq C (Cwhile B C)) Cskip).
    intuition vauto. rename s' into s.
    apply safe_ite with A; vauto.

    (* [C; while B C] is safe for [n] computation steps *)
    + intro SAT2. apply safe_seq with A; [phsolve|pmsolve|done| |].

      1:{ (* the program [C] is safe for [n] more steps *)
        apply CSL; auto; [phsolve|pmsolve]. }

      1:{ (* the composite program [Cwhile B C] is safe *)
        intros m ph' pm' s' g' LE V1 V2 S1 SAT3.
        apply safe_mono with n; auto. }

    (* the postcondition holds in case [C] is empty *)
    + by apply safe_done.
Qed.

Theorem rule_while :
  forall basic J A B C,
  csl basic J (Astar A (Aplain B)) C A ->
  csl basic J A (Cwhile B C) (Astar A (Aplain (Bnot B))).
Proof.
  intros basic J A B C CSL. red. split.
  (* the program [Cwhile B C] is a user program *)
  - by destruct CSL as (?&_).
  (* the program [Cwhile B C] is safe for any number of steps *)
  - intros. by apply safe_while.
Qed.


(** *** Assign rule *)

Lemma safe_assign :
  forall n basic J A x E ph pm s g,
  ~ assn_fv J x ->
  sat ph pm s g (assn_subst x E A) ->
  safe n basic (Cass x E) ph pm s g J A.
Proof.
  induction n as [|n IH]; vauto.
  intros basic J A x E ph pm s g H1 H2.
  repeat split; vauto.
  (* (2) absence of faults *)
  - red. intros phF pmF D1 D2 FIN1 FIN2 ABORT.
    inv ABORT.
  (* (5) program step *)
  - simpl. intros phJ phF pmJ pmF pmC h' s' C' D1 D2 D3 D4 H3 FIN1 WS1 INV FIN2 COV1 PSAFE STEP.
    inv STEP. clear STEP.
    exists ph, phJ. intuition.
    exists pm, pmJ, pmC. intuition.
    exists g, Cskip. intuition vauto.
    (* the resource invariant [J] is still satisfied *)
    + unfold invariant_sat in INV.
      red. intros _. rewrite sat_update; auto.
    (* program remains safe for [n] more steps *)
    + apply safe_done.
      by rewrite sat_subst in H2.
Qed.

Theorem rule_assign :
  forall basic J A x E,
  ~ assn_fv J x ->
  csl basic J (assn_subst x E A) (Cass x E) A.
Proof.
  ins. red. split; vauto. ins. by apply safe_assign.
Qed.


(** *** Rule of consequence *)

Lemma safe_conseq :
  forall n basic C ph pm s g J A1 A2,
  phValid ph ->
  pmValid pm ->
  pmSafe (phSnapshot ph) pm ->
  aEntails A1 A2 ->
  safe n basic C ph pm s g J A1 ->
  safe n basic C ph pm s g J A2.
Proof.
  induction n as [|n IH]; vauto.
  intros basic C ph pm s g J A1 A2 V1 V2 S1 ENT SAFE.
  repeat split; vauto.

  (* (1) terminal programs *)
  - intros ?. clarify.
    apply safe_skip in SAFE.
    by apply ENT.

  (* (2) absence of faults *)
  - red. intros phF pmF D1 D2 FIN1 FIN2 ABORT.
    destruct SAFE as (_&ABORT2&_).
    by apply ABORT2 in ABORT.

  (* (3) all heap accesses are in footprint *)
  - intros l H.
    destruct SAFE as (_&_&ACC&_).
    apply ACC in H. vauto.

  (* (4) all heap writes are in footprint *)
  - intros l H.
    destruct SAFE as (_&_&_&WRITE&_).
    apply WRITE in H. vauto.

  (* (5) program step *)
  - simpl. intros phJ phF pmJ pmF pmC h' s' C' D1 D2 D3 D4 H3 FIN1 WS1 INV FIN2 COV1 PSAFE1 STEP.
    destruct SAFE as (TERM&ABORT&ACC&WRITE&SAFE).
    apply SAFE with (pmJ := pmJ)(pmF := pmF)(pmC := pmC) in STEP; auto.
    destruct STEP as (ph'&phJ'&D5&D6&H2&FIN3&BASIC1&STEP).
    destruct STEP as (pm'&pmJ'&pmC'&D7&D8&H4&FIN4&WS2&BASIC2&COV2&PSAFE2&STEP).
    destruct STEP as (g'&C''&H5&GSTEP&INV1&SAFE1). clarify.
    exists ph', phJ'. intuition.
    exists pm', pmJ', pmC'. intuition.
    exists g', C''. intuition.
    apply IH with A1; auto; [phsolve|pmsolve|].

    1:{ (* [pm'] is safe with [ph']s snapshot heap *)
      apply pmSafe_weaken_l with pmJ'.
      apply pmSafe_weaken_l with pmF.
      rewrite H4.
      apply pmSafe_weaken_snapshot_l with phJ'; [done|].
      by apply pmSafe_weaken_snapshot_l with phF. }
Qed.

Theorem rule_conseq :
  forall basic J A1 A2 A1' A2' C,
  aEntails A1 A1' ->
  aEntails A2' A2 ->
  csl basic J A1' C A2' ->
  csl basic J A1 C A2.
Proof.
  intros basic J A1 A2 A1' A2' C EQ1 EQ2 CSL. red. split.
  (* the program [C] is a _user program_ *)
  - by destruct CSL as (?&_).
  (* the program [C] is safe for any number of steps *)
  - intros n ph pm s g V1 V2 S1 WF SAT.
    apply safe_conseq with A2'; vauto.
    destruct CSL as (_&SAFE).
    apply SAFE; auto.
Qed.


(** *** Disjunction rule *)

Theorem rule_disj :
  forall basic J A1 A2 A1' A2' C,
  csl basic J A1 C A1' ->
  csl basic J A2 C A2' ->
  csl basic J (Adisj A1 A2) C (Adisj A1' A2').
Proof.
  intros basic J A1 A2 A1' A2' C CSL1 CSL2. red. split.
  (* [C] is a basic program *)
  - red in CSL1. by destruct CSL1 as (?&_).
  (* [C] is safe for any number of steps *)
  - intros n ph pm s g V1 V2 S1 WF SAT.
    destruct CSL1 as (_&CSL1).
    destruct CSL2 as (_&CSL2).
    simpl in SAT. destruct SAT as [SAT|SAT].
    + apply safe_conseq with A1'; vauto. by apply CSL1.
    + apply safe_conseq with A2'; vauto. by apply CSL2.
Qed.

Corollary rule_disj_l :
  forall basic J A1 A2 A3 C,
  csl basic J A2 C A1 ->
  csl basic J A3 C A1 ->
  csl basic J (Adisj A2 A3) C A1.
Proof.
  intros basic J A1 A2 A3 C H1 H2.
  apply rule_conseq with (A1':=Adisj A2 A3)(A2':=Adisj A1 A1); auto.
  - by apply Adisj_idemp.
  - by apply rule_disj.
Qed.

Corollary rule_disj_r :
  forall basic J A1 A2 A3 C,
  csl basic J A1 C A2 ->
  csl basic J A1 C A3 ->
  csl basic J A1 C (Adisj A2 A3).
Proof.
  intros basic J A1 A2 A3 C H1 H2.
  apply rule_conseq with (A1':=Adisj A1 A1)(A2':=Adisj A2 A3); auto.
  - by apply Adisj_idemp.
  - by apply rule_disj.
Qed.

Lemma rule_disj_weaken :
  forall basic J A1 A2 A3 C,
  csl basic J A1 C A2 ->
  csl basic J A1 C (Adisj A2 A3).
Proof.
  intros basic J A1 A2 A3 C (H1&H2).
  red. split; auto. ins. apply safe_disj_weaken; auto.
Qed.


(** *** Frame rule *)

Lemma safe_frame :
  forall n basic C ph1 ph2 pm1 pm2 s g J A1 A2,
  phDisj ph1 ph2 ->
  pmDisj pm1 pm2 ->
  pmSafe (phSnapshot ph1) pm1 ->
  disjoint (assn_fv A2) (cmd_mod C) ->
  sat ph2 pm2 s g A2 ->
  safe n basic C ph1 pm1 s g J A1 ->
  safe n basic C (phUnion ph1 ph2) (pmUnion pm1 pm2) s g J (Astar A1 A2).
Proof.
  induction n as [|n IH]; vauto.
  intros basic C ph1 ph2 pm1 pm2 s g J A1 A2 D1 D2 S1 FV1 SAT1 SAFE1.
  repeat split; vauto.

  (* (1) terminal programs *)
  - intros ?. clarify.
    destruct SAFE1 as (TERM&_).
    exists ph1, ph2. intuition.
    exists pm1, pm2. intuition.

  (* (2) absence of faults *)
  - red. intros phF pmF D3 D4 FIN1 FIN2 ABORT1.
    destruct SAFE1 as (_&ABORT2&_).
    rewrite phUnion_assoc in ABORT1.
    rewrite pmUnion_assoc in ABORT1.
    apply ABORT2 in ABORT1; vauto.
    + phsolve.
    + pmsolve.
    + by rewrite <- phUnion_assoc.
    + by rewrite <- pmUnion_assoc.

  (* (3) all heap accesses are in the footprint *)
  - intros l FV2. destruct SAFE1 as (_&_&ACC&_).
    rewrite <- phUnion_cell.
    apply phcLt_weaken; auto.

  (* (4) all heap writes are in the footprint *)
  - intros l FV2. destruct SAFE1 as (_&_&_&WRITES&_).
    rewrite <- phUnion_cell.
    apply phcEntire_union; auto.

  (* (5) program step *)
  - simpl. intros phJ phF pmJ pmF pmC h' s' C' D3 D4 D5 D6 H1 FIN1 WS1 INV FIN2 COV1 PSAFE1 STEP.
    destruct SAFE1 as (_&_&_&_&SAFE1).
    rewrite phUnion_swap_r with (ph2:=ph2) in STEP.
    rewrite phUnion_swap_r with (ph2:=ph2) in STEP.
    rewrite phUnion_assoc in STEP.
    rewrite phUnion_comm with phF ph2 in STEP.
    apply SAFE1 with (pmJ := pmJ)(pmF := pmUnion pm2 pmF)(pmC := pmC) in STEP; clear SAFE1; auto.
    destruct STEP as (ph'&phJ'&D7&D8&H2&FIN3&BASIC1&STEP).
    destruct STEP as (pm'&pmJ'&pmC'&D9&D10&H3&FIN4&WS2&BASIC2&COV2&PSAFE2&STEP).
    destruct STEP as (g'&C''&H4&GSTEP&INV1&SAFE1). clarify.
    exists (phUnion ph' ph2), phJ'. intuition.

    1:{ (* disjointness of [ph' + ph2] and [phJ'] *)
      apply phDisj_union_r in D8; auto. 
      - rewrite phUnion_comm in D8.
        apply phDisj_assoc_l in D8; auto; phsolve.
      - apply phDisj_union_l with ph1; auto. phsolve. }

    1:{ (* disjointness of [ph' + ph2 + phJ'] and [phF] *)
      rewrite phUnion_swap_r.
      apply phDisj_assoc_r; auto.
      apply phDisj_union_l with ph1; auto. phsolve. }

    1:{ (* heap concretisation is proper *)
      rewrite phUnion_swap_r with (ph2 := ph2).
      by rewrite phUnion_assoc. }

    1:{ (* snapshot values are preserved, given that [C] is basic *)
      apply phSnapshot_disj_union_l; auto.
      apply phDisj_union_l with phJ; auto; [phsolve|].
      apply phDisj_union_r with phF; auto.
      - apply phDisj_union_l with ph1; auto. phsolve.
      - rewrite phUnion_comm with phJ ph'. phsolve. }

    exists (pmUnion pm' pm2), pmJ', pmC'. intuition.

    1:{ (* disjointness of [pm' + pm2] and [pmJ'] *)
      apply pmDisj_union_r in D10; auto.
      - rewrite pmUnion_comm in D10.
        apply pmDisj_assoc_l in D10; auto; pmsolve.
      - apply pmDisj_union_l with pm1; auto. pmsolve. }

    1:{ (* disjointness of [pm' + pm2 + pmJ'] and [pmF] *)
      rewrite pmUnion_swap_r.
      apply pmDisj_assoc_r; auto.
      apply pmDisj_union_l with pm1; auto. pmsolve. }

    1:{ (* structure of [pmC] is proper *)
      rewrite <- H3.
      rewrite pmUnion_swap_r with (pm2:=pm2).
      by rewrite <- pmUnion_assoc. }

    1:{ (* the process map has not been changed if [C] is basic *)
      by rewrite H5. }

    1:{ (* [pmC'] covers the new snapshot heap *)
      rewrite phUnion_swap_r with (ph2:=ph2).
      by rewrite phUnion_assoc. }

    1:{ (* the process map [pmC] is safe wrt. [ph + ph2 + phJ' + phF] *)
      rewrite phUnion_swap_r with (ph2:=ph2).
      by rewrite phUnion_assoc. }

    exists g', C''. intuition.

    1:{ (* the ghost semantics can make a matching step *)
      rewrite phUnion_swap_r with (ph2 := ph2).
      by rewrite phUnion_assoc. }

    apply IH; vauto.

    1:{ (* disjointness of [ph'] and [ph2] *)
      apply phDisj_union_l with phJ'; auto; [phsolve|].
      rewrite phUnion_comm.
      apply phDisj_union_r with phF; auto.
      apply phDisj_union_l with ph1; auto. phsolve. }

    1:{ (* disjointness of [pm'] and [pm2] *)
      apply pmDisj_union_l with pmJ'; auto; [pmsolve|].
      rewrite pmUnion_comm.
      apply pmDisj_union_r with pmF; auto.
      apply pmDisj_union_l with pm1; auto. pmsolve. }

    1:{ (* [pm'] is safe with [ph']s snapshot heap *)
      apply pmSafe_weaken_l with pmJ'.
      apply pmSafe_weaken_l with pm2.
      apply pmSafe_weaken_l with pmF.
      rewrite pmUnion_assoc. rewrite H3.
      apply pmSafe_weaken_snapshot_l with phJ'; [done|].
      by apply pmSafe_weaken_snapshot_l with (phUnion ph2 phF). }

    1:{ (* free variables of [A2] are not written to by [C''] *)
      red. intros x H4 H5. apply gstep_fv_mod in GSTEP.
      destruct GSTEP as (FV2&FV3&FV4&FV5).
      apply FV1 in H4. by apply FV3 in H5. }

    1:{ (* assertion [A1] is satisfied with [ph2] and [pm2] *)
      apply gstep_fv_mod in GSTEP.
      destruct GSTEP as (FV2&FV3&FV4&FV5).
      rewrite <- sat_agree with (s1:=s).
      rewrite <- sat_agree_ghost with (g1:=g). done.
      - intros x H2. apply FV5. intro. by apply FV1 with x.
      - intros x H2. apply FV4. intro. by apply FV1 with x. }

    1:{ (* [ph1] is disjoint with [phJ] *)
        phsolve. }

    1:{ (* disjointness of [ph1 + phJ] and [ph2 + phF] *)
      apply phDisj_assoc_l.
      - rewrite phUnion_comm.
        apply phDisj_assoc_r; auto. phsolve.
      - by rewrite phUnion_swap_r. }

    1:{ (* [pm1] is disjoint with [pmJ] *)
      pmsolve. }

    1:{ (* disjointness of [pm1 + pmJ] and [pm2 + pmF] *)
      apply pmDisj_assoc_l.
      - rewrite pmUnion_comm.
        apply pmDisj_assoc_r; auto. pmsolve.
      - by rewrite pmUnion_swap_r. }

    1:{ (* the composition of [pmC] is correct *)
      rewrite <- H1. rewrite pmUnion_assoc.
      rewrite pmUnion_swap_l with (pm2:=pm2).
      by repeat rewrite <- pmUnion_assoc. }

    1:{ (* the composite heap [ph1 + phJ + ph2 + phF] is finite *)
      rewrite phUnion_assoc.
      rewrite phUnion_swap_l with (ph2:=ph2).
      by repeat rewrite <- phUnion_assoc. }

    1:{ (* the map [pmC] covers the old snapshot heap *)
      rewrite <- phUnion_assoc.
      by rewrite phUnion_swap_r with (ph2:=phJ). }

    1:{ (* the map [pmC] is safe with [ph1 + phJ + ph2 + phF] *)
      rewrite phUnion_assoc.
      rewrite phUnion_swap_l with (ph2:=ph2).
      by repeat rewrite <- phUnion_assoc. }
Qed.

Theorem rule_frame :
  forall basic J A1 A2 A3 C,
  disjoint (assn_fv A3) (cmd_mod C) ->
  csl basic J A1 C A2 ->
  csl basic J (Astar A1 A3) C (Astar A2 A3).
Proof.
  intros basic J A1 A2 A3 C FV CSL. red. split.

  (* the program [C] is a user program *)
  - by destruct CSL as (?&_).

  (* the program [C] is safe for any number of steps *)
  - intros n ph pm s g V1 V2 S1 WF SAT.
    destruct CSL as (_&SAFE).
    destruct SAT as (ph1&ph2&D1&H1&SAT).
    destruct SAT as (pm1&pm2&D2&H2&SAT1&SAT2).
    rewrite <- H1, <- H2.

    (* [pm1] is safe with [ph1]s snapshot heap *)
    assert (S2 : pmSafe (phSnapshot ph1) pm1). {
      clarify. rewrite <- H2 in S1. clear H2.
      apply pmSafe_weaken_l with pm2.
      by apply pmSafe_weaken_snapshot_l with ph2. }

    apply safe_frame; auto.
    apply SAFE; auto; [phsolve|pmsolve].
Qed.


(** *** Heap reading *)

Lemma rule_lookup_std :
  forall basic x E1 q E2 J A,
  ~ In x (expr_fv E1) ->
  ~ In x (expr_fv E2) ->
  ~ assn_fv J x ->
  csl basic J (Astar (assn_subst x E2 A) (Apointsto PTTstd q E1 E2)) (Cread x E1) (Astar A (Apointsto PTTstd q E1 E2)).
Proof.
  intros basic x E1 q E2 J A FV1 FV2 FV3. red. split; vauto.
  intros [|n] ph pm s g V1 V2 S1 WF SAT. vauto.
  destruct SAT as (ph1&ph2&D1&EQ1&pm1&pm2&D2&EQ2&SAT1&(V3&SAT2)).
  clarify.

  assert (EQ3 : phcConcr (ph2 (expr_eval E1 s)) = Some (expr_eval E2 s)). {
    unfold sat in SAT2.
    apply phcConcr_le_some with (v := expr_eval E2 s) in SAT2; vauto. }
  assert (EQ4 : phcConcr (phUnion ph1 ph2 (expr_eval E1 s)) = Some (expr_eval E2 s)). {
    rewrite <- phUnion_cell.
    apply phcConcr_le_some with (phc1 := ph2 (expr_eval E1 s)); vauto.
    rewrite phcUnion_comm. apply phcLe_mono_pos; auto. phsolve. }

  repeat split; vauto.

  (* (2) absence of faults *)
  - red. intros phF pmF D3 D4 FIN1 FIN2 ABORT.
    inv ABORT. clear ABORT.
    unfold phConcr in H4. rewrite <- phUnion_cell in H4.
    apply phcConcr_le_none with (phc1 := phUnion ph1 ph2 (expr_eval E1 s)) in H4.
    + apply phcConcr_le_none with (phc1 := PHCstd q (expr_eval E2 s)) in H4; vauto.
    + by apply phcLe_mono_pos.

  (* (3) all heap accesses are in the footprint *)
  - intros l H1. simpl in H1. clarify.
    unfold sat in SAT2.
    apply phcLt_le_trans with (PHCstd q (expr_eval E2 s)); auto.
    transitivity (ph2 (expr_eval E1 s)); auto.
    rewrite phUnion_comm. apply phcLe_mono_pos. auto.
    by symmetry.

  (* (5) program step *)
  - simpl. intros phJ phF pmJ pmF pmC h' s' C' D3 D4 D5 D6 H1 FIN1 WS1 INV FIN2 COV1 PSAFE1 STEP.
    inv STEP. clear STEP.

    (* [v] equals the evaluation of [E1] *)
    assert (EQ5 : phcConcr (phUnion (phUnion (phUnion ph1 ph2) phJ) phF (expr_eval E1 s)) = Some (expr_eval E2 s)). {
      apply phcConcr_union, phcConcr_union; auto. }
    assert (EQ6 : expr_eval E2 s = v). {
      cut (Some (expr_eval E2 s) = Some v); try intuition vauto.
      by rewrite <- EQ5, <- H7. }

    clarify.
    exists (phUnion ph1 ph2), phJ. intuition.
    exists pm, pmJ, pmC. intuition.
    exists g, Cskip. intuition vauto.

    1:{ (* the resource invariant [J] is still satisfied *)
      intros _. rewrite sat_update; auto. }

    apply safe_done.
    exists ph1, ph2. repeat split; vauto.
    exists pm1, pm2. split; [done|].
    split; [done|]. split.
    + by rewrite sat_subst in SAT1.
    + unfold sat. split; [done|].
      unfold sat in SAT2.
      repeat rewrite expr_eval_upd; auto.
Qed.

Lemma rule_lookup_proc :
  forall basic x E1 q E2 J A,
  ~ In x (expr_fv E1) ->
  ~ In x (expr_fv E2) ->
  ~ assn_fv J x ->
  csl basic J (Astar (assn_subst x E2 A) (Apointsto PTTproc q E1 E2)) (Cread x E1) (Astar A (Apointsto PTTproc q E1 E2)).
Proof.
  intros basic x E1 q E2 J A FV1 FV2 FV3. red. split; vauto.
  intros [|n] ph pm s g V1 V2 S1 WF SAT. vauto.
  destruct SAT as (ph1&ph2&D1&EQ1&pm1&pm2&D2&EQ2&SAT1&(V3&SAT2)).
  clarify.

  assert (EQ3 : phcConcr (ph2 (expr_eval E1 s)) = Some (expr_eval E2 s)). {
    unfold sat in SAT2.
    apply phcConcr_le_some with (v := expr_eval E2 s) in SAT2; vauto. }
  assert (EQ4 : phcConcr (phUnion ph1 ph2 (expr_eval E1 s)) = Some (expr_eval E2 s)). {
    rewrite <- phUnion_cell.
    apply phcConcr_le_some with (phc1 := ph2 (expr_eval E1 s)); vauto.
    rewrite phcUnion_comm. apply phcLe_mono_pos; auto.
    by symmetry. }

  repeat split; vauto.

  (* (2) absence of faults *)
  - red. intros phF pmF D3 D4 FIN1 FIN2 ABORT.
    inv ABORT. clear ABORT.
    unfold phConcr in H4. rewrite <- phUnion_cell in H4.
    apply phcConcr_le_none with (phc1 := phUnion ph1 ph2 (expr_eval E1 s)) in H4.
    + apply phcConcr_le_none with (phc1 := PHCproc q (expr_eval E2 s)) in H4; vauto.
    + by apply phcLe_mono_pos.

  (* (3) all heap accesses are in the footprint *)
  - intros l H1. simpl in H1. clarify.
    unfold sat in SAT2.
    apply phcLt_le_trans with (PHCproc q (expr_eval E2 s)); auto.
    transitivity (ph2 (expr_eval E1 s)); auto.
    rewrite phUnion_comm. apply phcLe_mono_pos. auto.
    by symmetry.

  (* (5) program step *)
  - simpl. intros phJ phF pmJ pmF pmC h' s' C' D3 D4 D5 D6 H1 FIN1 WS1 INV FIN2 COV1 PSAFE1 STEP.
    inv STEP. clear STEP.

    (* [v] equals the evaluation of [E1] *)
    assert (EQ5 : phcConcr (phUnion (phUnion (phUnion ph1 ph2) phJ) phF (expr_eval E1 s)) = Some (expr_eval E2 s)). {
      apply phcConcr_union, phcConcr_union; auto. }
    assert (EQ6 : expr_eval E2 s = v). {
      cut (Some (expr_eval E2 s) = Some v); try intuition vauto.
      by rewrite <- EQ5, <- H7. }

    clarify.
    exists (phUnion ph1 ph2), phJ. intuition.
    exists pm, pmJ, pmC. intuition.
    exists g, Cskip. intuition vauto.

    1:{ (* the resource invariant [J] is still satisfied *)
      intros _. rewrite sat_update; auto. }

    apply safe_done.
    exists ph1, ph2. repeat split; vauto.
    exists pm1, pm2. split; [done|].
    split; [done|]. split.

    + by rewrite sat_subst in SAT1.
    + unfold sat. split; [done|].
      unfold sat in SAT2.
      repeat rewrite expr_eval_upd; auto.
Qed.

Lemma rule_lookup_act :
  forall basic x E1 q E2 J A,
  ~ In x (expr_fv E1) ->
  ~ In x (expr_fv E2) ->
  ~ assn_fv J x ->
  csl basic J (Astar (assn_subst x E2 A) (Apointsto PTTact q E1 E2)) (Cread x E1) (Astar A (Apointsto PTTact q E1 E2)).
Proof.
  intros basic x E1 q E2 J A FV1 FV2 FV3. red. split; vauto.
  intros [|n] ph pm s g V1 V2 S1 WF SAT. vauto.
  destruct SAT as (ph1&ph2&D1&EQ1&pm1&pm2&D2&EQ2&SAT1&(V3&(v'&SAT2))).
  clarify.

  assert (EQ3 : phcConcr (ph2 (expr_eval E1 s)) = Some (expr_eval E2 s)). {
    unfold sat in SAT2.
    apply phcConcr_le_some with (v := expr_eval E2 s) in SAT2; vauto. }
  assert (EQ4 : phcConcr (phUnion ph1 ph2 (expr_eval E1 s)) = Some (expr_eval E2 s)). {
    rewrite <- phUnion_cell.
    apply phcConcr_le_some with (phc1 := ph2 (expr_eval E1 s)); vauto.
    rewrite phcUnion_comm. apply phcLe_mono_pos; auto.
    by symmetry. }

  repeat split; vauto.

  (* (2) absence of faults *)
  - red. intros phF pmF D3 D4 FIN1 FIN2 ABORT.
    inv ABORT. clear ABORT.
    unfold phConcr in H4. rewrite <- phUnion_cell in H4.
    apply phcConcr_le_none with (phc1 := phUnion ph1 ph2 (expr_eval E1 s)) in H4.
    + apply phcConcr_le_none with (phc1 := PHCact q (expr_eval E2 s) v') in H4; vauto.
    + by apply phcLe_mono_pos.

  (* (3) all heap accesses are in the footprint *)
  - intros l H1. simpl in H1. clarify.
    unfold sat in SAT2.
    apply phcLt_le_trans with (PHCact q (expr_eval E2 s) v'); auto.
    transitivity (ph2 (expr_eval E1 s)); auto.
    rewrite phUnion_comm. apply phcLe_mono_pos. auto.
    by symmetry.

  (* (5) program step *)
  - simpl. intros phJ phF pmJ pmF pmC h' s' C' D3 D4 D5 D6 H1 FIN1 WS1 INV FIN2 COV1 PSAFE1 STEP.
    inv STEP. clear STEP.

    (* [v] equals the evaluation of [E1] *)
    assert (EQ5 : phcConcr (phUnion (phUnion (phUnion ph1 ph2) phJ) phF (expr_eval E1 s)) = Some (expr_eval E2 s)). {
      apply phcConcr_union, phcConcr_union; auto. }
    assert (EQ6 : expr_eval E2 s = v). {
      cut (Some (expr_eval E2 s) = Some v); try intuition vauto.
      by rewrite <- EQ5, <- H7. }

    clarify.
    exists (phUnion ph1 ph2), phJ. intuition.
    exists pm, pmJ, pmC. intuition.
    exists g, Cskip. intuition vauto.

    1:{ (* the resource invariant [J] is still satisfied *)
      intros _. rewrite sat_update; auto. }

    apply safe_done.
    exists ph1, ph2. repeat split; vauto.
    exists pm1, pm2. split; [done|].
    split; [done|]. split.

    + by rewrite sat_subst in SAT1.
    + unfold sat. split; [done|].
      exists v'. unfold sat in SAT2.
      repeat rewrite expr_eval_upd; auto.
Qed.

Theorem rule_lookup :
  forall basic x E1 q E2 J A t,
  ~ In x (expr_fv E1) ->
  ~ In x (expr_fv E2) ->
  ~ assn_fv J x ->
  csl basic J (Astar (assn_subst x E2 A) (Apointsto t q E1 E2)) (Cread x E1) (Astar A (Apointsto t q E1 E2)).
Proof.
  intros basic x E1 q E2 J A t FV1 FV2 FV3. destruct t.
  - by apply rule_lookup_std.
  - by apply rule_lookup_proc.
  - by apply rule_lookup_act.
Qed.


(** *** Heap writing *)

(** Soundness of the rules for heap writing. In the paper these rules are
    presented as a single rule (for presentational convenience), but here
    we handle heap writing via two separate rules -- one for handling
    points-to ownership predicates of type [PTTstd], and one for [PTTact]. *)

Theorem rule_write_std :
  forall basic J E1 E2 E3,
  csl basic J (Apointsto PTTstd 1 E1 E3) (Cwrite E1 E2) (Apointsto PTTstd 1 E1 E2).
Proof.
  intros basic J E1 E2 E3. red. split; vauto.
  intros [|n] ph pm s g V1 V2 S1 WF (V3&SAT).
  vauto. repeat split; vauto.

	(* (2) absence of faults *)
  - red. intros phF pmF D1 D2 _ _ ABORT.
    inv ABORT. clear ABORT.
    unfold sat in SAT.
    unfold phConcr in H4.
    rewrite <- phUnion_cell in H4.
    apply phcConcr_le_none with (phc1 := PHCstd 1 (expr_eval E3 s)) in H4; vauto.
    transitivity (ph (expr_eval E1 s)); vauto.
    by apply phcLe_mono_pos.

	(* (3) all heap accesses are in the footprint *)
  - intros l H1. unfold sat in SAT.
    simpl in H1. clarify.
    apply phcLt_le_trans with (PHCstd 1 (expr_eval E3 s)); auto.

  (* (4) all heap writes are in footprint *)
  - intros l H1. simpl in H1. clarify.
    unfold sat in SAT.
    apply phcEntire_le with (PHCstd 1 (expr_eval E3 s)); vauto.

  (* (5) program step *)
  - simpl. intros phJ phF pmJ pmF pmC h' s' C' D1 D2 D3 D4 H1 FIN1 WS1 INV FIN2 COV1 PSAFE1 STEP.
    inv STEP. clear STEP. subst l l0 v' v'0.
    unfold sat in SAT.
    apply phcLe_entire_eq in SAT; vauto.

    (* [phJ l] is free *)
    assert (H2 : phJ (expr_eval E1 s') = PHCfree). {
      red in D1. red in D1.
      specialize D1 with (expr_eval E1 s').
      apply phcDisj_entire_free in D1; vauto.
      rewrite <- SAT. desf. }

    (* [phF l] is free *)
    assert (H3 : phF (expr_eval E1 s') = PHCfree). {
      red in D2. red in D2.
      specialize D2 with (expr_eval E1 s').
      rewrite <- phUnion_cell in D2.
      rewrite H2 in D2. rewrite phcUnion_free_l in D2.
      apply phcDisj_entire_free in D2; vauto.
      rewrite <- SAT. desf. }

    pose (ph' := phUpdate ph (expr_eval E1 s') (PHCstd 1 (expr_eval E2 s'))).

    (* the new snapshot heap equals the old snapshot heap *)
    assert (H4 : phSnapshot (phUnion (phUnion ph phJ) phF) = phSnapshot (phUnion (phUnion ph' phJ) phF)). {
      extensionality l. unfold phSnapshot.
      repeat rewrite <- phUnion_cell. subst ph'.
      unfold phUpdate, update. desf. rewrite H2, H3.
      repeat rewrite phcUnion_free_l. rewrite <- SAT. vauto. }

    exists (phUpdate ph (expr_eval E1 s') (PHCstd 1 (expr_eval E2 s'))), phJ.
    repeat split.

    1:{ (* the updated permission heap is disjoint with [phJ] *)
      intro l. unfold phUpdate, update. desf. rewrite H2.
      apply phDisj_iden_l. desf. }

    1:{ (* the updated permission heap, together with [phJ], is disjoint with [phF] *)
      intro l. unfold phUpdate, update, phUnion. desf.
      - rewrite H2, H3, phcUnion_free_l.
        by apply phcDisj_free_l.
      - by apply D2. }

    1:{ (* heap concretisations match after the heap update *)
      assert (H5 : phcConcr (PHCstd 1 (expr_eval E2 s')) = Some (expr_eval E2 s')). { simpls. }
      rewrite <- H5. rewrite <- phConcr_update.
      repeat rewrite phUnion_update_free; vauto. }

    1:{ (* the updated heap is still finite *)
      by apply hFinite_update. }

    1:{ (* if [C] is basic, the snapshot heap has not changed *)
      rewrite phSnapshot_upd. extensionality l.
      unfold phSnapshot. unfold phUpdate, hUpdate, update. desf.
      rewrite <- SAT. simpls. }

    exists pm, pmJ, pmC. intuition.

    1:{ (* the map [pmC] covers the updated snapshot heap *)
      subst ph'.  by rewrite <- H4. }

    1:{ (* [pmC] is safe with respect to the updated heap *)
      subst ph'. by rewrite <- H4. }

    exists g, Cskip. intuition.

    1:{ (* the ghost semantics can make a matching step *)
      by apply gstep_write with v. }

    1:{ (* the program is safe for another [n] computation steps *)
      apply safe_done. simpls.
      unfold phUpdate, update. desf. }
Qed.

Theorem rule_write_act :
  forall basic J E1 E2 E3,
  csl basic J (Apointsto PTTact 1 E1 E3) (Cwrite E1 E2) (Apointsto PTTact 1 E1 E2).
Proof.
  intros basic J E1 E2 E3. red. split; vauto.
  intros [|n] ph pm s g V1 V2 S1 WF (V3&SAT).
  vauto. destruct SAT as (v'&SAT).
  repeat split; vauto.

	(* (2) absence of faults *)
  - red. intros phF pmF D1 D2 _ _ ABORT.
    inv ABORT. clear ABORT.
    unfold phConcr in H4.
    rewrite <- phUnion_cell in H4.
    apply phcConcr_le_none with (phc1 := PHCact 1 (expr_eval E3 s) v') in H4; vauto.
    transitivity (ph (expr_eval E1 s)); vauto.
    by apply phcLe_mono_pos.

	(* (3) all heap accesses are in the footprint *)
  - intros l H1. unfold sat in SAT.
    simpl in H1. clarify.
    apply phcLt_le_trans with (PHCact 1 (expr_eval E3 s) v'); auto.

  (* (4) all heap writes are in footprint *)
  - intros l H1. simpl in H1. clarify.
    apply phcEntire_le with (PHCact 1 (expr_eval E3 s) v'); vauto.

  (* (5) program step *)
  - simpl. intros phJ phF pmJ pmF pmC h' s' C' D1 D2 D3 D4 H1 FIN1 WS1 INV FIN2 COV1 PSAFE1 STEP.
    inv STEP. clear STEP. subst l l0 v'0 v'1.
    apply phcLe_entire_eq in SAT; vauto.

    (* [phJ l] is free *)
    assert (H2 : phJ (expr_eval E1 s') = PHCfree). {
      red in D1. red in D1.
      specialize D1 with (expr_eval E1 s').
      apply phcDisj_entire_free in D1; vauto.
      rewrite <- SAT. desf. }

    (* [phF l] is free *)
    assert (H3 : phF (expr_eval E1 s') = PHCfree). {
      red in D2. red in D2.
      specialize D2 with (expr_eval E1 s').
      rewrite <- phUnion_cell in D2.
      rewrite H2 in D2. rewrite phcUnion_free_l in D2.
      apply phcDisj_entire_free in D2; vauto.
      rewrite <- SAT. desf. }

    pose (ph' := phUpdate ph (expr_eval E1 s') (PHCact 1 (expr_eval E2 s') v')).

    (* the new snapshot heap equals the old snapshot heap *)
    assert (H4 : phSnapshot (phUnion (phUnion ph phJ) phF) = phSnapshot (phUnion (phUnion ph' phJ) phF)). {
      extensionality l. unfold phSnapshot.
      repeat rewrite <- phUnion_cell. subst ph'.
      unfold phUpdate, update. desf. rewrite H2, H3.
      repeat rewrite phcUnion_free_l. rewrite <- SAT. vauto. }

    exists (phUpdate ph (expr_eval E1 s') (PHCact 1 (expr_eval E2 s') v')), phJ.
    repeat split.

    1:{ (* the updated permission heap is disjoint with [phJ] *)
      intro l. unfold phUpdate, update. desf. rewrite H2.
      apply phDisj_iden_l. desf. }

    1:{ (* the updated permission heap, together with [phJ], is disjoint with [phF] *)
      intro l. unfold phUpdate, update, phUnion. desf.
      - rewrite H2, H3, phcUnion_free_l.
        by apply phcDisj_free_l.
      - by apply D2. }

    1:{ (* heap concretisations match after the heap update *)
      assert (H5 : phcConcr (PHCact 1 (expr_eval E2 s') v') = Some (expr_eval E2 s')) by simpls.
      rewrite <- H5. rewrite <- phConcr_update.
      repeat rewrite phUnion_update_free; vauto. }

    1:{ (* the updated heap is still finite *)
      by apply hFinite_update. }

    1:{ (* if [C] is basic, the snapshot heap has not changed *)
      rewrite phSnapshot_upd. extensionality l.
      unfold phSnapshot, phUpdate, hUpdate, update. desf.
      rewrite <- SAT. by simpls. }

    exists pm, pmJ, pmC. intuition.

    1:{ (* the map [pmC] covers the updated snapshot heap *)
      subst ph'. by rewrite <- H4. }

    1:{ (* [pmC] is safe wrt. the updated heap *)
      subst ph'. by rewrite <- H4. }

    exists g, Cskip. intuition.

    1:{ (* the ghost semantics can make a matching step *)
      by apply gstep_write with v. }

    1:{ (* the program is safe for another [n] computation steps *)
      apply safe_done. simpls.
      split; [done|]. exists v'.
      unfold phUpdate, update. desf. }
Qed.


(** *** Heap allocation *)

Theorem rule_alloc :
  forall basic x E J,
  ~ In x (expr_fv E) ->
  ~ assn_fv J x ->
  csl basic J Atrue (Calloc x E) (Apointsto PTTstd perm_full (Evar x) E).
Proof.
  intros basic x E J FV1 FV2. red. split; vauto.
  intros [|n] ph pm s g V1 V2 S1 WF SAT.
  vauto. repeat split; vauto.

  (* (2) absence of faults *)
  - red. intros phF pmF D1 D2 FIN1 FIN2 ABORT.
    inv ABORT. clear ABORT.
    apply H4. by apply hFinite_free.

  (* (5) program step *)
  - simpl. intros phJ phF pmJ pmF pmC h' s' C' D1 D2 D3 D4 H1 FIN1 WS1 INV FIN2 COV1 PSAFE1 STEP.
    inv STEP. clear STEP. unfold phConcr in H7.

    (* the heap cell at location [l] is free *)
    assert (H2 : phUnion (phUnion ph phJ) phF l = PHCfree). {
      apply phcConcr_none_free in H7; auto. by apply phcUnion_valid. }
    unfold phUnion in H2.
    apply phcUnion_free in H2. destruct H2 as (H2&H3).
    apply phcUnion_free in H2. destruct H2 as (H2&H4).
    pose (ph' := phUpdate ph l (PHCstd perm_full v)).

    (* the new snapshot heap equals the old snapshot heap *)
    assert (H5 : phSnapshot (phUnion (phUnion ph phJ) phF) = phSnapshot (phUnion (phUnion ph' phJ) phF)). {
      extensionality l'. unfold phSnapshot.
      repeat rewrite <- phUnion_cell. subst ph'.
      unfold phUpdate, update. desf. rewrite H2, H3, H4.
      repeat rewrite phcUnion_free_l. vauto. }

    exists ph', phJ. intuition subst ph'.

    1:{ (* the updated heap is disjoint with [phJ] *)
      intro l'. unfold phUpdate, update. desf.
      rewrite H4. by apply phcDisj_free_l. }

    1:{ (* the updated heap, together with [phJ], is disjoint with [phF] *)
      intro l'. unfold phUpdate, update, phUnion. desf.
      - rewrite H3, H4. rewrite phcUnion_free_l. phcsolve.
      - by apply D2. }

    1:{ (* the heap concretisations match after the heap update *)
      assert (H6 : phcConcr (PHCstd perm_full v) = Some v) by simpls.
      rewrite <- H6. rewrite <- phConcr_update.
      repeat rewrite phUnion_update_free; vauto. }

    1:{ (* the updated heap is still finite *)
      by apply hFinite_update. }

    1:{ (* if [C] is basic, the snapshot heap has not changed *)
      rewrite phSnapshot_upd. simpl.
      extensionality l'. unfold phSnapshot, phUpdate, hUpdate, update.
      desf. rewrite H2. simpls. }

    exists pm, pmJ, pmC. intuition.

    1:{ (* the map [pmC] covers the new snapshot heap *)
      by rewrite <- H5. }

    1:{ (* the map [pmC] is safe with the new snapshot heap *)
      by rewrite <- H5. }

    exists g, Cskip. repeat split; auto.

    1:{ (* the ghost semantics can make a matching step *)
      constructor. unfold phConcr, phUnion.
      rewrite H2, H3, H4. by repeat rewrite phcUnion_free_l. }

    1:{ (* the resource invariant [J] is still satisfied *)
      unfold invariant_sat in INV.
      red. simpls. intros _. intuition.
      by apply sat_update. }

    1:{ (* the program is safe for another [n] steps *)
      apply safe_done. simpl. split; [done|].
      unfold sUpdate. rewrite update_apply.
      unfold phUpdate. rewrite update_apply.
      intuition. apply Qcle_refl.
      by rewrite expr_eval_upd. }
Qed.


(** *** Heap disposal *)

Theorem rule_dispose  :
  forall basic E1 E2 J,
  csl basic J (Apointsto PTTstd perm_full E1 E2) (Cdispose E1) Atrue.
Proof.
  intros basic E1 E2 J. red. split; vauto.
  intros [|n] ph pm s g V1 V2 S1 WF (V3&SAT).
  vauto. repeat split; vauto.

	(* (2) absence of faults *)
  - red. intros phF pmF D1 D2 FIN1 FIN2 ABORT.
    inv ABORT. clear ABORT. unfold phConcr in H4.
    assert (H2 : phUnion ph phF (expr_eval E1 s) = PHCfree). {
      apply phcConcr_none_free in H4; vauto.
      by apply phUnion_valid. }
    rewrite <- phUnion_cell in H2.
    apply phcUnion_free in H2.
    destruct H2 as (H2&H3).
    rewrite H2 in SAT. simpls.

  (* (3) all heap accesses are in the footprint *)
  - intros l H1. simpl in H1. clarify.
    apply phcLt_le_trans with (PHCstd perm_full (expr_eval E2 s)); vauto.

  (* (4) all heap writes are in footprint *)
  - intros l H1. simpl in H1. clarify.
    apply phcLe_entire_eq in SAT; vauto.
    rewrite <- SAT. vauto.

  (* (5) program step *)
  - simpl. intros phJ phF pmJ pmF pmC h' s' C' D1 D2 D3 D4 H1 FIN1 WS1 INV FIN2 COV1 PSAFE1 STEP.
    inv STEP. clear STEP. subst l l0.

    (* [ph l] is full *)
    assert (H2 : ph (expr_eval E1 s') = PHCstd perm_full (expr_eval E2 s')). {
      apply phcLe_entire_eq in SAT; vauto. }

    clear SAT.

    (* [phJ l] is free *)
    assert (H3 : phJ (expr_eval E1 s') = PHCfree). {
      red in D1. red in D1.
      specialize D1 with (expr_eval E1 s').
      apply phcDisj_entire_free in D1; vauto.
      rewrite H2. desf. }

    (* [phF l] is free *)
    assert (H4 : phF (expr_eval E1 s') = PHCfree). {
      red in D2. red in D2.
      specialize D2 with (expr_eval E1 s').
      rewrite <- phUnion_cell in D2.
      rewrite H3 in D2. rewrite phcUnion_free_l in D2.
      apply phcDisj_entire_free in D2; vauto.
      rewrite H2. desf. }

    pose (ph' := phUpdate ph (expr_eval E1 s') PHCfree).

    (* the new snapshot heap equals the old snapshot heap *)
    assert (H5 : phSnapshot (phUnion (phUnion ph phJ) phF) = phSnapshot (phUnion (phUnion ph' phJ) phF)). {
      extensionality l'. unfold phSnapshot.
      repeat rewrite <- phUnion_cell. subst ph'.
      unfold phUpdate, update. desf. rewrite H2, H3, H4.
      repeat rewrite phcUnion_free_l. vauto. }

    exists ph', phJ. intuition subst ph'.

    1:{ (* the updated heap is disjoint with [phJ] *)
      intro l'. unfold phUpdate, update. desf.
      apply phcDisj_free_r. by rewrite H3. }

    1:{ (* the updated heap, together with [phJ], is disjoint with [phF] *)
      intro l'. unfold phUpdate, update, phUnion. desf.
      - rewrite H3, H4, phcUnion_free_l.
        by apply phcDisj_free_r.
      - by apply D2. }

    1:{ (* the heap concretisations should be proper also after the update *)
      assert (H6 : phcConcr PHCfree = None) by simpls.
      rewrite <- H6. rewrite <- phConcr_update.
      repeat rewrite phUnion_update_free; vauto. }

    1:{ (* the heap should be finite after the update *)
      by apply hFinite_update. }

    1:{ (* if [C] is basic, the snapshot heap has not changed *)
      rewrite phSnapshot_upd. simpl.
      extensionality l'. unfold phUpdate, hUpdate, update. desf.
      unfold phSnapshot. rewrite H2. simpls. }

    exists pm, pmJ, pmC. intuition.

    1:{ (* the map [pmC] covers the new snapshot heap *)
      by rewrite <- H5. }

    1:{ (* the map [pmC] is safe with the new snapshot heap *)
      by rewrite <- H5. }

    exists g, Cskip. intuition vauto.
    apply safe_done. simpls.
Qed.


(** *** Parallel composition *)

Lemma safe_par  :
  forall n basic C1 C2 ph1 ph2 pm1 pm2 s g J A1 A2,
  phDisj ph1 ph2 ->
  pmDisj pm1 pm2 ->
  pmSafe (phSnapshot ph1) pm1 ->
  pmSafe (phSnapshot ph2) pm2 ->
  cmd_wf (Cpar C1 C2) ->
  disjoint (cmd_fv C1) (cmd_mod C2) ->
  disjoint (assn_fv A1) (cmd_mod C2) ->
  disjoint (assn_fv J) (cmd_mod C2) ->
  disjoint (cmd_fv C2) (cmd_mod C1) ->
  disjoint (assn_fv A2) (cmd_mod C1) ->
  disjoint (assn_fv J) (cmd_mod C1) ->
  safe n basic C1 ph1 pm1 s g J A1 ->
  safe n basic C2 ph2 pm2 s g J A2 ->
  safe n basic (Cpar C1 C2) (phUnion ph1 ph2) (pmUnion pm1 pm2) s g J (Astar A1 A2).
Proof.
  induction n as [|n IH]; vauto.
  intros basic C1 C2 ph1 ph2 pm1 pm2 s g J A1 A2.
  intros D1 D2 S1 S2 WF FV1 FV2 FV3 FV4 FV5 FV6 SAFE1 SAFE2.
  repeat split; vauto.

  (* (2) absence of faults *)
  - red. intros phF pmF D3 D4 FIN1 FIN2 ABORT.
    inv ABORT; clear ABORT.

    (* case 1 : no faults in [C1] *)
    + rewrite phUnion_assoc, pmUnion_assoc in H5.
      destruct SAFE1 as (_&ABORT1&_).
      apply ABORT1 in H5; auto.
      * phsolve.
      * pmsolve.
      * by rewrite <- phUnion_assoc.
      * by rewrite <- pmUnion_assoc.

    (* case 2 : no faults in [C2] *)
    + rewrite phUnion_comm with ph1 ph2 in H5.
      rewrite pmUnion_comm with (pm1 := pm1)(pm2 := pm2) in H5.
      rewrite phUnion_assoc, pmUnion_assoc in H5.
      destruct SAFE2 as (_&ABORT2&_).
      apply ABORT2 in H5; auto.
      * apply phDisj_assoc_l; auto; [by symmetry|].
        by rewrite phUnion_comm.
      * apply pmDisj_assoc_l; auto; [by symmetry|].
        by rewrite pmUnion_comm.
      * rewrite <- phUnion_assoc.
        by rewrite phUnion_comm with ph2 ph1.
      * rewrite <- pmUnion_assoc.
        by rewrite pmUnion_comm with (pm1 := pm2)(pm2 := pm1).

    (* case 3: no deadlocks *)
    + inversion WF as (WF1&WF2&LOCKED).
      apply LOCKED. intuition.

    (* case 4: no data races - scenario 1 *)
    + apply H7. red. intros l F7 F8.
      destruct SAFE1 as (_&_&_&WR&_).
      destruct SAFE2 as (_&_&ACC&_&_).
      apply WR in F7. apply ACC in F8. clear ACC WR.
      red in D1. red in D1. specialize D1 with l.
      apply phcDisj_entire_free in D1; vauto.
      rewrite D1 in F8. by apply phcLt_irrefl in F8.

    (* case 5 : no data races - scenario 2 *)
    + apply H7. red. intros l F7 F8.
      destruct SAFE1 as (_&_&ACC&_&_).
      destruct SAFE2 as (_&_&_&WR&_).
      apply ACC in F7. apply WR in F8. clear ACC WR.
      red in D1. red in D1.
      specialize D1 with l. symmetry in D1.
      apply phcDisj_entire_free in D1; vauto.
      rewrite D1 in F7. by apply phcLt_irrefl in F7.

  (* (3) all heap accesses are in footprint *)
  - intros l F7. destruct F7 as [F7 | F7].

    (* heap accesses in [C1] are in the footprint *)
    + destruct SAFE1 as (_&_&ACC&_&_).
      apply ACC in F7. clear ACC.
      rewrite <- phUnion_cell.
      apply phcLt_le_trans with (ph1 l); vauto.
      by apply phcLe_mono_pos.

    (* heap accesses in [C2] are in the footprint *)
    + destruct SAFE2 as (_&_&ACC&_&_).
      apply ACC in F7. clear ACC.
      rewrite <- phUnion_cell.
      apply phcLt_le_trans with (ph2 l); vauto.
      rewrite phcUnion_comm. apply phcLe_mono_pos; auto.
      by symmetry.

  (* (4) all heap writes are in footprint *)
  - intros l F7. destruct F7 as [F7 | F7].

    (* heap writes in [C1] are in the footprint *)
    + destruct SAFE1 as (_&_&_&WR&_).
      apply WR in F7. clear WR.
      rewrite <- phUnion_cell.
      apply phcEntire_union; vauto.

    (* heap writes in [C2] are in the footprint *)
    + destruct SAFE2 as (_&_&_&WR&_).
      apply WR in F7. clear WR.
      rewrite <- phUnion_cell.
      rewrite phcUnion_comm. apply phcEntire_union; auto.
      by symmetry.

  (* (5) program step *)
  - simpl. intros phJ phF pmJ pmF pmC h' s' C' D3 D4 D5 D6 H1 FIN1 WS1 INV FIN2 COV1 PSAFE1 STEP.
    inv STEP; clear STEP.

    (* step in [C1] *)
    + rewrite phUnion_swap_r with (ph2 := ph2) in H4.
      rewrite phUnion_assoc in H4.
      apply SAFE1 with (pmJ := pmJ)(pmF := pmUnion pm2 pmF)(pmC := pmC) in H4; clear SAFE1; auto.
      destruct H4 as (ph'&phJ'&D7&D8&H2&FIN3&BASIC1&H4).
      destruct H4 as (pm'&pmJ'&pmC'&D9&D10&H3&FIN4&WS2&BASIC2&COV2&PSAFE2&H4).
      destruct H4 as (g'&C''&H4&GSTEP&INV1&SAFE1). clarify.
      exists (phUnion ph' ph2), phJ'. intuition.

      1:{ (* disjointness of [ph' + ph2] and [pjJ'] *)
        apply phDisj_union_r in D8; auto.
        - rewrite phUnion_comm in D8.
          apply phDisj_assoc_l in D8; auto; [phsolve|by symmetry].
        - apply phDisj_union_l with ph1; auto.
          apply phDisj_union_l with phJ; auto; [by symmetry|].
          by rewrite phUnion_comm. }

      1:{ (* disjointness of [ph' + ph2 + phJ'] and [phF] *)
        rewrite phUnion_swap_r.
        apply phDisj_assoc_r; auto.
        apply phDisj_union_l with ph1; auto.
        apply phDisj_union_l with phJ; auto; [by symmetry|].
        by rewrite phUnion_comm. }

      1:{ (* heap concretisation is proper *)
        rewrite phUnion_swap_r with (ph2 := ph2).
        by rewrite phUnion_assoc. }

      1:{ (* if [C1] is basic, the snapshot heap has not changed *)
        apply phSnapshot_disj_union_l; auto.
        apply phDisj_union_l with phJ; auto.
        - rewrite H2. by symmetry.
        - apply phDisj_union_r with phF; auto.
          + apply phDisj_union_l with ph1; auto.
            apply phDisj_union_l with phJ; auto; [by symmetry|].
            by rewrite phUnion_comm.
          + rewrite phUnion_comm with phJ ph'.
            by rewrite H2. }

      exists (pmUnion pm' pm2), pmJ', pmC'. intuition.

      1:{ (* disjointness of [pm' + pm2] and [pmJ'] *)
        apply pmDisj_union_r in D10; auto.
        - rewrite pmUnion_comm in D10.
          apply pmDisj_assoc_l in D10; auto; [by symmetry|pmsolve].
        - apply pmDisj_union_l with pm1; auto.
          apply pmDisj_union_l with pmJ; auto; [by symmetry|].
          by rewrite pmUnion_comm. }

      1:{ (* disjointness of [pm' + pm2 + pmJ'] and [pmF] *)
        rewrite pmUnion_swap_r.
        apply pmDisj_assoc_r; auto.
        apply pmDisj_union_l with pm1; auto.
        apply pmDisj_union_l with pmJ; auto; [by symmetry|].
        by rewrite pmUnion_comm. }

      1:{ (* composition of [pmC] is proper *)
        rewrite <- H3.
        rewrite pmUnion_swap_r with (pm2 := pm2).
        by rewrite pmUnion_assoc. }

      1:{ (* the process map has not changed, given that [C1] is basic *)
        by rewrite H5. }

      1:{ (* the map [pmC'] covers the new snapshot heap *)
        rewrite phUnion_swap_r with (ph2 := ph2).
        by rewrite phUnion_assoc. }

      1:{ (* the map [pmC'] is safe with the new snapshot heap *)
        rewrite phUnion_swap_r with (ph2 := ph2).
        by rewrite phUnion_assoc. }

      exists g', (Cpar C'' C2). intuition vauto.

      1:{ (* ghost semantics can make a step *)
        rewrite phUnion_swap_r with (ph2 := ph2).
        rewrite phUnion_assoc.
        apply gstep_par_l; auto.
        by rewrite <- cmd_locked_plain. }

      1:{ (* the resource invariant [J] is still satisfied *)
        unfold invariant_sat in INV1.
        red. simpl. intro H9.
        apply not_or_and in H9.
        destruct H9 as (H9&H10).
        by apply INV1. }

      apply IH; intuition vauto.

      1:{ (* disjointness of [ph'] and [ph2] *)
        apply phDisj_union_l with phJ'; auto; [by symmetry|].
        rewrite phUnion_comm.
        apply phDisj_union_r with phF; auto.
        apply phDisj_union_l with ph1; auto.
        apply phDisj_union_l with phJ; auto; [by symmetry|].
        by rewrite phUnion_comm. }

      1:{ (* disjointness of [pm'] and [pm2] *)
        apply pmDisj_union_l with pmJ'; auto; [by symmetry|].
        rewrite pmUnion_comm.
        apply pmDisj_union_r with pmF; auto.
        apply pmDisj_union_l with pm1; auto.
        apply pmDisj_union_l with pmJ; auto; [by symmetry|].
        by rewrite pmUnion_comm. }

      1:{ (* [pm'] is safe with [ph']s snapshot heap *)
        apply pmSafe_weaken_l with pmJ'.
        apply pmSafe_weaken_l with (pmUnion pm2 pmF).
        rewrite H3. clear H3.
        apply pmSafe_weaken_snapshot_l with phJ'; [done|].
        by apply pmSafe_weaken_snapshot_l with (phUnion ph2 phF). }

      1:{ (* the program [Cpar C'' C2] is well-formed *)
        destruct WF as (WF1&WF2&LOCKED).
        constructor; repeat split; auto.
        (* the program [C''] is well-formed *)
        * by apply gstep_wf_pres in GSTEP.
        (* the programs [C''] and [C2] are not both locked *)
        * intro H9. destruct H9 as (H9&H10).
          by rewrite cmd_locked_plain in H8. }

      1:{ (* free variables in [C''] are not modified in [C2] *)
        red. intros x FV7 FV8. apply gstep_fv_mod in GSTEP.
        destruct GSTEP as (FV9&FV10&FV11&FV12).
        apply FV9 in FV7. by apply FV1 with x. }

      1:{ (* free variables in [C2] are not modified in [C''] *)
        red. intros x FV7 FV8. apply gstep_fv_mod in GSTEP.
        destruct GSTEP as (FV9&FV10&FV11&FV12).
        apply FV10 in FV8. by apply FV4 with x. }

      1:{ (* free variables in [A2] are not modified in [C''] *)
        red. intros x FV7 FV8. apply gstep_fv_mod in GSTEP.
        destruct GSTEP as (FV9&FV10&FV11&FV12).
        apply FV10 in FV8. by apply FV5 with x. }

      1:{ (* free variables in [J] are not modified in [C''] *)
        red. intros x FV7 FV8. apply gstep_fv_mod in GSTEP.
        destruct GSTEP as (FV9&FV10&FV11&FV12).
        apply FV10 in FV8. by apply FV6 with x. }

      1:{ (* program is safe for [n] more steps *)
        apply gstep_fv_mod in GSTEP.
        destruct GSTEP as (_&_&FV9&FV10).
        apply safe_agree with s; auto.
        1:{ intros x FV7. apply FV9. intro FV8. by apply FV5 with x. }
        1:{ intros x FV7. apply FV9. intro FV8. by apply FV6 with x. }
        1:{ intros x FV7. apply FV9. intro FV8. by apply FV4 with x. }
        apply safe_agree_ghost with g; auto.
        1:{ intros x FV7. apply FV10. intro FV8. by apply FV5 with x. }
        1:{ intros x FV7. apply FV10. intro FV8. by apply FV6 with x. }
        1:{ intros x FV7. apply FV10. intro FV8. by apply FV4 with x. }
        apply safe_mono with (S n). apply le_n_Sn. by simpls. }

      1:{ (* disjointness of [ph1] and [phJ] *)
        apply phDisj_union_l with ph2; auto; [by symmetry|].
        by rewrite phUnion_comm. }

      1:{ (* disjointness of [ph1 + phJ] and [ph2 + phF] *)
        apply phDisj_assoc_l.
        - rewrite phUnion_comm.
          apply phDisj_assoc_r; auto. phsolve.
        - by rewrite phUnion_swap_r. }

      1:{ (* disjointness of [pm1] and [pmJ] *)
        apply pmDisj_union_l with pm2; [pmsolve|].
        by rewrite pmUnion_comm. }

      1:{ (* disjointness of [pm1 + pmJ] and [pm2 + pmF] *)
        apply pmDisj_assoc_l.
        - rewrite pmUnion_comm.
          apply pmDisj_assoc_r; auto. pmsolve.
        - by rewrite pmUnion_swap_r. }

      1:{ (* composition of [pmC] is proper *)
        rewrite <- H1.
        rewrite pmUnion_swap_r with (pm2 := pm2).
        by repeat rewrite pmUnion_assoc. }

      1:{ (* the resource invariant [J] was satisfied before the step *)
        unfold invariant_sat in INV.
        red. simpls. intro LOCKED. apply INV.
        apply and_not_or. split; auto.
        by rewrite cmd_locked_plain in H8. }

      1:{ (* the permission heap [ph1 + ph + ph2 + phF] is finite *)
        rewrite <- phUnion_assoc.
        by rewrite phUnion_swap_r with ph1 phJ ph2. }

      1:{ (* the map [pmC] covers the old snapshot heap *)
        rewrite <- phUnion_assoc.
        by rewrite phUnion_swap_r with (ph2 := phJ). }

      1:{ (* the map [pmC] is safe with the old snapshot heap *)
        rewrite <- phUnion_assoc.
        by rewrite phUnion_swap_r with (ph2 := phJ). }

    (* step in [C2] *)
    + rewrite phUnion_comm with ph1 ph2 in H4.
      rewrite phUnion_swap_r with (ph2 := ph1) in H4.
      rewrite phUnion_assoc in H4.
      apply SAFE2 with (pmJ := pmJ)(pmF := pmUnion pm1 pmF)(pmC := pmC) in H4; clear SAFE2; auto.
      destruct H4 as (ph'&phJ'&D7&D8&H2&FIN3&BASIC1&H4).
      destruct H4 as (pm'&pmJ'&pmC'&D9&D10&H3&FIN4&WS2&BASIC2&COV2&PSAFE2&H4).
      destruct H4 as (g'&C''&H4&GSTEP&INV1&SAFE2). clarify.
      exists (phUnion ph1 ph'), phJ'. intuition.

      1:{ (* disjointness of [ph1 + ph'] and [phF] *)
        apply phDisj_assoc_r; auto.
        apply phDisj_union_l with phF; auto.
        - symmetry. apply phDisj_union_l with ph2; [by symmetry|].
          rewrite phUnion_comm.
          apply phDisj_union_l with phJ; auto; [by symmetry|].
          by rewrite phUnion_comm.
        - symmetry. by rewrite phUnion_comm with phF ph1. }

      1:{ (* disjointness of [ph1 + ph' + phJ'] and [phF] *)
        rewrite phUnion_comm with ph1 ph'.
        rewrite phUnion_swap_r with (ph2 := ph1).
        apply phDisj_assoc_r; auto.
        apply phDisj_union_l with ph2; auto; [by symmetry|].
        apply phDisj_union_l with phJ; auto.
        symmetry. by rewrite phUnion_comm.
        rewrite phUnion_comm.
        by rewrite phUnion_comm with ph2 ph1. }

      1:{ (* heap concretisation is proper *)
        rewrite phUnion_comm with ph1 ph'.
        rewrite phUnion_swap_r with (ph2 := ph1).
        by rewrite phUnion_assoc. }

      1:{ (* if [C1] is basic, the snapshot heap has not changed *)
        apply phSnapshot_disj_union_r; auto; [phsolve|].
        apply phDisj_union_l with phJ; auto.
        - rewrite H2. by symmetry.
        - apply phDisj_union_r with phF; auto.
          + apply phDisj_union_l with ph2; [phsolve|].
            apply phDisj_union_l with phJ.
            * symmetry. by rewrite phUnion_comm.
            * rewrite phUnion_comm.
              by rewrite phUnion_comm with ph2 ph1.
          + rewrite phUnion_comm with phJ ph'. by rewrite H2. }

      exists (pmUnion pm1 pm'), pmJ', pmC'. intuition.

      1:{ (* disjointness of [pm1 + pm'] and [pmF] *)
        apply pmDisj_assoc_r; auto.
        apply pmDisj_union_l with pmF.
        - symmetry. apply pmDisj_union_l with pm2; [pmsolve|].
          rewrite pmUnion_comm.
          apply pmDisj_union_l with pmJ; [pmsolve|].
          by rewrite pmUnion_comm.
        - symmetry.
          by rewrite pmUnion_comm with (pm1:=pmF)(pm2:=pm1). }

      1:{ (* disjointness of [pm1 + pm' + pmJ'] and [pmF] *)
        rewrite pmUnion_comm with (pm1:=pm1)(pm2:=pm').
        rewrite pmUnion_swap_r with (pm2 := pm1).
        apply pmDisj_assoc_r; auto.
        apply pmDisj_union_l with pm2; [pmsolve|].
        apply pmDisj_union_l with pmJ.
        - symmetry. by rewrite pmUnion_comm.
        - rewrite pmUnion_comm.
          by rewrite pmUnion_comm with (pm1:=pm2)(pm2:=pm1). }

      1:{ (* composition of [pmC] is proper *)
        rewrite pmUnion_comm with (pm1:=pm1)(pm2:=pm').
        rewrite <- H3.
        rewrite pmUnion_swap_r with (pm2:=pm1).
        by rewrite pmUnion_assoc. }

      1:{ (* the process map has not changed, given that [C1] is basic *)
        by rewrite H5. }

      1:{ (* the map [pmC'] covers the new snapshot heap *)
        rewrite phUnion_comm with ph1 ph'.
        rewrite phUnion_swap_r with (ph2 := ph1).
        by rewrite phUnion_assoc. }

      1:{ (* the map [pmC'] is safe with the new snapshot heap *)
        rewrite phUnion_comm with ph1 ph'.
        rewrite phUnion_swap_r with (ph2 := ph1).
        by rewrite phUnion_assoc. }

      exists g', (Cpar C1 C''). intuition vauto.

      1:{ (* ghost semantics can make a step *)
        rewrite phUnion_comm with ph1 ph2.
        rewrite phUnion_swap_r with (ph2 := ph1).
        rewrite phUnion_assoc.
        apply gstep_par_r; auto.
        by rewrite <- cmd_locked_plain. }

      1:{ (* the resource invariant [J] is still satisfied *)
        unfold invariant_sat in INV.
        red. simpls. intro H.
        apply not_or_and in H.
        destruct H as (H'&H). clear H'.
        by apply INV1. }

      apply IH; intuition vauto.

      1:{ (* disjointness of [ph1] and [ph'] *)
        symmetry.
        apply phDisj_union_l with phJ'; [phsolve|].
        rewrite phUnion_comm.
        apply phDisj_union_r with phF; auto.
        apply phDisj_union_l with ph2; [phsolve|].
        rewrite phUnion_comm.
        apply phDisj_union_l with phJ; [phsolve|].
        by rewrite phUnion_comm. }

      1:{ (* disjointness of [pm1] and [pm'] *)
        symmetry.
        apply pmDisj_union_l with pmJ'; [pmsolve|].
        rewrite pmUnion_comm.
        apply pmDisj_union_r with pmF; auto.
        apply pmDisj_union_l with pm2; [pmsolve|].
        rewrite pmUnion_comm.
        apply pmDisj_union_l with pmJ; [pmsolve|].
        by rewrite pmUnion_comm. }

      1:{ (* [pm'] is safe with [ph']s snapshot heap *)
        apply pmSafe_weaken_l with pmJ'.
        apply pmSafe_weaken_l with (pmUnion pm1 pmF).
        rewrite H3. clear H3.
        apply pmSafe_weaken_snapshot_l with phJ'; [done|].
        by apply pmSafe_weaken_snapshot_l with (phUnion ph1 phF). }

      1:{ (* the program [Cpar C1 C''] is well-formed *)
        destruct WF as (WF1&WF2&LOCKED).
        constructor; repeat split; auto.
        (* the program [C''] is well-formed *)
        * by apply gstep_wf_pres in GSTEP.
        (* the programs [C1] and [C''] are not both locked *)
        * intro H9. destruct H9 as (H9&H10).
          by rewrite cmd_locked_plain in H8. }

      1:{ (* free variables in [C1] are not modified in [C''] *)
        red. intros x FV7 FV8. apply gstep_fv_mod in GSTEP.
        destruct GSTEP as (FV9&FV10&FV11&FV12).
        apply FV10 in FV8. by apply FV1 with x. }

      1:{ (* free variables in [A1] are not modified in [C''] *)
        red. intros x FV7 FV8. apply gstep_fv_mod in GSTEP.
        destruct GSTEP as (FV9&FV10&FV11&FV12).
        apply FV10 in FV8. by apply FV2 with x. }

      1:{ (* free variables in [J] are not modified in [C''] *)
        red. intros x FV7 FV8. apply gstep_fv_mod in GSTEP.
        destruct GSTEP as (FV9&FV10&FV11&FV12).
        apply FV10 in FV8. by apply FV3 with x. }

      1:{ (* free variables in [J] are not modified in [C''] *)
        red. intros x FV7 FV8. apply gstep_fv_mod in GSTEP.
        destruct GSTEP as (FV9&FV10&FV11&FV12).
        apply FV9 in FV7. by apply FV4 with x. }

      1:{ (* program is safe for [n] more steps *)
        apply gstep_fv_mod in GSTEP.
        destruct GSTEP as (_&_&FV9&FV10).
        apply safe_agree with s; auto.
        1:{ intros x FV7. apply FV9. intro FV8. by apply FV2 with x. }
        1:{ intros x FV7. apply FV9. intro FV8. by apply FV3 with x. }
        1:{ intros x FV7. apply FV9. intro FV8. by apply FV1 with x. }
        apply safe_agree_ghost with g; auto.
        1:{ intros x FV7. apply FV10. intro FV8. by apply FV2 with x. }
        1:{ intros x FV7. apply FV10. intro FV8. by apply FV3 with x. }
        1:{ intros x FV7. apply FV10. intro FV8. by apply FV1 with x. }
        apply safe_mono with (S n). apply le_n_Sn. by simpls. }

      1:{ (* disjointness of [ph2] and [phJ] *)
        apply phDisj_union_l with ph1; auto. }

      1:{ (* disjointness of [ph2 + phJ] and [ph1 + phF] *)
        apply phDisj_assoc_l. rewrite phUnion_comm.
        - apply phDisj_assoc_r; [phsolve|].
          symmetry. by rewrite phUnion_comm.
        - rewrite phUnion_swap_r.
          by rewrite phUnion_comm with ph2 ph1. }

      1:{ (* disjointness of [pm2] and [pmJ] *)
        apply pmDisj_union_l with pm1; auto. }

      1:{ (* disjointness of [pm2 + pmJ] and [pm1 + pmF] *)
        apply pmDisj_assoc_l.
        rewrite pmUnion_comm.
        - apply pmDisj_assoc_r; [pmsolve|].
          symmetry. by rewrite pmUnion_comm.
        - rewrite pmUnion_swap_r.
          by rewrite pmUnion_comm with (pm1:=pm2)(pm2:=pm1). }

      1:{ (* composition of [pmC] is proper *)
        rewrite <- H1.
        rewrite pmUnion_comm with (pm1 := pm1)(pm2 := pm2).
        rewrite pmUnion_swap_r with (pm2 := pm1).
        by repeat rewrite pmUnion_assoc. }

      1:{ (* the resource invariant [J] was satisfied before the step *)
        unfold invariant_sat in INV.
        red. simpls. intro H9. apply INV.
        apply and_not_or. split; vauto.
        by rewrite cmd_locked_plain in H8. }

      1:{ (* the heap [ph2 + phJ + ph1 + phF] is finite *)
        rewrite <- phUnion_assoc.
        rewrite phUnion_swap_r with ph2 phJ ph1.
        by rewrite phUnion_comm with ph2 ph1. }

      1:{ (* the map [pmC] covers the old snapshot heap *)
        rewrite <- phUnion_assoc.
        rewrite phUnion_swap_r with (ph2 := phJ).
        by rewrite phUnion_comm with ph2 ph1. }

      1:{ (* the map [pmC] is safe with the old snapshot heap *)
        rewrite <- phUnion_assoc.
        rewrite phUnion_swap_r with (ph2 := phJ).
        by rewrite phUnion_comm with ph2 ph1. }

    (* [C1] and [C2] are both empty *)
    + symmetry in H3, H4.
      apply plain_skip in H3.
      apply plain_skip in H4. clarify.
      exists (phUnion ph1 ph2), phJ. intuition.
      exists (pmUnion pm1 pm2), pmJ, pmC. intuition.
      exists g, Cskip. intuition.

      1:{ (* the ghost semantics can make a matching step *)
        by constructor. }

      1:{ (* the resource invariant [J] is satisfied *)
        unfold invariant_sat in INV.
        red. simpls. intuition. }

      1:{ (* the program is safe for [n] more steps *)
        apply safe_done. simpls.
        exists ph1, ph2. intuition.
        exists pm1, pm2. intuition. }
Qed.

Theorem rule_par :
  forall basic C1 C2 J A1 A2 A1' A2',
  disjoint (cmd_fv C1) (cmd_mod C2) ->
  disjoint (assn_fv A1') (cmd_mod C2) ->
  disjoint (assn_fv J) (cmd_mod C2) ->
  disjoint (cmd_fv C2) (cmd_mod C1) ->
  disjoint (assn_fv A2') (cmd_mod C1) ->
  disjoint (assn_fv J) (cmd_mod C1) ->
  csl basic J A1 C1 A1' ->
  csl basic J A2 C2 A2' ->
  csl basic J (Astar A1 A2) (Cpar C1 C2) (Astar A1' A2').
Proof.
  intros basic C1 C2 J A1 A2 A1' A2' FV1 FV2 FV3 FV4 FV5 FV6 CSL1 CSL2.
  red. split; vauto.

  (* the program [Cpar C1 C2] is a user program *)
  - constructor.
    + by destruct CSL1 as (?&_).
    + by destruct CSL2 as (?&_).

  (* the program [Cpar C1 C2] is safe for [n] computation steps *)
  - intros n ph pm s g V1 V2 S1 WF SAT.
    destruct SAT as (ph1&ph2&D1&H1&pm1&pm2&D2&H2&SAT1&SAT2).

    (* [pm1] is safe with [ph1]'s snapshot heap *)
    assert (S3 : pmSafe (phSnapshot ph1) pm1). {
      apply pmSafe_weaken_l with pm2.
      rewrite H2. clear H2. clarify.
      by apply pmSafe_weaken_snapshot_l with ph2. }

    (* [pm2] is safe with [ph2]'s snapshot heap *)
    assert (S4 : pmSafe (phSnapshot ph2) pm2). {
      apply pmSafe_weaken_r with pm1.
      rewrite H2. clear H2. clarify.
      by apply pmSafe_weaken_snapshot_r with ph1. }

    rewrite <- H1, <- H2.
    apply safe_par; auto.

    (* the program [C1] is safe for [n] computation steps *)
    + destruct CSL1 as (_&SAFE).
      apply SAFE; auto.
      * by apply phDisj_valid_l in D1.
      * by apply pmDisj_valid_l in D2.
      * by destruct WF as (WF1&WF2&LOCKED).

    (* the program [C2] is safe for [n] computation steps *)
    + destruct CSL2 as (_&SAFE).
      apply SAFE; auto.
      * by apply phDisj_valid_r in D1.
      * by apply pmDisj_valid_r in D2.
      * by destruct WF as (WF1&WF2&LOCKED).
Qed.


(** *** Existential quantification *)

Theorem rule_ex :
  forall basic C J (A1 A2 : Val -> Assn),
    (forall x, csl basic J (A1 x) C (A2 x)) ->
  csl basic J (Aex A1) C (Aex A2).
Proof.
  intros basic C J A1 A2 CSL.
  red. split; auto.

  (* the program [C] is a user program *)
  - specialize CSL with val_unit.
    by destruct CSL as (USER&_).

  (* the program [C] is safe for any number of steps *)
  - intros n ph pm s g V1 V2 S1 WF SAT.
    destruct SAT as (v&SAT).
    apply safe_conseq with (A2 v); vauto.
    by apply CSL.
Qed.


(** *** Share rule *)

Lemma safe_share :
  forall n C ph1 ph2 pm1 pm2 s g J A1 A2,
  phDisj ph1 ph2 ->
  pmDisj pm1 pm2 ->
  pmSafe (phSnapshot ph1) pm1 ->
  pmSafe (phSnapshot ph2) pm2 ->
  invariant_sat ph2 pm2 s g C A2 ->
  safe n False C ph1 pm1 s g (Astar J A2) A1 ->
  safe n False C (phUnion ph1 ph2) (pmUnion pm1 pm2) s g J (Astar A1 A2).
Proof.
  induction n as [|n IH]; vauto.
  intros C ph1 ph2 pm1 pm2 s g J A1 A2 D1 D2 S1 S2 SAT SAFE.
  repeat split; vauto.

  (* (1) terminating programs *)
  - intro H1. clarify.
    exists ph1, ph2. intuition.
    exists pm1, pm2. intuition.
    destruct SAFE as (TERM&_).
    by apply TERM.

  (* (2) absence of faults *)
  - red. intros phF pmF D3 D4 FIN1 FIN2 ABORT.
    rewrite phUnion_assoc in ABORT.
    rewrite pmUnion_assoc in ABORT.
    destruct SAFE as (_&ABORT1&_).
    apply ABORT1 in ABORT; auto.
    (* [ph1] is disjoint with [ph2 + phF] *)
    + by apply phDisj_assoc_l.
    (* [pm1] is disjoint with [pm2 + pmF] *)
    + by apply pmDisj_assoc_l.
    (* [ph1 + ph2 + phF] is finite *)
    + by rewrite <- phUnion_assoc.
    (* [pm1 + pm2 + pmF] is finite *)
    + by rewrite <- pmUnion_assoc.

  (* (3) all shared-memory reads of [C] are in the footprint *)
  - intros l H1.
    destruct SAFE as (_&_&ACC&_).
    apply ACC in H1. clear ACC.
    rewrite <- phUnion_cell.
    apply phcLt_le_trans with (ph1 l); vauto.
    by apply phcLe_mono_pos.

  (* (4) all shared-memory writes of [C] are in the footprint *)
  - intros l H1. destruct SAFE as (_&_&_&WRITES&_).
    apply WRITES in H1. clear WRITES.
    rewrite <- phUnion_cell.
    apply phcEntire_union; vauto.

  (* (5) program step *)
  - simpl. intros phJ phF pmJ pmF pmC h' s' C' D3 D4 D5 D6 H1 FIN1 WS1 INV FIN2 COV1 PSAFE1 STEP.
    rewrite phUnion_assoc with ph1 ph2 phJ in STEP.
    cut (cmd_locked C' \/ ~ cmd_locked C'); [|apply classic].
    intro H. destruct H as [LOCKED | LOCKED].

    (* the program [C'] is locked *)
    + destruct SAFE as (_&_&_&_&SAFE).
      apply SAFE with (pmJ := pmUnion pm2 pmJ)(pmF := pmF)(pmC := pmC) in STEP; clear SAFE; auto.
      destruct STEP as (ph'&phJ'&D7&D8&H2&FIN3&BASIC1&STEP).
      destruct STEP as (pm'&pmJ'&pmC'&D9&D10&H3&FIN4&WS2&BASIC2&COV2&PSAFE2&STEP).
      destruct STEP as (g'&C''&H4&GSTEP&INV1&SAFE). clarify.

      (* [pm'] is safe with [ph']'s snapshot heap *)
      assert (S3 : pmSafe (phSnapshot ph') pm'). {
        apply pmSafe_weaken_l with pmJ'.
        apply pmSafe_weaken_l with pmF.
        rewrite H3. clear H3.
        apply pmSafe_weaken_snapshot_l with phJ'; [done|].
        by apply pmSafe_weaken_snapshot_l with phF. }

      exists ph', phJ'. intuition.
      exists pm', pmJ', pmC'. intuition.
      exists g', C''. intuition.

      1:{ (* the ghost semantics can make a matching step *)
        by repeat rewrite phUnion_assoc in *. }

      1:{ (* the resource invariant [J] is still satisfied *)
        unfold invariant_sat in INV1.
        red. intro H2. apply INV1 in H2.
        clear INV1. simpl in H2.
        destruct H2 as (ph1'&ph2'&D11&H4&pm1'&pm2'&D12&H5&SAT1&SAT2).
        rewrite <- H4, <- H5. by apply sat_weaken. }

      1:{ (* the program is safe for [n] more steps *)
        rewrite <- phUnion_iden_l with ph'.
        rewrite <- pmUnion_iden_l with pm'.
        apply IH; auto.
        (* [ph'] is disjoint with the identity heap *)
        - apply phDisj_iden_r.
          by apply phDisj_valid_l in D7.
        (* [pm'] is disjoint with the identity process map *)
        - apply pmDisj_iden_r.
          by apply pmDisj_valid_l in D9.
        (* the identity process map is safe *)
        - by apply pmSafe_iden.
        (* [A2] is satisfied as a resource invariant *)
        - red. clarify. intro H2.
          by rewrite cmd_locked_plain in LOCKED. }

      1:{ (* [ph1] is disjoint with [ph2 + phJ] *)
        by apply phDisj_assoc_l. }

      1:{ (* [ph1 + ph2 + phJ] is disjoint with [phF] *)
        by rewrite <- phUnion_assoc. }

      1:{ (* [pm1] is disjoint with [pm2 + pmJ] *)
        by apply pmDisj_assoc_l. }

      1:{ (* [pm1 + pm2 + pmJ] is disjoint with [pmF] *)
        by rewrite <- pmUnion_assoc. }

      1:{ (* [pm1 + pm2 + pmJ + pmJ] is indeed bisimilar to [pmC] *)
        by rewrite <- pmUnion_assoc. }

      1:{ (* the resource invariant was satisfied before the step *)
        red. intro H2. clarify.
        unfold invariant_sat in SAT, INV.
        assert (H3 : sat ph2 pm2 s g A2) by by apply SAT in H2.
        assert (H4 : sat phJ pmJ s g J) by by apply INV in H2.
        exists phJ, ph2. intuition.
        - symmetry. by apply phDisj_union_l with ph1.
        - by rewrite phUnion_comm.
        - exists pmJ, pm2. intuition.
          + symmetry. by apply pmDisj_union_l with pm1.
          + by rewrite pmUnion_comm. }

      1:{ (* the heap [ph1 + ph2 + phJ + phF] is finite *)
        by rewrite <- phUnion_assoc. }

      1:{ (* the map [pmC] covers the old snapshot heap *)
        by rewrite <- phUnion_assoc. }

      1:{ (* the map [pmC] is safe with the old snapshot heap *)
        by rewrite <- phUnion_assoc. }

    (* the program [C'] is not locked *)
    + destruct SAFE as (_&_&_&_&SAFE).
      apply SAFE with (pmJ := pmUnion pm2 pmJ)(pmF := pmF)(pmC := pmC) in STEP; clear SAFE; auto.
      destruct STEP as (ph'&phJ'&D7&D8&H2&FIN3&BASIC1&STEP).
      destruct STEP as (pm'&pmJ'&pmC'&D9&D10&H3&FIN4&WS2&BASIC2&COV2&PSAFE2&STEP).
      destruct STEP as (g'&C''&H4&GSTEP&INV1&SAFE). clarify.
      rewrite cmd_locked_plain in LOCKED.
      unfold invariant_sat in INV1.
      apply INV1 in LOCKED. clear INV1.
      simpl in LOCKED.
      destruct LOCKED as (phJ''&ph2'&D11&H2&pmJ''&pm2'&D12&H4&SAT1&SAT2).
      clarify. exists (phUnion ph' ph2'), phJ''. intuition.

      1:{ (* disjointness of [ph' + ph2'] and [phJ''] *)
        apply phDisj_assoc_r; [phsolve|].
        by rewrite phUnion_comm. }

      1:{ (* disjointness of [ph' + ph2' + phJ''] and [phF] *)
        rewrite phUnion_swap_r.
        by rewrite phUnion_assoc. }

      1:{ (* heap concretisation is proper *)
        rewrite phUnion_swap_r with (ph2 := ph2').
        by repeat rewrite phUnion_assoc. }

      exists (pmUnion pm' pm2'), pmJ'', pmC'. intuition.

      1:{ (* disjointness of [pm' + pm2'] and [pmJ''] *)
        apply pmDisj_assoc_r; [pmsolve|].
        rewrite pmUnion_comm. by rewrite H4. }

      1:{ (* disjointness of [pm' + pm2' + pmJ''] and [pmF] *)
        rewrite pmUnion_swap_r, pmUnion_assoc.
        by rewrite H4. }

      1:{ (* structure of [pmC] is proper *)
        rewrite <- H3, <- H4.
        rewrite pmUnion_swap_r with (pm2 := pm2').
        by repeat rewrite pmUnion_assoc. }

      1:{ (* the map [pmC'] covers the new snapshot heap *)
        rewrite phUnion_swap_r with (ph2 := ph2').
        repeat rewrite phUnion_assoc.
        by repeat rewrite phUnion_assoc in COV2. }

      1:{ (* the map [pmC'] is safe with the new snapshot heap *)
        rewrite phUnion_swap_r with (ph2 := ph2').
        repeat rewrite phUnion_assoc.
        by repeat rewrite phUnion_assoc in PSAFE2. }

      exists g', C''. intuition.

      1:{ (* the ghost semantics can make a matching step *)
        by rewrite phUnion_assoc with ph1 ph2 phJ. }

      1:{ (* the resource invariant [J] is still maintained *)
        red. intuition. }

      apply IH; vauto.

      1: { (* disjointness of [ph'] and [ph2'] *)
        apply phDisj_union_r with phJ''; [phsolve|].
        by rewrite phUnion_comm. }

      1:{ (* disjointness of [pm'] and [pm2'] *)
        apply pmDisj_union_r with pmJ''; [pmsolve|].
        by rewrite pmUnion_comm, H4. }

      1:{ (* [pm'] is safe with [ph']'s snapshot heap *)
        apply pmSafe_weaken_l with pmJ'.
        apply pmSafe_weaken_l with pmF.
        rewrite H3. clear H3.
        apply pmSafe_weaken_snapshot_l with (phUnion phJ'' ph2'); [done|].
        by apply pmSafe_weaken_snapshot_l with phF. }

      1:{ (* [pm2'] is safe with [ph2']'s snapshot heap *)
        apply pmSafe_weaken_r with pmJ''.
        apply pmSafe_weaken_l with pmF.
        rewrite H4. clear H4.
        apply pmSafe_weaken_r with pm'.
        rewrite <- pmUnion_assoc.
        rewrite H3. clear H3.
        apply pmSafe_weaken_snapshot_r with phJ''; [done|].
        apply pmSafe_weaken_snapshot_r with ph'; [done|].
        by apply pmSafe_weaken_snapshot_l with phF. }

      1:{ (* disjointness of [ph1] and [ph2 + phJ] *)
        apply phDisj_union_l with phF; auto.
        - symmetry. apply phDisj_union_l with ph2; [phsolve|].
          rewrite phUnion_comm.
          apply phDisj_union_l with phJ; [phsolve|].
          rewrite phUnion_comm; auto.
        - apply phDisj_assoc_r; auto.
          apply phDisj_assoc_l; auto.
          symmetry. by rewrite <- phUnion_assoc. }

      1:{ (* [ph1 + ph2 + phJ] is disjoint with [phF] *)
        by rewrite <- phUnion_assoc. }

      1:{ (* disjointness of [pm1] and [pm2 + pmJ] *)
        apply pmDisj_union_l with pmF; auto.
        - symmetry. apply pmDisj_union_l with pm2; [pmsolve|].
          rewrite pmUnion_comm.
          apply pmDisj_union_l with pmJ; [pmsolve|].
          by rewrite pmUnion_comm; auto.
        - rewrite pmUnion_comm with (pm1:=pmF)(pm2:=pm1).
          apply pmDisj_compat; [pmsolve|pmsolve|].
          rewrite pmUnion_comm with (pm1:=pmF)(pm2:=pmJ).
          apply pmDisj_assoc_l; pmsolve. }

      1:{ (* [pm1 + pm2 + pmJ] is disjoint with [pmF] *)
        by rewrite <- pmUnion_assoc. }

      1:{ (* [pm1 + pm2 + pmJ + pmF] is disjoint with [pmC] *)
        by rewrite <- pmUnion_assoc. }

      1:{ (* satisfiability of the postcondition *)
        exists phJ, ph2. intuition; [phsolve|phsolve|].
        exists pmJ, pm2. intuition; [pmsolve|pmsolve]. }

      1:{ (* the heap [ph1 + ph2 + phJ + phF] is finite *)
        by rewrite <- phUnion_assoc. }

      1:{ (* the map [pmC] covers the old snapshot heap *)
        by rewrite <- phUnion_assoc. }

      1:{ (* the map [pmC] is safe with the old snapshot heap *)
        by rewrite <- phUnion_assoc. }
Qed.

Theorem rule_share :
  forall C J A1 A2 A3,
  csl False (Astar J A3) A1 C A2 ->
  csl False J (Astar A1 A3) C (Astar A2 A3).
Proof.
  intros C J A1 A2 A3 CSL.
  red. split; vauto.

  (* the program [C] is a user program *)
  - by destruct CSL as (USER&_).

  (* the program [C] is safe for any number of steps *)
  - intros n ph pm s g V1 V2 S1 WF SAT.
    simpl in SAT.
    destruct SAT as (ph1&ph2&D1&H1&pm1&pm2&D2&H2&SAT1&SAT2).

    (* [pm1] is safe with [ph1]'s snapshot heap *)
    assert (S2 : pmSafe (phSnapshot ph1) pm1). {
      apply pmSafe_weaken_l with pm2.
      rewrite H2. clear H2. clarify.
      by apply pmSafe_weaken_snapshot_l with ph2. }

    (* [pm2] is safe with [ph2]'s snapshot heap *)
    assert (S3 : pmSafe (phSnapshot ph2) pm2). {
      apply pmSafe_weaken_r with pm1.
      rewrite H2. clear H2. clarify.
      by apply pmSafe_weaken_snapshot_r with ph1. }

    rewrite <- H1, <- H2.
    apply safe_share; auto.

    (* the resource invariant [A3] is satisfied *)
    + red. intro H. exact SAT2.

    (* the program is safe with [Astar J A3] the resource invariant *)
    + destruct CSL as (_&SAFE).
      apply SAFE; auto; [phsolve|pmsolve].
Qed.


(** *** Atomic rule *)

Lemma safe_atom :
  forall n C ph pm s g J A,
  safe n False C ph pm s g Atrue (Astar A J) ->
  safe n False (Cinatom C) ph pm s g J A.
Proof.
  induction n as [|n IH]; vauto.
  intros C ph pm s g J A SAFE.
  repeat split; vauto.

  (* (2) absence of faults *)
  - red. intros phF pmF D1 D2 FIN1 FIN2 ABORT.
    inv ABORT. clear ABORT.
    destruct SAFE as (_&AB&_).
    by apply AB in H4.

  (* (3) all shared-memory accesses are in the footprint *)
  - intros l H1. destruct SAFE as (_&_&ACC&_).
    apply ACC. simpls.

  (* (4) all shared-memory writes are in the footprint *)
  - intros l H1. destruct SAFE as (_&_&_&WRITES&_).
    apply WRITES. simpls.

  (* (5) program step *)
  - simpl. intros phJ phF pmJ pmF pmC h' s' C' D3 D4 D5 D6 H1 FIN1 WS1 INV FIN2 COV1 PSAFE1 STEP.
    inv STEP; clear STEP.

    (* the program [C] is not empty *)
    + destruct SAFE as (_&_&_&_&SAFE).
      apply SAFE with (pmJ := pmJ)(pmF := pmF)(pmC := pmC) in H3; vauto.
      clear SAFE.
      destruct H3 as (ph'&phJ'&D7&D8&H2&FIN3&BASIC1&H3).
      destruct H3 as (pm'&pmJ'&pmC'&D9&D10&H3&FIN4&WS2&BASIC2&COV2&PSAFE2&H4).
      destruct H4 as (g'&C''&H4&GSTEP&INV1&SAFE). clarify.
      exists ph', phJ'. intuition.
      exists pm', pmJ', pmC'. intuition.
      exists g', (Cinatom C''). intuition.

      1:{ (* the ghost semantics can make a matching step *)
        by constructor. }

      1:{ (* the resource invariant [J] is still maintained *)
        red. by simpls. }

    (* the program [C] is empty *)
    + symmetry in H3. apply plain_skip in H3.
      clarify. destruct SAFE as (TERM&_).
      assert (H3 : sat ph pm s' g (Astar A J)) by by apply TERM.
      clear TERM. simpl in H3.
      destruct H3 as (ph1&ph2&D7&H2&pm1&pm2&D8&H3&SAT1&SAT2).
      clarify.
      exists ph1, (phUnion ph2 phJ). intuition.

      1:{ (* disjointness of [ph1] and [ph2 + phJ] *)
        apply phDisj_union_r with phF.
        - apply phDisj_union_l with ph1; [phsolve|].
          by rewrite <- phUnion_assoc.
        - apply phDisj_assoc_l; [phsolve|].
          by rewrite <- phUnion_assoc. }

      1:{ (* [ph1 + ph2 + phJ] is disjoint with [phF] *)
        by rewrite <- phUnion_assoc. }

      1:{ (* the concretisation of [ph1 + ph2 + phJ + phF] is as expected *)
        by rewrite <- phUnion_assoc. }

      exists pm1, (pmUnion pm2 pmJ), pmC. intuition.

      1:{ (* disjointness of [pm1] and [pm2 + pmJ] *)
        pmclarify. apply pmDisj_union_r with pmF; auto.
        - apply pmDisj_union_l with pm1; [pmsolve|].
          by rewrite <- pmUnion_assoc.
        - apply pmDisj_assoc_l; [pmsolve|].
          by rewrite <- pmUnion_assoc. }

      1:{ (* [pm1 + pm2 + pmJ] is disjoint with [pmF] *)
        rewrite <- pmUnion_assoc. by rewrite H3. }

      1:{ (* the composition [pm1 + pm2 + pmJ + pmF] describes [pmC] *)
        rewrite <- pmUnion_assoc. by rewrite H3. }

      1:{ (* the map [pmC] covers the old snapshot heap *)
        by rewrite <- phUnion_assoc. }

      1:{ (* the map [pmC] is safe with the old snapshot heap *)
        by rewrite <- phUnion_assoc. }

      exists g, Cskip. intuition vauto.

      1:{ (* the resource invariant is still satisfied *)
        red. intros H'. clear H'.
        apply sat_weaken; auto.
        by apply phDisj_union_l with ph1.
        apply pmDisj_union_l with pm1; auto.
        by rewrite H3. }

      by apply safe_done.
Qed.

Theorem rule_atom :
  forall C J A1 A2,
  csl False Atrue (Astar A1 J) C (Astar A2 J) ->
  csl False J A1 (Catomic C) A2.
Proof.
  intros C J A1 A2 CSL. red. split.

  (* the program [Catomic C] is a _user program_ *)
  - destruct CSL as (WF&_). vauto.

  (* the program [Catomic C] is _safe_ for any number of steps *)
  - intros [|n] ph pm s g V1 V2 WF SAT. vauto.
    repeat split; vauto.

    (* absence of faults *)
    + red. intros phF pmF D1 D2 FIN1 FIN2 ABORT.
      inv ABORT.

    (* program step *)
    + simpl. intros phJ phF pmJ pmF pmC h' s' C' D1 D2 D3 D4 H1 FIN1 WS1 INV FIN2 COV1 PSAFE STEP.
      inv STEP. unfold invariant_sat in INV.
      assert (H2 : sat phJ pmJ s' g J). { apply INV. intuition. }
      clear INV.
      exists (phUnion ph phJ), phIden. intuition.

      1:{ (* [ph + phJ + phIden] is disjoint with [phF] *)
        by rewrite phUnion_iden_l. }

      1:{ (* the concretisations are proper *)
        by rewrite phUnion_iden_l. }

      exists (pmUnion pm pmJ), pmIden, pmC. intuition.

      1:{ (* [pm + pmJ + pmIden] is disjoint with [pmF] *)
        by rewrite pmUnion_iden_l. }

      1:{ (* [pm + pmJ + pmIden + pmF] is bisimilar to [pmC] *)
        by rewrite pmUnion_iden_l. }

      1:{ (* the map [pmC] covers the old snapshot heap *)
        by rewrite phUnion_iden_l. }

      1:{ (* the map [pmC] is safe with the old snapshot heap *)
        by rewrite phUnion_iden_l. }

      exists g, (Cinatom C). intuition vauto.

      1:{ (* the resource invariant [J] is still maintained *)
        red. ins. }

      apply safe_atom.
      destruct CSL as ( _&SAFE).
      apply SAFE; vauto; [phsolve|pmsolve| |].

      1:{ (* [pm + pmJ] is safe with [ph + phJ]'s snapshot heap *)
        apply pmSafe_weaken_l with pmF.
        rewrite H1. clear H1. clarify.
        by apply pmSafe_weaken_snapshot_l with phF. }

      exists ph, phJ. intuition vauto.
      exists pm, pmJ. intuition vauto.
Qed.


(** *** Process init rule *)

Theorem rule_proc_init :
  forall Pf E J (x : Var)(xs : list ProcVar)(f1 f2 : ProcVar -> Expr),
  let HP := Pf E in
  let b := precondition HP in
  let B := hcond_convert b f2 in
  let fq := fun _ => perm_full in
    (forall y, In y (hcond_fpv b) -> In y xs) ->
  ~ assn_fv J x ->
  ~ (exists y : ProcVar, In y xs /\ In x (expr_fv (f1 y))) ->
  ~ (exists y : ProcVar, In y xs /\ In x (expr_fv (f2 y))) ->
  csl False J
    (Astar (Aiter (ApointstoIter xs fq f1 f2 PTTstd)) (Aplain B))
    (Cproc x Pf E xs f1)
    (Astar (Astar (Aiter (ApointstoIter xs fq f1 f2 PTTproc)) (Aproc x perm_full HP xs f1)) (Aplain B)).
Proof.
  simpl. intros Pf E J x xs f1 f2.
  red. intros FV1 FV2 FV3 FV4. split; vauto.
  intros [|n] ph pm s g V1 V2 S1 WF SAT. vauto.
  destruct SAT as (ph1&ph2&D1&H1&pm1&pm2&D2&H2&SAT1&SAT2).
  set (F1 := expr_eval_map f1 s : ProcVar -> Val).
  set (F2 := expr_eval_map f2 s : ProcVar -> Val).
  repeat split; vauto.

  (* (2) absence of faults *)
  - red. intros phF pmF D3 D4 FIN1 FIN2 ABORT.
    inv ABORT. clear ABORT.
    apply H5. by apply pmFinite_free.

  (* (3) all shared-memory accesses are in the footprint *)
  - intros l (y&H1&H3). clarify.
    unfold ApointstoIter in SAT1.
    apply Aiter_In_l with (eq_dec:=procvar_eq_dec)(x0:=y) in SAT1; auto.
    + destruct SAT1 as (ph1'&ph2'&D3&H3&pm1'&pm2'&D4&H4&SAT1&SAT1').
      unfold sat in SAT1. destruct SAT1 as (_&SAT1).
      apply phcEntire_le in SAT1; vauto.
      2:{ by apply phDisj_valid_l in D3. }
      apply phcLt_le_trans with ((phUnion ph1' ph2') (expr_eval (f1 y) s)); vauto.
      * apply phcLt_weaken; vauto.
        by apply phcLt_entire_free.
      * apply phcLe_mono_pos. vauto.
    + by apply phDisj_valid_l in D1.
    + by apply pmDisj_valid_l in D2.

  (* (5) program step *)
  - simpl. intros phJ phF pmJ pmF pmC h' s' C' D3 D4 D5 D6 H1 FIN1 WS1 INV FIN2 COV1 PSAFE1 STEP.
    inv STEP. generalize SAT1. intro SAT1'.
    apply ApointstoIter_conv_std_proc in SAT1.

    (* the process map has a free entry (due to its finiteness) *)
    assert (H6 : exists pid, pmC pid = PEfree) by by apply pmFinite_free.
    destruct H6 as (pid&H6).

    pose (ls := map (expr_eval_map f1 s') xs : list Val).
    pose (ph1' := phConvProcMult ph1 ls).
    replace (map (expr_eval_map f1 s') xs) with ls in SAT1; auto.
    replace (phConvProcMult ph1 ls) with ph1' in SAT1; auto.

    (* [ph1 l] is a full standard cell, and [ph2 l], [phJ l] and [phF l] are empty for every location [l] in [ls] *)
    assert (HV1 : forall y : ProcVar, In y xs -> ph1 (F1 y) = PHCstd perm_full (F2 y)). {
      intros y HV1. apply ApointstoIter_sat_single_std with (x0 := y) in SAT1'; auto.
      apply phcLe_entire_eq in SAT1'; vauto. by apply phDisj_valid_l in D1. }
    assert (HVL1 : forall l : Val, In l ls -> exists v, ph1 l = PHCstd perm_full v). {
      intros l HLV1. subst ls. apply in_map_iff in HLV1.
      destruct HLV1 as (y&?&HLV1). clarify. exists (F2 y). by apply HV1. }
    assert (HV2 : forall y : ProcVar, In y xs -> ph2 (F1 y) = PHCfree). {
      intros y HV2. red in D1. red in D1. specialize D1 with (F1 y).
      rewrite HV1 in D1; auto. apply phcDisj_entire_free in D1; vauto. }
    assert (HVL2 : forall l, In l ls -> ph2 l = PHCfree). {
      intros l HVL2. subst ls. apply in_map_iff in HVL2.
      destruct HVL2 as (y&?&HVL2). clarify. by apply HV2. }
    assert (HV3 : forall y : ProcVar, In y xs -> phJ (F1 y) = PHCfree). {
      intros y HV3. red in D3. red in D3. specialize D3 with (F1 y).
      rewrite <- phUnion_cell in D3. rewrite HV1, HV2 in D3; auto.
      apply phcDisj_entire_free in D3; vauto. }
    assert (HVL3 : forall l, In l ls -> phJ l = PHCfree). {
      intros l HVL3. subst ls. apply in_map_iff in HVL3.
      destruct HVL3 as (y&?&HVL3). clarify. by apply HV3. }
    assert (HV4 : forall y : ProcVar, In y xs -> phF (F1 y) = PHCfree). {
      intros y HV4. red in D4. red in D4. specialize D4 with (F1 y).
      repeat rewrite <- phUnion_cell in D4. rewrite HV1, HV2, HV3 in D4; auto.
      apply phcDisj_entire_free in D4; vauto. }
    assert (HVL4 : forall l, In l ls -> phF l = PHCfree). {
      intros l HVL4. subst ls. apply in_map_iff in HVL4.
      destruct HVL4 as (y&?&HVL4). clarify. by apply HV4. }
    assert (HV5 : forall y : ProcVar, In y xs -> ph1' (F1 y) = PHCproc perm_full (F2 y)). {
      intros y HV5. subst ph1'. rewrite phConvProcMult_apply; vauto.
      - rewrite HV1; auto.
      - by apply in_map. }
    assert (HVL5 : forall l, In l ls -> exists v, ph1' l = PHCproc perm_full v). {
      intros l HVL5. subst ls. apply in_map_iff in HVL5.
      destruct HVL5 as (y&?&HVL5). clarify. apply HV5 in HVL5.
      exists (F2 y). vauto. }

    (* the heap [ph1'] is disjoint in every composition in which [ph1] is also disjoint *)
    assert (DISJ1 : phDisj ph1' ph2). {
      rewrite <- phConvProcMult_free with ls ph2; auto.
      subst ph1'. by apply phConvProcMult_disj. }
    assert (DISJ2 : phDisj (phUnion ph1' ph2) phJ). {
      rewrite <- phConvProcMult_free with ls ph2; auto.
      rewrite <- phConvProcMult_free with ls phJ; auto.
      subst ph1'. rewrite <- phConvProcMult_union; vauto.
      by apply phConvProcMult_disj. }
    assert (DISJ3 : phDisj (phUnion (phUnion ph1' ph2) phJ) phF). {
      rewrite <- phConvProcMult_free with ls ph2; auto.
      rewrite <- phConvProcMult_free with ls phJ; auto.
      rewrite <- phConvProcMult_free with ls phF; auto.
      subst ph1'. repeat rewrite <- phConvProcMult_union; vauto.
      by apply phConvProcMult_disj. }

    (* some results on the concrete- and snapshot values of [ph1] with respect to locations in [ls] *)
    assert (HS1 : forall y : ProcVar, In y xs -> phcConcr (ph1 (F1 y)) = Some (F2 y)). {
      intros y HS1. rewrite HV1; auto. }
    assert (HSL1 : forall l, In l ls -> exists v, phcConcr (ph1 l) = Some v). {
      intros l HSL1. apply HVL1 in HSL1. destruct HSL1 as (v&HSL1). exists v. by rewrite HSL1. }
    assert (HS2 : forall y : ProcVar, In y xs -> phcSnapshot (ph1 (F1 y)) = None). {
      intros y HS2. rewrite HV1; auto. }
    assert (HSL2 : forall l, In l ls -> phcSnapshot (ph1 l) = None). {
      intros l HSL2. apply HVL1 in HSL2. destruct HSL2 as (v&HSL2). by rewrite HSL2. }
    assert (HS3 : forall y : ProcVar, In y xs -> phcSnapshot (ph1' (F1 y)) = Some (F2 y)). {
      intros y HS3. rewrite HV5; auto. }
    assert (HSL3 : forall l, In l ls -> exists v, phcSnapshot (ph1' l) = Some v). {
      intros l HSL3. apply HVL5 in HSL3. destruct HSL3 as (v&HSL3). exists v. by rewrite HSL3. }

    exists (phUnion ph1' ph2), phJ. intuition vauto.

    1:{ (* the heap concretisation is proper *)
      rewrite <- phConvProcMult_free with (xs := ls)(ph := ph2) at 1; auto.
      rewrite <- phConvProcMult_free with (xs := ls)(ph := phJ) at 1; auto.
      rewrite <- phConvProcMult_free with (xs := ls)(ph := phF) at 1; auto.
      subst ph1'. repeat rewrite <- phConvProcMult_union; vauto.
      by rewrite phConvProcMult_concr. }

    (* the entries [pm1 pid], [pm2 pid], [pmJ pid] and [pmF pid] are all free *)
    assert (PDISJ1 : pmUnion (pmUnion pm pmJ) pmF pid = PEfree). {
      apply pmeBisim_free with (pmC pid); auto.
      symmetry. by apply H1. }
    apply pmeUnion_free in PDISJ1. destruct PDISJ1 as (PDISJ1&PDISJ2).
    apply pmeUnion_free in PDISJ1. destruct PDISJ1 as (PDISJ1&PDISJ3).
    assert (PDISJ4 : pmUnion pm1 pm2 pid = PEfree). {
      apply pmeBisim_free with (pm pid); auto.
      symmetry. by apply H2. }
    apply pmeUnion_free in PDISJ4. destruct PDISJ4 as (PDISJ4&PDISJ5).

    (* construct the updated process maps *)
    rename s' into s.
    pose (HP := Pf E).
    pose (P := pDehybridise HP s).
    pose (pm' := pmUpdate pm pid (PEelem perm_full P xs F1)).
    pose (pmC' := pmUpdate pmC pid (PEelem perm_full P xs F1)).
    exists pm', pmJ, pmC'. repeat split; auto.

    1:{ (* the process maps [pm'] and [pmJ] are disjoint *)
      subst pm'. intro pid'. unfold pmUpdate, update. desf.
      rewrite PDISJ3. by apply pmeDisj_free_l. }

    1:{ (* the process maps [pm' + pmJ] and [pmF] are disjoint *)
      subst pm'. intro pid'. rewrite <- pmUnion_elem.
      unfold pmUpdate, update. desf.
      - rewrite PDISJ2, PDISJ3. rewrite pmeUnion_free_l.
        by apply pmeDisj_free_l.
      - by apply D6. }

    1:{ (* the composition [pm' + pmJ + pmF] equals [pmC] *)
      subst pmC'. intro pid'. unfold pmUpdate, update. desf.
      - repeat rewrite <- pmUnion_elem.
        rewrite PDISJ2, PDISJ3. repeat rewrite pmeUnion_free_l.
        subst pm'. unfold pmUpdate, update. desf.
      - red in H1. red in H1. specialize H1 with pid'.
        rewrite <- H1. repeat rewrite <- pmUnion_elem.
        repeat apply pmeUnion_bisim_l. subst pm'.
        unfold pmUpdate, update. desf. }

    1:{ (* [pmC'] is finite *)
      subst pmC'. by apply pmFinite_update. }

    1:{ (* [pmC'] is well-structured *)
      subst pmC'. apply pmWs_update; vauto.
      intros pid' l K1 ACC1 ACC2. simpl in ACC1.
      apply COV1 in ACC2. destruct ACC2 as (v&ACC2).
      unfold phSnapshot in ACC2.
      repeat rewrite <- phUnion_cell in ACC2.
      rewrite HVL2, HVL3, HVL4 in ACC2; vauto.
      repeat rewrite phcUnion_free_l in ACC2.
      apply in_map_iff in ACC1. destruct ACC1 as (y&ACC1'&ACC1). vauto.
      apply ApointstoIter_sat_single_std with (x0:=y) in SAT1'; vauto.
      apply phcLe_entire_eq in SAT1'; vauto.
      - subst F1. unfold expr_eval_map in ACC2.
        rewrite <- SAT1' in ACC2. vauto.
      - by apply phDisj_valid_l in D1. }

    1:{ (* if the program is basic, then the process map has not changed *)
    intro. contradiction. }

    1: { (* the map [pmC'] covers the new snapshot heap *)
      subst pmC'. apply pmCovers_update.

      (* the new process maps entry is covered in the new snapshot heap *)
      - intros l H13. simpl in H13. subst F1. generalize H13. intro H13'.
        apply in_map_iff in H13. destruct H13 as (y&H13&H14). vauto.
        apply ApointstoIter_sat_single_proc with (x0 := y) in SAT1; vauto.
        apply phcLe_entire_eq in SAT1; vauto.
        + exists (expr_eval (f2 y) s). unfold phSnapshot.
          repeat rewrite <- phUnion_cell.
          rewrite HVL2, HVL3, HVL4; vauto.
          repeat rewrite phcUnion_free_l.
          subst ph1' ls. unfold expr_eval_map at 2.
          rewrite <- SAT1. by vauto.
        + apply phConvProcMult_valid.
         by apply phDisj_valid_l in D1.

      (* all existing process map entries are still covered in the new snapshot heap *)
      - apply pmCovers_subheap with (phSnapshot (phUnion (phUnion (phUnion ph1 ph2) phJ) phF)); vauto.
        intros l v H13. subst ph1'.
        rewrite <- phConvProcMult_free with (xs := ls)(ph := ph2) at 1; auto.
        rewrite <- phConvProcMult_free with (xs := ls)(ph := phJ) at 1; auto.
        rewrite <- phConvProcMult_free with (xs := ls)(ph := phF) at 1; auto.
        repeat rewrite <- phConvProcMult_union; vauto.
        unfold phSnapshot in *.
        assert (K1 : In l ls \/ ~ In l ls) by by apply classic.
        destruct K1 as [K1 | K1].
        + repeat rewrite <- phUnion_cell in H13.
          rewrite HVL2, HVL3, HVL4 in H13; vauto. repeat rewrite phcUnion_free_l in H13.
          subst ls. apply in_map_iff in K1. destruct K1 as (y&K1&K2). vauto.
          apply ApointstoIter_sat_single_std with (x0 := y) in SAT1'; vauto.
          apply phcLe_entire_eq in SAT1'; vauto.
          * subst F1. unfold expr_eval_map in H13.
            rewrite <- SAT1' in H13. by vauto.
          * by apply phDisj_valid_l in D1.
        + rewrite <- phConvProcMult_pres; vauto. }

    1:{ (* the map [pmC'] is safe with the new snapshot heap *)
      subst pmC'. intro pid'. unfold pmUpdate, update. desf.

      (* the new entry is safe *)
      - red. intros ps IN1. subst HP P.
        apply precondition_safe. unfold sat in SAT2.
        rewrite cHybridise_conv_eval with (ps:=ps) in SAT2; auto.
        intros y IN2.
        assert (IN3 : In y xs) by by apply FV1.
        assert (PS1 : phcSnapshot (ph1' (F1 y)) = Some (ps y)). {
          rewrite <- IN1; auto. rewrite HS3; auto.
          symmetry. unfold phSnapshot. repeat rewrite <- phUnion_cell.
          rewrite HV2, HV3, HV4; auto. repeat rewrite phcUnion_free_l.
          by apply HS3. }
        assert (PS2 : Some (ps y) = Some (F2 y)). {
          rewrite <- PS1. by apply HS3. }
        vauto.

      (* all existing entries are still safe *)
      - apply pmeSafe_heap_acc with (phSnapshot (phUnion (phUnion (phUnion ph1 ph2) phJ) phF)); auto.
        intros l IN1. unfold phSnapshot.
        repeat apply phcSnapshot_disj_union_l; auto.
        (* the location [l] can not be in [ls] *)
        assert (IN2 : exists v, phcSnapshot (phUnion (phUnion (phUnion ph1 ph2) phJ) phF l) = Some v). {
          red in COV1. specialize COV1 with pid'. red in COV1.
          apply COV1 in IN1. clear COV1. destruct IN1 as (v&IN1). vauto. }
        assert (IN3 : ~ In l ls). {
          intro IN3. generalize IN3. intro IN4.
          apply HSL2 in IN3. destruct IN2 as (v&IN2).
          cut (phcSnapshot (phUnion (phUnion (phUnion ph1 ph2) phJ) phF l) = None); intuition vauto.
          repeat rewrite <- phUnion_cell. rewrite HVL2, HVL3, HVL4; vauto.
          by repeat rewrite phcUnion_free_l. }
        subst ph1'. by rewrite <- phConvProcMult_pres. }

    exists (sUpdate g x pid), Cskip. repeat split; vauto.

    1: { (* the resource invariant is still maintained *)
      unfold invariant_sat in INV.
      red. simpls. intros _. intuition.
      by apply sat_update_ghost. }

    apply safe_done. exists ph1', ph2. repeat split.

    1:{ (* [ph1'] is disjoint with [ph2] *)
      subst ph1'. rewrite <- phConvProcMult_free with ls ph2; auto.
      by apply phConvProcMult_disj. }

    pose (pm1' := pmUpdate pm1 pid (PEelem perm_full P xs F1)).
    exists pm1', pm2. repeat split; auto.

    1:{ (* [pm1'] is disjoint with [pm2] *)
      subst pm1'. intro pid'. unfold pmUpdate, update. desf.
      rewrite PDISJ5. apply pmeDisj_free_l. by vauto. }

    1:{ (* the addition [pm1' + pm2] equals [pm'] *)
      intro pid'. rewrite <- pmUnion_elem.
      subst pm'. unfold pmUpdate, update. desf.
      - rewrite PDISJ5. rewrite pmeUnion_free_l.
        subst pm1'. unfold pmUpdate, update. desf.
      - red in H2. red in H2. specialize H2 with pid'.
        rewrite <- H2. rewrite <- pmUnion_elem.
        apply pmeUnion_bisim_l. subst pm1'.
        unfold pmUpdate, update. desf. }

    exists ph1', phIden. repeat split.

    1:{ (* [ph1'] is disjoint with the identity heap *)
      apply phDisj_iden_l. subst ph1'.
      apply phConvProcMult_valid.
      by apply phDisj_valid_l in D1. }

    1:{ (* [ph1' + iden] equals [ph1'] (which is trivial) *)
      by rewrite phUnion_iden_l. }

    exists pmIden, pm1'. repeat split; vauto.

    1:{ (* [pm1'] is disjoint with the identity process map *)
      apply pmDisj_iden_r. subst pm1'.
      intro pid'. unfold pmUpdate, update. desf.
      by apply pmDisj_valid_l in D2. }

    1:{ (* [iden + pm1'] equals [pm1'] (which is trivial) *)
      by rewrite pmUnion_iden_r. }

    1:{ (* the iterated separating conjunction part of the postcondition is satisfied *)
      apply ApointstoIter_conv_std_proc; vauto.
      rewrite sat_update_ghost.
      - apply sat_ApointstoIter_indep with pm1; vauto.
      - intro FV. rewrite assn_fv_ApointstoIter in FV.
        destruct FV as (y&V3&V4).
        destruct V4 as [V4 | V4]; vauto.
        + apply FV3. exists y. vauto.
        + apply FV4. exists y. vauto. }

    1:{ (* the process predicate part of the postcondition holds *)
      unfold sat. exists PEfree. split; vauto.
      unfold sUpdate. rewrite update_apply.
      rewrite pmeUnion_free_l. subst pm1'.
      unfold pmUpdate. rewrite update_apply.
      by vauto. }
Qed.


(** *** Process finish rule *)

Theorem rule_proc_finish :
  forall HP J (x : Var)(xs : list ProcVar)(f1 f2 : ProcVar -> Expr),
  let fq := fun _ => perm_full in
  csl False J
    (Astar (Aiter (ApointstoIter xs fq f1 f2 PTTproc)) (Aproc x perm_full (HPalt HP HPepsilon) xs f1))
    (Cendproc x)
    (Aiter (ApointstoIter xs fq f1 f2 PTTstd)).
Proof.
  intros PH J x xs f1 f2. red. split; vauto.
  intros [|n] ph pm s g V1 V2 S1 WF SAT. vauto.
  set (F1 := expr_eval_map f1 s : ProcVar -> Val).
  set (F2 := expr_eval_map f2 s : ProcVar -> Val).
  destruct SAT as (ph1&ph2&D1&H1&pm1&pm2&D2&H2&SAT1&SAT2).
  repeat split; vauto.

  (* (2) absence of faults - two cases *)
  - red. intros phF pmF D3 D4 FIN1 FIN2 ABORT.
    inv ABORT; clear ABORT.

    (* case 1: [(pm + pmF) pid] can not be empty *)
    + apply H5. clear H5. unfold sat in SAT2.
      destruct SAT2 as (pme&D5&H1).
      apply pmeEntire_union; vauto. left.
      red in H2. red in H2. specialize H2 with (g x).
      rewrite <- H2, <- pmUnion_elem.
      apply pmeEntire_union; vauto. right.
      rewrite H1. apply pmeEntire_union; vauto.

    (* case 2: the process entry at [(pm + pmF) pid] must terminate *)
    + apply H6. clear H6. unfold sat in SAT2.
      destruct SAT2 as (pme&D5&SAT2).
      rewrite pmeEntire_exp_l in SAT2; vauto.
      red in H2. red in H2. specialize H2 with (g x).
      rewrite <- pmUnion_elem in H2. rewrite SAT2 in H2.
      rewrite pmeEntire_exp_r in H2; vauto.

      1:{ (* [P] terminates *)
        rewrite <- pmUnion_elem in H0. rewrite <- H2 in H0.
        rewrite pmeEntire_exp_l in H0; vauto.
        - simpl in H0. destruct H0 as (K1&K2&K3&K4).
          clarify. rewrite <- K2. by vauto.
        - red in D4. red in D4. specialize D4 with (g x).
          by rewrite <- H2 in D4. }

      1:{ (* [pm1] is disjoint with [pm2] *)
        rewrite <- SAT2. auto. }

  (* (5) program step *)
  - simpl.
    intros phJ phF pmJ pmF pmC h' s' C'
      D3 D4 D5 D6 H1 FIN1 WS1 INV FIN2 COV1 PSAFE1 STEP.
    inv STEP. generalize SAT1. intro SAT1'.
    apply ApointstoIter_conv_proc_std in SAT1.
    pose (ys := map (expr_eval_map f1 s') xs : list Val).
    pose (ph1' := phConvStdMult ph1 ys).

    (* [ph2 l] is free for every [l] in the iterated separation conjunction *)
    assert (H3 : forall l, In l ys -> ph2 l = PHCfree). {
      intros l' H3. apply ApointstoIter_perm_full with (l := l') in SAT1; vauto.
      rewrite phConvStdMult_entire in SAT1.
      red in D1. red in D1. specialize D1 with l'.
      by apply phcDisj_entire_free in D1. }

    (* [phJ l] is free for every [l] in the iterated separation conjunction *)
    assert (H4 : forall l, In l ys -> phJ l = PHCfree). {
      intros l' H4. apply ApointstoIter_perm_full with (l := l') in SAT1; vauto.
      rewrite phConvStdMult_entire in SAT1.
      red in D3. red in D3. specialize D3 with l'.
      apply phcDisj_entire_free in D3; vauto.
      rewrite <- phUnion_cell. rewrite H3; auto.
      by rewrite phcUnion_free_l. }

    (* [phF l] is free for every [l] in the iterated separation conjunction *)
    assert (H5 : forall l, In l ys -> phF l = PHCfree). {
      intros l' H5. apply ApointstoIter_perm_full with (l := l') in SAT1; vauto.
      rewrite phConvStdMult_entire in SAT1.
      red in D4. red in D4. specialize D4 with l'.
      apply phcDisj_entire_free in D4; vauto.
      repeat rewrite <- phUnion_cell.
      rewrite H3, H4; auto.
      by repeat rewrite phcUnion_free_l. }

    exists (phUnion ph1' ph2), phJ. repeat split; vauto.

    1:{ (* disjointness of [ph1' + ph2] and [phJ] *)
      subst ph1'.
      rewrite <- phConvStdMult_free with ys ph2; auto.
      rewrite <- phConvStdMult_union; vauto.
      rewrite <- phConvStdMult_free with ys phJ; auto.
      by apply phConvStdMult_disj. }

    1:{ (* disjointness of [ph1' + ph2 + phJ] and [phF] *)
      subst ph1'.
      rewrite <- phConvStdMult_free with ys ph2; auto.
      rewrite <- phConvStdMult_union; vauto.
      rewrite <- phConvStdMult_free with ys phJ; auto.
      rewrite <- phConvStdMult_union; vauto.
      rewrite <- phConvStdMult_free with ys phF; auto.
      by apply phConvStdMult_disj. }

    1:{ (* the heap concretisation is proper *)
      subst ph1'.
      rewrite <- phConvStdMult_free with (xs:=ys)(ph:=ph2) at 1; auto.
      rewrite <- phConvStdMult_union; vauto.
      rewrite <- phConvStdMult_free with (xs:=ys)(ph:=phJ) at 1; auto.
      rewrite <- phConvStdMult_union; vauto.
      rewrite <- phConvStdMult_free with (xs:=ys)(ph:=phF) at 1; auto.
      rewrite <- phConvStdMult_union; vauto.
      by rewrite phConvStdMult_concr. }

    unfold sat in SAT2. destruct SAT2 as (pme&D7&H6).
    assert (H8 : pme = PEfree) by by apply pmeDisj_entire_free in D7.
    clarify. rewrite pmeUnion_free_l in H6.

    (* the map [pm1] is free at (g x) *)
    assert (H9 : pm1 (g x) = PEfree). {
      red in D2. red in D2. specialize D2 with (g x).
      symmetry in D2. apply pmeDisj_entire_free in D2; vauto.
      rewrite H6. vauto. }

    (* the entry [pm (g x)] equals [pm2 (g x)] *)
    assert (H10 : pmeBisim (pm (g x)) (pm2 (g x))). {
      red in H2. red in H2. specialize H2 with (g x).
      rewrite <- H2. rewrite <- pmUnion_elem.
      rewrite H9, H6. by rewrite pmeUnion_free_r. }

    rewrite H6 in H10.

    (* the map [pmJ] is free at (g x) *)
    assert (H11 : pmJ (g x) = PEfree). {
      red in D5. red in D5. specialize D5 with (g x).
      apply pmeDisj_entire_free in D5; vauto.
      rewrite H10. vauto. }

    (* the map [pmF] is free at (g x) *)
    assert (H12 : pmF (g x) = PEfree). {
      red in D6. red in D6. specialize D6 with (g x).
      rewrite <- pmUnion_elem in D6. rewrite H11 in D6.
      rewrite pmeUnion_free_l in D6.
      apply pmeDisj_entire_free in D6; vauto.
      rewrite H10. vauto. }

    (* the map [pmC] is full at (g x) *)
    assert (H13 : pmeEntire (pmC (g x))). {
      red in H1. red in H1. specialize H1 with (g x).
      rewrite <- H1. repeat rewrite <- pmUnion_elem.
      rewrite H10, H11, H12.
      repeat rewrite pmeUnion_free_l. by vauto. }

    (* the new snapshot heap equals the old snapshot heap at all locations accessed by entries in [pmC] other than [pmC (g x)] *)
    assert (H14 : forall pid l, pid <> g x -> In l (pmeProj (pmC pid)) ->
        phSnapshot (phUnion (phUnion (phUnion ph1' ph2) phJ) phF) l =
        phSnapshot (phUnion (phUnion (phUnion ph1 ph2) phJ) phF) l). {
      intros pid l K1 K2. subst ph1'.
      assert (H : ~ In l ys). {
        intro K3. red in WS1.
        apply WS1 with (p2 := g x) in K2; vauto.
        red in H1. red in H1. specialize H1 with (g x).
        rewrite <- H1. repeat rewrite <- pmUnion_elem.
        rewrite H10, H11, H12.
        repeat rewrite pmeUnion_free_l. by vauto. }
      rewrite <- phConvStdMult_free with (xs:=ys)(ph:=ph2) at 1; auto.
      rewrite <- phConvStdMult_union; vauto.
      rewrite <- phConvStdMult_free with (xs:=ys)(ph:=phJ) at 1; auto.
      rewrite <- phConvStdMult_union; vauto.
      rewrite <- phConvStdMult_free with (xs:=ys)(ph:=phF) at 1; auto.
      rewrite <- phConvStdMult_union; vauto.
      unfold phSnapshot. by rewrite <- phConvStdMult_pres. }

    exists (pmUpdate pm (g x) PEfree), pmJ, (pmUpdate pmC (g x) PEfree).
    repeat split; vauto.

    1:{ (* the updated [pm] is still disjoint with [pmJ] *)
      intro pid'. unfold pmUpdate, update. desf.
      apply pmeDisj_free_r. by apply pmDisj_valid_r in D5. }

    1:{ (* the updated [pm + pmJ] is still disjoint with [pmJ] *)
      intro pid'. rewrite <- pmUnion_elem.
      unfold pmUpdate, update. desf.
      - rewrite pmeUnion_free_r.
        apply pmeDisj_union_l with (pm (g x)); vauto.
        by apply D6.
      - by apply D6. }

    1:{ (* the update [pm + pmJ + pmF] equals the updated [pmC] *)
      intro pid'. repeat rewrite <- pmUnion_elem.
      unfold pmUpdate, update. desf.
      - rewrite H11, H12. by rewrite pmeUnion_free_r.
      - by apply H1. }

    1:{ (* the new process map is finite *)
      by apply pmFinite_update. }

    1:{ (* the new process map is well-structured *)
      by apply pmWs_update; vauto. }

    1:{ (* the new process map covers the new snapshot heap *)
      red. intro pid. unfold pmUpdate, update. desf.
      apply pmeCovers_agrees with (phSnapshot (phUnion (phUnion (phUnion ph1 ph2) phJ) phF)); vauto.
      intros l K1. rewrite H14 with (pid := pid); intuition vauto. }

    1:{ (* the new process map is safe with the new snapshot heap *)
      red. intro pid. unfold pmUpdate, update. desf.
      apply pmeSafe_heap_acc with (phSnapshot (phUnion (phUnion (phUnion ph1 ph2) phJ) phF)); vauto.
      intros l K1. rewrite H14 with (pid := pid); intuition vauto. }

    exists g, Cskip. repeat split; vauto.

    1:{ (* the ghost semantics can make a matching step *)
      apply pmeEntire_content in H13.
      destruct H13 as (P'&xs'&f&H13). clarify.
      red in H1. red in H1. specialize H1 with (g x).
      rewrite H13 in H1. repeat rewrite <- pmUnion_elem in H1.
      rewrite H10, H11, H12 in H1.
      repeat rewrite pmeUnion_free_l in H1.
      simpl in H1. desf.
      apply gstep_proc_end with P' xs' f; vauto.
      - by rewrite H13.
      - rewrite <- H0. clear H0. vauto. }

    apply safe_done.
    remember (pmUpdate pm (g x) PEfree) as pm'.

    (* [pm'] is valid *)
    assert (G1 : pmValid pm'). {
      subst pm'. unfold pmUpdate, update. red.
      intros p. by desf. }

    rewrite <- pmUnion_iden_l with pm'.
    apply sat_weaken; auto.

    1:{ (* [ph1'] is disjoint with [ph2] *)
      subst ph1'. rewrite <- phConvStdMult_free with ys ph2; auto.
      by apply phConvStdMult_disj. }

    apply ApointstoIter_conv_proc_std.
    by apply sat_ApointstoIter_indep with pm1.
Qed.


(** *** Action rule *)

(** The soundness proof of the action rule requires some
    extra auxiliary definitions and properties, in particular
    that the metadata that is stored in [Cinact] commands
    actually makes sense with respect to the rest of the
    state that is maintained. The central definition that helps
    with is is [metadata_agree]. *)

Lemma phcConcr_snapshot_none :
  forall pme, phcConcr pme = None -> phcSnapshot pme = None.
Proof. intros ??. unfold phcConcr, phcSnapshot in *. desf. Qed.

Definition metadata_agree (pid : Val)(a : Act)(v : Val)(xs : list ProcVar)(f : ProcVar -> Val)(h hs : Heap)(pm : ProcMap) : Prop :=
  (* (1) the process map [pm] must have an entry at [pid] *)
  exists (q : Qc)(P : Proc),
    pmeBisim (pm pid) (PEelem q P xs f) /\
  (* (2) all free variables of the action [a]
         must be covered by [pm pid] *)
    (forall x : ProcVar, In x (act_fv a v) -> In x xs) /\
  (* (3) the heaps [h] and [hs] must agree on all locations
         corresponding to variables in [xs] *)
    (forall x : ProcVar, In x xs -> h (f x) = hs (f x)) /\
  (* (4) a process store can be constructed from the heap
         that satisfies the guard of [a] *)
    exists ps : ProcStore,
      (forall x : ProcVar, In x xs -> h (f x) = Some (ps x)) /\
        pcond_eval (guard a v) ps = true.

Lemma metadata_agree_pmBisim :
  forall pid a v xs f h hs pm1 pm2,
  pmBisim pm1 pm2 ->
  metadata_agree pid a v xs f h hs pm1 ->
  metadata_agree pid a v xs f h hs pm2.
Proof.
  intros pid a v xs f h hs pm1 pm2 H1 H2.
  unfold metadata_agree in *.
  destruct H2 as (q&P&H2&H3&H4&ps&H5&H6).
  exists q, P. intuition vauto.
  by rewrite <- H1.
Qed.

Add Parametric Morphism : metadata_agree
  with signature eq ==> eq ==> eq ==> eq ==> eq ==> eq ==> eq ==> pmBisim ==> iff
    as metadata_agree_pmBisim_mor.
Proof.
  intros pid p a xs f h hs pm1 pm2 H1. split; intro H2.
  - apply metadata_agree_pmBisim with pm1; auto.
  - apply metadata_agree_pmBisim with pm2; auto.
    by symmetry.
Qed.

Lemma metadata_agree_F :
  forall pid a v xs F1 F2 h hs pm,
    (forall x : ProcVar, In x xs -> F1 x = F2 x) ->
  metadata_agree pid a v xs F1 h hs pm ->
  metadata_agree pid a v xs F2 h hs pm.
Proof.
  intros pid p a xs F1 F2 h hs pm IN1 H1.
  unfold metadata_agree in *.
  destruct H1 as (q&P&H1&H2&H3&ps&H4&H5).
  exists q, P. intuition vauto.
  - rewrite H1. by apply pmeBisim_F.
  - rewrite <- IN1; vauto. by apply H3.
  - exists ps. split; vauto. intros y IN2.
    by rewrite <- IN1; auto.
Qed.

(** Now to the actual soundness result, which can be proven
    using the following (rather involved) key lemma: *)

Lemma safe_action :
  forall n C ph pm pm' (s g : Store) x hs q E HP HQ (xs ys1 ys2 : list ProcVar) a (fq : ProcVar -> Qc)(f1 f2 : ProcVar -> Expr)(J A : Assn),
  let B2 := hcond_convert (heffect a E) f2 in
  let F1 := expr_eval_map f1 s : ProcVar -> Val in
  let v := expr_eval E s in
  metadata_agree (g x) a v xs F1 hs (phSnapshot ph) pm' ->
  Permutation xs (ys1 ++ ys2) ->
  (forall y : ProcVar, In y ys1 -> fq y <> perm_full) ->
  (forall y : ProcVar, In y ys2 -> fq y = perm_full) ->
  (forall y : ProcVar, In y xs -> perm_valid (fq y)) ->
  (forall y : ProcVar, disjoint (expr_fv (f1 y)) (cmd_mod C)) ->
  disjoint (expr_fv E) (cmd_mod C) ->
  disjoint (hproc_fv HP) (cmd_mod C) ->
  disjoint (hproc_fv HQ) (cmd_mod C) ->
  ~ cmd_mod C x ->
  cmd_basic C ->
  pmDisj pm pm' ->
  sat phIden pm' s g (Aproc x q (HPalt (HPseq (HPact a E) HP) HQ) xs f1) ->
  safe n True C ph pm s g J (Astar (Astar (Aiter (ApointstoIter_procact xs fq f1 f2)) (Aplain B2)) A) ->
  safe n False (Cinact (GMdata (g x) a v hs) C) ph (pmUnion pm pm') s g J (Astar (Astar (Astar (Aiter (ApointstoIter xs fq f1 f2 PTTproc)) (Aproc x q HP xs f1)) (Aplain B2)) A).
Proof.
  induction n as [|n IH]. vauto.
  intros C ph pm pm' s g x hs q E HP HQ xs ys1 ys2
    a fq f1 f2 J A B2 F1 v AGR1 PERM1 PERM2 PERM3 VF
    DISJ1 DISJ2 DISJ3 DISJ4 DISJ5 BASIC1 D1 SAT1 SAFE1.
  set (F2 := expr_eval_map f2 s : ProcVar -> Val).

  (* variable [y] is in [xs] iff [y] is in either [ys1] or [ys2] *)
  assert (PERM4 : forall y : ProcVar, In y xs <-> In y ys1 \/ In y ys2). {
    intro y. split; intros.
    - apply Permutation_in with (x:=y) in PERM1; auto.
      apply in_app_or in PERM1.
      destruct PERM1 as [PERM1|PERM1]; vauto.
    - symmetry in PERM1.
      apply Permutation_in with (x:=y) in PERM1; auto.
      by apply in_or_app. }

  repeat split; vauto.

  (* (2) absence of faults - five possible faulting cases *)
  - red. clear IH. intros phF pmF D3 D4 FIN1 FIN2 ABORT1.
    destruct SAFE1 as (TERM1&ABORT2&_).
    inv ABORT1; vauto.

    (* case 1: fault in program [C] *)
    + rewrite pmUnion_assoc in H4.
      apply ABORT2 in H4; vauto.
      * by apply pmDisj_assoc_l.
      * by rewrite <- pmUnion_assoc.

    (* case 2: the process map does not contain an entry at [pid] *)
    + apply H4. clear H4.
      destruct AGR1 as (q'&P'&AGR1&_).
      assert (OCC1 : pmeOcc (pm' (g x))) by by rewrite AGR1.
      apply pmeOcc_union_l with (c2 := pm (g x)) in OCC1; auto.
      rewrite pmeUnion_comm in OCC1.
      apply pmeOcc_union_l with (c2 := pmF (g x)) in OCC1; auto.
      * by apply D4.
      * by symmetry.

    (* case 3: not all process variables in [xs] are covered by the snapshot heap *)
    + unfold metadata_agree in AGR1.
      destruct AGR1 as (q'&P'&AGR1&_&_&ps&AGR2&_).
      repeat rewrite <- pmUnion_pme in H5.
      destruct H9 as (x'&H9&H10).
      assert (PAGR1 : pmeOcc (pm' (g x))) by by rewrite AGR1.
      assert (PAGR2 : pmeWeakAgree (pm' (g x)) (pmUnion pm pm' (g x))). {
        unfold pmUnion. rewrite pmeUnion_comm.
        apply pmeWeakAgree_union_occ; auto.
        by symmetry. }
      assert (PAGR3 : pmeWeakAgree (pm' (g x)) (pmUnion (pmUnion pm pm') pmF (g x))). {
        transitivity (pmUnion pm pm' (g x)); auto.
        apply pmeWeakAgree_union_occ; auto.
        apply pmeOcc_union_r; auto. }
      rewrite AGR1 in PAGR3. repeat rewrite <- pmUnion_pme in PAGR3.
      rewrite H5 in PAGR3. unfold pmeWeakAgree in PAGR3.
      repeat desf. rename xs0 into xs.
      assert (PC1 : forall y : ProcVar, In y xs -> f y = F1 y). {
        intros. apply map_eq_In with xs; vauto. }
      rewrite PC1 in H10; auto.
      rewrite AGR2 in H10; vauto.

    (* case 4: not all process variables in [xs] are covered by the concrete heap *)
    + destruct H9 as (x'&H9&H10).
      destruct AGR1 as (q'&P'&AGR1&AGR2&AGR3&ps&AGR4&AGR5).
      assert (PAGR1 : pmeOcc (pm' (g x)))by by rewrite AGR1.
      assert (PAGR2 : pmeWeakAgree (pm' (g x)) (pmUnion pm pm' (g x))). {
        unfold pmUnion. rewrite pmeUnion_comm.
        apply pmeWeakAgree_union_occ; auto.
        by symmetry. }
      assert (PAGR3 : pmeWeakAgree (pm' (g x)) (pmUnion (pmUnion pm pm') pmF (g x))). {
        transitivity (pmUnion pm pm' (g x)); auto.
        apply pmeWeakAgree_union_occ; auto.
        apply pmeOcc_union_r; auto. }
      rewrite AGR1 in PAGR3.
      repeat rewrite <- pmUnion_pme in PAGR3.
      rewrite H5 in PAGR3. unfold pmeWeakAgree in PAGR3.
      repeat desf. rename xs0 into xs, q0 into q''.
      assert (PC1 : forall y : ProcVar, In y xs -> f y = F1 y). {
        intros. apply map_eq_In with xs; vauto. }
      assert (K1 : phcConcr (ph (f x')) = None). {
        apply phcConcr_le_none with (phcUnion (ph (f x')) (phF (f x'))); vauto.
        apply phcLe_mono_pos; auto. }
      assert (K2 : phcSnapshot (ph (f x')) = None). {
        by apply phcConcr_snapshot_none. }
      assert (K3 : hs (F1 x') = None). {
        rewrite AGR3; auto. unfold phSnapshot.
        rewrite <- K2; vauto. rewrite PC1; vauto. }
      assert (K4 : hs (F1 x') = Some (ps x')) by by apply AGR4.
      by congruence.

    (* case 5: the process semantics can not make a synchronising step *)
    + assert (SAT2 : @Cskip GhostMetadata = Cskip). { vauto. }
      apply TERM1 in SAT2. clear TERM1.

      (* [ph] and [pm are both valid] *)
      assert (V1 : phValid ph). {
        by apply phDisj_valid_l in D3. }
      assert (V2 : pmValid pm). {
        by apply pmDisj_valid_l in D1. }

      apply assn_weaken_l in SAT2; auto.
      destruct SAT2 as (ph1&ph2&D5&H13&pm1&pm2&D6&H14&SAT2&SAT3).
      destruct AGR1 as (q'&P'&AGR1&AGR2&AGR3&ps&AGR4&AGR5).
      destruct SAT1 as (pme&D7&SAT1).

      assert (PAGR1 : pmeOcc (pm' (g x))) by by rewrite AGR1.
      assert (PAGR2 : pmeWeakAgree (pm' (g x)) (pmUnion pm pm' (g x))). {
        unfold pmUnion. rewrite pmeUnion_comm.
        apply pmeWeakAgree_union_occ; auto.
        by symmetry. }
      assert (PAGR3 : pmeWeakAgree (pm' (g x)) (pmUnion (pmUnion pm pm') pmF (g x))). {
        transitivity (pmUnion pm pm' (g x)); auto.
        apply pmeWeakAgree_union_occ; auto.
        apply pmeOcc_union_r; auto. }

      rewrite AGR1 in PAGR3. repeat rewrite <- pmUnion_pme in PAGR3.
      rewrite H7 in PAGR3. unfold pmeWeakAgree in PAGR3.
      repeat desf. rename q0 into q'', xs0 into xs.

      (* auxiliary properties related to the guard and effect of [a] *)
      assert (K1 : forall y : ProcVar, In y xs -> f y = F1 y). {
        intros. by apply map_eq_In with xs. }
      assert (K2 : pstore_agree xs ps ps1). {
        intros y K2.
        cut (Some (ps y) = Some (ps1 y)); [intuition vauto|].
        rewrite <- AGR4, <- H9; vauto. rewrite K1; vauto. }
      assert (K3 : pcond_eval (guard a v) ps1 = true). {
        rewrite pcond_agree with (s2 := ps); vauto.
        apply pstore_agree_weaken with xs; [|by symmetry].
        intros y K3. apply AGR2. unfold act_fv.
        apply in_or_app. by left. }
      assert (K4 : forall y : ProcVar, In y (pcond_fv (effect a v)) -> In y xs). {
        intros y K4. apply AGR2. unfold act_fv.
        apply in_or_app. by right. }
      assert (V3 : phValid ph1). { by apply phDisj_valid_l in D5. }
      assert (V4 : pmValid pm1). { by apply pmDisj_valid_l in D6. }

      apply sat_procact_iter_permut with (ys := ys1 ++ ys2) in SAT2; auto.
      apply ApointstoIter_procact_split in SAT2; auto.
      destruct SAT2 as (ph1a&ph1b&D8&ADD1&pm1a&pm1b&D9&ADD2&SAT1a&SAT1b).
      clarify.

      (* auxiliary properties about the contents of [ph1a] and [ph1b] *)
      assert (HC1 : forall y : ProcVar, In y ys1 ->
          exists q : Qc, perm_valid q /\ ph1a (expr_eval (f1 y) s) = PHCproc q (expr_eval (f2 y) s)). {
        intros y HC1.
        apply ApointstoIter_sat_single_proc with (x0 := y) in SAT1a; auto.
        apply phcLe_diff in SAT1a; vauto.
        - destruct SAT1a as (phc&D11&SAT1a). rewrite <- SAT1a.
          unfold phcDisj in D11. destruct phc as [|q'''|q'''|q'''|]; vauto.
          unfold phcUnion. desf. exists (fq y + q'''); split; vauto.
          by apply perm_add_valid.
        - simpl. apply VF. rewrite PERM4. by left.
        - by apply phDisj_valid_l in D8. }
      assert (HC2 : forall y : ProcVar, In y ys2 ->
          exists v : Val, ph1b (expr_eval (f1 y) s) = PHCact perm_full (expr_eval (f2 y) s) v). {
        intros y HC2.
        apply ApointstoIter_sat_single_act with (x0 := y) in SAT1b; auto.
        destruct SAT1b as (v'&SAT1b).
        apply phcLe_entire_eq in SAT1b; vauto.
        - rewrite <- SAT1b. exists v'. rewrite PERM3; vauto.
        - by apply phDisj_valid_r in D8.
        - rewrite PERM3; vauto. }

      (* the effect of [a] holds with [ps2] *)
      assert (K5 : pcond_eval (effect a v) ps2 = true). {
        rewrite <- cond_eval_conv with (s := s)(f := f2); vauto.

        1:{ (* prove that [a]'s effect actually holds. *)
          subst B2 v. simpl in SAT3.
          rewrite <- SAT3. clear SAT3.
          symmetry. by apply heffect_corr. }

        intros y K5.
        cut (Some (ps2 y) = Some (expr_eval (f2 y) s)); [intuition vauto|].
        rewrite <- H10; [|by apply K4].
        rewrite K1; [|by apply K4].
        apply K4 in K5. rewrite PERM4 in K5. destruct K5 as [K5 | K5].
        - apply HC1 in K5. destruct K5 as (q'''&K5&K6).
          unfold phConcr.
          repeat (rewrite <- phUnion_cell; apply phcConcr_union; auto).
          subst F1. unfold expr_eval_map. rewrite K6. simpls.
        - apply HC2 in K5. destruct K5 as (v'&K5).
          unfold phConcr.
          rewrite <- phUnion_cell. apply phcConcr_union; auto.
          rewrite <- phUnion_cell. apply phcConcr_union; auto.
          rewrite phUnion_comm.
          rewrite <- phUnion_cell. apply phcConcr_union; auto.
          + by symmetry.
          + subst F1. unfold expr_eval_map.
            rewrite K5. simpls. }

      (* determine the contents of [pm' (g x)] *)
      rewrite AGR1 in SAT1. apply pmeBisim_equality in AGR1.
      destruct AGR1 as (Q'&F1'&AGR1&PEQ1).
      rewrite PEQ1 in SAT1. clear PEQ1.

      (* make shorthands for leftover process components *)
      simpl ((pDehybridise (HPalt (HPseq (HPact a E) HP) HQ) s)) in SAT1.
      remember (pDehybridise HP s) as CP.
      remember (pDehybridise HQ s) as CQ.

      (* the process component in [pm + pm' + pmF (g x)] is able to do an [a] step  *)
      assert (PC1 : exists q1 Q1, pmeBisim (PEelem q' Q' xs F1') (PEelem q1 (Ppar (Palt (Pseq (Pact a v) CP) CQ) Q1) xs F1')). {
        red in D7. unfold pmeUnion in SAT1. repeat desf.
        - exists (q + q0), P0. rewrite SAT1. vauto. red in SAT1. desf.
        - exists q, Pepsilon. rewrite bisim_par_comm. 
          rewrite bisim_par_epsilon_l. red in SAT1. desf. }
      destruct PC1 as (q1&Q1&PC1).
      assert (PC2 : exists q2 Q2, pmeBisim (pmeUnion (pm (g x)) (PEelem q' Q' xs F1')) (PEelem q2 (Ppar Q' Q2) xs F1') ). {
        red in D1. red in D1. specialize D1 with (g x).
        rewrite AGR1 in D1. red in D1.
        unfold pmeUnion. repeat desf; vauto.
        - exists (q0 + q'), P0. by rewrite bisim_par_comm.
        - exists q', Pepsilon. rewrite bisim_par_comm.
          by rewrite bisim_par_epsilon_l. }
      destruct PC2 as (q2&Q2&PC2).
      rewrite <- AGR1 in PC2.
      assert (PC3 : exists q3 Q3, pmeBisim (pmeUnion (PEelem q2 (Ppar Q' Q2) xs F1') (pmF (g x))) (PEelem q3 (Ppar Q' Q3) xs F1')). {
        red in D4. red in D4. specialize D4 with (g x).
        rewrite PC2 in D4. red in D4.
        unfold pmeUnion. repeat desf; vauto.
        exists (q2 + q0), (Ppar Q2 P0).
        by rewrite bisim_par_assoc. }
      destruct PC3 as (q3&Q3&PC3).
      rewrite <- PC2 in PC3. clear PC2 q2 Q2.
      repeat rewrite pmUnion_pme in PC3.
      rewrite H7 in PC3.

      (* the process [P''] can do an [a] step and end up in some process [P'''] *)
      assert (PS1 : bisim Q' (Ppar (Palt (Pseq (Pact a v) CP) CQ) Q1)). {
        red in PC1. repeat desf. }
      assert (PS2 : pstep (Ppar (Palt (Pseq (Pact a v) CP) CQ) Q1) ps1 (PLact a v) (Ppar (Pseq Pepsilon CP) Q1) ps2). {
        apply pstep_par_l, pstep_alt_l, pstep_seq_l, pstep_act; auto. }
      assert (PS3 : exists Q'', pstep Q' ps1 (PLact a v) Q'' ps2). {
        inv PS1. clear PS1. destruct H as (_&_&_&H).
        apply H in PS2. destruct PS2 as (Q''&PS2&PS3).
        by exists Q''. }
      destruct PS3 as (Q''&PS3).
      assert (PS4 : pstep (Ppar Q' Q3) ps1 (PLact a v) (Ppar Q'' Q3) ps2). {
        by apply pstep_par_l. }
      assert (PS5 : bisim P (Ppar Q' Q3)). {
        red in PC3. repeat desf. }
      assert (PS6 : exists P'', pstep P ps1 (PLact a v) P'' ps2). {
        inv PS5. destruct H as (_&_&_&H).
        apply H in PS4. destruct PS4 as (P''&PS4&_).
        by exists P''. }
      destruct PS6 as (P''&PS6).

      (* the proof concludes by contradiction of H10 and PS6 *)
      apply H11. by exists P''.

  (* (3) all shared-memory accesses are in the footprint *)
  - intros l H1. simpl in H1.
    destruct SAFE1 as (_&_&ACC&_).
    by apply ACC.

  (* (4) all shared-memory writes are in the footprint *)
  - intros l H1. simpl in H1.
    destruct SAFE1 as (_&_&_&WRITES&_).
    by apply WRITES.

  (* (5) program step *)
  - simpl. intros phJ phF pmJ pmF pmC h' s' C' D2 D3 D4 D5 H1 FIN1 WS1 INV FIN2 COV1 PSAFE1 STEP.
    inv STEP.

    (* the program [C] is not empty *)
    + destruct SAFE1 as (_&_&_&_&SAFE1).

      (* the program transition did not affect the evaluation of [f1] for every process variable in [xs] *)
      assert (PRES1 : forall y : ProcVar, expr_eval (f1 y) s = expr_eval (f1 y) s'). {
        intros y. apply expr_agree. red. intros z IN1.
        apply step_fv_mod in H3. destruct H3 as (_&_&H3).
        apply H3. intro MOD1. unfold disjoint in DISJ1.
        apply DISJ1 with (y := y)(x := z); auto.
        by rewrite cmd_mod_plain. }
      assert (PRES2 : forall y : ProcVar, expr_eval_map f1 s y = expr_eval_map f1 s' y). {
        intros y. unfold expr_eval_map. by apply PRES1. }

      (* the program transition did not affect the evaluation of [E] *)
      assert (PRES3 : expr_eval E s = expr_eval E s'). {
        apply expr_agree. red. intros z IN1.
        apply step_fv_mod in H3. destruct H3 as (_&_&H3).
        apply H3. intro MOD1. unfold disjoint in DISJ2.
        apply DISJ2 with z; auto. by rewrite cmd_mod_plain. }

      apply SAFE1 with (pmJ := pmJ)(pmF := pmUnion pm' pmF)(pmC := pmC) in H3; vauto; clear SAFE1.
      destruct H3 as (ph'&phJ'&D7&D8&H2&FIN3&BASIC2&H3).
      destruct H3 as (pm''&pmJ'&pmC'&D9&D10&H3&FIN4&WS2&BASIC3&COV2&PSAFE2&H4).
      destruct H4 as (g'&C''&H4&GSTEP&INV1&SAFE). clarify.
      intuition desf. generalize GSTEP. intro GSTEP'.
      apply gstep_basic_ghostdata_pres in GSTEP'; auto. desf.

      exists ph', phJ'. repeat split; vauto.
      exists (pmUnion pm'' pm'), pmJ', pmC'. repeat split; vauto.

      1:{ (* the process maps [pm'' + pm'] and [pmJ'] are disjoint *)
        by rewrite <- H4, <- H5. }
      1:{ (* the process maps [pm'' + pm' + pmJ'] and [pmF] are disjoint *)
        by rewrite <- H4, <- H5. }
      { (* the process maps [pm'' + pm' + pmJ' + pmF] and [pmC] are equal *)
        by rewrite <- H4, <- H5. }

      exists g', (Cinact (GMdata (g' x) a v hs) C'').
      repeat split; vauto.
      subst B2 v. rewrite PRES3.
      apply IH with (HQ := HQ)(ys1 := ys1)(ys2 := ys2); vauto.

      1:{ (* the metadata of the active action is still agreed upon *)
        rewrite <- H2. rewrite <- PRES3.
        by apply metadata_agree_F with (expr_eval_map f1 s). }

      1:{ (* the free variables of [f1 y] are still disjoint with [cmd_mod C''] for every [y] in [xs] *)
      intros y. apply gstep_fv_mod in GSTEP.
      destruct GSTEP as (_&GSTEP&_).
      red. intros z IN1 IN2. unfold disjoint in DISJ1.
      apply DISJ1 with (y:=y)(x:=z); auto. }

      1:{ (* [E] is not modified by [C''] *)
        red. intros y IN1 IN2. red in DISJ2.
        apply DISJ2 with y; auto.
        apply gstep_fv_mod in GSTEP.
        destruct GSTEP as (_&GSTEP&_).
        by apply GSTEP. }

      1:{ (* any free variables in [HP] are not modified by [C''] *)
        red. intros y IN1 IN2. apply DISJ3 with y; auto.
        apply gstep_fv_mod in GSTEP.
        destruct GSTEP as (_&GSTEP&_).
        by apply GSTEP. }

      1:{ (* any free variables in [HQ] are not modified by [C''] *)
        red. intros y IN1 IN2. apply DISJ4 with y; auto.
        apply gstep_fv_mod in GSTEP.
        destruct GSTEP as (_&GSTEP&_).
        by apply GSTEP. }

      1:{ (* the program variable [x] is not modified by [C''] *)
        intros IN1. apply DISJ5.
        apply gstep_fv_mod in GSTEP.
        destruct GSTEP as (_&GSTEP&_).
        by apply GSTEP. }

      1:{ (* the program [C''] is still basic *)
        apply gstep_basic_pres in GSTEP; vauto. }

      1:{ (* the process maps [pm''] and [pm'] are disjoint *)
        by rewrite <- H4. }

      1:{ (* the process map [pm'] still satisfies the process ownership assertion *)
      apply sat_agree with (s1:=s); auto.
      intros y IN1. simpl in IN1.
      destruct IN1 as [IN1|[[[IN1|IN1]|IN1]|IN1]]; vauto.
      - apply gstep_fv_mod in GSTEP.
        destruct GSTEP as (_&_&GSTEP&_). by apply GSTEP.
      - apply gstep_fv_mod in GSTEP.
        destruct GSTEP as (_&_&GSTEP&_).
        apply GSTEP. clear GSTEP. intro MOD.
        red in DISJ2. by apply DISJ2 with y.
      - apply gstep_fv_mod in GSTEP.
        destruct GSTEP as (_&_&GSTEP&_).
        apply GSTEP. intro IN2.
        by apply DISJ3 with y.
      - apply gstep_fv_mod in GSTEP.
        destruct GSTEP as (_&_&GSTEP&_).
        apply GSTEP. intro IN2.
        by apply DISJ4 with y.
      - unfold expr_map_fv in IN1. destruct IN1 as (z&IN1).
        apply gstep_fv_mod in GSTEP.
        destruct GSTEP as (_&_&GSTEP&_).
        apply GSTEP; vauto. intro IN2.
        apply DISJ1 with (y:=z)(x:=y); vauto. }

      1:{ (* the process maps [pm] and [pmJ] are disjoint *)
        apply pmDisj_union_l with pm'; auto.
        - by symmetry.
        - by rewrite pmUnion_comm. }

      1:{ (* the process maps [pm + pmJ] and [pm' + pmF] are disjoint *)
        assert (K1 : pmDisj pmJ pmF). {
          apply pmDisj_union_l with (pmUnion pm pm'); auto. }
        apply pmDisj_compat; auto.
        apply pmDisj_assoc_l; auto. }

      1:{ (* the process maps [pm + pmJ + pm' + pmF] equals [pmC] up to bisimulation *)
        rewrite <- pmUnion_assoc.
        by rewrite pmUnion_swap_r with (pm3 := pm'). }

    (* the program [C] is empty *)
    + assert (C = Cskip) by by apply plain_skip.
      clarify. clear IH. destruct SAFE1 as (SAFE1'&_).
      assert (SAFE1 : Cskip = @Cskip GhostMetadata) by trivial.
      apply SAFE1' in SAFE1. clear SAFE1'.
      destruct SAFE1 as (ph3'&ph3&D6&H2&pm3'&pm3&D7&H4&SAT2&SAT3).
      destruct SAT2 as (ph2'&ph2&D8&H5&pm2'&pm2&D9&H6&SAT2&SAT4).
      clarify.

      (* [ph2'] and [pm2'] are both valid *)
      assert (V1 : phValid ph2') by by apply phDisj_valid_l in D8.
      assert (V2 : pmValid pm2') by by apply pmDisj_valid_l in D9.

      (* splitting the iterated separating conjunction in SAT2 *)
      apply sat_procact_iter_permut with (ys := ys1 ++ ys2) in SAT2; auto.
      apply ApointstoIter_procact_split in SAT2; auto.
      destruct SAT2 as (ph1a&ph1b&D10&H7&pm1a&pm1b&D11&H8&SAT1a&SAT1b). clarify.
      set (ls := map (expr_eval_map f1 s') xs : list Val).
      set (ls1 := map (expr_eval_map f1 s') ys1 : list Val).
      set (ls2 := map (expr_eval_map f1 s') ys2 : list Val).
      set (ph1b' := phConvProcMult ph1b ls2).

      (* [ph1a], [ph1b], [pm1a] and [pm1b] are all valid *)
      assert (V3 : phValid ph1a) by by apply phDisj_valid_l in D10.
      assert (V4 : phValid ph1b) by by apply phDisj_valid_r in D10.
      assert (V5 : pmValid pm1a) by by apply pmDisj_valid_l in D11.
      assert (V6 : pmValid pm1b) by by apply pmDisj_valid_r in D11.

      (* [ph1a l] contains a process cell for every [l] in [ls1], and [ph1b l] contains a full action cell for every [l] in [ls2] *)
      assert (HV1 : forall y : ProcVar, In y ys2 -> exists v : Val, ph1b (F1 y) = PHCact perm_full (F2 y) v). {
        intros y HV1. apply ApointstoIter_sat_single_act with (x0 := y) in SAT1b; auto.
        destruct SAT1b as (v'&SAT1b). rewrite PERM3 in SAT1b; auto.
        apply phcLe_entire_eq in SAT1b; vauto. subst F1.
        unfold expr_eval_map. rewrite <- SAT1b. by exists v'. }
      assert (HV1' : forall l : Val, In l ls2 -> exists v1 v2 : Val, ph1b l = PHCact perm_full v1 v2). {
        intros l HV1'. subst ls2. apply in_map_iff in HV1'.
        destruct HV1' as (y&?&HV1').
        apply HV1 in HV1'. destruct HV1' as (v'&HV1').
        clarify. by exists (expr_eval (f2 y) s'), v'. }
      assert (HV2 : forall y : ProcVar, In y ys1 -> exists q : Qc, perm_valid q /\ ph1a (F1 y) = PHCproc q (F2 y)). {
        intros y HV2. apply ApointstoIter_sat_single_proc with (x0 := y) in SAT1a; auto.
        apply phcLe_diff in SAT1a; vauto.
        - destruct SAT1a as (phc&D12&SAT1a). subst F1.
          unfold expr_eval_map. rewrite <- SAT1a.
          red in D12. destruct phc as [|q''|q''|q''|]; vauto.
          unfold phcUnion. desf. exists (fq y + q''); split; vauto.
          by apply perm_add_valid.
        - simpl. apply VF. rewrite PERM4. by left. }
      assert (HV2' : forall l : Val, In l ls1 -> exists q v, perm_valid q /\ ph1a l = PHCproc q v). {
        intros l HV2'. subst ls1. apply in_map_iff in HV2'.
        destruct HV2' as (y&?&HV2').
        apply HV2 in HV2'. destruct HV2' as (q'&?&HV2').
        clarify. exists q', (expr_eval (f2 y) s'). split; vauto. }
      assert (HV3 : forall y : ProcVar, In y ys1 -> ph1b (F1 y) = PHCfree \/ exists q v, perm_valid q /\ ph1b (F1 y) = PHCproc q v). {
        intros y HV3. apply HV2 in HV3. destruct HV3 as (?&?&HV3).
        red in D10. red in D10. specialize D10 with (F1 y).
        rewrite HV3 in D10. red in D10. repeat desf; vauto.
        right. exists q0, (expr_eval (f2 y) s'). intuition vauto.
        by apply perm_disj_valid_r in D10. }

      (* [ph1b l] is full, and [ph1a l], [ph2 l], [ph3 l], [phJ l] and [phF l] are all empty for every [l] in [ls2] *)
      assert (HC1 : forall l : Val, In l ls2 -> phcEntire (ph1b l)). {
        intros l HC1. apply HV1' in HC1. destruct HC1 as (?&?&HC1). rewrite HC1. simpls. }
      assert (HC2 : forall l : Val, In l ls2 -> ph1a l = PHCfree). {
        intros l HC2. red in D10. red in D10.
        specialize D10 with l. symmetry in D10.
        apply phcDisj_entire_free in D10; auto. }
      assert (HV4 : forall y : ProcVar, In y ys2 -> ph1a (F1 y) = PHCfree). {
        intros y HC2'. apply HC2. subst ls2. by apply in_map. }
      assert (HC3 : forall l : Val, In l ls2 -> ph2 l = PHCfree). {
        intros l HC3. red in D8. red in D8.
        specialize D8 with l. rewrite <- phUnion_cell in D8.
        rewrite HC2 in D8; auto. rewrite phcUnion_free_r in D8.
        apply phcDisj_entire_free in D8; auto. }
      assert (HC4 : forall l : Val, In l ls2 -> ph3 l = PHCfree). {
        intros l HC4. red in D6. red in D6.
        specialize D6 with l.
        apply phcDisj_entire_free in D6; auto.
        repeat rewrite <- phUnion_cell. rewrite HC2, HC3; auto.
        rewrite phcUnion_free_l, phcUnion_free_r. by apply HC1. }
      assert (HC5 : forall l : Val, In l ls2 -> phJ l = PHCfree). {
        intros l HC5. red in D2. red in D2. specialize D2 with l.
        apply phcDisj_entire_free in D2; auto.
        repeat rewrite <- phUnion_cell. rewrite HC2, HC3, HC4; auto.
        rewrite phcUnion_free_l, phcUnion_free_r, phcUnion_free_l. by apply HC1. }
      assert (HC6 : forall l : Val, In l ls2 -> phF l = PHCfree). {
        intros l HC6. red in D3. red in D3.
        specialize D3 with l.
        apply phcDisj_entire_free in D3; auto.
        repeat rewrite <- phUnion_cell.
        rewrite HC2, HC3, HC4, HC5; auto.
        repeat rewrite phcUnion_free_l.
        rewrite phcUnion_free_r. by apply HC1. }

      (* the heap [ph1b'] is disjoint in every compositions in which [ph1b] is also disjoint *)
      assert (DISJ6 : phDisj ph1a ph1b'). {
        rewrite <- phConvProcMult_free with ls2 ph1a; auto.
        by apply phConvProcMult_disj. }
      assert (DISJ7 : phDisj (phUnion ph1a ph1b') ph2). {
        rewrite <- phConvProcMult_free with ls2 ph1a; auto.
        rewrite <- phConvProcMult_free with ls2 ph2; auto.
        subst ph1b'. rewrite <- phConvProcMult_union; vauto.
        by apply phConvProcMult_disj. }
      assert (DISJ8 : phDisj (phUnion (phUnion ph1a ph1b') ph2) ph3). {
        rewrite <- phConvProcMult_free with ls2 ph1a; auto.
        rewrite <- phConvProcMult_free with ls2 ph2; auto.
        rewrite <- phConvProcMult_free with ls2 ph3; auto.
        subst ph1b'. repeat rewrite <- phConvProcMult_union; vauto.
        by apply phConvProcMult_disj. }
      assert (DISJ9 : phDisj (phUnion (phUnion (phUnion ph1a ph1b') ph2) ph3) phJ). {
        rewrite <- phConvProcMult_free with ls2 ph1a; auto.
        rewrite <- phConvProcMult_free with ls2 ph2; auto.
        rewrite <- phConvProcMult_free with ls2 ph3; auto.
        rewrite <- phConvProcMult_free with ls2 phJ; auto.
        subst ph1b'. repeat rewrite <- phConvProcMult_union; vauto.
        by apply phConvProcMult_disj. }
      assert (DIS10 : phDisj (phUnion (phUnion (phUnion (phUnion ph1a ph1b') ph2) ph3) phJ) phF). {
        rewrite <- phConvProcMult_free with ls2 ph1a; auto.
        rewrite <- phConvProcMult_free with ls2 ph2; auto.
        rewrite <- phConvProcMult_free with ls2 ph3; auto.
        rewrite <- phConvProcMult_free with ls2 phJ; auto.
        rewrite <- phConvProcMult_free with ls2 phF; auto.
        subst ph1b'. repeat rewrite <- phConvProcMult_union; vauto.
        by apply phConvProcMult_disj. }

      (* the heap location [l] is in [ls] iff [l] is in [ls1] or [ls2] *)
      assert (LDISJ1 : forall l : Val, In l ls <-> In l ls1 \/ In l ls2). {
        intro l. split; intro LDISJ.
        - subst ls. apply in_map_iff in LDISJ.
          destruct LDISJ as (y&LDISJ1&LDISJ2). clarify.
          apply PERM4 in LDISJ2. destruct LDISJ2 as [LDISJ2|LDISJ2].
          + left. subst ls1. by apply in_map.
          + right. subst ls2. by apply in_map.
        - destruct LDISJ as [LDISJ | LDISJ].
          + subst ls1. apply in_map_iff in LDISJ.
            destruct LDISJ as (y&LDISJ1&LDISJ2). clarify.
            subst ls. apply in_map, PERM4. by left.
          + subst ls2. apply in_map_iff in LDISJ.
            destruct LDISJ as (y&LDISJ1&LDISJ2). clarify.
            subst ls. apply in_map, PERM4. by right. }

      (* the lists [ls1] and [ls2] are disjoint, as well as [xs1] and [xs2] *)
      assert (LDISJ2 : forall l : Val, In l ls1 -> In l ls2 -> False). {
        intros l IN1 IN2.
        apply HV1' in IN2. destruct IN2 as (?&?&IN2).
        apply HV2' in IN1. destruct IN1 as (q'&?&V7&IN1).
        red in D10. red in D10. specialize D10 with l.
        rewrite IN1, IN2 in D10. red in D10. repeat desf. }
      assert (LDISJ3 : forall y : ProcVar, In y ys1 -> In y ys2 -> False). {
        intros y IN1 IN2. apply LDISJ2 with (expr_eval_map f1 s' y).
        - subst ls1. by apply in_map.
        - subst ls2. by apply in_map. }
      assert (LDISJ4 : forall l : Val, In l ls1 -> In l ls). {
        intros l LDISJ4. rewrite LDISJ1. by left. }
      assert (LDISJ5 : forall l : Val, In l ls2 -> In l ls). {
        intros l LDISJ5. rewrite LDISJ1. by right. }

      exists (phUnion (phUnion (phUnion ph1a ph1b') ph2) ph3), phJ.
      repeat split; vauto.

      1:{ (* all concrete heap values are preserved by the computation step *)
        rewrite <- phConvProcMult_free with (xs := ls2)(ph := ph1a) at 1; auto.
        rewrite <- phConvProcMult_free with (xs := ls2)(ph := ph2) at 1; auto.
        rewrite <- phConvProcMult_free with (xs := ls2)(ph := ph3) at 1; auto.
        rewrite <- phConvProcMult_free with (xs := ls2)(ph := phJ) at 1; auto.
        rewrite <- phConvProcMult_free with (xs := ls2)(ph := phF) at 1; auto.
        subst ph1b'. repeat rewrite <- phConvProcMult_union; vauto.
        by apply phConvProcMult_concr. }

      (* determine the exact contents of [pm' (g x)] *)
      destruct SAT1 as (pme&D12&SAT1).
      destruct AGR1 as (q'&P'&AGR1&AGR2&AGR3&ps1&AGR4&AGR5).
      rewrite AGR1 in SAT1. apply pmeBisim_equality in AGR1.
      destruct AGR1 as (P''&F1'&AGR1&PEQ1).
      rewrite PEQ1 in SAT1. clear PEQ1.
      clear P'. rename P'' into P'.

      (* getting rid of [pme] *)
      assert (PMV1 : exists R : Proc,
          (pme = PEfree /\ R = Pepsilon /\ q = q') \/
          (exists q'', pmeBisim pme (PEelem q'' R xs F1) /\ perm_disj q q'' /\ q' = q + q'')). {
        red in D12. repeat desf; vauto.
        - exists P. right. exists q0. red in SAT1.
          unfold pmeUnion in SAT1. repeat desf.
        - exists Pepsilon. left. repeat split; vauto.
          rewrite pmeUnion_free_l in SAT1.
          red in SAT1. repeat desf. }
      destruct PMV1 as (R&PMV1).

      (* [F1] and [F1'] agree on every process variable in [xs] *)
      assert (PACC1 : map F1' xs = ls). {
        destruct PMV1 as [(PMV1&PMV2&PMV3)|(q''&PMV1&PMV2&PMV3)]; vauto.
        - rewrite pmeUnion_free_l in SAT1.
          unfold pmeBisim in SAT1. subst ls. repeat desf.
        - rewrite PMV1 in SAT1. unfold pmeUnion in SAT1. repeat desf.
          unfold pmeBisim in SAT1. subst ls. repeat desf. }
      assert (PACC2 : pmeProj (pm' (g x)) = ls). { by rewrite AGR1. }
      assert (PACC3 : forall l : Val, In l ls -> In l (pmeProj (pmC (g x)))). {
        intros l PACC3. red in H1. red in H1.
        specialize H1 with (g x).
        rewrite <- H1. rewrite <- PACC2 in PACC3.
        apply pmeProj_union, pmeProj_union; auto.
        rewrite <- pmUnion_elem, pmeUnion_comm.
        apply pmeProj_union; auto. by symmetry. }
      assert (PACC4 : forall y : ProcVar, In y xs -> F1 y = F1' y). {
        subst F1. destruct PMV1 as [(PMV1&PMV2&PMV3) | (q''&PMV1&PMV2&PMV3)]; vauto.
        - rewrite pmeUnion_free_l in SAT1.
          red in SAT1. repeat desf.
          intros y PACC4. apply map_eq_In with xs; auto.
        - rewrite PMV1 in SAT1. unfold pmeUnion in SAT1. repeat desf.
          red in SAT1. repeat desf.
          intros y PACC4. apply map_eq_In with xs; auto. }

      (* all free variables in the guard and effect of [a] are also in [xs]. *)
      assert (FV1 : forall y : ProcVar, In y (pcond_fv (guard a v)) -> In y xs). {
        intros y FV1. apply AGR2. unfold act_fv. apply in_or_app. by left. }
      assert (FV2 : forall y : ProcVar, In y (pcond_fv (effect a v)) -> In y xs). {
        intros y FV2. apply AGR2. unfold act_fv. apply in_or_app. by right. }

      (* fix a process store [ps2] that satisfies the effect of [a] *)
      set (ps2 := expr_eval_map f2 s' : ProcStore).
      generalize SAT4. intro SAT4'. unfold sat in SAT4. subst B2.
      rewrite heffect_corr in SAT4.
      rewrite cond_eval_conv with (ps := ps2) in SAT4; auto.

      (* make shorthands for leftover process components *)
      rename s' into s.
      simpl ((pDehybridise (HPalt (HPseq (HPact a E) HP) HQ) s)) in SAT1.
      remember (pDehybridise HP s) as CP.
      remember (pDehybridise HQ s) as CQ.

      (* [P'] can perform an [a] action and end up as some process [P''] *)
      assert (PSTEP1 : pstep (Pact a v) ps1 (PLact a v) Pepsilon ps2). { by apply pstep_act. }
      assert (PSIM1 : bisim P' (Ppar (Palt (Pseq (Pact a v) CP) CQ) R)). {
        destruct PMV1 as [(PMV1&PMV2&PMV3) | (q''&PMV1&PMV2&PMV3)]; vauto.
        - rewrite pmeUnion_free_l in SAT1.
          unfold pmeBisim in SAT1. repeat desf.
          rename SAT0 into SAT2.
          rewrite SAT2. rewrite bisim_par_comm.
          rewrite bisim_par_epsilon_l. done.
        - rewrite PMV1 in SAT1. unfold pmeUnion in SAT1.
          repeat desf. unfold pmeBisim in SAT1.
          by repeat desf. }
      assert (PSTEP2 : pstep (Ppar (Palt (Pseq (Pact a v) CP) CQ) R) ps1 (PLact a v) (Ppar (Pseq Pepsilon CP) R) ps2). {
        by apply pstep_par_l, pstep_alt_l, pstep_seq_l. }
      assert (PSTEP3 : exists P'' : Proc, pstep P' ps1 (PLact a v) P'' ps2 /\ bisim P'' (Ppar CP R)). {
        inv PSIM1. destruct H as (_&_&_&H). apply H in PSTEP2.
        destruct PSTEP2 as (P''&PSTEP2&PBISIM2).
        exists P''. split; vauto.
        rewrite PBISIM2. by rewrite bisim_seq_epsilon_r. }
      destruct PSTEP3 as (P''&PSTEP3&PSIM2).

      (* relating the concretisations and snapshots of the old and new heaps *)
      assert (CS1 : forall y : ProcVar, In y ys2 -> phcConcr (ph1b (F1 y)) = phcSnapshot (ph1b' (F1 y))). {
        intros y CS1. subst ph1b'.
        rewrite phConvProcMult_apply; auto.
        - apply HV1 in CS1; auto. destruct CS1 as (v'&CS1).
          rewrite CS1. by simpls.
        - subst ls2. by apply in_map. }
      assert (CS2 : forall y : ProcVar, In y ys1 -> phcConcr (ph1a (F1 y)) = phcSnapshot (ph1a (F1 y))). {
        intros y CS2. apply HV2 in CS2. destruct CS2 as (?&?&CS2). rewrite CS2. vauto. }
      assert (CS3 : forall y : ProcVar, In y ys2 -> phcConcr (ph1a (F1 y)) = phcSnapshot (ph1a (F1 y))). {
        intros y CS3. rewrite HV4; vauto. }
      assert (CS4 : forall y : ProcVar, In y ys1 -> phcConcr (ph1b (F1 y)) = phcSnapshot (ph1b' (F1 y))). {
        intros y CS4. subst ph1b'.
        assert (IN1 : ~ In y ys2). { intro IN1. by apply LDISJ3 with y. }
        assert (IN2 : ~ In (expr_eval_map f1 s y) ls2). {
          intro IN2. apply LDISJ2 with (expr_eval_map f1 s y); vauto.
          subst ls1. by apply in_map. }
        rewrite <- phConvProcMult_pres; vauto.
        apply HV3 in CS4. destruct CS4 as [CS4 | CS4].
        - subst F1. rewrite CS4. vauto.
        - destruct CS4 as (?&?&?&CS4). subst F1. rewrite CS4. vauto. }
      assert (CS5 : forall y : ProcVar, In y xs -> phcConcr (ph1b (F1 y)) = phcSnapshot (ph1b' (F1 y))). {
        intros y CS5. apply PERM4 in CS5. destruct CS5 as [CS5 | CS5].
        - by apply CS4.
        - by apply CS1. }
      assert (CS6 : forall y : ProcVar, In y xs -> phcConcr (ph1a (F1 y)) = phcSnapshot (ph1a (F1 y))). {
        intros y CS6. apply PERM4 in CS6. destruct CS6 as [CS6 | CS6].
        - by apply CS2.
        - by apply CS3. }
      assert (CS7 : forall y : ProcVar, In y xs ->
          phcConcr (phUnion ph1a ph1b (F1 y)) = phcSnapshot (phUnion ph1a ph1b' (F1 y))). {
        intros y CS7. apply phcConcr_snapshot_compat; auto. }
      assert (CS8 : forall y : ProcVar, In y xs ->
          phcConcr (phUnion ph1a ph1b (F1 y)) = phcSnapshot (phConvProcMult (phUnion ph1a ph1b) ls2 (F1 y))). {
        intros y CS8. apply CS7 in CS8; auto.
        rewrite phConvProcMult_union; auto.
        rewrite phConvProcMult_free with (ph := ph1a); auto. }

      (* the concrete- and snapshot heap contain an element at every location corresponding to variables in [xs] *)
      assert (CSV1 : forall y : ProcVar, In y ys1 -> phcConcr (ph1a (F1 y)) = Some (F2 y)). {
        intros y CSV1. apply HV2 in CSV1. destruct CSV1 as (?&?&CSV1). rewrite CSV1. vauto. }
      assert (CSV2 : forall y : ProcVar, In y ys1 -> phcSnapshot (ph1a (F1 y)) = Some (F2 y)). {
        intros y CSV2. apply HV2 in CSV2. destruct CSV2 as (?&?&CSV2). rewrite CSV2. vauto. }
      assert (CSV3 : forall y : ProcVar, In y ys2 -> phcConcr (ph1b (F1 y)) = Some (F2 y)). {
        intros y CSV3. apply HV1 in CSV3. destruct CSV3 as (?&CSV3). rewrite CSV3. vauto. }
      assert (CSV4 : forall y : ProcVar, In y ys2 -> phcSnapshot (ph1b' (F1 y)) = Some (F2 y)). {
        intros y CSV4. subst ph1b'.
        assert (IN1 : In (expr_eval_map f1 s y) ls2). { subst ls2. by apply in_map. }
        rewrite phConvProcMult_apply; auto.
        apply HV1 in CSV4. destruct CSV4 as (?&CSV4). rewrite CSV4. vauto. }
      assert (CSV4' : forall y : ProcVar, In y ys2 -> exists v : Val, phcSnapshot (ph1b (F1 y)) = Some v). {
        intros y CSV4'. apply HV1 in CSV4'. destruct CSV4' as (v'&CSV4').
        exists v'. rewrite CSV4'. vauto. }
      assert (CSV5 : forall y : ProcVar, In y xs -> phcConcr (phUnion ph1a ph1b (F1 y)) = Some (F2 y)). {
        intros y CSV5. rewrite PERM4 in CSV5. destruct CSV5 as [CSV5 | CSV5].
        - apply CSV1 in CSV5. by apply phcConcr_union.
        - apply CSV3 in CSV5. rewrite phUnion_comm.
          apply phcConcr_union; auto.
          by symmetry. }
      assert (CSV6 : forall y : ProcVar, In y xs -> phcSnapshot (phUnion ph1a ph1b' (F1 y)) = Some (F2 y)). {
        intros y CSV6. rewrite PERM4 in CSV6. destruct CSV6 as [CSV6 | CSV6].
        - apply CSV2 in CSV6. apply phcSnapshot_union; auto.
        - apply CSV4 in CSV6. rewrite phUnion_comm.
          apply phcSnapshot_union; auto.
          by symmetry. }
      assert (CSV6' : forall y : ProcVar, In y xs -> exists v : Val, phcSnapshot (phUnion ph1a ph1b (F1 y)) = Some v). {
        intros y CSV6'. rewrite PERM4 in CSV6'.
        destruct CSV6' as [CSV6'|CSV6'].
        - apply CSV2 in CSV6'. exists (F2 y).
          apply phcSnapshot_union; auto.
        - apply CSV4' in CSV6'. destruct CSV6' as (v'&CSV6').
          rewrite phUnion_comm. exists v'.
          apply phcSnapshot_union; auto.
          by symmetry. }
      assert (CSV7 : forall y : ProcVar, In y xs -> phcSnapshot (phConvProcMult (phUnion ph1a ph1b) ls2 (F1 y)) = Some (F2 y)). {
        intros y CSV7. apply CSV6 in CSV7; auto.
        rewrite phConvProcMult_union; auto.
        rewrite phConvProcMult_free with (ph := ph1a); auto. }

      (* results on the snapshot values of [ph1a + ph1b + ph2 + ph2 + phJ + phF] *)
      assert (CSV8 : forall y : ProcVar, In y xs ->
          phcConcr (phUnion (phUnion (phUnion (phUnion (phUnion ph1a ph1b) ph2) ph3) phJ) phF (F1 y)) =
          phcConcr (phUnion ph1a ph1b (F1 y))). {
        intros y CSV8. rewrite CSV5; auto.
        apply phcConcr_union, phcConcr_union, phcConcr_union, phcConcr_union; auto. }
      assert (CSV9 : forall y : ProcVar, In y xs ->
          phcSnapshot (phConvProcMult (phUnion (phUnion (phUnion (phUnion (phUnion ph1a ph1b) ph2) ph3) phJ) phF) ls2 (F1 y)) =
          phcSnapshot (phUnion (phUnion (phUnion (phUnion (phUnion ph1a ph1b') ph2) ph3) phJ) phF (F1 y))). {
        intros y CSV9. subst ph1b'.
        repeat rewrite phConvProcMult_union; auto.
        rewrite phConvProcMult_free with (ph := phF); auto.
        rewrite phConvProcMult_free with (ph := phJ); auto.
        rewrite phConvProcMult_free with (ph := ph3); auto.
        rewrite phConvProcMult_free with (ph := ph2); auto.
        rewrite phConvProcMult_free with (ph := ph1a); auto. }
      assert (CSV10 : forall y : ProcVar, In y xs ->
          phcSnapshot (phConvProcMult (phUnion (phUnion (phUnion (phUnion (phUnion ph1a ph1b) ph2) ph3) phJ) phF) ls2 (F1 y)) =
          phcSnapshot (phConvProcMult (phUnion ph1a ph1b) ls2 (F1 y))). {
        intros y CSV10. rewrite CSV9, CSV7; auto.
        apply phcSnapshot_union, phcSnapshot_union, phcSnapshot_union, phcSnapshot_union; auto. }
      assert (CSV11 : forall y : ProcVar, In y xs ->
          phcSnapshot (phUnion (phUnion (phUnion ph1a ph1b) ph2) ph3 (F1 y)) =
          phcSnapshot (phUnion ph1a ph1b (F1 y))). {
        intros y CSV11. apply CSV6' in CSV11; auto.
        destruct CSV11 as (v'&CSV11). rewrite CSV11.
        apply phcSnapshot_union, phcSnapshot_union; auto. }
      assert (CSV12 : forall y : ProcVar, In y xs ->
          phcSnapshot (phUnion (phUnion (phUnion (phUnion (phUnion ph1a ph1b) ph2) ph3) phJ) phF (F1 y)) =
          phcSnapshot (phUnion ph1a ph1b (F1 y))). {
        intros y CSV12. apply CSV6' in CSV12; auto.
        destruct CSV12 as (v'&CSV12). rewrite CSV12.
        apply phcSnapshot_union, phcSnapshot_union, phcSnapshot_union, phcSnapshot_union; auto. }

      (* results on the concrete values of projections of [F1] *)
      assert (PS1 : forall y : ProcVar, In y xs -> phcSnapshot (phUnion ph1a ph1b' (F1 y)) = Some (ps2 y)). {
        intros y PS1. rewrite CSV6; auto. }
      assert (PS2 : forall y : ProcVar, In y xs -> phcSnapshot (phConvProcMult (phUnion ph1a ph1b) ls2 (F1 y)) = Some (ps2 y)). {
        intros y PS2. apply PS1 in PS2; auto.
        rewrite phConvProcMult_union; auto.
        rewrite phConvProcMult_free with (ph := ph1a); auto. }
      assert (PS3 : forall y : ProcVar, In y xs -> phcConcr (phUnion ph1a ph1b (F1 y)) = Some (ps2 y)). {
        intros y PS3. rewrite CSV5; auto. }

      pose (pme' := PEelem q' P'' xs F1').
      pose (pm'' := pmUpdate pm' (g x) pme').
      pose (pme'' := pmeUnion (pmeUnion (pmeUnion (pm (g x)) (pm'' (g x))) (pmJ (g x))) (pmF (g x))).

      (* results on the contents of [pme'] and [pme''] *)
      assert (PC1 : exists q' Q',
          pmeBisim (pmeUnion (pm (g x)) (pm' (g x))) (PEelem q' (Ppar P' Q') xs F1') /\
          pmeBisim (pmeUnion (pm (g x)) pme') (PEelem q' (Ppar P'' Q') xs F1')). {
        subst pme'. red in D1. red in D1.
        specialize D1 with (g x).
        unfold pmeUnion. red in D1. clear PMV1. repeat desf.
        - exists (q0 + q'), P. split; by rewrite bisim_par_comm.
        - exists q', Pepsilon. split.
          + rewrite bisim_par_comm. by rewrite bisim_par_epsilon_l.
          + rewrite bisim_par_comm. by rewrite bisim_par_epsilon_l. }
      destruct PC1 as (q1&Q1&PC1&PC1').
      assert (PC2 : exists q' Q',
          pmeBisim (pmeUnion (PEelem q1 (Ppar P' Q1) xs F1') (pmJ (g x))) (PEelem q' (Ppar P' Q') xs F1') /\
          pmeBisim (pmeUnion (PEelem q1 (Ppar P'' Q1) xs F1') (pmJ (g x))) (PEelem q' (Ppar P'' Q') xs F1')). {
        subst pme'. red in D4. red in D4.
        specialize D4 with (g x).
        rewrite PC1 in D4. unfold pmeUnion. red in D4.
        clear PMV1. repeat desf.
        - exists (q1 + q0), (Ppar Q1 P). split.
          + by rewrite bisim_par_assoc.
          + by rewrite bisim_par_assoc.
        - exists q1, Q1. split; vauto. }
      destruct PC2 as (q2&Q2&PC2&PC2').
      rewrite <- PC1 in PC2. rewrite <- PC1' in PC2'.
      assert (PC3 : exists q' Q',
          pmeBisim (pmeUnion (PEelem q2 (Ppar P' Q2) xs F1') (pmF (g x))) (PEelem q' (Ppar P' Q') xs F1') /\
          pmeBisim (pmeUnion (PEelem q2 (Ppar P'' Q2) xs F1') (pmF (g x))) (PEelem q' (Ppar P'' Q') xs F1')). {
        subst pme'. red in D5. red in D5.
        specialize D5 with (g x).
        rewrite PC2 in D5. unfold pmeUnion. red in D5. clear PMV1. repeat desf.
        - exists (q2 + q0), (Ppar Q2 P). split.
          + by rewrite bisim_par_assoc.
          + by rewrite bisim_par_assoc.
        - exists q2, Q2. split; vauto. }
      destruct PC3 as (q3&Q3&PC3&PC3').
      rewrite <- PC2 in PC3. rewrite <- PC2' in PC3'.
      assert (PC4 : pmeBisim (pmC (g x)) (PEelem q3 (Ppar P' Q3) xs F1')). {
        red in H1. red in H1. specialize H1 with (g x).
        by rewrite H1 in PC3. }
      assert (PC5 : pmeBisim pme'' (PEelem q3 (Ppar P'' Q3) xs F1')). {
        subst pme'' pm''. unfold pmUpdate.
        repeat rewrite update_apply. by rewrite PC3'. }
      clear PC1 PC1' Q1 q1 PC2 PC2' Q2 q2 PC3 PC3'.

      pose (pmC' := pmUpdate pmC (g x) (PEelem q3 (Ppar P'' Q3) xs F1')).

      (* properties of process map agreement, of [pm'] and [pmC'] *)
      assert (PAGR1 : pmAgree pm' pm''). {
        subst pm''. intro pid. clear PMV1.
        unfold pmUpdate, update. desf.
        rewrite AGR1. vauto. }
      assert (PAGR2 : pmAgree (pmUnion pm pm') (pmUnion pm pm'')). {
        by apply pmAgree_union_r. }
      assert (PAGR3 : pmAgree (pmUnion (pmUnion pm pm') pmJ) (pmUnion (pmUnion pm pm'') pmJ)). {
        by apply pmAgree_union_l. }
      assert (PAGR4 : pmAgree pmC pmC'). {
        subst pmC' pme''. rewrite <- H1. rewrite <- PC5.
        repeat rewrite pmUnion_update.
        unfold pmUpdate.
        repeat rewrite <- update_idle.
        replace (pm'' (g x)) with pme'; vauto.
        - replace (pmUpdate pm' (g x) pme') with pm''; vauto.
          by apply pmAgree_union_l.
        - subst pm''. unfold pmUpdate.
          by rewrite update_apply. }

      (* disjointness properties involving [pm''] *)
      assert (PDJ1 : pmDisj pm pm''). {
        by rewrite <- PAGR1. }
      assert (PDJ2 : pmDisj (pmUnion (pmUnion (pmUnion pm1a pm1b) pm2) pm3) pm''). {
        rewrite <- PAGR1. by rewrite H8, H6, H4. }
      assert (PDJ3 : pmDisj (pmUnion (pmUnion pm1a pm1b) pm2) pm''). {
        apply pmDisj_union_l with pm3; auto.
        - symmetry. by rewrite H8, H6.
        - by rewrite pmUnion_comm. }
      assert (PDJ4 : pmDisj (pmUnion pm1a pm1b) pm''). {
        apply pmDisj_union_l with pm2; auto.
        - symmetry. by rewrite H8.
        - by rewrite pmUnion_comm. }

      exists (pmUnion pm pm''), pmJ, pmC'. repeat split; vauto.

      1:{ (* [pm + pm''] is disjoint with [pmJ] *)
        by rewrite <- PAGR2. }
      1:{ (* [pm + pm'' + pmJ] is disjoint with [pmF] *)
        by rewrite <- PAGR3. }

      1:{ (* the composition of [pmC'] is proper *)
        subst pm''. unfold pmUpdate.
        rewrite update_idle with Val ProcMapEntry val_eq_dec pm (g x).
        rewrite update_idle with Val ProcMapEntry val_eq_dec pmJ (g x).
        rewrite update_idle with Val ProcMapEntry val_eq_dec pmF (g x).
        repeat rewrite <- pmUnion_update.
        subst pmC' pme''.  rewrite <- PC5.
        rewrite <- H1. unfold pmUpdate.
        by rewrite update_apply. }

      1:{ (* [pmC'] is finite *)
        by rewrite <- PAGR4. }
      1:{ (* [pmC'] is well-structured *)
        by rewrite <- PAGR4. }

      1:{ (* [pmC'] is covered by the new snapshot heap *)
        apply pmCovers_agree with pmC; auto.
        apply pmCovers_occ with (phSnapshot (phUnion (phUnion (phUnion (phUnion (phUnion ph1a ph1b) ph2) ph3) phJ) phF)); auto.
        unfold phSnapshot. intros l IN1. subst ph1b'.
        rewrite <- phConvProcMult_free with ls2 ph1a; auto.
        rewrite <- phConvProcMult_free with ls2 ph2; auto.
        rewrite <- phConvProcMult_free with ls2 ph3; auto.
        rewrite <- phConvProcMult_free with ls2 phJ; auto.
        rewrite <- phConvProcMult_free with ls2 phF; auto.
        repeat rewrite <- phConvProcMult_union; auto.
        assert (IN2 : In l ls2 \/ ~ In l ls2). { by apply classic. }
        intro IN3. apply IN1. destruct IN2 as [IN2 | IN2].
        - subst ls2. apply in_map_iff in IN2.
          destruct IN2 as (y&IN2&IN2'). clarify.
          assert (IN4 : In y xs). { rewrite PERM4. by right. }
          rewrite CSV10 in IN3; auto. rewrite CSV7 in IN3; vauto.
        - rewrite <- phConvProcMult_pres in IN3; auto. }

      1:{ (* [pmC'] is safe with the new snapshot heap *)
        rewrite <- phConvProcMult_free with ls2 ph1a; auto.
        rewrite <- phConvProcMult_free with ls2 ph2; auto.
        rewrite <- phConvProcMult_free with ls2 ph3; auto.
        rewrite <- phConvProcMult_free with ls2 phJ; auto.
        rewrite <- phConvProcMult_free with ls2 phF; auto.
        subst ph1b'. repeat rewrite <- phConvProcMult_union; vauto.
        subst pmC'. intro pid. unfold pmUpdate, update.
        destruct (val_eq_dec (g x) pid); vauto.

        (* [pid] is equal to [g x] *)
        - red. intros ps IN1.
          red in PSAFE1. specialize PSAFE1 with (g x).
          rewrite PC4 in PSAFE1. red in PSAFE1.
          specialize PSAFE1 with ps1.

          (* the process [Ppar P' Q3] is safe with the process store [ps] *)
          assert (PSAFE2 : psafe (Ppar P' Q3) ps1). {
            apply PSAFE1. intros y PSAFE2.
            rewrite <- AGR4, AGR3; auto. rewrite <- PACC4; auto.
            unfold phSnapshot. rewrite CSV11; auto. }

          (* the process stores [ps] and [ps2] agree on all free variables on [a] *)
          assert (IN2 : forall y : ProcVar, In y xs -> ps2 y = ps y). {
            intros y IN2. cut (Some (ps2 y) = Some (ps y)); [intuition vauto|].
            rewrite <- IN1, <- PS2; auto. unfold phSnapshot. symmetry.
            rewrite <- PACC4; auto. }
          assert (IN3 : pstore_agree (act_fv a v) ps2 ps). {
            intros y IN3. by apply IN2, AGR2. }
          inv PSAFE2. destruct H as (_&H).
          apply H with (PLact a v). apply pstep_par_l.
          by apply pstep_act_agree with ps2.

        (* [pid] is not equal to [g x] *)
        - red in PSAFE1. specialize PSAFE1 with pid.
          apply pmeSafe_heap_acc with (phSnapshot (phUnion (phUnion (phUnion (phUnion (phUnion ph1a ph1b) ph2) ph3) phJ) phF)); auto.
          intros l ACC1.
          assert (ACC2 : ~ In l (pmeProj (pmC (g x)))). {
            intro ACC2. red in WS1.
            apply WS1 with (p2 := g x) in ACC1; auto. }
          assert (ACC3 : ~ In l ls). { intro ACC3. by apply ACC2, PACC3. }
          unfold phSnapshot.
          rewrite <- phConvProcMult_pres; auto. }

      exists g, Cskip. repeat split; vauto.

      1:{ (* the ghost semantics can make a step *)
        apply gstep_act_r with (P := Ppar P' Q3)(ps1 := ps1)(ps2 := ps2); vauto.
        - intros y IN1. rewrite <- PACC4; auto.
        - intros y IN1. rewrite <- PACC4; auto.
          unfold phConcr. rewrite CSV8; auto. }

      apply safe_done. rewrite <- H4, <- H6, <- H8.
      rewrite pmUnion_swap_r with (pm3 := pm'').
      exists (phUnion (phUnion ph1a ph1b') ph2), ph3.
      repeat split; vauto.
      exists (pmUnion (pmUnion (pmUnion pm1a pm1b) pm2) pm'').
      exists pm3. repeat split; vauto.

      1:{ (* disjointness of [pm1a + pm1b + pm2 + pm''] and [pm3] *)
        apply pmDisj_swap_r; auto.
        by rewrite H8, H6. }

      rewrite pmUnion_swap_r with (pm3 := pm'').
      exists (phUnion ph1a ph1b'), ph2. repeat split; vauto.
      exists (pmUnion (pmUnion pm1a pm1b) pm''), pm2. repeat split; vauto.

      1:{ (* disjointness of [pm1a + pm1b + pm''] and [pm2] *)
        apply pmDisj_swap_r; auto.
        by rewrite H8. }

      rewrite <- phUnion_iden_l with (ph := phUnion ph1a ph1b').
      exists (phUnion ph1a ph1b'), phIden. repeat split; auto.
      exists (pmUnion pm1a pm1b), pm''. repeat split; vauto.

      1:{ (* the iterated heap ownership assertion holds (again) *)
        apply sat_ApointstoIter_permut with (xs0 := ys1 ++ ys2); auto.
        rewrite <- ApointstoIter_app.
        apply sat_iter_add_l.
        exists ph1a, ph1b'. repeat split; vauto.
        exists pm1a, pm1b. repeat split; vauto.
        subst ph1b'. by apply ApointstoIter_conv_act_proc. }

      1:{ (* the process ownership predicate holds (again) *)
        unfold sat. subst pm''. exists pme. split; vauto.
        unfold pmUpdate. rewrite update_apply.
        subst pme'. rewrite PSIM2.
        destruct PMV1 as [(PMV1&PMV2&PMV3)|(q''&PMV1&PMV2&PMV3)]; vauto.
        - rewrite pmeUnion_free_l.
          rewrite bisim_par_comm.
          by rewrite bisim_par_epsilon_l.
        - rewrite PMV1. unfold pmeUnion. desf. }
Qed.

Theorem rule_act :
  forall x a E C xs J q HP HQ (f1 f2 f2' : ProcVar -> Expr)(fq : ProcVar -> Qc) A1 A2,
  let B1 := hcond_convert (hguard a E) f2 in
  let B2 := hcond_convert (heffect a E) f2' in
  (forall y v, In y (act_fv a v) -> In y xs) ->
  (forall y : ProcVar, In y xs -> perm_valid (fq y)) ->
  (forall y : ProcVar, disjoint (expr_fv (f1 y)) (cmd_mod C)) ->
  disjoint (expr_fv E) (cmd_mod C) ->
  disjoint (hproc_fv HP) (cmd_mod C) ->
  disjoint (hproc_fv HQ) (cmd_mod C) ->
  ~ cmd_mod C x ->
  csl True J (Astar (Astar (Aiter (ApointstoIter_procact xs fq f1 f2)) (Aplain B1)) A1) C (Astar (Astar (Aiter (ApointstoIter_procact xs fq f1 f2')) (Aplain B2)) A2) ->
  csl False J
    (Astar (Astar (Astar (Aiter (ApointstoIter xs fq f1 f2 PTTproc)) (Aproc x q (HPalt (HPseq (HPact a E) HP) HQ) xs f1)) (Aplain B1)) A1)
    (Cact x a E C)
    (Astar (Astar (Astar (Aiter (ApointstoIter xs fq f1 f2' PTTproc)) (Aproc x q HP xs f1)) (Aplain B2)) A2).
Proof.
  intros x a E C xs J q HP HQ f1 f2 f2' fq
    A1 A2 B1 B2 FV1 VF1 VF2 VF3 VF4 VF5 VF6 CSL.
  red. split; vauto.

  1:{ (* [Cact x a E C] is a user program *)
    simpl. by destruct CSL as (?&_). }

  intros [|n] ph pm s g V1 V2 S1 WF1 SAT1. vauto.
  set (F1 := expr_eval_map f1 s : ProcVar -> Val).
  set (F2 := expr_eval_map f2 s : ProcVar -> Val).
  repeat split; vauto.

  (* (2) absence of faults *)
  - red. intros phF pmF D1 D2 FIN1 FIN2 ABORT1. inv ABORT1.

  (* (5) program step *)
  - simpl. intros phJ phF pmJ pmF pmC h' s' C' D1 D2 D3 D4 H1 FIN1 WS1 INV FIN2 COV1 PSAFE1 STEP.
    inv STEP. apply Astar_assoc_r, Astar_assoc_r in SAT1; vauto.
    destruct SAT1 as (ph1&ph2&D5&H2&pm1&pm2&D6&H3&SAT1&SAT2). clarify.

    (* [xs] can be split into two lists, one with read-only permissions and the other with write permissions *)
    assert (K1 : exists ys1 ys2 : list ProcVar,
        Permutation xs (ys1 ++ ys2) /\
        (forall x : ProcVar, In x ys1 -> fq x <> perm_full) /\
        (forall x : ProcVar, In x ys2 -> fq x = perm_full)). {
      pose (f := fun x : ProcVar => if Qc_eq_dec (fq x) perm_full then false else true).
      pose (ys := partition f xs).
      exists (fst ys), (snd ys). repeat split.
      - apply partition_permut with f. by apply partition_res.
      - intros y H2. apply partition_f_left with (xs0 := xs)(ys2 := snd ys)(f0 := f) in H2; auto.
        + subst f. simpls. desf.
        + by apply partition_res.
      - intros y H2. apply partition_f_right with (xs0 := xs)(ys1 := fst ys)(f0 := f) in H2; auto.
        + subst f. simpls. desf.
        + by apply partition_res. }
    destruct K1 as (ys1&ys2&H2&H4&H5).

    (* any variable [y] is in [xs] iff [y] is in [ys1] or [ys2] *)
    assert (LDISJ1 : forall y : ProcVar, In y xs <-> In y ys1 \/ In y ys2). {
      intro y. split; intro H8.
      - apply Permutation_in with (x := y) in H2; auto.
        apply in_app_or in H2. destruct H2 as [H2 | H2]; vauto.
      - symmetry in H2. apply Permutation_in with (x := y) in H2; auto.
        by apply in_or_app. }

    (* [ph1] and [pm1] are both valid *)
    assert (V3 : phValid ph1). { by apply phDisj_valid_l in D5. }
    assert (V4 : pmValid pm1). { by apply pmDisj_valid_l in D6. }

    (* split the iterated separating conjunction in SAT1 into a process- and an action part *)
    generalize SAT1. intro SAT1'.
    apply sat_ApointstoIter_permut with (ys := ys1 ++ ys2) in SAT1; auto.
    rewrite <- ApointstoIter_app in SAT1. apply Aiter_add_r in SAT1; auto.
    destruct SAT1 as (ph1a&ph1b&D7&H6&pm1a&pm1b&D8&H7&SAT1a&SAT1b). clarify.
    generalize SAT1b. intro SAT1b'. apply ApointstoIter_conv_proc_act in SAT1b.
    set (ls := map F1 xs : list Val).
    set (ls1 := map F1 ys1 : list Val).
    set (ls2 := map F1 ys2 : list Val).
    set (ph1b' := phConvActMult ph1b ls2).
    replace (map (expr_eval_map f1 s') ys2) with (ls2) in SAT1b; auto.
    replace (phConvActMult ph1b ls2) with ph1b' in SAT1b; auto.

    (* location [l] is in [ls] iff [l] is in [ls1] or [ls2] *)
    assert (LDISJ2 : forall l : Val, In l ls <-> In l ls1 \/ In l ls2). {
      intro l. split; intro H8.
      - subst ls. apply in_map_iff in H8.
        destruct H8 as (y&H8&H9). clarify.
        apply LDISJ1 in H9. destruct H9 as [H9 | H9].
        + left. subst ls1. by apply in_map.
        + right. subst ls2. by apply in_map.
      - destruct H8 as [H8 | H8].
        + subst ls1. apply in_map_iff in H8.
          destruct H8 as (y&H8&H9). clarify.
          subst ls. apply in_map, LDISJ1. by left.
        + subst ls2. apply in_map_iff in H8.
          destruct H8 as (y&H8&H9). clarify.
          subst ls. apply in_map, LDISJ1. by right. }

    (* the concrete- and snapshot heap contain an element at every location corresponding to variables in [xs] *)
    assert (HC1 : forall y : ProcVar, In y xs ->
        exists q : Qc, perm_valid q /\ phUnion ph1a ph1b (F1 y) = PHCproc q (F2 y)). {
      intros y HC1. apply ApointstoIter_sat_single_proc with (x0 := y) in SAT1'; auto.
      apply phcLe_diff in SAT1'; vauto.
      - destruct SAT1' as (phc&D11&SAT1').
        unfold phcDisj in D11. repeat desf; vauto.
        unfold phcUnion in SAT1'. desf. exists (fq y + q0).
        intuition vauto. by apply perm_add_valid.
      - simpl. by apply VF1. }
    assert (HCL1 : forall l : Val, In l ls -> exists q v, perm_valid q /\ phUnion ph1a ph1b l = PHCproc q v). {
      intros l HCL1. subst ls. apply in_map_iff in HCL1.
      destruct HCL1 as (y&?&HCL1). desf.
      apply HC1 in HCL1. destruct HCL1 as (q'&?&?).
      exists q'. intuition vauto. }
    assert (HC2 : forall y : ProcVar, In y ys2 -> ph1b (F1 y) = PHCproc perm_full (F2 y)). {
      intros y HC2. subst ph1b'.
      apply ApointstoIter_sat_single_proc with (x0 := y) in SAT1b'; auto.
      rewrite H5 in SAT1b'; auto.
      apply phcLe_entire_eq in SAT1b'; vauto.
      by apply phDisj_valid_r in D7. }
    assert (HCL2 : forall l : Val, In l ls2 -> exists v : Val, ph1b l = PHCproc perm_full v). {
      intros l HCL2. subst ls2. apply in_map_iff in HCL2.
      destruct HCL2 as (y&?&HCL2). desf.
      apply HC2 in HCL2. rewrite HCL2. by exists (F2 y). }
    assert (HC3 : forall y : ProcVar, In y ys1 -> exists q : Qc, perm_valid q /\ ph1a (F1 y) = PHCproc q (F2 y)). {
      intros y HC3. apply ApointstoIter_sat_single_proc with (x0 := y) in SAT1a; auto.
      apply phcLe_diff in SAT1a; vauto.
      - destruct SAT1a as (phc&D11&SAT1a).
        subst F1. unfold expr_eval_map. rewrite <- SAT1a.
        unfold phcDisj in D11. destruct phc as [|q'|q'|q'|]; vauto.
        unfold phcUnion. desf. exists (fq y + q'); split; vauto.
        by apply perm_add_valid.
      - simpl. apply VF1. rewrite LDISJ1. by left.
      - by apply phDisj_valid_l in D7. }
    assert (HCL3 : forall l : Val, In l ls1 -> exists q v, perm_valid q /\ ph1a l = PHCproc q v). {
      intros l HCL3. subst ls1. apply in_map_iff in HCL3.
      destruct HCL3 as (y&?&HCL3). desf. apply HC3 in HCL3. unfold expr_eval_map.
      destruct HCL3 as (q'&HCL3). by exists q', (expr_eval (f2 y) s'). }
    assert (HC4 : forall y : ProcVar, In y ys1 -> ph1b (F1 y) = PHCfree \/ exists q, perm_valid q /\ ph1b (F1 y) = PHCproc q (F2 y)). {
      intros y HC4. assert (IN1 : In y xs). { apply LDISJ1. by left. }
      apply HC3 in HC4. destruct HC4 as (q'&?&HC4).
      apply HC1 in IN1. destruct IN1 as (q''&?&IN1).
      red in D7. red in D7. specialize D7 with (F1 y).
      rewrite HC4 in D7. red in D7. unfold phUnion in IN1.
      repeat desf; vauto.
      right. exists q0. intuition vauto.
      by apply perm_disj_valid_r in D7. }
    assert (HCL4 : forall l : Val, In l ls1 -> ph1b l = PHCfree \/ exists q v, perm_valid q /\ ph1b l = PHCproc q v). {
      intros l HCL4. subst ls1. apply in_map_iff in HCL4.
      destruct HCL4 as (y&?&HCL4). clarify.
      apply HC4 in HCL4. destruct HCL4 as [HCL4 | (q'&?&HCL4)]; vauto.
      right. exists q', (F2 y). vauto. }
    assert (HC5 : forall y : ProcVar, In y ys2 -> ph1a (F1 y) = PHCfree). {
      intros y HC5. apply HC2 in HC5.
      red in D7. red in D7. specialize D7 with (F1 y).
      rewrite HC5 in D7.
      symmetry in D7. apply phcDisj_entire_free in D7; vauto. }
    assert (HCL5 : forall l : Val, In l ls2 -> ph1a l = PHCfree). {
      intros l HCL5. subst ls2. apply in_map_iff in HCL5.
      destruct HCL5 as (y&?&HCL5). clarify. by apply HC5 in HCL5. }
    assert (HC6 : forall y : ProcVar, In y xs -> ph2 (F1 y) = PHCfree \/ exists q, perm_valid q /\ ph2 (F1 y) = PHCproc q (F2 y)). {
      intros y HC6. apply HC1 in HC6. destruct HC6 as (q'&?&HC6).
      red in D5. red in D5. specialize D5 with (F1 y).
      rewrite HC6 in D5. red in D5.
      repeat desf; vauto. right. exists q0. intuition vauto.
      by apply perm_disj_valid_r in D5. }
    assert (HCL6 : forall l : Val, In l ls -> ph2 l = PHCfree \/ exists q v, perm_valid q /\ ph2 l = PHCproc q v). {
      intros l HCL6. subst ls. apply in_map_iff in HCL6.
      destruct HCL6 as (y&?&HCL6). clarify.
      apply HC6 in HCL6. destruct HCL6 as [HCL6 | (q'&?&HCL6)]; vauto.
      right. exists q', (F2 y). split; vauto. }

    (* the sequences [ls1] and [ls2] are disjoint *)
    assert (LDISJ3 : forall l : Val, In l ls1 -> In l ls2 -> False). {
      intros l H8 H9. apply HCL2 in H9.
      destruct H9 as (v'&H9). apply HCL3 in H8.
      destruct H8 as (q'&v''&H8&H10).
      red in D7. red in D7. specialize D7 with l.
      rewrite H9, H10 in D7. unfold phcDisj in D7. desf.
      by apply perm_disj_full_neg_l with q'. }

    (* [ph1b l] is full for every [l] in [ls2]; and [ph1a l], [ph2 l], [phJ l] and [phF l] are all free *)
    assert (HV1 : forall y : ProcVar, In y ys2 -> phcEntire (ph1b (F1 y))). {
      intros y HV1. apply HC2 in HV1. by rewrite HV1. }
    assert (HVL1 : forall l : Val, In l ls2 -> phcEntire (ph1b l)). {
      intros y HVL1. apply HCL2 in HVL1. destruct HVL1 as (?&HVL1). by rewrite HVL1. }
    assert (HV2 : forall y : ProcVar, In y ys2 -> ph1a (F1 y) = PHCfree). {
      intros y HV2. apply HC5 in HV2. by rewrite HV2. }
    assert (HVL2 : forall l : Val, In l ls2 -> ph1a l = PHCfree). {
      intros l HVL2. by apply HCL5. }
    assert (HV3 : forall y : ProcVar, In y ys2 -> ph2 (F1 y) = PHCfree). {
      intros y HV3. red in D5. red in D5.
      specialize D5 with (F1 y).
      apply phcDisj_entire_free in D5; auto.
      rewrite <- phUnion_cell. rewrite HV2; auto.
      rewrite phcUnion_free_r. by apply HV1. }
    assert (HVL3 : forall l : Val, In l ls2 -> ph2 l = PHCfree). {
      intros l HVL3. subst ls2. apply in_map_iff in HVL3.
      destruct HVL3 as (y&?&HVL3). clarify. by apply HV3. }
    assert (HV4 : forall y : ProcVar, In y ys2 -> phJ (F1 y) = PHCfree). {
      intros y HV4. red in D1. red in D1.
      specialize D1 with (F1 y).
      apply phcDisj_entire_free in D1; auto.
      repeat rewrite <- phUnion_cell. rewrite HV2, HV3; auto.
      rewrite phcUnion_free_l, phcUnion_free_r. by apply HV1. }
    assert (HVL4 : forall l : Val, In l ls2 -> phJ l = PHCfree). {
      intros l HVL4. subst ls2. apply in_map_iff in HVL4.
      destruct HVL4 as (y&?&HVL4). clarify. by apply HV4. }
    assert (HV5 : forall y : ProcVar, In y ys2 -> phF (F1 y) = PHCfree). {
      intros y HV5. red in D2. red in D2.
      specialize D2 with (F1 y).
      apply phcDisj_entire_free in D2; auto.
      repeat rewrite <- phUnion_cell. rewrite HV2, HV3, HV4; auto.
      rewrite phcUnion_free_l, phcUnion_free_r, phcUnion_free_l. by apply HV1. }
    assert (HVL5 : forall l : Val, In l ls2 -> phF l = PHCfree). {
      intros l HVL5. subst ls2. apply in_map_iff in HVL5.
      destruct HVL5 as (y&?&HVL5). clarify. by apply HV5. }

    (* the heap [ph1b'] remains disjoint in all compositions in which [ph1b] is disjoint *)
    assert (DISJ1 : phDisj ph1a ph1b'). {
      rewrite <- phConvActMult_free with ls2 ph1a; auto.
      by apply phConvActMult_disj. }
    assert (DISJ2 : phDisj (phUnion ph1a ph1b') ph2). {
      rewrite <- phConvActMult_free with ls2 ph1a; auto.
      rewrite <- phConvActMult_free with ls2 ph2; auto.
      subst ph1b' F1. rewrite <- phConvActMult_union; vauto.
      by apply phConvActMult_disj. }
    assert (DISJ3 : phDisj (phUnion (phUnion ph1a ph1b') ph2) phJ). {
      rewrite <- phConvActMult_free with ls2 ph1a; auto.
      rewrite <- phConvActMult_free with ls2 ph2; auto.
      rewrite <- phConvActMult_free with ls2 phJ; auto.
      subst ph1b' F1. repeat rewrite <- phConvActMult_union; vauto.
      by apply phConvActMult_disj. }
    assert (DISJ4 : phDisj (phUnion (phUnion (phUnion ph1a ph1b') ph2) phJ) phF). {
      rewrite <- phConvActMult_free with ls2 ph1a; auto.
      rewrite <- phConvActMult_free with ls2 ph2; auto.
      rewrite <- phConvActMult_free with ls2 phJ; auto.
      rewrite <- phConvActMult_free with ls2 phF; auto.
      subst ph1b' F1. repeat rewrite <- phConvActMult_union; vauto.
      by apply phConvActMult_disj. }

    (* [ph2] and [pm2] are valid *)
    assert (V5 : phValid (phUnion ph1a ph1b')). { by apply phUnion_valid. }
    assert (V6 : phValid ph2). { by apply phDisj_valid_r in D5. }
    assert (V7 : pmValid pm2). { by apply pmDisj_valid_r in D6. }

    (* results of concretisations of heap locations under [F1] and [F2] *)
    assert (CSV1 : forall y : ProcVar, In y ys1 -> phcConcr (ph1a (F1 y)) = Some (F2 y)). {
      intros y CSV1. apply HC3 in CSV1. destruct CSV1 as (q'&?&CSV1). by rewrite CSV1. }
    assert (CSVL1 : forall l : Val, In l ls1 -> exists v : Val, phcConcr (ph1a l) = Some v). {
      intros l CSVL1. apply HCL3 in CSVL1. destruct CSVL1 as (?&v'&?&CSVL1).
      rewrite CSVL1. by exists v'. }
    assert (CSV2 : forall y : ProcVar, In y ys2 -> phcConcr (ph1a (F1 y)) = None). { ins. by rewrite HC5. }
    assert (CSVL2 : forall l : Val, In l ls2 -> phcConcr (ph1a l) = None). { ins. by rewrite HCL5. }
    assert (CSV3 : forall y : ProcVar, In y ys2 -> phcConcr (ph1b (F1 y)) = Some (F2 y)). {
      intros y CSV3. apply HC2 in CSV3. rewrite CSV3. vauto. }
    assert (CSVL3 : forall l : Val, In l ls2 -> exists v : Val, phcConcr (ph1b l) = Some v). {
      intros l CSVL3. apply HCL2 in CSVL3. destruct CSVL3 as (v'&CSVL3). rewrite CSVL3. by exists v'. }
    assert (CSV4 : forall y : ProcVar, In y xs -> phcConcr (phUnion ph1a ph1b (F1 y)) = Some (F2 y)). {
      intros y CSV4. apply LDISJ1 in CSV4. destruct CSV4 as [CSV4 | CSV4].
      - apply CSV1 in CSV4. apply phcConcr_union; auto.
      - apply CSV3 in CSV4. rewrite phUnion_comm.
        apply phcConcr_union; auto.
        by symmetry. }
    assert (CSVL4 : forall l : Val, In l ls -> exists v : Val, phcConcr (phUnion ph1a ph1b l) = Some v). {
      intros l CSVL4. subst ls. apply in_map_iff in CSVL4.
      destruct CSVL4 as (y&?&CSVL4). clarify.
      apply CSV4 in CSVL4. by exists (F2 y). }
    assert (CSV5 : forall y : ProcVar, In y xs -> phcConcr (phUnion (phUnion ph1a ph1b) ph2 (F1 y)) = Some (F2 y)). {
      intros y CSV5. rewrite <- phUnion_cell. apply phcConcr_union; auto. }
    assert (CSVL5 : forall l : Val, In l ls -> exists v, phcConcr (phUnion (phUnion ph1a ph1b) ph2 l) = Some v). {
      intros l CSVL5. apply CSVL4 in CSVL5. destruct CSVL5 as (v&CSVL5).
      exists v. rewrite <- phUnion_cell. apply phcConcr_union; auto. }

    (* relations between the concrete- and snapshot values of [ph1a], [ph1b] and [ph1b'] with respect to [xs] *)
    assert (CS1 : forall y : ProcVar, In y xs -> phcConcr (ph2 (F1 y)) = phcSnapshot (ph2 (F1 y))). {
      intros y CS1. apply HC6 in CS1.
      destruct CS1 as [CS1 | (q'&?&CS1)]; by rewrite CS1. }
    assert (CSL1 : forall l : Val, In l ls -> phcConcr (ph2 l) = phcSnapshot (ph2 l)). {
      intros l CSL1. apply HCL6 in CSL1.
      destruct CSL1 as [CSL1 | (?&?&?&CSL1)]; by rewrite CSL1. }
    assert (CS2 : forall y : ProcVar, In y ys1 -> phcConcr (ph1a (F1 y)) = phcSnapshot (ph1a (F1 y))). {
      intros y CS2. apply HC3 in CS2.
      destruct CS2 as (?&?&CS2). by rewrite CS2. }
    assert (CSL2 : forall l : Val, In l ls1 -> phcConcr (ph1a l) = phcSnapshot (ph1a l)). {
      intros l CSL2. apply HCL3 in CSL2.
      destruct CSL2 as (?&?&?&CSL2). by rewrite CSL2. }
    assert (CS3 : forall y : ProcVar, In y ys2 -> phcConcr (ph1a (F1 y)) = phcSnapshot (ph1a (F1 y))). {
      intros y CS3. by rewrite HV2. }
    assert (CSL3 : forall l : Val, In l ls2 -> phcConcr (ph1a l) = phcSnapshot (ph1a l)). {
      intros l CSL3. by rewrite HVL2. }
    assert (CS4 : forall y : ProcVar, In y xs -> phcConcr (ph1a (F1 y)) = phcSnapshot (ph1a (F1 y))). {
      intros y CS4. apply LDISJ1 in CS4.
      destruct CS4 as [CS4 | CS4]; auto. }
    assert (CSL4 : forall l : Val, In l ls -> phcConcr (ph1a l) = phcSnapshot (ph1a l)). {
      intros l CSL4. apply LDISJ2 in CSL4.
      destruct CSL4 as [CSL4 | CSL4]; auto. }
    assert (CS5 : forall y : ProcVar, In y ys2 -> phcConcr (ph1b (F1 y)) = phcSnapshot (ph1b (F1 y))). {
      intros y CS5. apply HC2 in CS5. by rewrite CS5. }
    assert (CSL5 : forall l : Val, In l ls2 -> phcConcr (ph1b l) = phcSnapshot (ph1b l)). {
      intros l CSL5. apply HCL2 in CSL5.
      destruct CSL5 as (?&CSL5). by rewrite CSL5. }
    assert (CS6 : forall y : ProcVar, In y ys1 -> phcConcr (ph1b (F1 y)) = phcSnapshot (ph1b (F1 y))). {
      intros y CS6. apply HC4 in CS6.
      destruct CS6 as [CS6 | (?&?&CS6)]; by rewrite CS6. }
    assert (CSL6 : forall l : Val, In l ls1 -> phcConcr (ph1b l) = phcSnapshot (ph1b l)). {
      intros l CSL6. apply HCL4 in CSL6.
      destruct CSL6 as [CSL6 | (?&?&?&CSL6)]; by rewrite CSL6. }
    assert (CS7 : forall y : ProcVar, In y xs -> phcConcr (ph1b (F1 y)) = phcSnapshot (ph1b (F1 y))). {
      intros y CS7. apply LDISJ1 in CS7.
      destruct CS7 as [CS7 | CS7]; auto. }
    assert (CSL7 : forall l : Val, In l ls -> phcConcr (ph1b l) = phcSnapshot (ph1b l)). {
      intros l CSL7. apply LDISJ2 in CSL7.
      destruct CSL7 as [CSL7 | CSL7]; auto. }
    assert (CS8 : forall y : ProcVar, In y xs ->
        phConcr (phUnion (phUnion (phUnion (phUnion ph1a ph1b) ph2) phJ) phF) (F1 y) =
        phConcr (phUnion (phUnion ph1a ph1b) ph2) (F1 y)). {
      intros y CS8. unfold phConcr. rewrite CSV5; auto.
      rewrite <- phUnion_cell. apply phcConcr_union; auto.
      rewrite <- phUnion_cell. apply phcConcr_union; auto. }
    assert (CSL8 : forall l : Val, In l ls ->
        phConcr (phUnion (phUnion (phUnion (phUnion ph1a ph1b) ph2) phJ) phF) l =
        phConcr (phUnion (phUnion ph1a ph1b) ph2) l). {
      intros l CSL8. subst ls. apply in_map_iff in CSL8.
      destruct CSL8 as (y&?&CSL8). clarify. auto. }

    (* the concrete and snapshot values of [ph1b] and [ph1b'] coincide *)
    assert (CSR1 : phConcr ph1b = phConcr ph1b'). {
      subst ph1b'. by rewrite phConvActMult_concr. }
    assert (CSRL1 : forall l : Val, phcConcr (ph1b l) = phcConcr (ph1b' l)). {
      intro l. by apply equal_f with l in CSR1. }
    assert (CSR2 : phSnapshot ph1b = phSnapshot ph1b'). {
      extensionality l. subst ph1b'. unfold phSnapshot.
      assert (IN : In l ls2 \/ ~ In l ls2). { by apply classic. }
      destruct IN as [IN | IN].
      - rewrite phConvActMult_apply; auto.
        apply HCL2 in IN. destruct IN as (?&IN). by rewrite IN.
      - by rewrite <- phConvActMult_pres. }
    assert (CSRL2 : forall l : Val, phcSnapshot (ph1b l) = phcSnapshot (ph1b' l)). {
      intro l. by apply equal_f with l in CSR2. }
    assert (CSR3 : forall y : ProcVar, In y xs -> phcConcr (phUnion ph1a ph1b (F1 y)) = phcSnapshot (phUnion ph1a ph1b' (F1 y))). {
      intros y CSR3. rewrite <- phUnion_cell.
      apply phcConcr_snapshot_compat; auto. rewrite CS7, <- CSRL2; auto. }
    assert (CSRL3 : forall l : Val, In l ls -> phcConcr (phUnion ph1a ph1b l) = phcSnapshot (phUnion ph1a ph1b' l)). {
      intros l CSRL3. rewrite <- phUnion_cell.
      apply phcConcr_snapshot_compat; auto. rewrite CSL7, <- CSRL2; auto. }

    exists (phUnion (phUnion ph1a ph1b') ph2), phJ.
    repeat split; vauto.

    1:{ (* the heap concretisation is proper *)
      rewrite <- phConvActMult_free with (xs := ls2)(ph := ph1a) at 1; auto.
      rewrite <- phConvActMult_free with (xs := ls2)(ph := ph2) at 1; auto.
      rewrite <- phConvActMult_free with (xs := ls2)(ph := phJ) at 1; auto.
      rewrite <- phConvActMult_free with (xs := ls2)(ph := phF) at 1; auto.
      subst ph1b'. repeat rewrite <- phConvActMult_union; vauto.
      by rewrite phConvActMult_concr. }

    pose (phC := phUnion (phUnion (phUnion (phUnion ph1a ph1b) ph2) phJ) phF).
    pose (h := phConcr phC).
    pose (hs := phSnapshot phC).
    exists pm, pmJ, pmC. repeat split; vauto.

    1:{ (* [pmC] covers the updated snapshot heap *)
      intros l H6. apply pmCovers_occ with hs; auto.
      rewrite <- phConvActMult_free with ls2 ph1a; auto.
      rewrite <- phConvActMult_free with ls2 ph2; auto.
      rewrite <- phConvActMult_free with ls2 phJ; auto.
      rewrite <- phConvActMult_free with ls2 phF; auto.
      subst ph1b'. repeat rewrite <- phConvActMult_union; vauto.
      by apply phConvActMult_snapshot_occ. }

    1:{ (* [pmC] is safe with the updated snapshot heap *)
      apply pmSafe_subheap with hs; auto.
      intros l v H6. subst hs phC.
      rewrite <- H6. unfold phSnapshot.
      repeat apply phcSnapshot_disj_union_l; auto.
      apply phcSnapshot_disj_union_r; auto.
      - by symmetry.
      - by symmetry. }

    rename s' into s.
    pose (v := expr_eval E s).
    exists g, (Cinact (GMdata (g x) a v h) C).
    repeat split; vauto.

    1:{ (* the resource invariant is still maintained *)
      unfold invariant_sat in INV. simpl in INV.
      intuition vauto. }

    (* take the process ownership predicate in [SAT2] apart *)
    destruct SAT2 as (ph3&ph4&D9&EQ1&pm3&pm4&D10&EQ2&SAT2a&SAT2b).
    clarify.
    set (pm' := pmUnion (pmUnion (pmUnion pm1a pm1b) pm4) pm3).
    assert (EQ1 : pmBisim pm pm'). {
      rewrite <- H3, <- H7, <- EQ2.
      rewrite <- pmUnion_assoc.
      rewrite pmUnion_swap_r with (pm3 := pm4); auto. }

    (* most of the remainder of the proof follows from [safe_action] *)
    rewrite EQ1. subst pm'.
    apply safe_action with HQ ys1 ys2; vauto.

    1:{ (* the metadata of the activated action is agreed upon *)
      unfold metadata_agree.
      assert (PS1 : exists q P, pmeBisim (pm3 (g x)) (PEelem q P xs F1)). {
        unfold sat in SAT2a.
        simpl (pDehybridise (HPalt (HPseq (HPact a E) HP) HQ) s) in SAT2a.
        replace (expr_eval E s) with v in SAT2a; [|done].
        destruct SAT2a as (pme&D11&SAT2a).
        unfold pmeDisj in D11. repeat desf; vauto.
        unfold pmeUnion in SAT2a. desf.
        remember (pDehybridise HP s) as CP.
        remember (pDehybridise HQ s) as CQ.
        exists (q + q0), (Ppar (Palt (Pseq (Pact a v) CP) CQ) P).
        by vauto. }
      destruct PS1 as (q'&P'&PS1).
      exists q', P'. repeat split; vauto.
      - intros y IN1. by apply FV1 with (expr_eval E s).
      - intros y IN1. subst h phC.
        assert (IN2 : In (expr_eval_map f1 s y) ls). {
          subst ls. by apply in_map. }
        rewrite CSL8; auto.
        unfold phConcr, phSnapshot.
        apply phcConcr_snapshot_compat; auto.
      - exists F2. split; vauto.
        + intros y H8. unfold expr_eval_map.
          subst h phC. unfold phConcr.
          rewrite <- phUnion_cell. apply phcConcr_union; auto.
          rewrite <- phUnion_cell. apply phcConcr_union; auto.
          rewrite <- phUnion_cell. apply phcConcr_union; auto.
          apply HC1 in H8. destruct H8 as (q''&H8&H9).
          subst F1. unfold expr_eval_map in H9. rewrite H9. simpls.
        + rewrite <- cond_eval_conv with (s:=s)(f:=f2); vauto.
          apply assn_weaken_l in SAT2b; auto.
          * by rewrite <- hguard_corr.
          * by apply phDisj_valid_r in D9.
          * by apply pmDisj_valid_r in D10. }

    1:{ (* [pm1a + pm1b + pm4] and [pm3] are disjoint *)
      rewrite H7. apply pmDisj_assoc_r; auto.
      - by symmetry.
      - rewrite pmUnion_comm. by rewrite EQ2. }

    (* [ph3] and [ph4] are free for every location in [ls2] *)
    assert (HVL6 : forall l : Val, In l ls2 -> ph3 l = PHCfree). {
      intros l HVL6. apply HVL3 in HVL6.
      apply phcUnion_free in HVL6. desf. }
    assert (HVL7 : forall l : Val, In l ls2 -> ph4 l = PHCfree). {
      intros l HVL7. apply HVL3 in HVL7.
      apply phcUnion_free in HVL7. desf. }

    apply CSL; vauto.

    1:{ (* the heap [ph1a + ph1b' + ph3 + ph4] is valid *)
      rewrite <- phConvActMult_free with (ph := ph1a)(xs := ls2); auto.
      rewrite <- phConvActMult_free with (ph := ph3)(xs := ls2); auto.
      rewrite <- phConvActMult_free with (ph := ph4)(xs := ls2); auto.
      subst ph1b'. repeat rewrite <- phConvActMult_union; vauto.
      by apply phConvActMult_valid. }

    1:{ (* the maps [pm1a + pm1b + pm4] is valid *)
      rewrite H7. apply pmUnion_valid.
      apply pmDisj_union_r with pm3; auto.
      - by symmetry.
      - rewrite pmUnion_comm. by rewrite EQ2. }

    1:{ (* [pm1a + pm1b + pm4] is safe with [ph1a + ph1b' + ph3 + ph4]'s snapshot heap *)
      assert (PHS1 : phSnapshot (phUnion (phUnion ph1a ph1b') (phUnion ph3 ph4)) = 
          phSnapshot (phUnion (phUnion ph1a ph1b) (phUnion ph3 ph4))). {
        apply phSnapshot_disj_union_l; auto.
        apply phSnapshot_disj_union_r; auto.
        + by symmetry.
        + by symmetry. }
      rewrite PHS1.
      apply pmSafe_weaken_l with pm3.
      by rewrite <- EQ1. }

    1:{ (* the program [C] is well-formed *)
      simpl in WF1. by apply cmd_basic_wf. }

    (* the precondition of the Hoare-triple for [C] is satisfied *)
    apply sat_star_assoc_l.
    exists (phUnion (phUnion ph1a ph1b') ph3), ph4.
    repeat split; vauto.

    1:{ (* [ph1a + ph1b' + ph3] and [ph4] are disjoint *)
      apply phDisj_assoc_r; auto. }

    1:{ (* associativity of [ph1a + ph1b' + ph3 + ph4] *)
      by rewrite phUnion_assoc. }

    exists (pmUnion pm1a pm1b), pm4.
    repeat split; vauto.

    1:{ (* [pm1a + pm1b] and [pm4] are disjoint *)
      rewrite H7. apply pmDisj_union_r with pm3; auto.
      - by symmetry.
      - rewrite pmUnion_comm. by rewrite EQ2. }

    rewrite <- pmUnion_iden_l with (pmUnion pm1a pm1b).
    apply sat_weaken; auto.

    1:{ (* [ph1a + ph1b] and [ph3] are disjoint *)
      apply phDisj_union_r with ph4; auto. }

    1:{ (* the iterated heap ownership assertion is (still) satisfied *)
      apply sat_procact_iter_permut with (xs0 := ys1 ++ ys2); auto.
      apply ApointstoIter_procact_merge; auto.
      exists ph1a, ph1b'. repeat split; vauto.
      exists pm1a, pm1b. repeat split; vauto. }
Qed.


(** *** Query rule *)

(** We use the following small helper definition
    (only for technical reasons). *)

Definition DisjWrapper (P Q : Prop) := P \/ Q.

Lemma wrap : forall P Q, P \/ Q -> DisjWrapper P Q.
Proof. intros P Q H1. red. done. Qed.
Lemma unwrap : forall P Q, DisjWrapper P Q -> P \/ Q.
Proof. intros P Q H1. red in H1. done. Qed.

(** And now the actual rule. *)

Theorem rule_query :
  forall x HB HP HQ q (xs : list ProcVar)(f1 f2 : ProcVar -> Expr)(fq : ProcVar -> Qc) J A,
  (forall y : ProcVar, In y (hcond_fpv HB) -> In y xs) ->
  (forall y : ProcVar, In y xs -> perm_valid (fq y)) ->
  let B := hcond_convert HB f2 in
  csl False J
    (Astar (Astar (Aiter (ApointstoIter xs fq f1 f2 PTTproc)) (Aproc x q (HPalt (HPseq (HPassert HB) HP) HQ) xs f1)) A)
    (Cquery x)
    (Astar (Astar (Astar (Aiter (ApointstoIter xs fq f1 f2 PTTproc)) (Aproc x q HP xs f1)) (Aplain B)) A).
Proof.
  intros x HB HP HQ q xs f1 f2 fq J A IN1 IN2 B.
  split; vauto.
  intros [|n] ph pm s g V1 V2 S1 WF SAT. vauto.

  (* some shorthand notations *)
  set (F1 := expr_eval_map f1 s : ProcVar -> Val).
  set (F2 := expr_eval_map f2 s : ProcVar -> Val).
  set (ls := map F1 xs : list Val).
  set (CB := cDehybridise HB s).
  set (CP := pDehybridise HP s).
  set (CQ := pDehybridise HQ s).
  set (pid := g x).

  (* a property concerning free variables in [CB] *)
  assert (IN3 : forall y : ProcVar, In y (pcond_fv CB) -> In y xs). {
    intros y K1. apply cDehybridise_fpv in K1.
    by apply IN1. }

  (* decompose the precondition *)
  destruct SAT as (ph'&ph3&D3&D4&pm'&pm3&D5&D6&SAT&SAT1).
  destruct SAT as (ph1&ph2&D8&D9&pm1&pm2&D10&D11&SAT2&SAT3).
  clarify.

  unfold sat in SAT3.
  destruct SAT3 as (c'&SAT3&SAT4).

  (* [pm2 pid] contains the expected entry *)
  assert (PS1 : exists q1 P1,
      pmeBisim (pm2 pid) (PEelem q1 (Ppar (Palt (Pseq (Passert CB) CP) CQ) P1) xs F1) /\
      (c' = PEfree /\ q1 = q /\ P1 = Pepsilon \/ exists q1', pmeBisim c' (PEelem q1' P1 xs F1) /\ q1 = q + q1')). {
    simpl (pDehybridise (HPalt (HPseq (HPassert HB) HP) HQ) s) in SAT3.
    replace (expr_eval_map f1 s) with F1; [|done].
    unfold pmeDisj in SAT3. repeat desf; vauto.
    - unfold pmeUnion in SAT4. desf.
      exists (q + q0), P. intuition vauto.
    - unfold pmeUnion in SAT3. desf.
      exists q, Pepsilon.
      rewrite bisim_par_epsilon_r. by vauto. }
  destruct PS1 as (q1&P1&PS1&PS1').
  apply wrap in PS1'.

  (* [pm1 + pm2 pid] contains the expected entry *)
  assert (PS2 : exists q2 P2,
      pmeBisim (pmeUnion (pm1 pid) (pm2 pid)) (PEelem q2 (Ppar (Ppar (Palt (Pseq (Passert CB) CP) CQ) P1) P2) xs F1) /\
      (pm1 pid = PEfree /\ q1 = q2 /\ P2 = Pepsilon \/
      exists q2', pmeBisim (pm1 pid) (PEelem q2' P2 xs F1) /\ q2 = q2' + q1)). {
    red in D10. red in D10.
    specialize D10 with pid.
    rewrite PS1 in D10.
    red in D10. repeat desf; vauto.
    (* [pm1 pid] is not free *)
    - exists (q0 + q1), P.
      rewrite PS1. unfold pmeUnion.
      desf. split.
      + by rewrite bisim_par_comm.
      + right. exists q0. intuition.
        apply pmeBisim_F.
        intros. apply map_eq_In with xs; vauto.
    (* [pm1 pid] is free *)
    - exists q1, Pepsilon. rewrite PS1.
      rewrite pmeUnion_free_r. split.
      + by rewrite bisim_par_epsilon_r.
      + by left. }
  destruct PS2 as (q2&P2&PS2&PS2').
  rewrite pmUnion_elem in PS2.
  apply wrap in PS2'.

  (* [pm1 + pm2] coincides with [pm'] at entry [pid] *)
  assert (PS3 : pmeBisim (pmUnion pm1 pm2 pid) (pm' pid)). {
    red in D11. red in D11.
    specialize D11 with pid. by rewrite D11. }
  rewrite PS3 in PS2.

  (* [pm' + pm3 pid] contains the expected entry *)
  assert (PS4 : exists q3 P3,
      pmeBisim (pmeUnion (pm' pid) (pm3 pid)) (PEelem q3 (Ppar (Ppar (Ppar (Palt (Pseq (Passert CB) CP) CQ) P1) P2) P3) xs F1) /\
      (pm3 pid = PEfree /\ q2 = q3 /\ P3 = Pepsilon \/
      exists q3', pmeBisim (pm3 pid) (PEelem q3' P3 xs F1) /\ q3 = q2 + q3')). {
    red in D5. red in D5. specialize D5 with pid.
    rewrite PS2 in D5.
    red in D5. repeat desf; vauto.
    - exists (q2 + q0), P.
      rewrite PS2. unfold pmeUnion.
      desf. intuition.
      right. exists q0. intuition vauto.
    - exists q2, Pepsilon. rewrite PS2.
      rewrite pmeUnion_free_l. intuition vauto.
      by rewrite bisim_par_epsilon_r. }
  destruct PS4 as (q3&P3&PS4&PS4').
  apply wrap in PS4'.

  (* [pm' + pm3] coincides with [pm] at entry [pid] *)
  assert (PS5 : pmeBisim (pmUnion pm' pm3 pid) (pm pid)). {
    red in D6. red in D6.
    specialize D6 with pid. by rewrite D6. }
  rewrite PS5 in PS4.

  (* [ph1] and [pm1] are both valid *)
  assert (VALID1 : phValid ph1). { by apply phDisj_valid_l in D8. }
  assert (VALID2 : pmValid pm1). { by apply pmDisj_valid_l in D10. }

  (* the heap contains an element at every location corresponding to variables in [xs] *)
 assert (HC1 : forall y : ProcVar, In y xs ->
      exists q : Qc, perm_valid q /\ ph1 (F1 y) = PHCproc q (F2 y)). {
    intros y HC1. apply ApointstoIter_sat_single_proc with (x0 := y) in SAT2; auto.
    apply phcLe_diff in SAT2; vauto.
    - destruct SAT2 as (phc&D12&SAT2).
      unfold phcDisj in D12. repeat desf; vauto.
      unfold phcUnion in SAT2. desf. exists (fq y + q0).
      intuition vauto. by apply perm_add_valid.
    - simpl. by apply IN2. }
  assert (HCL1 : forall l : Val, In l ls ->
      exists q v, perm_valid q /\ ph1 l = PHCproc q v). {
    intros l HCL1. subst ls. apply in_map_iff in HCL1.
    destruct HCL1 as (y&?&HCL1). desf.
    apply HC1 in HCL1. destruct HCL1 as (q'&?&?).
    exists q'. intuition vauto. }
  assert (HC2 : forall y : ProcVar, In y xs ->
      ph2 (F1 y) = PHCfree \/
      exists q, perm_valid q /\ ph2 (F1 y) = PHCproc q (F2 y)). {
    intros y HC2. apply HC1 in HC2. destruct HC2 as (q'&?&HC2).
    red in D8. red in D8. specialize D8 with (F1 y).
    rewrite HC2 in D8. red in D8.
    repeat desf; vauto. right.
    exists q0. intuition vauto.
    by apply perm_disj_valid_r in D8. }
  assert (HCL2 : forall l : Val, In l ls ->
      ph2 l = PHCfree \/
      exists q v, perm_valid q /\ ph2 l = PHCproc q v). {
    intros l HCL2. subst ls. apply in_map_iff in HCL2.
    destruct HCL2 as (y&?&HCL2). clarify.
    apply HC2 in HCL2. destruct HCL2 as [HCL2|(q'&?&HCL6)]; vauto.
    right. exists q', (F2 y). split; vauto. }
  assert (HC3 : forall y : ProcVar, In y xs ->
      exists q : Qc, perm_valid q /\
        phUnion ph1 ph2 (F1 y) = PHCproc q (F2 y)). {
    intros y HC3. generalize HC3. intro HC4.
    apply HC1 in HC3. apply HC2 in HC4.
    destruct HC3 as (q'&G1&HC3).
    red in D8. red in D8. specialize D8 with (F1 y).
    rewrite HC3 in D8. red in D8.
    unfold phUnion, phcUnion. repeat desf.
    - exists q'. intuition.
    - exists (q' + q0). intuition.
      by apply perm_add_valid. }
  assert (HCL3 : forall l : Val, In l ls ->
      exists q v, perm_valid q /\
        phUnion ph1 ph2 l = PHCproc q v). {
    intros l HCL3. subst ls. apply in_map_iff in HCL3.
    destruct HCL3 as (y&?&HCL3). desf.
    apply HC3 in HCL3. destruct HCL3 as (q'&?&?).
    exists q'. intuition vauto. }
  assert (HC4 : forall y : ProcVar, In y xs ->
      ph3 (F1 y) = PHCfree \/
      exists q, perm_valid q /\ ph3 (F1 y) = PHCproc q (F2 y)). {
    intros y HC4. apply HC3 in HC4. destruct HC4 as (q'&?&HC4).
    red in D3. red in D3. specialize D3 with (F1 y).
    rewrite HC4 in D3. red in D3.
    repeat desf; vauto. right.
    exists q0. intuition vauto.
    by apply perm_disj_valid_r in D3. }
  assert (HCL4 : forall l : Val, In l ls ->
      ph3 l = PHCfree \/
      exists q v, perm_valid q /\ ph3 l = PHCproc q v). {
    intros l HCL4. subst ls. apply in_map_iff in HCL4.
    destruct HCL4 as (y&?&HCL4). clarify.
    apply HC4 in HCL4. destruct HCL4 as [HCL4|(q'&?&HCL6)]; vauto.
    right. exists q', (F2 y). split; vauto. }
  assert (HC5 : forall y : ProcVar, In y xs ->
      exists q : Qc, perm_valid q /\
        phUnion (phUnion ph1 ph2) ph3 (F1 y) = PHCproc q (F2 y)). {
    intros y HC5. generalize HC5. intro HC6.
    apply HC3 in HC5. apply HC4 in HC6.
    destruct HC5 as (q'&G1&HC5).
    red in D3. red in D3. specialize D3 with (F1 y).
    rewrite HC5 in D3. red in D3.
    destruct HC6 as [HC6|(q''&G2&HC6)]; vauto.
    - rewrite HC6 in D3. desf.
      exists q'. intuition.
      rewrite <- phUnion_cell.
      rewrite HC6. by rewrite phcUnion_free_l.
    - rewrite HC6 in D3. desf.
      exists (q' + q''). intuition vauto.
      * by apply perm_add_valid.
      * rewrite <- phUnion_cell.
        rewrite HC5, HC6.
        unfold phcUnion. desf. }
  assert (HCL5 : forall l : Val, In l ls ->
      exists q v, perm_valid q /\
        phUnion (phUnion ph1 ph2) ph3 l = PHCproc q v). {
    intros l HCL5. subst ls. apply in_map_iff in HCL5.
    destruct HCL5 as (y&?&HCL5). desf.
    apply HC5 in HCL5. destruct HCL5 as (q'&?&?).
    exists q'. intuition vauto. }

  (* results of concretisations of heap locations under [F1] and [F2] *)
  assert (CSV1 : forall y : ProcVar, In y xs -> phcConcr (ph1 (F1 y)) = Some (F2 y)). {
    intros y CSV1. apply HC1 in CSV1.
    destruct CSV1 as (q'&?&CSV1). by rewrite CSV1. }
  assert (CSV2 : forall y : ProcVar, In y xs -> phcConcr (phUnion ph1 ph2 (F1 y)) = Some (F2 y)). {
    intros y CSV2. apply HC3 in CSV2.
    destruct CSV2 as (q'&?&CSV2). by rewrite CSV2. }
  assert (CSV3 : forall y : ProcVar, In y xs -> phcConcr (phUnion (phUnion ph1 ph2) ph3 (F1 y)) = Some (F2 y)). {
    intros y CSV3. apply HC5 in CSV3.
    destruct CSV3 as (q'&?&CSV3). by rewrite CSV3. }

  (* results concerning snapshots of heap locations under [F1] and [F2] *)
  assert (CS1 : forall y : ProcVar, In y xs -> phcConcr (ph1 (F1 y)) = phcSnapshot (ph1 (F1 y))). {
    intros y CS1. apply HC1 in CS1.
    destruct CS1 as (q'&?&CS1).
    by rewrite CS1. }
  assert (CS2 : forall y : ProcVar, In y xs -> phcConcr (ph2 (F1 y)) = phcSnapshot (ph2 (F1 y))). {
    intros y CS2. apply HC2 in CS2.
    destruct CS2 as [CS2|(q'&?&CS2)]; by rewrite CS2. }
  assert (CS3 : forall y : ProcVar, In y xs -> phcConcr (phUnion ph1 ph2 (F1 y)) = phcSnapshot (phUnion ph1 ph2 (F1 y))). {
    intros y CS3. apply HC3 in CS3.
    destruct CS3 as (q'&?&CS3).
    by rewrite CS3. }
  assert (CS4 : forall y : ProcVar, In y xs -> phcConcr (ph3 (F1 y)) = phcSnapshot (ph3 (F1 y))). {
    intros y CS4. apply HC4 in CS4.
    destruct CS4 as [CS4|(q'&?&CS4)]; by rewrite CS4. }
  assert (CS5 : forall y : ProcVar, In y xs -> phcConcr (phUnion (phUnion ph1 ph2) ph3 (F1 y)) = phcSnapshot (phUnion (phUnion ph1 ph2) ph3 (F1 y))). {
    intros y CS5. apply HC5 in CS5.
    destruct CS5 as (q'&?&CS5).
    by rewrite CS5. }

  (* the entry [pm pid] is safe with the assumed snapshot heap *)
  assert (PMS1 : pmeSafe (phSnapshot (phUnion (phUnion ph1 ph2) ph3)) (pm pid)). {
    red in S1. by apply S1. }

  repeat split; vauto.

  (* (2) absence of faults -- three possible cases *)
  - red. intros phF pmF D1 D2 FIN1 FIN2 ABORT1.

    (* [pm + pmF pid] contains the expected entry *)
    assert (PS6 : exists q4 P4,
        pmeBisim (pmeUnion (pm pid) (pmF pid)) (PEelem q4 (Ppar (Ppar (Ppar (Ppar (Palt (Pseq (Passert CB) CP) CQ) P1) P2) P3) P4) xs F1)). {
      red in D2. red in D2. specialize D2 with pid.
      rewrite PS4 in D2.
      red in D2. repeat desf; vauto.
      - exists (q3 + q0), P.
        rewrite PS4. unfold pmeUnion. by desf.
      - exists q3, Pepsilon. rewrite PS4.
        rewrite pmeUnion_free_l.
        by rewrite bisim_par_epsilon_r. }
    destruct PS6 as (q4&P4&PS6).

    (* the heap together with [phF] contains an element at every location corresponding to variables in [xs] *)
    assert (HC6 : forall y : ProcVar, In y xs ->
        phF (F1 y) = PHCfree \/
        exists q, perm_valid q /\ phF (F1 y) = PHCproc q (F2 y)). {
      intros y HC6. apply HC5 in HC6.
      destruct HC6 as (q'&?&HC6).
      red in D1. red in D1. specialize D1 with (F1 y).
      rewrite HC6 in D1. red in D1.
      repeat desf; vauto. right.
      exists q0. intuition vauto.
      by apply perm_disj_valid_r in D1. }
    assert (HCL6 : forall l : Val, In l ls ->
      phF l = PHCfree \/
      exists q v, perm_valid q /\ phF l = PHCproc q v). {
      intros l HCL6. subst ls. apply in_map_iff in HCL6.
      destruct HCL6 as (y&?&HCL6). clarify.
      apply HC6 in HCL6. destruct HCL6 as [HCL6|(q'&?&HCL6)]; vauto.
      right. exists q', (F2 y). split; vauto. }
    assert (HC7 : forall y : ProcVar, In y xs ->
        exists q : Qc, perm_valid q /\
          phUnion (phUnion (phUnion ph1 ph2) ph3) phF (F1 y) = PHCproc q (F2 y)). {
      intros y HC7. generalize HC7. intro HC7'.
      apply HC5 in HC7. apply HC6 in HC7'.
      destruct HC7 as (q'&G1&HC7).
      red in D1. red in D1. specialize D1 with (F1 y).
      rewrite HC7 in D1. red in D1.
      destruct HC7' as [HC7'|(q''&G2&HC7')]; vauto.
      - rewrite HC7' in D1. desf.
        exists q'. intuition.
        rewrite <- phUnion_cell.
        rewrite HC7'. by rewrite phcUnion_free_l.
      - rewrite HC7' in D1. desf.
        exists (q' + q''). intuition vauto.
        * by apply perm_add_valid.
        * rewrite <- phUnion_cell.
          rewrite HC7, HC7'. unfold phcUnion. desf. }
    assert (HCL7 : forall l : Val, In l ls ->
        exists q v, perm_valid q /\
          phUnion (phUnion (phUnion ph1 ph2) ph3) phF l = PHCproc q v). {
      intros l HCL7. subst ls. apply in_map_iff in HCL7.
      destruct HCL7 as (y&?&HCL7). desf.
      apply HC7 in HCL7. destruct HCL7 as (q'&?&?).
      exists q'. intuition vauto. }

    inv ABORT1; clear ABORT1.

    (* case 1: the process map does not contain an entry at [pid] *)
    + apply H4. clear H4.
      subst pid0. replace (g x) with pid; [|done]. 
      unfold pmUnion. rewrite PS6. vauto.

    (* case 2: not all process variables in [xs] are covered by the concrete heap *)
    + destruct H5 as (y&H6&H7).

      (* we first have to establish that [q0 = q3], [xs0 = xs], etc. *)
      rename H0 into H5. unfold pmUnion in H5.
      subst pid0. replace (g x) with pid in *; [|done].
      rewrite PS6 in H5. red in H5. repeat desf.
      rename xs0 into xs.

      (* [f] and [F1] agree in all values in [xs] *)
      assert (PC1 : forall y : ProcVar, In y xs -> f y = F1 y). {
        intros. apply map_eq_In with xs; vauto. }

      (* complete the proof *)
      generalize H6. intro H6'.
      apply HC7 in H6. clear HC7.
      destruct H6 as (q'&H6&H8).
      apply PC1 in H6'. clarify. clear PC1.
      rewrite H6' in H7. clear H6'.
      unfold phConcr in H7.
      rewrite H8 in H7. vauto.

    (* case 3: the process can not make a synchronising reduction step *)
    + subst pid0. replace (g x) with pid in *; [|done].
      unfold pmUnion in H0. rewrite PS6 in H0.
      unfold pmeBisim in H0. desf.
      rename xs0 into xs.

      (* [f] and [F1] agree in all values in [xs] *)
      assert (PC1 : forall y : ProcVar, In y xs -> f y = F1 y). {
        intros. apply map_eq_In with xs; vauto. }

      (* results of concretisations and snapshots of heap locations under [F1] *)
      assert (CSV4 : forall y : ProcVar, In y xs -> phcConcr (phUnion (phUnion (phUnion ph1 ph2) ph3) phF (F1 y)) = Some (F2 y)). {
        intros y CSV4. apply HC7 in CSV4.
        destruct CSV4 as (q'&?&CSV4). by rewrite CSV4. }
      assert (CS6 : forall y : ProcVar, In y xs -> phcConcr (phUnion (phUnion (phUnion ph1 ph2) ph3) phF (F1 y)) = phcSnapshot (phUnion (phUnion (phUnion ph1 ph2) ph3) phF (F1 y))). {
        intros y CS6. apply HC7 in CS6.
        destruct CS6 as (q'&?&CS6).
        by rewrite CS6. }

      (* the process [?CB . CP || CQ || ...] is safe with [ps] *)
      assert (PMS2 : psafe (Ppar (Ppar (Ppar (Palt (Pseq (Passert CB) CP) CQ) P1) P2) P3) ps). {
        rewrite PS4 in PMS1.
        red in PMS1. apply PMS1. clear PMS1.
        intros y H8. unfold phSnapshot.
        rewrite <- CS5; [|done].
        rewrite CSV3; [|done].
        rewrite <- H1; [|done].
        rewrite PC1; [|done]. unfold phConcr.
        by rewrite <- CSV4. }

      inv PMS2. clear PMS2. destruct H as (PMS2&_).

      (* more specifically, [?CB] does not fault *)
      assert (PMS3 : ~ pfault (Passert CB) ps). {
        intro PMS3. apply PMS2. repeat apply pfault_par_l.
        apply pfault_alt_l. by apply pfault_seq_l. }

      clear PMS2. apply passn_nfault in PMS3.

      (* the process [?CB . CP || CQ || ...] can make an assertion step *)
      assert (PMS4 : pstep (Ppar (Ppar (Ppar (Ppar (Palt (Pseq (Passert CB) CP) CQ) P1) P2) P3) P4) ps PLassert (Ppar (Ppar (Ppar (Ppar (Pseq Pepsilon CP) P1) P2) P3) P4) ps). {
        repeat apply pstep_par_l.
        apply pstep_alt_l.
        apply pstep_seq_l.
        by apply pstep_assert. }

      (* finish the proof *)
      inv H2. clear H2. destruct H as (_&_&PMS5&_).
      apply PMS5 in PMS4. clear PMS5.
      destruct PMS4 as (P'&PMS4&PMS5).
      apply H6. by exists P'.

  (* (5) program step *)
  - simpl. intros phJ phF pmJ pmF pmC h' s' C'
      G1 G2 G3 G4 H1 FIN1 WS1 INV FIN2 COV1 PSAFE1 STEP.
    inv STEP.
    exists (phUnion (phUnion ph1 ph2) ph3), phJ.
    intuition.

    (* [pm + pmJ pid] contains the expected entry *)
    assert (PS6 : exists q4 P4,
        pmeBisim (pmeUnion (pm pid) (pmJ pid)) (PEelem q4 (Ppar (Ppar (Ppar (Ppar (Palt (Pseq (Passert CB) CP) CQ) P1) P2) P3) P4) xs F1) /\
        (pmJ pid = PEfree /\ q3 = q4 /\ P4 = Pepsilon \/
        exists q4', pmeBisim (pmJ pid) (PEelem q4' P4 xs F1) /\ q4 = q3 + q4')). {
      red in G3. red in G3. specialize G3 with pid.
      rewrite PS4 in G3.
      red in G3. repeat desf; vauto.
      - exists (q3 + q0), P.
        rewrite PS4. unfold pmeUnion.
        intuition desf. right.
        exists q0. intuition vauto.
      - exists q3, Pepsilon. rewrite PS4.
        rewrite pmeUnion_free_l. intuition vauto.
        by rewrite bisim_par_epsilon_r. }
    destruct PS6 as (q4&P4&PS6&PS6').
    apply wrap in PS6'.

    (* [pm + pmJ + pmF pid] contains the expected entry *)
    assert (PS7 : exists q5 P5,
        pmeBisim (pmeUnion (pmUnion pm pmJ pid) (pmF pid)) (PEelem q5 (Ppar (Ppar (Ppar (Ppar (Ppar (Palt (Pseq (Passert CB) CP) CQ) P1) P2) P3) P4) P5) xs F1) /\
        (pmF pid = PEfree /\ q4 = q5 /\ P5 = Pepsilon \/
        exists q5', pmeBisim (pmF pid) (PEelem q5' P5 xs F1) /\ q5 = q4 + q5')). {
      rewrite pmUnion_elem.
      red in G4. red in G4. specialize G4 with pid.
      rewrite PS6 in G4.
      red in G4. repeat desf; vauto.
      - exists (q4 + q0), P.
        rewrite <- pmUnion_elem.
        rewrite PS6. unfold pmeUnion.
        intuition desf. right.
        exists q0. intuition vauto.
      - exists q4, Pepsilon.
        rewrite <- pmUnion_elem. rewrite PS6.
        rewrite Heq. rewrite pmeUnion_free_l.
        intuition vauto.
        by rewrite bisim_par_epsilon_r. }
    destruct PS7 as (q5&P5&PS7&PS7').
    apply wrap in PS7'.

    (* the heap together with [phF] contains an element at every location corresponding to variables in [xs] *)
    assert (HC6 : forall y : ProcVar, In y xs ->
        phJ (F1 y) = PHCfree \/
        exists q, perm_valid q /\ phJ (F1 y) = PHCproc q (F2 y)). {
      intros y HC6. apply HC5 in HC6.
      destruct HC6 as (q'&?&HC6).
      red in G1. red in G1. specialize G1 with (F1 y).
      rewrite HC6 in G1. red in G1.
      repeat desf; vauto. right.
      exists q0. intuition vauto.
      by apply perm_disj_valid_r in G1. }
    assert (HCL6 : forall l : Val, In l ls ->
      phJ l = PHCfree \/
      exists q v, perm_valid q /\ phJ l = PHCproc q v). {
      intros l HCL6. subst ls. apply in_map_iff in HCL6.
      destruct HCL6 as (y&?&HCL6). clarify.
      apply HC6 in HCL6. destruct HCL6 as [HCL6|(q'&?&HCL6)]; vauto.
      right. exists q', (F2 y). split; vauto. }
    assert (HC7 : forall y : ProcVar, In y xs ->
        exists q : Qc, perm_valid q /\
          phUnion (phUnion (phUnion ph1 ph2) ph3) phJ (F1 y) = PHCproc q (F2 y)). {
      intros y HC7. generalize HC7. intro HC7'.
      apply HC5 in HC7. apply HC6 in HC7'.
      destruct HC7 as (q'&K1&HC7).
      red in G1. red in G1. specialize G1 with (F1 y).
      rewrite HC7 in G1. red in G1.
      destruct HC7' as [HC7'|(q''&K2&HC7')]; vauto.
      - rewrite HC7' in G1. desf.
        exists q'. intuition.
        rewrite <- phUnion_cell.
        rewrite HC7'. by rewrite phcUnion_free_l.
      - rewrite HC7' in G1. desf.
        exists (q' + q''). intuition vauto.
        * by apply perm_add_valid.
        * rewrite <- phUnion_cell.
          rewrite HC7, HC7'. unfold phcUnion.
          by desf. }
    assert (HCL7 : forall l : Val, In l ls ->
        exists q v, perm_valid q /\
        phUnion (phUnion (phUnion ph1 ph2) ph3) phJ l = PHCproc q v). {
      intros l HCL7. subst ls. apply in_map_iff in HCL7.
      destruct HCL7 as (y&?&HCL7). desf.
      apply HC7 in HCL7. destruct HCL7 as (q'&?&?).
      exists q'. intuition vauto. }
    assert (HC8 : forall y : ProcVar, In y xs ->
        phF (F1 y) = PHCfree \/
        exists q, perm_valid q /\ phF (F1 y) = PHCproc q (F2 y)). {
      intros y HC8. apply HC7 in HC8.
      destruct HC8 as (q'&?&HC8).
      red in G2. red in G2. specialize G2 with (F1 y).
      rewrite HC8 in G2. red in G2.
      repeat desf; vauto. right.
      exists q0. intuition vauto.
      by apply perm_disj_valid_r in G2. }
    assert (HCL8 : forall l : Val, In l ls ->
        phF l = PHCfree \/
        exists q v, perm_valid q /\ phF l = PHCproc q v). {
      intros l HCL8. subst ls. apply in_map_iff in HCL8.
      destruct HCL8 as (y&?&HCL8). clarify.
      apply HC8 in HCL8.
      destruct HCL8 as [HCL8|(q'&?&HCL8)]; vauto.
      right. exists q', (F2 y). split; vauto. }
    assert (HC9 : forall y : ProcVar, In y xs ->
        exists q : Qc, perm_valid q /\
        (phUnion (phUnion (phUnion (phUnion ph1 ph2) ph3) phJ) phF) (F1 y) = PHCproc q (F2 y)). {
      intros y HC9. generalize HC9. intro HC9'.
      apply HC7 in HC9. apply HC8 in HC9'.
      destruct HC9 as (q'&K1&HC9).
      red in G2. red in G2. specialize G2 with (F1 y).
      rewrite HC9 in G2. red in G2.
      destruct HC9' as [HC9'|(q''&K2&HC9')]; vauto.
      - rewrite HC9' in G2. desf.
        exists q'. intuition.
        rewrite <- phUnion_cell.
        rewrite HC9'. by rewrite phcUnion_free_l.
      - rewrite HC9' in G2. desf.
        exists (q' + q''). intuition vauto.
        * by apply perm_add_valid.
        * rewrite <- phUnion_cell.
          rewrite HC9, HC9'. unfold phcUnion.
          by desf. }
    assert (HCL9 : forall l : Val, In l ls ->
        exists q v, perm_valid q /\
        phUnion (phUnion (phUnion (phUnion ph1 ph2) ph3) phJ) phF l = PHCproc q v). {
      intros l HCL9. subst ls. apply in_map_iff in HCL9.
      destruct HCL9 as (y&?&HCL9). desf.
      apply HC9 in HCL9. destruct HCL9 as (q'&?&?).
      exists q'. intuition vauto. }

    (* results of concretisations of heap locations under [F1] *)
    assert (CSV4 : forall y : ProcVar, In y xs -> phcConcr (phUnion (phUnion (phUnion ph1 ph2) ph3) phJ (F1 y)) = Some (F2 y)). {
      intros y CSV4. apply HC7 in CSV4.
      destruct CSV4 as (q'&?&CSV4). by rewrite CSV4. }
    assert (CSV5 : forall y : ProcVar, In y xs -> phcConcr (phUnion (phUnion (phUnion (phUnion ph1 ph2) ph3) phJ) phF (F1 y)) = Some (F2 y)). {
      intros y CSV5. apply HC9 in CSV5.
      destruct CSV5 as (q'&?&CSV5). by rewrite CSV5. }

    (* results of snapshots of heap locations under [F1] *)
    assert (CS6 : forall y : ProcVar, In y xs -> phcConcr (phUnion (phUnion (phUnion ph1 ph2) ph3) phJ (F1 y)) = phcSnapshot (phUnion (phUnion (phUnion ph1 ph2) ph3) phJ (F1 y))). {
      intros y CS6. apply HC7 in CS6.
      destruct CS6 as (q'&?&CS6).
      by rewrite CS6. }
    assert (CS7 : forall y : ProcVar, In y xs -> phcConcr (phUnion (phUnion (phUnion (phUnion ph1 ph2) ph3) phJ) phF (F1 y)) = phcSnapshot (phUnion (phUnion (phUnion (phUnion ph1 ph2) ph3) phJ) phF (F1 y))). {
      intros y CS7. apply HC9 in CS7.
      destruct CS7 as (q'&?&CS7).
      by rewrite CS7. }

    (* the process [?CB . CP || CQ || ...] is safe with [ps] *)
    assert (PMS2 : psafe (Ppar (Ppar (Ppar (Palt (Pseq (Passert CB) CP) CQ) P1) P2) P3) F2). {
      rewrite PS4 in PMS1.
      red in PMS1. apply PMS1. clear PMS1.
      intros y H8. unfold phSnapshot.
      rewrite <- CS5; [|done].
      by rewrite CSV3. }

    inv PMS2. clear PMS2. destruct H as (PMS2&_).

    (* more specifically, [?CB] does not fault *)
    assert (PMS3 : ~ pfault (Passert CB) F2). {
      intro PMS3. apply PMS2. repeat apply pfault_par_l.
      apply pfault_alt_l. by apply pfault_seq_l. }

    clear PMS2. apply passn_nfault in PMS3.
    rename PMS3 into PMS2.

    (* the process [?CB . CP || CQ || ...] can make an assertion step *)
    assert (PSTEP1 : forall ps,
        (forall x : ProcVar, In x xs -> phSnapshot ph1 (F1 x) = Some (ps x)) ->
        pstep (Passert CB) ps PLassert Pepsilon ps). {
      intros ps K1.
      apply pstep_assert.
      rewrite pcond_agree with (s2 := F2); [done|].
      intros y K2.
      apply IN3 in K2.
      generalize K2. intro K2'.
      apply K1 in K2. clear K1.
      unfold phSnapshot in K2.
      rewrite <- CS1 in K2; [|done].
      rewrite CSV1 in K2; [|done]. vauto. }
    assert (PMS3 : forall ps,
        (forall x : ProcVar, In x xs -> phSnapshot (phUnion (phUnion (phUnion ph1 ph2) ph3) phJ) (F1 x) = Some (ps x)) ->
        pstep (Ppar (Ppar (Ppar (Ppar (Palt (Pseq (Passert CB) CP) CQ) P1) P2) P3) P4) ps PLassert (Ppar (Ppar (Ppar (Ppar (Pseq Pepsilon CP) P1) P2) P3) P4) ps). {
      intros ps K1.
      repeat apply pstep_par_l.
      apply pstep_alt_l.
      apply pstep_seq_l.
      apply PSTEP1.
      intros y K2.
      generalize K2. intro K2'.
      apply K1 in K2. clear K1.
      unfold phSnapshot. unfold phSnapshot in K2.
      rewrite <- CS1; [|done].
      rewrite CSV1; [|done].
      rewrite <- CSV4; [|done].
      by rewrite CS6. }
    assert (PMS3' : forall ps,
        (forall x : ProcVar, In x xs -> phSnapshot (phUnion (phUnion (phUnion (phUnion ph1 ph2) ph3) phJ) phF) (F1 x) = Some (ps x)) ->
        pstep (Ppar (Ppar (Ppar (Ppar (Ppar (Palt (Pseq (Passert CB) CP) CQ) P1) P2) P3) P4) P5) ps PLassert (Ppar (Ppar (Ppar (Ppar (Ppar (Pseq Pepsilon CP) P1) P2) P3) P4) P5) ps). {
      intros ps K1.
      apply pstep_par_l.
      apply PMS3. clear PMS3.
      intros y K2.
      unfold phSnapshot.
      rewrite <- CS6; [|done].
      rewrite CSV4; [|done].
      rewrite <- CSV5; [|done].
      rewrite CS7; [|done].
      by apply K1. }

    (* construct a new version of [pm2] and [pmC] *)
    pose (pm2' := pmUpdate pm2 pid (PEelem q1 (Ppar CP P1) xs F1)).
    pose (pmC' := pmUnion (pmUnion (pmUnion (pmUnion pm1 pm2') pm3) pmJ) pmF).
    pose (pmC'' := pmUpdate pmC pid (PEelem q5 (Ppar (Ppar (Ppar (Ppar (Ppar (Pseq Pepsilon CP) P1) P2) P3) P4) P5) xs F1)).

    (* agreement of [pm2] with [pm2'] *)
    assert (PAGR1 : pmAgree pm2 pm2'). {
      subst pm2'. intro pid'.
      unfold pmUpdate, update. desf.
      rewrite PS1. vauto. }

    (* agreemment of [pmC] and pmC' *)
    assert (PAGR2 : pmAgree pmC pmC'). {
      rewrite <- H1. clear H1.
      rewrite <- D6. clear D6.
      rewrite <- D11. clear D11.
      subst pmC'. by rewrite PAGR1. }

    (* bisimulation equivalences of the updated process maps [pm2'] and [pmC'] *)
    assert (NPS1 : pmeBisim (pmUnion pm1 pm2' pid) (PEelem q2 (Ppar (Ppar CP P1) P2) xs F1)). {
      rewrite <- pmUnion_elem.
      subst pm2'. unfold pmUpdate.
      rewrite update_apply.
      apply unwrap in PS2'.
      destruct PS2' as [(PS2'&?&?)|(q2'&PS2'&PS2'')]; vauto.
      - rewrite PS2'. rewrite pmeUnion_free_r.
        by rewrite bisim_par_epsilon_r.
      - rewrite PS2'. unfold pmeUnion. desf.
        by rewrite bisim_par_comm. }
    assert (NPS2 : pmeBisim (pmUnion (pmUnion pm1 pm2') pm3 pid) (PEelem q3 (Ppar (Ppar (Ppar CP P1) P2) P3) xs F1)). {
      rewrite <- pmUnion_elem.
      rewrite NPS1. apply unwrap in PS4'.
      destruct PS4' as [(PS4'&?&?)|(q4'&PS4'&PS4'')]; vauto.
      - rewrite PS4'. rewrite pmeUnion_free_l.
        by rewrite bisim_par_epsilon_r.
      - rewrite PS4'. unfold pmeUnion. desf. }
    assert (NPS3 : pmeBisim (pmUnion (pmUnion (pmUnion pm1 pm2') pm3) pmJ pid) (PEelem q4 (Ppar (Ppar (Ppar (Ppar CP P1) P2) P3) P4) xs F1)). {
      rewrite <- pmUnion_elem.
      rewrite NPS2. apply unwrap in PS6'.
      destruct PS6' as [(PS6'&?&?)|(q4'&PS6'&PS6'')]; vauto.
      - rewrite PS6'. rewrite pmeUnion_free_l.
        by rewrite bisim_par_epsilon_r.
      - rewrite PS6'. unfold pmeUnion. desf. }
    assert (NPS4 : pmeBisim (pmUnion (pmUnion (pmUnion (pmUnion pm1 pm2') pm3) pmJ) pmF pid) (PEelem q5 (Ppar (Ppar (Ppar (Ppar (Ppar CP P1) P2) P3) P4) P5) xs F1)). {
      rewrite <- pmUnion_elem.
      rewrite NPS3. apply unwrap in PS7'.
      destruct PS7' as [(PS7'&?&?)|(q4'&PS7'&PS7'')]; vauto.
      - rewrite PS7'. rewrite pmeUnion_free_l.
        by rewrite bisim_par_epsilon_r.
      - rewrite PS7'. unfold pmeUnion. desf. }

    (* relations between [pmC'] and [pmC''] *)
    assert (PEQ1 : pmeBisim (pmC' pid) (pmC'' pid)). {
      subst pmC' pmC''.
      unfold pmUpdate. rewrite update_apply.
      rewrite bisim_seq_epsilon_r.
      by rewrite NPS4. }
    assert (PEQ2 : forall pid', pid <> pid' -> pmeBisim (pmC' pid') (pmC'' pid')). {
      intros pid' K1.
      subst pmC' pmC''.
      unfold pmUpdate, update. desf.
      repeat rewrite <- pmUnion_elem.
      subst pm2'.
      unfold pmUpdate, update. desf.
      rewrite <- H1.
      apply pmeUnion_bisim_l.
      rewrite <- pmUnion_elem.
      apply pmeUnion_bisim_l.
      rewrite <- D6.
      rewrite <- pmUnion_elem.
      apply pmeUnion_bisim_l.
      rewrite <- D11.
      rewrite <- pmUnion_elem.
      by apply pmeUnion_bisim_l. }
    assert (PEQ3 : pmBisim pmC' pmC''). {
      intros pid'.
      assert (K1 : pid = pid' \/ pid <> pid') by apply classic.
      destruct K1 as [K1|K1]; vauto.
      by apply PEQ2. }

    (* the process [?CB . CP + CQ || P1 || ...] is safe with [F2] *)
    assert (PMS4 : forall ps,
        (forall x : ProcVar, In x xs -> phSnapshot (phUnion (phUnion (phUnion (phUnion ph1 ph2) ph3) phJ) phF) (F1 x) = Some (ps x)) ->
        psafe (Ppar (Ppar (Ppar (Ppar (Ppar (Palt (Pseq (Passert CB) CP) CQ) P1) P2) P3) P4) P5) ps). {
      intros ps K1.
      red in PSAFE1. specialize PSAFE1 with pid.
      rewrite <- H1 in PSAFE1.
      rewrite <- pmUnion_elem in PSAFE1.
      rewrite PS7 in PSAFE1.
      red in PSAFE1. apply PSAFE1.
      intros y K2. by apply K1. }

    (* the composite process is still safe after performing the assertion step *)
    assert (PMS5 : forall ps,
        (forall x : ProcVar, In x xs -> phSnapshot (phUnion (phUnion (phUnion (phUnion ph1 ph2) ph3) phJ) phF) (F1 x) = Some (ps x)) ->
        psafe (Ppar (Ppar (Ppar (Ppar (Ppar CP P1) P2) P3) P4) P5) ps). {
      intros ps K1.
      generalize K1. intro K1'.
      apply PMS4 in K1. clear PMS4.
      inv K1. clear K1. destruct H as (_&K1).
      apply PMS3' in K1'. clear PMS3'.
      apply K1 in K1'. clear K1.
      by rewrite bisim_seq_epsilon_r in K1'. }

    (* the entry [pmC' pid] is safe *)
    assert (PMS6 : pmeSafe (phSnapshot (phUnion (phUnion (phUnion (phUnion ph1 ph2) ph3) phJ) phF)) (pmC' pid)). {
      subst pmC'. rewrite NPS4. red. desf. }

    (* [pmC] and [pmC'] are the same on all entries but [pid] *)
    assert (PFV1 : forall pid', pid <> pid' -> pmeBisim (pmC pid') (pmC' pid')). {
      intros pid' K1. subst pmC'.
      repeat rewrite <- pmUnion_elem.
      subst pm2'. unfold pmUpdate, update. desf.
      rewrite <- H1.
      repeat rewrite <- pmUnion_elem.
      repeat apply pmeUnion_bisim_l; auto.
      rewrite <- D6.
      rewrite <- pmUnion_elem.
      apply pmeUnion_bisim_l; auto.
      rewrite <- D11.
      rewrite <- pmUnion_elem.
      by apply pmeUnion_bisim_l; auto. }

    (* [pmC'] is safe with the snapshot heap under subject *)
    assert (PMS8 : pmSafe (phSnapshot (phUnion (phUnion (phUnion (phUnion ph1 ph2) ph3) phJ) phF)) pmC'). {
      intro pid'.
      assert (K1 : pid = pid' \/ pid <> pid') by apply classic.
      destruct K1 as [K1|K1]; vauto.
      apply PFV1 in K1.
      by rewrite <- K1. }

    exists (pmUnion (pmUnion pm1 pm2') pm3).
    exists pmJ.
    exists pmC''.
    repeat split; vauto.

    1:{ (* [pm1 + pm2' + pm3] is disjoint with [pmJ] *)
      rewrite <- PAGR1.
      rewrite D11.
      by rewrite D6. }

    1:{ (* [pm1 + pm2 + pm3 + pmJ] is disjoint with [pmF] *)
      rewrite <- PAGR1.
      rewrite D11.
      by rewrite D6. }

    1:{ (* [pmC''] is finite *)
      rewrite <- PEQ3.
      by rewrite <- PAGR2. }

    1:{ (* [pmC''] is well-structured *)
      rewrite <- PEQ3.
      by rewrite <- PAGR2. }

    1:{ (* [pmC''] still covers the snapshot heap *)
      rewrite <- PEQ3.
      by rewrite <- PAGR2. }

    1:{ (* [pmC''] is safe with the snapshot heap *)
      by rewrite <- PEQ3. }

    exists g, Cskip.
    repeat split; vauto.

    1:{ (* the ghost semantics can make a matching step *)
      subst pmC''.
      apply gstep_query with (P:=Ppar (Ppar (Ppar (Ppar (Ppar (Palt (Pseq (Passert CB) CP) CQ) P1) P2) P3) P4) P5)(ps:=F2); vauto.
      - subst pid.
        rewrite <- H1.
        rewrite <- pmUnion_elem.
        by rewrite PS7.
      - apply PMS3'; vauto.
        intros y K1.
        unfold phSnapshot.
        rewrite <- CS7; [|done].
        by rewrite CSV5. }

    apply safe_done.
    exists (phUnion ph1 ph2), ph3.
    intuition vauto.
    exists (pmUnion pm1 pm2'), pm3.
    intuition vauto.

    1:{ (* [pm1 + pm2'] are disjoint with [pm3] *)
      rewrite <- PAGR1.
      by rewrite D11. }

    exists (phUnion ph1 ph2), phIden.
    intuition vauto.

    1:{ (* [ph1 + ph2] is disjoint with the identity heap *)
      phsolve. }

    1:{ (* [ph1 + ph2 + phIden] equals [ph1 + ph2] *)
      by rewrite phUnion_iden_l. }

    exists (pmUnion pm1 pm2'), pmIden.
    intuition vauto.

    1:{ (* [pm1 + pm2'] is disjoint with the identity map *)
      rewrite <- PAGR1. pmsolve. }

    1:{ (* [pm1 + pm2' + pmIden] equals [pm1 + pm2'] *)
      by rewrite pmUnion_iden_l. }

    exists ph1, ph2. intuition vauto.
    exists pm1, pm2'. intuition vauto.

    1:{ (* [pm1] is disjoint with [pm2'] *)
      by rewrite <- PAGR1. }

    1:{ (* the process ownership predicate is established *)
      unfold sat.
      apply unwrap in PS1'.
      destruct PS1' as [(K1&K2&K3)|(q1'&K1&K2)]; vauto.
      (* [P1] does not have any behaviour *)
      - exists PEfree. intuition.
        subst pm2' pid F1 CP.
        unfold pmUpdate. rewrite update_apply.
        rewrite bisim_par_epsilon_r.
        by rewrite pmeUnion_free_l.
      (* [P1] has behaviour *)
      - exists c'. intuition vauto.
        rewrite K1. clear K1.
        unfold pmeUnion. desf.
        subst pm2' CP F1.
        unfold pmUpdate.
        by rewrite update_apply. }

    1:{ (* the assertion [B] is satisfied *)
      subst B F2 CB. unfold sat.
      rewrite cHybridise_conv_eval with (ps:=expr_eval_map f2 s'); vauto. }
Qed.

End Soundness.
