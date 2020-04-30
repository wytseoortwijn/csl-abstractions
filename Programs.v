Require Import Bool.
Require Import HahnBase.
Require Import Heaps.
Require Import List.
Require Import Morphisms.
Require Import Permissions.
Require Import Prelude.
Require Import Process.
Require Import ProcMap.
Require Import Setoid.

Import ListNotations.

Set Implicit Arguments.


(** * Programs *)

Module Type Programs
  (dom : Domains)
  (heaps : Heaps dom)
  (procs : Processes dom)
  (procmaps : ProcMaps dom heaps procs).

Export dom heaps procs procmaps.


(** ** Statics *)

(** *** Expressions *)

Inductive Expr :=
  | Econst(v : Val)
  | Evar(x : Var)
  | Eop(E1 E2 : Expr).

Add Search Blacklist "Expr_rect".
Add Search Blacklist "Expr_ind".
Add Search Blacklist "Expr_rec".
Add Search Blacklist "Expr_sind".

(** Below is a helper tactic for doing induction
    on the structure of (program) expressions. *)

Ltac expr_induction E :=
  induction E as [
    (* constants *)
    v|
    (* variables *)
    x|
    (* binary operations *)
    E1 IH1 E2 IH2
  ].

(** Expressions have decidable equality. *)

Lemma expr_eq_dec :
  forall E1 E2 : Expr, { E1 = E2 } + { E1 <> E2 }.
Proof.
  decide equality.
  - apply val_eq_dec.
  - apply var_eq_dec.
Qed.

(** **** Conversions *)

(** The following operation converts process expressions
    to program expressions. *)

Fixpoint pexpr_convert (e : ProcExpr)(f : ProcVar -> Expr) : Expr :=
  match e with
    | PEconst v => Econst v
    | PEvar x => f x
    | PEop e1 e2 => Eop (pexpr_convert e1 f) (pexpr_convert e2 f)
  end.

(** **** Free variables *)

(** Free variables of expressions are defined in the standard way. *)

Fixpoint expr_fv (E : Expr) : list Var :=
   match E with
    | Econst v => []
    | Evar x => [x]
    | Eop E1 E2 => expr_fv E1 ++ expr_fv E2
  end.

Definition expr_map_fv {T} (f : T -> Expr)(x : Var) : Prop :=
  exists t : T, In x (expr_fv (f t)).

(** **** Substitution *)

(** Substitution within expressions is defined in the standard way. *)

Fixpoint expr_subst (x : Var)(E E' : Expr) : Expr :=
  match E' with
    | Econst v => Econst v
    | Evar y => if var_eq_dec x y then E else Evar y
    | Eop E1 E2 => Eop (expr_subst x E E1) (expr_subst x E E2)
  end.

Definition expr_subst_map {T} (x : Var)(E : Expr)(f : T -> Expr) : T -> Expr :=
  fun y : T => expr_subst x E (f y).

(** Standard properties of substitution. *)

Lemma expr_subst_pres :
  forall E1 E2 x, ~ In x (expr_fv E1) -> expr_subst x E2 E1 = E1.
Proof.
  expr_induction E1; intros E x' H; simpls; intuition desf.
  rewrite IH1, IH2; auto.
  - intro H1. apply H. apply in_or_app. by right.
  - intro H1. apply H. apply in_or_app. by left.
Qed.

Lemma expr_subst_pres_map {T} :
  forall (f : T -> Expr) E x,
  ~ expr_map_fv f x -> expr_subst_map x E f = f.
Proof.
  intros f E x H1.
  extensionality t. apply expr_subst_pres.
  intro H2. apply H1. by exists t.
Qed.

Lemma expr_subst_comm :
  forall E x1 x2 E1 E2,
  x1 <> x2 ->
  ~ In x1 (expr_fv E2) ->
  ~ In x2 (expr_fv E1) ->
  expr_subst x1 E1 (expr_subst x2 E2 E) =
  expr_subst x2 E2 (expr_subst x1 E1 E).
Proof.
  expr_induction E; intros x1 x2 E1' E2' H1 H2 H3;
    simpl; vauto.
  (* variables *)
  - destruct (var_eq_dec x1 x), (var_eq_dec x2 x); vauto.
    + simpl. desf. by rewrite expr_subst_pres.
    + simpl. desf. by rewrite expr_subst_pres.
    + simpl. desf.
  (* operations *)
  - by rewrite IH1, IH2.
Qed.

Lemma expr_subst_comm_val :
  forall E x1 x2 v1 v2,
  x1 <> x2 ->
  expr_subst x1 (Econst v1) (expr_subst x2 (Econst v2) E) =
  expr_subst x2 (Econst v2) (expr_subst x1 (Econst v1) E).
Proof.
  intros E c1 c2 v1 v2 H1.
  by rewrite expr_subst_comm.
Qed.


(** *** Hybrid expressions *)

(** Hybrid expressions are expressions that have both
    program variables and process variables (and are thus
    a hybrid between [Expr] and [ProcExpr]). *)

Inductive HExpr :=
  | HEconst(v : Val)
  | HEprocvar(x : ProcVar)
  | HEprogvar(x : Var)
  | HEop(E1 E2 : HExpr).

Add Search Blacklist "HExpr_rect".
Add Search Blacklist "HExpr_ind".
Add Search Blacklist "HExpr_rec".
Add Search Blacklist "HExpr_sind".

(** Below is a helper tactic for doing induction
    on the structure of hybrid expressions. *)

Ltac hexpr_induction E :=
  induction E as [v|x|x|E1 IH1 E2 IH2].

(** **** Free variables *)

(** The following operation determines the set of free
    _program_ variables in a hybrid expression. *)

Fixpoint hexpr_fv (E : HExpr) : list Var :=
  match E with
    | HEconst _ => []
    | HEprocvar _ => []
    | HEprogvar x => [x]
    | HEop E1 E2 => hexpr_fv E1 ++ hexpr_fv E2
  end.

(** And the following is for determining the set of
    free _process_ variables in hybrid expressions *)

Fixpoint hexpr_fpv (E : HExpr) : list ProcVar :=
  match E with
    | HEconst _ => []
    | HEprocvar x => [x]
    | HEprogvar _ => []
    | HEop E1 E2 => hexpr_fpv E1 ++ hexpr_fpv E2
  end.

(** **** Hybridisation *)

(** The following operation allows to make a hybrid expression
    out of an ordinary expression. *)

Fixpoint peHybridise (e : ProcExpr) : HExpr :=
  match e with
    | PEconst v => HEconst v
    | PEvar x => HEprocvar x
    | PEop e1 e2 => HEop (peHybridise e1) (peHybridise e2)
  end.

Fixpoint eHybridise (E : Expr) : HExpr :=
  match E with
    | Econst v => HEconst v
    | Evar x => HEprogvar x
    | Eop E1 E2 => HEop (eHybridise E1) (eHybridise E2)
  end.

(** **** Conversions *)

(** Below is an operation that converts hybrid expressions to
    ordinary program expressions. *)

Fixpoint hexpr_convert (E : HExpr)(f : ProcVar -> Expr) : Expr :=
  match E with
    | HEconst v => Econst v
    | HEprocvar x => f x
    | HEprogvar x => Evar x
    | HEop E1 E2 => Eop (hexpr_convert E1 f) (hexpr_convert E2 f)
  end.


(** *** Conditions *)

Inductive Cond :=
  | Bconst(b : bool)
  | Bnot(B : Cond)
  | Band(B1 B2 : Cond)
  | Beq(E1 E2 : Expr).

Add Search Blacklist "Cond_rect".
Add Search Blacklist "Cond_ind".
Add Search Blacklist "Cond_rec".
Add Search Blacklist "Cond_sind".

(** Below is a helper tactic for doing induction
    on the structure of (program) conditions. *)

Ltac cond_induction B :=
  induction B as [
    (* constant Booleans *)
    b|
    (* negation *)
    B IH|
    (* conjunction *)
    B1 IH1 B2 IH2|
    (* equality *)
    E1 E2
  ].

(** Conditions have decidable equality. *)

Lemma cond_eq_dec :
  forall B1 B2 : Cond, { B1 = B2 } + { B1 <> B2 }.
Proof.
  decide equality.
  - apply bool_dec.
  - apply expr_eq_dec.
  - apply expr_eq_dec.
Qed.

(** Some sugar *)

Definition Bor B1 B2 := Bnot (Band (Bnot B1) (Bnot B2)).
Definition Bimplies B1 B2 := Bor (Bnot B1) B2.
Definition Bequiv B1 B2 := Band (Bimplies B1 B2) (Bimplies B2 B1).


(** **** Conversions *)

(** The following operation converts process conditions
    to program conditions. *)

Fixpoint pcond_convert (b : ProcCond)(f : ProcVar -> Expr) : Cond :=
  match b with
    | PBconst b' => Bconst b'
    | PBnot b' => Bnot (pcond_convert b' f)
    | PBand b1 b2 => Band (pcond_convert b1 f) (pcond_convert b2 f)
    | PBeq e1 e2 => Beq (pexpr_convert e1 f) (pexpr_convert e2 f)
  end.

(** **** Free variables *)

(** Free variables of conditions are defined in the standard way. *)

Fixpoint cond_fv (B : Cond) : list Var :=
   match B with
    | Bconst b => nil
    | Bnot B' => cond_fv B'
    | Band B1 B2 => cond_fv B1 ++ cond_fv B2
    | Beq E1 E2 => expr_fv E1 ++ expr_fv E2
  end.

(** **** Substitution *)

(** Substitution within conditions is defined in the standard way. *)

Fixpoint cond_subst (x : Var)(E : Expr)(B : Cond) : Cond :=
  match B with
    | Bconst b => Bconst b
    | Bnot B' => Bnot (cond_subst x E B')
    | Band B1 B2 => Band (cond_subst x E B1) (cond_subst x E B2)
    | Beq E1 E2 => Beq (expr_subst x E E1) (expr_subst x E E2)
  end.

(** Standard properties of substitution. *)

Lemma cond_subst_pres :
  forall B E x, ~ In x (cond_fv B) -> cond_subst x E B = B.
Proof.
  cond_induction B; intros E x H; simpls.
  - by rewrite IH.
  - rewrite IH1, IH2; intuition.
  - repeat rewrite expr_subst_pres; intuition.
Qed.


(** *** Hybrid conditions *)

(** Hybrid conditions are conditions that have both
    program variables and process variables (and are thus
    a hybrid between [Cond] and [ProcCond]). *)

Inductive HCond :=
  | HBconst(b : bool)
  | HBnot(B : HCond)
  | HBand(B1 B2 : HCond)
  | HBeq(E1 E2 : HExpr).

Add Search Blacklist "HCond_rect".
Add Search Blacklist "HCond_ind".
Add Search Blacklist "HCond_rec".
Add Search Blacklist "HCond_sind".

(** Below is a helper tactic for doing induction
    on the structure of hybrid conditions. *)

Ltac hcond_induction B :=
  induction B as [
    (* constnats *)
    b|
    (* negation *)
    B IH|
    (* conjunction *)
    B1 IH1 B2 IH2|
    (* expression equality *)
    E1 E2
  ].

(** **** Free variables *)

(** The following operation determines the set of free
    _program_ variables in a hybrid condition. *)

Fixpoint hcond_fv (B : HCond) : list Var :=
  match B with
    | HBconst _ => []
    | HBnot B' => hcond_fv B'
    | HBand B1 B2 => hcond_fv B1 ++ hcond_fv B2
    | HBeq E1 E2 => hexpr_fv E1 ++ hexpr_fv E2
  end.

(** And the following operation determines the set of free
    _process_ variables in hybrid conditions. *)

Fixpoint hcond_fpv (B : HCond) : list ProcVar :=
  match B with
    | HBconst _ => []
    | HBnot B' => hcond_fpv B'
    | HBand B1 B2 => hcond_fpv B1 ++ hcond_fpv B2
    | HBeq E1 E2 => hexpr_fpv E1 ++ hexpr_fpv E2
  end.

(** **** Hybridisation *)

(** The following operation enables one to construct hybrid
    conditions out of ordinary (program) conditions. *)

Fixpoint pcHybridise (b : ProcCond) : HCond :=
  match b with
    | PBconst v => HBconst v
    | PBnot b' => HBnot (pcHybridise b')
    | PBand b1 b2 => HBand (pcHybridise b1) (pcHybridise b2)
    | PBeq e1 e2 => HBeq (peHybridise e1) (peHybridise e2)
  end.

Fixpoint cHybridise (B : Cond) : HCond :=
  match B with
    | Bconst v => HBconst v
    | Bnot B' => HBnot (cHybridise B')
    | Band B1 B2 => HBand (cHybridise B1) (cHybridise B2)
    | Beq E1 E2 => HBeq (eHybridise E1) (eHybridise E2)
  end.

(** **** Conversions *)

(** The following operation is for converting hybrid conditions
    to ordinary program conditions. *)

Fixpoint hcond_convert (B : HCond)(f : ProcVar -> Expr) : Cond :=
  match B with
    | HBconst b => Bconst b
    | HBnot B' => Bnot (hcond_convert B' f)
    | HBand B1 B2 => Band (hcond_convert B1 f) (hcond_convert B2 f)
    | HBeq E1 E2 => Beq (hexpr_convert E1 f) (hexpr_convert E2 f)
  end.


(** *** Hybrid processes *)

(** Hybrid processes [P] are ordinary processes in which
    any (Boolean) expression occuring inside [P] may contain
    program variables (in addition to process variables). *)

Inductive HProc :=
  | HPepsilon
  | HPdelta
  | HPact(a : Act)(E : Expr)
  | HPassert(B : HCond)
  | HPseq(P1 P2 : HProc)
  | HPalt(P1 P2 : HProc)
  | HPpar(P1 P2 : HProc)
  | HPlmerge(P1 P2 : HProc)
  | HPsum(f : Val -> HProc)
  | HPcond(B : Cond)(P : HProc)
  | HPiter(P : HProc).

Add Search Blacklist "HProc_rect".
Add Search Blacklist "HProc_ind".
Add Search Blacklist "HProc_rec".
Add Search Blacklist "HProc_sind".

Lemma HPsum_ext :
  forall f f', f = f' -> HPsum f = HPsum f'.
Proof. intuition vauto. Qed.

(** Below is a shorthand tactic for doing induction
    on the inductive structure of hybrid processes. *)

Ltac hproc_induction P :=
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
    B P IH|
    (* iteration *)
    P IH
  ].

(** **** Free variables *)

Fixpoint hproc_fv (P : HProc)(x : Var) : Prop :=
  match P with
    | HPepsilon => False
    | HPdelta => False
    | HPact a E => In x (expr_fv E)
    | HPassert B => In x (hcond_fv B)
    | HPseq Q R => hproc_fv Q x \/ hproc_fv R x
    | HPalt Q R => hproc_fv Q x \/ hproc_fv R x
    | HPpar Q R => hproc_fv Q x \/ hproc_fv R x
    | HPlmerge Q R => hproc_fv Q x \/ hproc_fv R x
    | HPsum f => exists v, hproc_fv (f v) x
    | HPcond B Q => In x (cond_fv B) \/ hproc_fv Q x
    | HPiter Q => hproc_fv Q x
  end.

(** **** Hybridisation *)

(** The following operation enables one to construct a
    hybrid process out of an ordinary process. *)

Fixpoint pHybridise (P : Proc) : HProc :=
  match P with
    | Pepsilon => HPepsilon
    | Pdelta => HPdelta
    | Pact a v => HPact a (Econst v)
    | Passert b => HPassert (pcHybridise b)
    | Pseq Q R => HPseq (pHybridise Q) (pHybridise R)
    | Palt Q R => HPalt (pHybridise Q) (pHybridise R)
    | Ppar Q R => HPpar (pHybridise Q) (pHybridise R)
    | Plmerge Q R => HPlmerge (pHybridise Q) (pHybridise R)
    | Psum f => HPsum (fun v => pHybridise (f v))
    | Pcond b Q => HPcond (Bconst b) (pHybridise Q)
    | Piter Q => HPiter (pHybridise Q)
  end.


(** *** Commands *)

(** Commands are parameterised by a type, which is the type of the
    metadata that is stored in action blocks (see the [Cinact] constructor).
    We later define a ghost operational semantics (in which the metadata
    component is used to maintain extra runtime information
    regarding abstract models. *)

Inductive Cmd (T : Type) :=
  | Cskip
  | Cseq(C1 C2 : Cmd T)
  | Cass(x : Var)(E : Expr)
  | Cread(x : Var)(E : Expr)
  | Cwrite(E1 E2 : Expr)
  | Cite(B : Cond)(C1 C2 : Cmd T)
  | Cwhile(B : Cond)(C : Cmd T)
  | Cpar(C1 C2 : Cmd T)
  | Calloc(x : Var)(E : Expr)
  | Cdispose(E : Expr)
  | Catomic(C : Cmd T)
  | Cinatom(C : Cmd T)
  | Cproc(x : Var)(P : Expr -> HProc)(E : Expr)(xs : list ProcVar)(f : ProcVar -> Expr)
  | Cact(x : Var)(a : Act)(E : Expr)(C : Cmd T)
  | Cinact(m : T)(C : Cmd T)
  | Cquery(x : Var)
  | Cendproc(x : Var).

Add Search Blacklist "Cmd_rect".
Add Search Blacklist "Cmd_ind".
Add Search Blacklist "Cmd_rec".
Add Search Blacklist "Cmd_sind".

Arguments Cskip {_}.
Arguments Cseq {_}.
Arguments Cass {_}.
Arguments Cread {_}.
Arguments Cwrite {_}.
Arguments Cite {_}.
Arguments Cwhile {_}.
Arguments Cpar {_}.
Arguments Calloc {_}.
Arguments Cdispose {_}.
Arguments Catomic {_}.
Arguments Cinatom {_}.
Arguments Cproc {_}.
Arguments Cact {_}.
Arguments Cquery {_}.
Arguments Cinact {_}.
Arguments Cendproc {_}.

(** A shorthand for doing induction over commands: *)

Ltac cmd_induction C :=
  induction C as [|
    (* sequential *)
    C1 IH1 C2 IH2|
    (* assignment *)
    x E|
    (* heap reading *)
    x E|
    (* heap writing *)
    E1 E2|
    (* if-then-else *)
    B C1 IH1 C2 IH2|
    (* while *)
    B C IH|
    (* parallel *)
    C1 IH1 C2 IH2|
    (* heap allocation *)
    x E|
    (* heap disposal *)
    E|
    (* atomics *)
    C IH|
    C IH|
    (* process - init *)
    x Pf E xs f|
    (* action programs *)
    x a E C IH|
    m C IH|
    (* querying *)
    x|
    (* process - end *)
    x
  ].

(** Some standard properties over the structure of commands. *)

Lemma cmd_neg_seq {T} :
  forall C2 C1 : Cmd T, ~ C2 = Cseq C1 C2.
Proof.
  cmd_induction C2; ins. intro. vauto.
  by apply IH2 in H.
Qed.

Lemma cmd_neg_ite_t {T} :
  forall (C1 C2 : Cmd T) B, ~ C1 = Cite B C1 C2.
Proof.
  cmd_induction C1; ins. intro. vauto.
  by apply IH1 in H1.
Qed.

Lemma cmd_neg_ite_f {T} :
  forall (C2 C1 : Cmd T) B, ~ C2 = Cite B C1 C2.
Proof.
  cmd_induction C2; ins. intro. vauto.
  by apply IH2 in H.
Qed.

(** **** Plain commands *)

(** Plain commands are commands without metadata components
    (or, technically, these are commands in which the metadata type is
    fixed and chosen to have only one inhabitant, namely [PMnone]). *)

Inductive PlainMetadata := PMnone.

Add Search Blacklist "PlainMetadata_rec".
Add Search Blacklist "PlainMetadata_ind".
Add Search Blacklist "PlainMetadata_rect".
Add Search Blacklist "PlainMetadata_sind".

Definition PlainCmd : Type := Cmd PlainMetadata.

Fixpoint plain {T} (C : Cmd T) : PlainCmd :=
  match C with
    | Cskip => Cskip
    | Cseq C1 C2 => Cseq (plain C1) (plain C2)
    | Cass x E => Cass x E
    | Cread x E => Cread x E
    | Cwrite E1 E2 => Cwrite E1 E2
    | Cite B C1 C2 => Cite B (plain C1) (plain C2)
    | Cwhile B C' => Cwhile B (plain C')
    | Cpar C1 C2 => Cpar (plain C1) (plain C2)
    | Calloc x E => Calloc x E
    | Cdispose E => Cdispose E
    | Catomic C' => Catomic (plain C')
    | Cinatom C' => Cinatom (plain C')
    | Cproc x P E xs f => Cproc x P E xs f
    | Cact x a E C' => Cact x a E (plain C')
    | Cquery x => Cquery x
    | Cinact _ C' => Cinact PMnone (plain C')
    | Cendproc x => Cendproc x
  end.

Lemma plain_skip {T} :
  forall C : Cmd T, plain C = Cskip -> C = Cskip.
Proof.
  cmd_induction C; intro H; intuition vauto.
Qed.

(** **** User programs *)

(** Any program is a _user program_ if it does not contain
    [Cinact] or [Cinatom] as a subprogram. *)

(** The program [Cinatom C] represents an atomic program [C]
    that is only partially executed. Such programs cannot be written
    by a user but are an artifact of the program dynamics.
    The same holds for [Cinact m C], which describes a partially
    executed action program [C] (and is a specification-only
    command besides). *)

Fixpoint cmd_user {T} (C : Cmd T) : Prop :=
  match C with
    | Cskip => True
    | Cseq C1 C2 => cmd_user C1 /\ cmd_user C2
    | Cass _ _ => True
    | Cread _ _ => True
    | Cwrite _ _ => True
    | Cite _ C1 C2 => cmd_user C1 /\ cmd_user C2
    | Cwhile _ C' => cmd_user C'
    | Cpar C1 C2 => cmd_user C1 /\ cmd_user C2
    | Calloc _ _ => True
    | Cdispose _ => True
    | Catomic C' => cmd_user C'
    | Cinatom _ => False
    | Cproc _ _ _ _ _ => True
    | Cact _ _ _ C' => cmd_user C'
    | Cquery _ => True
    | Cinact _ _ => False
    | Cendproc _ => True
  end.

Lemma cmd_user_plain {T} :
  forall C : Cmd T, cmd_user C = cmd_user (plain C).
Proof.
  cmd_induction C; simpls;
    try (by rewrite IHC1, IHC2);
    by rewrite IH1, IH2.
Qed.

(** **** Locked programs *)

(** Any program is defined to be _locked_
    if it contains [Cinatom] as a subprogram. *)

Fixpoint cmd_locked {T} (C : Cmd T) : Prop :=
  match C with
    | Cseq C1 _ => cmd_locked C1
    | Cpar C1 C2 => cmd_locked C1 \/ cmd_locked C2
    | Cinact _ C1 => cmd_locked C1
    | Cinatom _ => True
    | _ => False
  end.

Lemma cmd_locked_plain {T} :
  forall C : Cmd T, cmd_locked (plain C) = cmd_locked C.
Proof.
  cmd_induction C; ins. by rewrite IH1, IH2.
Qed.

(** **** Well-formed programs *)

(** Any program is defined to be _basic_ if it does not
    contain any process-related commands, and if there are
    no deadlocks in any of its parallel subprograms. *)

(** Any program is _well-formed_ if [C] is basic for every
    subcommand [Cact _ _ C] that occurs in the program, and if
    there are no deadlocks in any of its parallel subprograms,
    likewise to basic programs. *)

Fixpoint cmd_basic {T} (C : Cmd T) : Prop :=
  match C with
    | Cskip => True
    | Cseq C1 C2 => cmd_basic C1 /\ cmd_basic C2
    | Cass _ _ => True
    | Cread _ _ => True
    | Cwrite _ _ => True
    | Cite _ C1 C2 => cmd_basic C1 /\ cmd_basic C2
    | Cwhile _ C' => cmd_basic C'
    | Cpar C1 C2 => cmd_basic C1 /\ cmd_basic C2 /\ ~ (cmd_locked C1 /\ cmd_locked C2)
    | Calloc _ _ => True
    | Cdispose _ => True
    | Catomic C' => cmd_basic C'
    | Cinatom C' => cmd_basic C'
    | Cproc _ _ _ _ _ => False
    | Cact _ _ _ _ => False
    | Cinact _ _ => False
    | Cquery _ => False
    | Cendproc _ => False
  end.

Fixpoint cmd_wf {T} (C : Cmd T) : Prop :=
  match C with
    | Cskip => True
    | Cseq C1 C2 => cmd_wf C1 /\ cmd_wf C2
    | Cass _ _ => True
    | Cread _ _ => True
    | Cwrite _ _ => True
    | Cite _ C1 C2 => cmd_wf C1 /\ cmd_wf C2
    | Cwhile _ C' => cmd_wf C'
    | Cpar C1 C2 => cmd_wf C1 /\ cmd_wf C2 /\ ~ (cmd_locked C1 /\ cmd_locked C2)
    | Calloc _ _ => True
    | Cdispose _ => True
    | Catomic C' => cmd_wf C'
    | Cinatom C' => cmd_wf C'
    | Cproc _ _ _ _ _ => True
    | Cact _ _ _ C' => cmd_basic C'
    | Cinact _ C' => cmd_basic C'
    | Cquery _ => True
    | Cendproc _ => True
  end.

(** Any basic program is well-formed. *)

Lemma cmd_basic_wf {T} :
  forall C : Cmd T, cmd_basic C -> cmd_wf C.
Proof.
  cmd_induction C; intro H; simpls; intuition vauto.
Qed.

(** **** Free variables *)

(** The free variables of commands are defined in the standard way. *)

Fixpoint cmd_fv {T} (C : Cmd T)(x : Var) : Prop :=
  match C with
    | Cskip => False
    | Cass y E
    | Cread y E
    | Calloc y E => x = y \/ In x (expr_fv E)
    | Cwrite E1 E2 => In x (expr_fv E1) \/ In x (expr_fv E2)
    | Cite B C1 C2 => In x (cond_fv B) \/ cmd_fv C1 x \/ cmd_fv C2 x
    | Cwhile B C' => In x (cond_fv B) \/ cmd_fv C' x
    | Cseq C1 C2
    | Cpar C1 C2 => cmd_fv C1 x \/ cmd_fv C2 x
    | Cdispose E => In x (expr_fv E)
    | Catomic C'
    | Cinatom C' => cmd_fv C' x
    | Cproc y P E xs f =>
        x = y \/ In x (expr_fv E) \/ expr_map_fv f x \/
        exists v, hproc_fv (P v) x
    | Cact y _ E C' => x = y \/ In x (expr_fv E) \/ cmd_fv C' x
    | Cinact _ C' => cmd_fv C' x
    | Cquery y => x = y
    | Cendproc y => x = y
  end.

Lemma cmd_fv_plain {T} :
  forall C : Cmd T, cmd_fv C = cmd_fv (plain C).
Proof.
  cmd_induction C; simpls; try (by rewrite IHC1, IHC2).
  - by rewrite IH1, IH2.
  - by rewrite IH1, IH2.
  - by rewrite IH.
  - by rewrite IH1, IH2.
  - by rewrite IH.
Qed.

(** **** Modified variables *)

(** The operation [cmd_mod] captures the set of variables
    that are _modified_ (written to) by a given program,
    and is defined in the standard way (however, note that,
    for later convenience, [cmd_mod] is defined as a predicate,
    rather than a fixpoint operation that yields a list of variables). *)

Fixpoint cmd_mod {T} (C : Cmd T)(x : Var) : Prop :=
  match C with
    | Cskip => False
    | Cass y _
    | Cread y _ => x = y
    | Cwrite _ _ => False
    | Cseq C1 C2
    | Cpar C1 C2
    | Cite _ C1 C2 => cmd_mod C1 x \/ cmd_mod C2 x
    | Cwhile _ C' => cmd_mod C' x
    | Calloc y _ => x = y
    | Cdispose _ => False
    | Catomic C' => cmd_mod C' x
    | Cinatom C' => cmd_mod C' x
    | Cproc y _ _ _ _ => x = y
    | Cact _ _ _ C'
    | Cinact _ C' => cmd_mod C' x
    | Cquery _ => False
    | Cendproc _ => False
  end.

(** All variables written to by [C] occur freely in [C]. *)

Lemma cmd_fv_mod {T} :
  forall (C : Cmd T)(x : Var), cmd_mod C x -> cmd_fv C x.
Proof.
  cmd_induction C; intros y H; simpls; vauto.
  - destruct H as [H|H].
    left. by apply IH1.
    right. by apply IH2.
  - destruct H as [H|H].
    right. left. by apply IH1.
    right. right. by apply IH2.
  - right. by apply IH.
  - destruct H as [H|H].
    left. by apply IH1.
    right. by apply IH2.
  - by apply IH.
  - by apply IH.
  - right. right. by apply IH.
  - by apply IH.
Qed.

Lemma cmd_mod_plain {T} :
  forall C : Cmd T, cmd_mod C = cmd_mod (plain C).
Proof.
  cmd_induction C; simpls; by rewrite IH1, IH2.
Qed.


(** ** Dynamics *)

(** *** Stores *)

Definition Store := Var -> Val.

(** An update operation for stores: *)

Definition sUpdate (s : Store)(x : Var)(v : Val) : Store :=
  update var_eq_dec s x v.

Lemma sUpdate_comm :
  forall s x1 v1 x2 v2,
  x1 <> x2 ->
  sUpdate (sUpdate s x1 v1) x2 v2 =
  sUpdate (sUpdate s x2 v2) x1 v1.
Proof.
  intros s x1 v1 x2 v2 H1.
  extensionality y.
  unfold sUpdate, update. desf.
Qed.

(** The following definition captures two stores _agreeing_ on a
    given predicate [phi] over (program) variables. *)

Definition sAgree (phi : Var -> Prop)(s1 s2 : Store) : Prop :=
  forall x, phi x -> s1 x = s2 x.

(** Store agreement is a symmetric relation. *)

Global Instance sAgree_symm :
  forall phi, Symmetric (sAgree phi).
Proof.
  intros phi s1 s2 H1 x H2. symmetry. by apply H1.
Qed.

(** Below are several other useful properties of store agreement. *)

Lemma sAgree_split :
  forall phi1 phi2 s1 s2,
  sAgree (fun x => phi1 x \/ phi2 x) s1 s2 <->
  sAgree phi1 s1 s2 /\ sAgree phi2 s1 s2.
Proof.
  intros phi1 phi2 s1 s2. split; intro H1; [split|].
  - red. intros x H2. apply H1. by left.
  - red. intros x H2. apply H1. by right.
  - destruct H1 as (H1&H2). red. intros x [H3|H3].
    + by apply H1.
    + by apply H2.
Qed.

Lemma sAgree_app :
  forall xs1 xs2 s1 s2,
  sAgree (fun x => In x (xs1 ++ xs2)) s1 s2 <->
  sAgree (fun x => In x xs1) s1 s2 /\
  sAgree (fun x => In x xs2) s1 s2.
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

Lemma sAgree_weaken :
  forall (phi1 phi2 : Var -> Prop)(s1 s2 : Store),
    (forall x, phi1 x -> phi2 x) ->
  sAgree phi2 s1 s2 ->
  sAgree phi1 s1 s2.
Proof.
  intros phi1 phi2 s1 s2 H1 H2 s H3.
  by apply H2, H1.
Qed.


(** *** Denotational semantics *)

(** **** Expressions *)

Fixpoint expr_eval (E : Expr)(s : Store) : Val :=
  match E with
    | Econst v => v
    | Evar x => s x
    | Eop E1 E2 => val_op (expr_eval E1 s) (expr_eval E2 s)
  end.

Definition expr_eval_map {T} (f : T -> Expr)(s : Store) : T -> Val :=
  fun x : T => expr_eval (f x) s.

(** Standard properties relating substitution to evaluation: *)

Lemma expr_eval_subst :
  forall E2 E1 x s,
  expr_eval (expr_subst x E1 E2) s =
  expr_eval E2 (sUpdate s x (expr_eval E1 s)).
Proof.
  expr_induction E2; intros E y s; simpls.
  - unfold sUpdate, update. desf.
  - by rewrite IH1, IH2.
Qed.

Lemma expr_eval_subst_map {T} :
  forall (f : T -> Expr) E x s,
  expr_eval_map (expr_subst_map x E f) s =
  expr_eval_map f (sUpdate s x (expr_eval E s)).
Proof.
  intros f E x s. extensionality y.
  apply expr_eval_subst.
Qed.

(** The following lemma relates the evaluation of
    process expressions with the evaluation of
    program expressions. *)

Lemma expr_eval_conv :
  forall (e : ProcExpr)(ps : ProcStore)(s : Store)(f : ProcVar -> Expr),
    (forall x : ProcVar, In x (pexpr_fv e) -> ps x = expr_eval (f x) s) ->
  expr_eval (pexpr_convert e f) s = pexpr_eval e ps.
Proof.
  induction e as [v|x|e1 IH1 e2 IH2]; intros ps s f H; vauto.
  - simpl pexpr_convert. rewrite <- H; auto.
    simpl. by left.
  - simpl pexpr_convert. simpl pexpr_eval.
    rewrite <- IH1 with (s:=s)(f:=f); vauto.
    rewrite <- IH2 with (s:=s)(f:=f); vauto.
    + intros x H1. apply H. simpl.
      apply in_app_iff. by right.
    + intros x H1. apply H. simpl.
      apply in_app_iff. by left.
Qed.

(** The evaluation of expressions only depends on its free variables. *)

Lemma expr_agree :
  forall E s1 s2,
  sAgree (fun x => In x (expr_fv E)) s1 s2 ->
  expr_eval E s1 = expr_eval E s2.
Proof.
  induction E as [v|x|E1 IH1 E2 IH2]; intros s1 s2 H; simpls.
  - apply H. vauto.
  - apply sAgree_app in H. destruct H as (H1&H2).
    by rewrite IH1 with s1 s2, IH2 with s1 s2.
Qed.

Lemma expr_map_agree {T} :
  forall (f : T -> Expr) s1 s2,
    (forall x, expr_map_fv f x -> s1 x = s2 x) ->
  expr_eval_map f s1 = expr_eval_map f s2.
Proof.
  intros f s1 s2 H1.
  extensionality t. apply expr_agree.
  red. intros x H2. apply H1.
  by exists t.
Qed.

(** The following lemma relates expression evaluation to store updates. *)

Lemma expr_eval_upd :
  forall E s x v,
  ~ In x (expr_fv E) ->
  expr_eval E (sUpdate s x v) = expr_eval E s.
Proof.
  intros E s x v H1.
  rewrite expr_agree with E s (sUpdate s x v); vauto.
  intros y H2. unfold sUpdate, update. desf.
Qed.

(** Other useful properties of expression evaluation. *)

Lemma expr_eval_const :
  forall E s, expr_eval E s = expr_eval (Econst (expr_eval E s)) s.
Proof. expr_induction E; intro s; vauto. Qed.


(** **** Conditions *)

Fixpoint cond_eval (B : Cond)(s : Store) : bool :=
  match B with
    | Bconst b => b
    | Bnot B' => negb (cond_eval B' s)
    | Band B1 B2 => (cond_eval B1 s) && (cond_eval B2 s)
    | Beq E1 E2 => if val_eq_dec (expr_eval E1 s) (expr_eval E2 s) then true else false
  end.

Lemma cond_eval_excl :
  forall B s, cond_eval B s = true \/ cond_eval B s = false.
Proof.
  intros B s. rewrite <- Bool.not_true_iff_false.
  apply classic.
Qed.

(** A standard property that relates substitution to evaluation: *)

Lemma cond_eval_subst :
  forall B E x s,
  cond_eval (cond_subst x E B) s =
  cond_eval B (sUpdate s x (expr_eval E s)).
Proof.
  induction B as [b|B' IH|B1 IH1 B2 IH2|E1 E2];
    intros E x s; simpl; intuition.
  - by rewrite IH.
  - by rewrite IH1, IH2.
  - by repeat rewrite expr_eval_subst.
Qed.

(** The following lemma relates the evaluation of process conditions
    with the evaluation of program conditions. *)

Lemma cond_eval_conv :
  forall (b : ProcCond)(ps : ProcStore)(s : Store)(f : ProcVar -> Expr),
    (forall x : ProcVar, In x (pcond_fv b) -> ps x = expr_eval (f x) s) ->
  cond_eval (pcond_convert b f) s = pcond_eval b ps.
Proof.
  induction b as [b'|b' IH|b1 IH1 b2 IH2|e1 e2];
    intros ps s f H; vauto; simpls.
  - rewrite <- IH with (s:=s)(f:=f); vauto.
  - rewrite <- IH1 with (s:=s)(f:=f); vauto.
    rewrite <- IH2 with (s:=s)(f:=f); vauto.
    + intros x H1. apply H.
      apply in_app_iff. by right.
    + intros x H1. apply H.
      apply in_app_iff. by left.
  - repeat rewrite expr_eval_conv with (ps:=ps); vauto.
    + intros x H1. apply H.
      apply in_app_iff. by right.
    + intros x H1. apply H.
      apply in_app_iff. by left.
Qed.

(** The evaluation of conditions only depends on its free variables. *)

Lemma cond_agree :
  forall B s1 s2,
  sAgree (fun x => In x (cond_fv B)) s1 s2 ->
  cond_eval B s1 = cond_eval B s2.
Proof.
  induction B as [b|B' IH|B1 IH1 B2 IH2|E1 E2];
    intros s1 s2 H; simpls.
  - by rewrite IH with s1 s2.
  - apply sAgree_app in H. destruct H as (H1&H2).
    by rewrite IH1 with s1 s2, IH2 with s1 s2.
  - apply sAgree_app in H. destruct H as (H1&H2).
    by rewrite expr_agree with E1 s1 s2, expr_agree with E2 s1 s2.
Qed.

(** The following lemma relates condition evaluation to store updates. *)

Lemma cond_eval_upd :
  forall B s x v,
  ~ In x (cond_fv B) ->
  cond_eval B (sUpdate s x v) = cond_eval B s.
Proof.
  intros B s x v H1.
  rewrite cond_agree with B s (sUpdate s x v); vauto.
  intros y H2. unfold sUpdate, update. desf.
Qed.


(** *** Hybrid expressions *)

(** **** Dehybridisation *)

Fixpoint eDehybridise (E : HExpr)(s : Store) : ProcExpr :=
  match E with
    | HEconst v => PEconst v
    | HEprocvar x => PEvar x
    | HEprogvar x => PEconst (s x)
    | HEop E1 E2 => PEop (eDehybridise E1 s) (eDehybridise E2 s)
  end.

(** The following two properties relate hybridisation to evaluation. *)

Lemma eHybridise_eval :
  forall E s ps,
  pexpr_eval (eDehybridise (eHybridise E) s) ps = expr_eval E s.
Proof.
  induction E as [v|x|E1 IH1 E2 IH2]; intros s ps; vauto.
  simpl. by rewrite IH1, IH2.
Qed.

Lemma eHybridise_conv_eval :
  forall E s ps (f : ProcVar -> Expr),
    (forall x : ProcVar, In x (hexpr_fpv E) -> ps x = expr_eval (f x) s) ->
  expr_eval (hexpr_convert E f) s =
  pexpr_eval (eDehybridise E s) ps.
Proof.
  hexpr_induction E; intros s ps f H1; simpls.
  - symmetry. apply H1. vauto.
  - rewrite IH1 with (ps:=ps), IH2 with (ps:=ps); vauto.
    + intros x H2. apply H1. apply in_or_app. by right.
    + intros x H2. apply H1. apply in_or_app. by left.
Qed.

(** Dehybridising a hybridised process expression gives
    the original process expression *)

Lemma eDehybridise_hybridise :
  forall e s, e = eDehybridise (peHybridise e) s.
Proof.
  induction e as [v|x|e1 IH1 e2 IH2]; intro s; vauto.
  simpl. rewrite <- IH1 with s, <- IH2 with s; vauto.
Qed.

(** The following property related dehybrisation
    to freely occuring process variables. *)

Lemma eDehybridise_fpv :
  forall E s x,
  In x (hexpr_fpv E) <-> In x (pexpr_fv (eDehybridise E s)).
Proof.
  hexpr_induction E; intros s y; split; intro H1; vauto.
  - simpl. apply in_or_app. simpl in H1.
    apply in_app_or in H1.
    destruct H1 as [H1|H1].
    + left. by apply IH1.
    + right. by apply IH2.
  - simpl in H1. apply in_app_or in H1.
    simpl. apply in_or_app.
    destruct H1 as [H1|H1].
    + left. by apply IH1 with s.
    + right. by apply IH2 with s.
Qed.

(** **** Substitution *)

(** Substitution is defined in the standard sense. *)

Fixpoint hexpr_subst (x : Var)(E : Expr)(HE : HExpr) : HExpr :=
  match HE with
    | HEconst v => HEconst v
    | HEprocvar y => HEprocvar y
    | HEprogvar y =>
        if var_eq_dec x y
        then eHybridise E
        else HEprogvar y
    | HEop HE1 HE2 =>
        HEop (hexpr_subst x E HE1) (hexpr_subst x E HE2)
  end.

(** Substituting any (program) variable that does not occur
    freely inside the targetted hybrid expression
    does not change the expression. *)

Lemma hexpr_subst_pres :
  forall HE x E,
  ~ In x (hexpr_fv HE) -> hexpr_subst x E HE = HE.
Proof.
  induction HE as [v|y|y|HE1 IH1 HE2 IH2]; intros x E H1; simpls.
  - intuition. desf.
  - rewrite IH1, IH2; vauto.
    + intro H2. apply H1. apply in_or_app. by right.
    + intro H2. apply H1. apply in_or_app. by left.
Qed.

(** The following property relates dehybridisation to substitution. *)

Lemma eDehybridise_subst :
  forall HE x E s ps,
  pexpr_eval (eDehybridise (hexpr_subst x E HE) s) ps =
  pexpr_eval (eDehybridise HE (sUpdate s x (expr_eval E s))) ps.
Proof.
  induction HE as [v|y|y|HE1 IH1 HE2 IH2]; intros x E s ps; simpls.
  - unfold sUpdate, update.
    destruct (var_eq_dec x y); vauto.
    by rewrite eHybridise_eval.
  - by rewrite IH1, IH2.
Qed.

(** The dehybridisation of hybrid expressions
    only depends on its free variables. *)

Lemma eDehybridise_agree :
  forall E s1 s2,
  sAgree (fun x => In x (hexpr_fv E)) s1 s2 ->
  eDehybridise E s1 = eDehybridise E s2.
Proof.
  induction E as [v|y|y|HE1 IH1 HE2 IH2];
    intros s1 s2 H1; simpls.
  - rewrite H1; vauto.
  - rewrite IH1 with s1 s2, IH2 with s1 s2; auto.
    + intros x H2. apply H1. apply in_or_app. by right.
    + intros x H2. apply H1. apply in_or_app. by left.
Qed.


(** *** Hybrid conditions *)

(** **** Dehybridisation *)

Fixpoint cDehybridise (B : HCond)(s : Store) : ProcCond :=
  match B with
    | HBconst b => PBconst b
    | HBnot B' => PBnot (cDehybridise B' s)
    | HBand B1 B2 => PBand (cDehybridise B1 s) (cDehybridise B2 s)
    | HBeq E1 E2 => PBeq (eDehybridise E1 s) (eDehybridise E2 s)
  end.

(** The following two properties relate hybridisation to evaluation. *)

Lemma cHybridise_eval :
  forall B s ps,
  pcond_eval (cDehybridise (cHybridise B) s) ps = cond_eval B s.
Proof.
  induction B as [b|B' IH|B1 IH1 B2 IH2|E1 E2];
    intros s ps; simpls.
  - by rewrite IH.
  - by rewrite IH1, IH2.
  - by repeat rewrite eHybridise_eval.
Qed.

Lemma cHybridise_conv_eval :
  forall B s ps (f : ProcVar -> Expr),
    (forall x : ProcVar, In x (hcond_fpv B) -> ps x = expr_eval (f x) s) ->
  cond_eval (hcond_convert B f) s =
  pcond_eval (cDehybridise B s) ps.
Proof.
  hcond_induction B; intros s ps f H1; simpls.
  - rewrite IH with (ps:=ps); vauto.
  - rewrite IH1 with (ps:=ps), IH2 with (ps:=ps); vauto.
    + intros x H2. apply H1. apply in_or_app. by right.
    + intros x H2. apply H1. apply in_or_app. by left.
  - repeat rewrite eHybridise_conv_eval with (ps:=ps); auto.
    + intros x H2. apply H1. apply in_or_app. by right.
    + intros x H2. apply H1. apply in_or_app. by left.
Qed.

(** Dehybridising a hybridised process condition gives
    the same condition *)

Lemma cDehybridise_hybridise :
  forall b s, b = cDehybridise (pcHybridise b) s.
Proof.
  induction b as [v|b IH|b1 IH1 b2 IH2|e1 e2]; intro s; simpls.
  - by rewrite <- IH with s.
  - by rewrite <- IH1 with s,  <- IH2 with s.
  - by repeat rewrite <- eDehybridise_hybridise.
Qed.

(** The dehybridisation of hybrid conditions
    only depends on its free variables. *)

Lemma cDehybridise_agree :
  forall B s1 s2,
  sAgree (fun x => In x (hcond_fv B)) s1 s2 ->
  cDehybridise B s1 = cDehybridise B s2.
Proof.
  induction B as [b|B' IH|B1 IH1 B2 IH2|E1 E2];
    intros s1 s2 H1; simpls.
  - rewrite IH with s1 s2; auto.
  - rewrite IH1 with s1 s2, IH2 with s1 s2; auto.
    + intros x H2. apply H1. apply in_or_app. by right.
    + intros x H2. apply H1. apply in_or_app. by left.
  - repeat rewrite eDehybridise_agree with (s1:=s1)(s2:=s2); auto.
    + intros x H2. apply H1. apply in_or_app. by right.
    + intros x H2. apply H1. apply in_or_app. by left.
Qed.

(** The following property related dehybrisation
    to freely occuring process variables. *)

Lemma cDehybridise_fpv :
  forall B s x,
  In x (hcond_fpv B) <-> In x (pcond_fv (cDehybridise B s)).
Proof.
  hcond_induction B; intros s y; split; intro H1; vauto.
  - simpl in H1. simpl. by apply IH.
  - simpl in H1. simpl. by apply IH with s.
  - simpl in H1. apply in_app_or in H1.
    simpl. apply in_or_app.
    destruct H1 as [H1|H1].
    + left. by apply IH1.
    + right. by apply IH2.
  - simpl in H1. apply in_app_or in H1.
    simpl. apply in_or_app.
    destruct H1 as [H1|H1].
    + left. by apply IH1 with s.
    + right. by apply IH2 with s.
  - simpl in H1. apply in_app_or in H1.
    simpl. apply in_or_app.
    destruct H1 as [H1|H1].
    + left. by apply eDehybridise_fpv.
    + right. by apply eDehybridise_fpv.
  - simpl in H1. apply in_app_or in H1.
    simpl. apply in_or_app.
    destruct H1 as [H1|H1].
    + left. by apply eDehybridise_fpv with s.
    + right. by apply eDehybridise_fpv with s.
Qed.

(** **** Substitution *)

Fixpoint hcond_subst (x : Var)(E : Expr)(B : HCond) : HCond :=
  match B with
    | HBconst v => HBconst v
    | HBnot B' => HBnot (hcond_subst x E B')
    | HBand B1 B2 => HBand (hcond_subst x E B1) (hcond_subst x E B2)
    | HBeq E1 E2 => HBeq (hexpr_subst x E E1) (hexpr_subst x E E2)
  end.

(** Substituting any (program) variable that does not occur
    freely inside the targetted hybrid condition
    does not change the targetted condition. *)

Lemma hcond_subst_pres :
  forall B x E,
  ~ In x (hcond_fv B) -> hcond_subst x E B = B.
Proof.
  induction B as [b|B' IH|B1 IH1 B2 IH2|E1 E2];
    intros x E H1; simpls.
  - rewrite IH; vauto.
  - rewrite IH1, IH2; vauto.
    + intro H2. apply H1. apply in_or_app. by right.
    + intro H2. apply H1. apply in_or_app. by left.
  - repeat rewrite hexpr_subst_pres; vauto.
    + intro H2. apply H1. apply in_or_app. by right.
    + intro H2. apply H1. apply in_or_app. by left.
Qed.

(** The following property relates dehybridisation to substitution. *)

Lemma cDehybridise_subst :
  forall B x E s ps,
  pcond_eval (cDehybridise (hcond_subst x E B) s) ps =
  pcond_eval (cDehybridise B (sUpdate s x (expr_eval E s))) ps.
Proof.
  induction B as [b|B' IH|B1 IH1 B2 IH2|E1 E2];
    intros x E s ps; simpls.
  - by rewrite IH.
  - by rewrite IH1, IH2.
  - by repeat rewrite eDehybridise_subst.
Qed.


(** *** Hybrid processes *)

(** The following two functions, [hguard] and [heffect],
    are the hybrid counterparts of the functions
    [guard] and [effect] that constituting the
    guards and effects of actions *)

Parameter hguard : Act -> Expr -> HCond.
Parameter heffect : Act -> Expr -> HCond.

(** We need to make sure that the hybrid guards and effects
    make sense with respect to the ordinary guards and effects
    of actions. This is done in terms of the following properties: *)

Parameter hguard_corr :
  forall a E f s,
    cond_eval (hcond_convert (hguard a E) f) s =
    cond_eval (pcond_convert (guard a (expr_eval E s)) f) s.

Parameter heffect_corr :
  forall a E f s,
    cond_eval (hcond_convert (heffect a E) f) s =
    cond_eval (pcond_convert (effect a (expr_eval E s)) f) s.

(** **** (De)hybridisation *)

(** The dehybridisation operation [pDehybridise] for processes
    transforms any hybrid process to an ordinary process: *)

Fixpoint pDehybridise (P : HProc)(s : Store) : Proc :=
  match P with
    | HPepsilon => Pepsilon
    | HPdelta => Pdelta
    | HPact a E => Pact a (expr_eval E s)
    | HPassert B => Passert (cDehybridise B s)
    | HPseq P1 P2 => Pseq (pDehybridise P1 s) (pDehybridise P2 s)
    | HPalt P1 P2 => Palt (pDehybridise P1 s) (pDehybridise P2 s)
    | HPpar P1 P2 => Ppar (pDehybridise P1 s) (pDehybridise P2 s)
    | HPlmerge P1 P2 => Plmerge (pDehybridise P1 s) (pDehybridise P2 s)
    | HPsum f => Psum (fun v => pDehybridise (f v) s)
    | HPcond B Q => Pcond (cond_eval B s) (pDehybridise Q s)
    | HPiter Q => Piter (pDehybridise Q s)
  end.

(** Dehybridising a hybridised process yields the original process. *)

Lemma pDehybridise_hybridise :
  forall P s, P = pDehybridise (pHybridise P) s.
Proof.
  hproc_induction P; intro s; simpls; vauto.
  - by rewrite <- cDehybridise_hybridise.
  - by rewrite <- IH1, <- IH2.
  - by rewrite <- IH1, <- IH2.
  - by rewrite <- IH1, <- IH2.
  - by rewrite <- IH1, <- IH2.
  - apply proc_sum_ext.
    extensionality v. by apply IH.
  - by rewrite <- IH.
  - by rewrite <- IH.
Qed.

(** The dehybridisation of hybrid processes
    only depends on its free variables. *)

Lemma pDehybridise_agree :
  forall P s1 s2,
  sAgree (hproc_fv P) s1 s2 ->
  pDehybridise P s1 = pDehybridise P s2.
Proof.
  hproc_induction P; intros s1 s2 H1; vauto.
  (* actions *)
  - simpl. rewrite expr_agree with (s2:=s2); auto.
  (* assertions *)
  - simpl. rewrite cDehybridise_agree with (s2:=s2); auto.
  (* sequential *)
  - simpl. rewrite IH1 with (s2:=s2), IH2 with (s2:=s2); auto.
    + intros x H2. apply H1. simpl. by right.
    + intros x H2. apply H1. simpl. by left.
  (* choice *)
  - simpl. rewrite IH1 with (s2:=s2), IH2 with (s2:=s2); auto.
    + intros x H2. apply H1. simpl. by right.
    + intros x H2. apply H1. simpl. by left.
  (* parallel *)
  - simpl. rewrite IH1 with (s2:=s2), IH2 with (s2:=s2); auto.
    + intros x H2. apply H1. simpl. by right.
    + intros x H2. apply H1. simpl. by left.
  (* left-merge *)
  - simpl. rewrite IH1 with (s2:=s2), IH2 with (s2:=s2); auto.
    + intros x H2. apply H1. simpl. by right.
    + intros x H2. apply H1. simpl. by left.
  (* summation *)
  - simpl. apply proc_sum_ext. extensionality v.
    apply IH. intros x H2. apply H1. simpl. by exists v.
  (* conditionals *)
  - simpl. rewrite cond_agree with (s2:=s2).
    2:{ intros x H2. apply H1. simpl. by left. }
    rewrite IH with (s2:=s2); auto.
    intros x H2. apply H1. simpl. by right.
  (* iteration *)
  - simpl. rewrite IH with (s2:=s2); auto.
Qed.

(** **** Substitution *)

(** The substitution operation [hproc_subst x E P] replaces
    every occurence of the _program_ variable [x] by the
    expression [E] inside the hybrid process [P]. *)

Fixpoint hproc_subst (x : Var)(E : Expr)(P : HProc) : HProc :=
  match P with
    | HPepsilon => HPepsilon
    | HPdelta => HPdelta
    | HPact a E' => HPact a (expr_subst x E E')
    | HPassert B => HPassert (hcond_subst x E B)
    | HPseq P1 P2 => HPseq (hproc_subst x E P1) (hproc_subst x E P2)
    | HPalt P1 P2 => HPalt (hproc_subst x E P1) (hproc_subst x E P2)
    | HPpar P1 P2 => HPpar (hproc_subst x E P1) (hproc_subst x E P2)
    | HPlmerge P1 P2 => HPlmerge  (hproc_subst x E P1) (hproc_subst x E P2)
    | HPsum f => HPsum (fun v => hproc_subst x E (f v))
    | HPcond B Q => HPcond (cond_subst x E B) (hproc_subst x E Q)
    | HPiter Q => HPiter (hproc_subst x E Q)
  end.

(** The definition of sigma as used in the process algebra
    literature to define summation can now be encoded
    op top of substitution. *)

Definition HPsigma (x : Var)(P : HProc) : HProc :=
  HPsum (fun v => hproc_subst x (Econst v) P).

(** Substituting any (program) variable that does not occur
    freely inside the targetted hybrid process
    does not change the targetted process. *)

Lemma hproc_subst_pres :
  forall P x E,
  ~ hproc_fv P x -> (hproc_subst x E P) = P.
Proof.
  proc_induction P; intros x E' H1; simpls.
  (* actions *)
  - rewrite expr_subst_pres; vauto.
  (* assertions *)
  - rewrite hcond_subst_pres; vauto.
  (* sequential *)
  - rewrite IH1, IH2; vauto.
    + intro H2. apply H1. vauto.
    + intro H2. apply H1. vauto.
  (* choice *)
  - rewrite IH1, IH2; vauto.
    + intro H2. apply H1. vauto.
    + intro H2. apply H1. vauto.
  (* parallel *)
  - rewrite IH1, IH2; vauto.
    + intro H2. apply H1. vauto.
    + intro H2. apply H1. vauto.
  (* left-merge *)
  - rewrite IH1, IH2; vauto.
    + intro H2. apply H1. vauto.
    + intro H2. apply H1. vauto.
  (* summation *)
  - apply HPsum_ext. extensionality v.
    apply IH. intro H2. apply H1. vauto.
  (* conditionals *)
  - rewrite IH; vauto.
    + rewrite cond_subst_pres; auto.
    + intro H2. apply H1. vauto.
  (* iteration *)
  - rewrite IH; auto.
Qed.

(** The following property relates substitution with
    the dehybridisation of hybrid processes. *)

Lemma pDehybridise_subst :
  forall P x E s,
  bisim (pDehybridise (hproc_subst x E P) s) (pDehybridise P (sUpdate s x (expr_eval E s))).
Proof.
  proc_induction P; intros x E' s; vauto; simpls.
  (* actions *)
  - by rewrite expr_eval_subst.
  (* assertions *)
  - apply bisim_assert. extensionality s'.
    by apply cDehybridise_subst.
  (* sequential *)
  - apply bisim_seq; vauto.
  (* choice *)
  - apply bisim_alt; vauto.
  (* parallel *)
  - apply bisim_par; vauto.
  (* left-merge *)
  - apply bisim_lmerge; vauto.
  (* summations *)
  - apply bisim_sum; vauto.
  (* conditionals *)
  - apply bisim_cond; vauto.
    by apply cond_eval_subst.
  (* iteration *)
  - apply bisim_iter; vauto.
Qed.


(** *** Hybrid process bisimilarity *)

(** Bisimilarity of hybrid processes is lifted from the
    definition of bisimilarity [bisim] of (ordinary) processes. *)

Definition hbisim (P Q : HProc) : Prop :=
  forall s, bisim (pDehybridise P s) (pDehybridise Q s).
Definition hbisim_f : relation (Val -> HProc) :=
  pointwise_relation Val hbisim.

Notation "P ≃ Q" := (hbisim P Q) (only printing, at level 80).
Notation "f ≃ g" := (hbisim_f f g) (only printing, at level 80).

(** Bisimilarity of hybrid processes is an equivalence relation. *)

Global Instance hbisim_refl : Reflexive hbisim.
Proof. intros P. red. auto. Qed.
Global Instance hbisim_symm : Symmetric hbisim.
Proof. intros P Q H. red. symmetry. by apply H. Qed.
Global Instance hbisim_trans  : Transitive hbisim.
Proof. intros P Q R H1 H2 s. by transitivity (pDehybridise Q s). Qed.
Global Instance hbisim_equiv : Equivalence hbisim.
Proof. split; intuition. Qed.

Hint Resolve hbisim_refl : core.

Global Instance hbisim_f_refl : Reflexive hbisim_f.
Proof. intros f v s. auto. Qed.
Global Instance hbisim_f_symm : Symmetric hbisim_f.
Proof. intros f1 f2 H v s. symmetry. by apply H. Qed.
Global Instance hbisim_f_trans : Transitive hbisim_f.
Proof. intros f1 f2 f3 H1 H2 v. transitivity (f2 v); auto. Qed.
Global Instance hbisim_f_equiv : Equivalence hbisim_f.
Proof. split; intuition. Qed.

Hint Resolve hbisim_f_refl : core.

Add Parametric Morphism : pDehybridise
  with signature hbisim ==> eq ==> bisim
    as pDehybridise_bisim_mor.
Proof.
  intros P Q H1 s. red in H1. by apply H1.
Qed.


(** *** Congruence properties of hybrid processes *)

(** Bisimilarity of hybrid processes is a _congruence_
    for all process-algebraic connectives (this is entirely derived
    from the congruence properties of [bisim]). *)

Add Parametric Morphism : HPseq
  with signature hbisim ==> hbisim ==> hbisim as hbisim_seq.
Proof. intros ???????. by apply bisim_seq. Qed.
Add Parametric Morphism : HPalt
  with signature hbisim ==> hbisim ==> hbisim as hbisim_alt.
Proof. intros ???????. by apply bisim_alt. Qed.
Add Parametric Morphism : HPpar
  with signature hbisim ==> hbisim ==> hbisim as hbisim_par.
Proof. intros ???????. by apply bisim_par. Qed.
Add Parametric Morphism : HPlmerge
  with signature hbisim ==> hbisim ==> hbisim as hbisim_lmerge.
Proof. intros ???????. by apply bisim_lmerge. Qed.
Add Parametric Morphism : HPsum
  with signature hbisim_f ==> hbisim as hbisim_sum.
Proof.
  intros f1 f2 H1 s.
  apply bisim_sum. red. intro v. by apply H1.
Qed.
Add Parametric Morphism : HPcond
  with signature eq ==> hbisim ==> hbisim as hbisim_cond.
Proof. intros ?????. by apply bisim_cond. Qed.
Add Parametric Morphism : HPiter
  with signature hbisim ==> hbisim as hbisim_iter.
Proof. intros ????. by apply bisim_iter. Qed.


(** *** Axiomatisation of hybrid processes *)

(** All standard bisimulation equivalences can be derived
    from the definition of [bisim]. *)

(** The most important equivalences for the remaining theory
    are associativity and commutativity of parallel composition,
    which are given below. *)

Theorem hbisim_par_assoc :
  forall P Q R, hbisim (HPpar P (HPpar Q R)) (HPpar (HPpar P Q) R).
Proof. intros ????. by apply bisim_par_assoc. Qed.
Theorem hbisim_par_comm :
  forall P Q, hbisim (HPpar P Q) (HPpar Q P).
Proof. intros ???. by apply bisim_par_comm. Qed.
Theorem hbisim_par_epsilon_l :
  forall P, hbisim (HPpar HPepsilon P) P.
Proof. intros ??. simpl. by apply bisim_par_epsilon_l. Qed.
Theorem hbisim_par_epsilon_r :
  forall P, hbisim (HPpar P HPepsilon) P.
Proof. intros ??. simpl. by apply bisim_par_epsilon_r. Qed.

Theorem hbisim_sigma_alt :
  forall P E x,
  hbisim (HPsigma x P) (HPalt (hproc_subst x E P) (HPsigma x P)).
Proof.
  intros P E x s. simpl.
  rewrite pDehybridise_subst.
  assert (H1 : bisim_f
      (fun v => pDehybridise (hproc_subst x (Econst v) P) s)
      (fun v => pDehybridise P (sUpdate s x (expr_eval (Econst v) s)))). {
    red. red. intro v. by apply pDehybridise_subst. }
  repeat rewrite H1. clear H1.
  remember (fun v => pDehybridise P (sUpdate s x (expr_eval (Econst v) s))) as f.
  assert (H2 : bisim (pDehybridise P (sUpdate s x (expr_eval E s))) (f (expr_eval E s))). {
    subst f. by simpl. }
  rewrite H2. clear H2.
  apply bisim_sum_alt.
Qed.


(** *** Shared memory accesses *)

(** The operation [cmd_acc C s] defines the set of heap locations
    that are _accessed_ by the program [C] in a single execution step,
    where [s] is used to evaluate all expressions referring
    to heap locations. *)

(** Likewise, the operation [cmd_writes C s] determines the set
    of heap locations that are _written to_ by [C]
    in a single execution step. Note that, rather than yielding
    a set of heap locations, both these operations are defined
    as predicates instead for later convenience. *)

Fixpoint cmd_acc {T} (C : Cmd T)(s : Store)(l : Val) : Prop :=
  match C with
    | Cskip => False
    | Cseq C' _ => cmd_acc C' s l
    | Cass _ _ => False
    | Cread _ E
    | Cwrite E _ => l = expr_eval E s
    | Cite _ _ _
    | Cwhile _ _ => False
    | Cpar C1 C2 => cmd_acc C1 s l \/ cmd_acc C2 s l
    | Calloc _ _ => False
    | Cdispose E => l = expr_eval E s
    | Catomic _ => False
    | Cinatom C' => cmd_acc C' s l
    | Cproc _ _ _ xs f => exists x, In x xs /\ l = expr_eval (f x) s
    | Cact _ _ _ C' => False
    | Cinact _ C' => cmd_acc C' s l
    | Cquery _ => False
    | Cendproc _ => False
  end.

Fixpoint cmd_writes {T} (C : Cmd T)(s : Store)(l : Val) : Prop :=
  match C with
    | Cskip => False
    | Cseq C' _ => cmd_writes C' s l
    | Cass _ _
    | Cread _ _ => False
    | Cwrite E _ => l = expr_eval E s
    | Cite _ _ _
    | Cwhile _ _ => False
    | Cpar C1 C2 => cmd_writes C1 s l \/ cmd_writes C2 s l
    | Calloc _ _ => False
    | Cdispose E => l = expr_eval E s
    | Catomic _ => False
    | Cinatom C' => cmd_writes C' s l
    | Cproc _ _ _ _ _
    | Cact _ _ _ _ => False
    | Cinact _ C' => cmd_writes C' s l
    | Cquery _ => False
    | Cendproc _ => False
  end.

(** All writes to shared memory are also shared-memory accesses. *)

Lemma cmd_writes_acc {T} :
  forall (C : Cmd T) s l, cmd_writes C s l -> cmd_acc C s l.
Proof.
  cmd_induction C; intros s l H; simpls; vauto.
  - by apply IH1.
  - destruct H as [H|H].
    + left. by apply IH1.
    + right. by apply IH2.
  - by apply IH.
  - by apply IH.
Qed.

(** Other useful properties of shared-memory accesses. *)

Lemma cmd_acc_agree {T} :
  forall (C : Cmd T) s1 s2 l,
  sAgree (cmd_fv C) s1 s2 ->
  cmd_acc C s1 l = cmd_acc C s2 l.
Proof.
  cmd_induction C; intros s1 s2 l H; simpls; vauto.
  - apply sAgree_split in H.
    destruct H as (H1&H2).
    rewrite IH1 with (s2:=s2); auto.
  - apply sAgree_split in H.
    destruct H as (H1&H2).
    rewrite expr_agree with (s2:=s2); auto.
  - apply sAgree_split in H.
    destruct H as (H1&H2).
    rewrite expr_agree with (s2:=s2); auto.
  - apply sAgree_split in H.
    destruct H as (H1&H2).
    rewrite IH1 with (s2:=s2), IH2 with (s2:=s2); auto.
  - rewrite expr_agree with (s2:=s2); auto.
  - rewrite IH with (s2:=s2); auto.
  - apply f_equal. extensionality y.
    rewrite expr_agree with (s2:=s2); auto.
    red. intros z H1. apply H.
    right. right. left. by exists y.
  - rewrite IH with (s2:=s2); auto.
Qed.

Lemma cmd_writes_agree {T} :
  forall (C : Cmd T) s1 s2 l,
    (forall x, cmd_fv C x -> s1 x = s2 x) ->
  cmd_writes C s1 l = cmd_writes C s2 l.
Proof.
  cmd_induction C; intros s1 s2 l H; simpls; vauto.
  - rewrite IH1 with (s2:=s2); auto.
  - rewrite expr_agree with (s2:=s2); auto.
    red. ins. apply H. by left.
  - rewrite IH1 with (s2:=s2), IH2 with (s2:=s2); auto.
  - rewrite expr_agree with (s2:=s2); auto.
  - rewrite IH with (s2:=s2); auto.
  - rewrite IH with (s2:=s2); auto.
Qed.

Lemma cmd_acc_plain {T} :
  forall (C : Cmd T) s, cmd_acc (plain C) s = cmd_acc C s.
Proof.
  cmd_induction C; intros s; simpls; vauto.
  by rewrite IH1, IH2.
Qed.

Lemma cmd_writes_plain {T} :
  forall (C : Cmd T) s,
  cmd_writes (plain C) s = cmd_writes C s.
Proof.
  cmd_induction C; intros s; simpls; vauto.
  by rewrite IH1, IH2.
Qed.


(** *** Operational semantics *)

(** Below are the small-step reduction rules of the (standard)
    operational semantics of programs. *)

(** Observe that the process-related commands are ignored
    and handled as if they were comments, since these are
    specification-only. Moreover, the transition rules for the
    parallel composition only allow a program to make a step if the
    other program is not locked. This allows to model atomic programs
    using a small-step semantics. *)

Inductive step : Heap -> Store -> PlainCmd -> Heap -> Store -> PlainCmd -> Prop :=
  (* sequential *)
  | step_seq_l h s C1 h' s' C1' C2 :
    step h s C1 h' s' C1' ->
    step h s (Cseq C1 C2) h' s' (Cseq C1' C2)
  | step_seq_r h s C :
    step h s (Cseq Cskip C) h s C
  (* assign *)
  | step_assign h s x E :
    let v := expr_eval E s in
    step h s (Cass x E) h (sUpdate s x v) Cskip
  (* heap reading *)
  | step_read h s x E v :
    h (expr_eval E s) = Some v ->
    step h s (Cread x E) h (sUpdate s x v) Cskip
  (* heap writing *)
  | step_write h s E1 E2 v :
    let l := expr_eval E1 s in
    let v' := expr_eval E2 s in
    h l = Some v ->
    step h s (Cwrite E1 E2) (hUpdate h l (Some v')) s Cskip
  (* if-then-else *)
  | step_ite_t h s B C1 C2 :
    cond_eval B s = true ->
    step h s (Cite B C1 C2) h s C1
  | step_ite_f h s B C1 C2 :
    cond_eval B s = false ->
    step h s (Cite B C1 C2) h s C2
  (* while *)
  | step_while h s B C :
    step h s (Cwhile B C) h s (Cite B (Cseq C (Cwhile B C)) Cskip)
  (* heap (de)alloc *)
  | step_alloc h s x E l :
    let v := expr_eval E s in
    h l = None ->
    step h s (Calloc x E) (hUpdate h l (Some v)) (sUpdate s x l) Cskip
  | step_dispose h s E :
    let l := expr_eval E s in
    step h s (Cdispose E) (hUpdate h l None) s Cskip
  (* atomics *)
  | step_atom h s C :
    step h s (Catomic C) h s (Cinatom C)
  | step_inatom_l h s C h' s' C' :
    step h s C h' s' C' ->
    step h s (Cinatom C) h' s' (Cinatom C')
  | step_inatom_r h s :
    step h s (Cinatom Cskip) h s Cskip
  (* parallel *)
  | step_par_l h s C1 C2 h' s' C1' :
    step h s C1 h' s' C1' ->
    ~ cmd_locked C2 ->
    step h s (Cpar C1 C2) h' s' (Cpar C1' C2)
  | step_par_r h s C1 C2 h' s' C2' :
    step h s C2 h' s' C2' ->
    ~ cmd_locked C1 ->
    step h s (Cpar C1 C2) h' s' (Cpar C1 C2')
  | step_par_done h s :
    step h s (Cpar Cskip Cskip) h s Cskip
  (* process *)
  | step_proc_init h s X P E xs f :
    step h s (Cproc X P E xs f) h s Cskip
  | step_end h s X :
    step h s (Cendproc X) h s Cskip
  (* action *)
  | step_act h s X a E C :
    step h s (Cact X a E C) h s (Cinact PMnone C)
  | step_act_l h s C h' s' C' :
    step h s C h' s' C' ->
    step h s (Cinact PMnone C) h' s' (Cinact PMnone C')
  | step_act_r h s :
    step h s (Cinact PMnone Cskip) h s Cskip
  (* querying *)
  | step_query h s x :
    step h s (Cquery x) h s Cskip.

Add Search Blacklist "step_ind".
Add Search Blacklist "step_sind".

(** Program basicality, program well-formedness
    and heap finiteness all remain invariant
    during program execution. *)

Lemma step_basic_pres :
  forall C h s C' h' s',
  cmd_basic C -> step h s C h' s' C' -> cmd_basic C'.
Proof.
  cmd_induction C; intros h s C'' h' s' H1 H2;
    inv H2; simpls; desf; intuition vauto.
  - by apply IH1 in H8.
  - by apply IH1 in H5.
  - by apply IH2 in H5.
  - by apply IH in H4.
Qed.

Lemma step_wf_pres :
  forall C h s C' h' s',
  cmd_wf C -> step h s C h' s' C' -> cmd_wf C'.
Proof.
  cmd_induction C; intros h s C'' h' s' H1 H2;
    inv H2; simpls; desf; intuition vauto.
  - by apply IH1 in H8.
  - by apply IH1 in H5.
  - by apply IH2 in H5.
  - by apply IH in H4.
  - by apply step_basic_pres in H8.
Qed.

Lemma step_hFinite :
  forall C h s C' h' s',
  step h s C h' s' C' -> hFinite h -> hFinite h'.
Proof.
  cmd_induction C; intros h s C'' h' s' STEP FIN; inv STEP; vauto.
  - by apply IH1 in H6.
  - by apply hFinite_update.
  - by apply IH1 in H3.
  - by apply IH2 in H3.
  - by apply hFinite_update.
  - by apply hFinite_update.
  - by apply IH in H2.
  - by apply IH in H6.
Qed.

(** The sets of free and modified variables do not grow
    during program execution. *)

Lemma step_fv_mod :
  forall C h s C' h' s',
  step h s C h' s' C' ->
    (forall x, cmd_fv C' x -> cmd_fv C x) /\
    (forall x, cmd_mod C' x -> cmd_mod C x) /\
    (forall x, ~ cmd_mod C x -> s x = s' x).
Proof.
  cmd_induction C; intros h s C'' h' s' H1; inv H1; clear H1; simpls.
  (* sequential *)
  - repeat split; intros x H.
    + destruct H as [H|H]; vauto.
      apply IH1 in H7. destruct H7 as (H1&H2&H3).
      left. by apply H1.
    + destruct H as [H|H]; vauto.
      apply IH1 in H7. destruct H7 as (H1&H2&H3).
      left. by apply H2.
    + apply IH1 in H7. destruct H7 as (H1&H2&H3).
      apply H3. intro H4. apply H. by left.
  - repeat split; intros x H; by right.
  (* assign *)
  - repeat split; intros y H; vauto.
    unfold sUpdate, update. intuition desf.
  (* heap reading *)
  - repeat split; intros y H; vauto.
    unfold sUpdate, update. intuition desf.
  (* if-then-else *)
  - repeat split; intros y H; vauto.
  - repeat split; intros y H; vauto.
  (* while *)
  - repeat split; intros y H; vauto.
    destruct H as [|[|]]; vauto.
    destruct H as [|[|]]; vauto.
    destruct H as [[|]|]; vauto.
  (* parallel *)
  - apply IH1 in H4. clear IH1 IH2.
    destruct H4 as (H1&H2&H3).
    repeat split; intros y H; vauto.
    destruct H as [H|H].
    left. by apply H1. by right.
    destruct H as [H|H].
    left. by apply H2. by right.
    apply H3. intro H4. apply H. by left.
  - apply IH2 in H4. clear IH1 IH2.
    destruct H4 as (H1&H2&H3).
    repeat split; intros y H; vauto.
    destruct H as [H|H].
    by left. right. by apply H1.
    destruct H as [H|H].
    by left. right. by apply H2.
    apply H3. intro H4. apply H. by right.
  (* heap allocation *)
  - repeat split; intros y H; vauto.
    unfold sUpdate, update. intuition desf.
  (* atomics *)
  - apply IH in H3. desf.
  (* actions *)
  - repeat split; intros y H; vauto.
  - apply IH in H7. desf.
Qed.

(** Program execution commutes with store agreement: *)

Lemma step_agree :
  forall C h s1 s2 C' h' s1' (phi : Var -> Prop),
    (forall x, cmd_fv C x -> phi x) ->
    (sAgree phi s1 s2) ->
    step h s1 C h' s1' C' ->
  exists s2',
    (sAgree phi s1' s2') /\
    step h s2 C h' s2' C'.
Proof.
  cmd_induction C; intros h s1 s2 C'' h' s1' phi H1 H2 STEP;
    inv STEP; clear STEP; simpls; intuition vauto;
    unfold sAgree in *; try (exists s2; intuition vauto; fail).
  (* sequential *)
  - apply IH1 with (s2:=s2)(phi:=phi) in H8; vauto.
    destruct H8 as (s2'&H3&STEP).
    exists s2'. intuition vauto.
    intros x H. apply H1. by left.
  (* assignment *)
  - exists (sUpdate s2 x (expr_eval E s2)).
    split; vauto. intros y H. unfold sUpdate, update.
    destruct (var_eq_dec x y); auto. clarify.
    rewrite <- expr_agree with (s1:=s1); auto.
    unfold sAgree. intros x H'.
    apply H2, H1. by right.
  (* heap reading *)
  - rewrite expr_agree with (s2:=s2) in H8; vauto.
    exists (sUpdate s2 x v). split; vauto.
    intros y H3. unfold sUpdate, update.
    destruct (var_eq_dec x y); auto.
    red. intros y H. apply H2, H1. by right.
  (* heap writing *)
  - subst l l0 v' v'0.
    exists s2. split; vauto.
    rewrite expr_agree with (s2:=s2) in H8; vauto.
    repeat rewrite expr_agree with (s1:=s1')(s2:=s2); vauto.
    red. ins. apply H2, H1. by right.
    red. ins. apply H2, H1. by left.
    red. ins. apply H2, H1. by left.
  (* if-then-else *)
  - exists s2. split; vauto. constructor.
    rewrite <- cond_agree with (s1:=s1'); auto.
    red. ins. apply H2, H1. by left.
  - exists s2. split; vauto. constructor.
    rewrite <- cond_agree with (s1:=s1'); auto.
    red. ins. apply H2, H1. by left.
  (* parallel *)
  - apply IH1 with (s2:=s2)(phi:=phi) in H5; vauto.
    destruct H5 as (s2'&H3&H4).
    exists s2'. split; vauto.
    intros x H. apply H1. by left.
  - apply IH2 with (s2:=s2)(phi:=phi) in H5; vauto.
    destruct H5 as (s2'&H3&H4).
    exists s2'. split; vauto.
    intros x H. apply H1. by right.
  (* heap (de)allocation *)
  - subst v. rewrite expr_agree with (s2:=s2).
    exists (sUpdate s2 x l).
    split; vauto. intros y H3.
    unfold sUpdate, update.
    destruct (var_eq_dec x y); auto.
    red. ins. apply H2, H1. by right.
  - subst l l0. exists s2. split; vauto.
    rewrite expr_agree with (s2:=s2); vauto.
    red. ins. by apply H2, H1.
  (* atomics *)
  - apply IH with (s2:=s2)(phi:=phi) in H4; vauto.
    destruct H4 as (s2'&H4&H5).
    exists s2'. intuition vauto.
  (* processes *)
  - apply IH with (s2:=s2)(phi:=phi) in H8; vauto.
    destruct H8 as (s2'&H4&H5).
    exists s2'. split; vauto.
Qed.

(** A program reduction step always mutates the executed program;
    one does not end up in the same program after performing a
    computation step. *)

Lemma step_neg_C :
  forall C h s h' s', ~ step h s C h' s' C.
Proof.
  cmd_induction C; intros h s h' s' STEP;
    vauto; inv STEP; clear STEP.
  (* sequential *)
  - by apply IH1 in H5.
  - by apply cmd_neg_seq in H5.
  (* if-then-else *)
  - by apply cmd_neg_ite_t in H6.
  - by apply cmd_neg_ite_f in H6.
  (* parallel *)
  - by apply IH1 in H6.
  - by apply IH2 in H6.
  (* atomics *)
  - by apply IH in H5.
  (* actions *)
  - by apply IH in H5.
Qed.


(** *** Fault semantics *)

(** The fault semantics of program is defined in
    terms of the predicate [fault h s C] and captures
    whether [C] is able to _fault_ in a single computation
    step with respect to heap [h] and store [s]. *)

(** A _fault_ is defined to be a data-race, a deadlock,
    or a violation of memory safety. *)

(** Any program performs a _data-race_ if two threads
    access the same shared location,
    where one of these accesses is a write. *)

(** Any parallel program [Cpar C1 C2] is _deadlocked_ if
    [C1] and [C2] are both locked with respect to [cmd_locked]. *)

(** Moreover, any program is defined to be _memory safe_
    if it does not access a shared location has has not
    been allocated. *)

Inductive fault {T} : Heap -> Store -> Cmd T -> Prop :=
  (* heap reading *)
  | fault_read h s x E :
    h (expr_eval E s) = None -> fault h s (Cread x E)
  (* heap writing *)
  | fault_write h s E1 E2 :
    h (expr_eval E1 s) = None -> fault h s (Cwrite E1 E2)
  (* heap (de)allocation *)
  | fault_alloc h s x E :
    (~ exists l, h l = None) -> fault h s (Calloc x E)
  | fault_dispose h s E :
    h (expr_eval E s) = None -> fault h s (Cdispose E)
  (* parallel *)
  | fault_par_l h s C1 C2 :
    fault h s C1 -> ~ cmd_locked C2 -> fault h s (Cpar C1 C2)
  | fault_par_r h s C1 C2 :
    fault h s C2 -> ~ cmd_locked C1 -> fault h s (Cpar C1 C2)
  | fault_deadlock h s C1 C2 :
    cmd_locked C1 -> cmd_locked C2 -> fault h s (Cpar C1 C2)
  (* actions *)
  | fault_act h s m C :
    fault h s C -> fault h s (Cinact m C)
  (* sequential *)
  | fault_seq h s C1 C2 :
    fault h s C1 -> fault h s (Cseq C1 C2)
  (* atomics *)
  | fault_atom h s C :
    fault h s C -> fault h s (Cinatom C)
  (* data races *)
  | fault_race_l h s C1 C2 :
    ~ cmd_locked C1 ->
    ~ cmd_locked C2 ->
    ~ disjoint (cmd_writes C1 s) (cmd_acc C2 s) ->
    fault h s (Cpar C1 C2)
  | fault_race_r h s C1 C2 :
    ~ cmd_locked C1 ->
    ~ cmd_locked C2 ->
    ~ disjoint (cmd_acc C1 s) (cmd_writes C2 s) ->
    fault h s (Cpar C1 C2).

Add Search Blacklist "fault_ind".
Add Search Blacklist "fault_sind".

(** The fault semantics of programs is closed under store agreement. *)

Lemma fault_agree {T} :
  forall (C : Cmd T) h s1 s2,
  sAgree (cmd_fv C) s1 s2 -> fault h s1 C -> fault h s2 C.
Proof.
  cmd_induction C; intros h s1 s2 H1 H2;
    simpls; inv H2; clear H2.
  (* sequential *)
  - constructor. apply IH1 with s1; vauto.
    red. ins. apply H1. by left.
  (* heap reading *)
  - constructor.
    rewrite <- expr_agree with (s1 := s1); auto.
    unfold sAgree. intros y H2.
    apply H1. by right.
  (* heap writing *)
  - constructor.
    rewrite <- expr_agree with (s1 := s1); auto.
    unfold sAgree. intros y H2.
    apply H1. by left.
  (* parallel *)
  - apply fault_par_l; vauto.
    apply IH1 with s1; auto.
    red. ins. apply H1. vauto.
  - apply fault_par_r; vauto.
    apply IH2 with s1; auto.
    red. ins. apply H1. vauto.
  - by apply fault_deadlock.
  (* data races *)
  - apply sAgree_split in H1.
    destruct H1 as (H1&H2).
    apply fault_race_l; vauto.
    intro H4. apply H7. clear H7.
    red. intros l F1 F2.
    rewrite cmd_writes_agree with (s4:=s2) in F1; auto.
    rewrite cmd_acc_agree with (s4:=s2) in F2; auto.
    by apply H4 with l.
  - apply sAgree_split in H1.
    destruct H1 as (H1&H2).
    apply fault_race_r; vauto.
    intro H4. apply H7. clear H7.
    red. intros l F1 F2.
    rewrite cmd_acc_agree with (s4:=s2) in F1; auto.
    rewrite cmd_writes_agree with (s4:=s2) in F2; auto.
    by apply H4 with l.
  (* heap (de)allocation *)
  - by constructor.
  - constructor. rewrite <- expr_agree with (s1:=s1); auto.
  (* atomics *)
  - constructor. apply IH with s1; auto.
  (* actions *)
  - constructor. apply IH with s1; auto.
Qed.

(** The following theorem shows that the operational semantics
    and fault semantics are coherent, by showing a property
    of progress: every configuration that does not fault
    can either make a computation step or has already terminated. *)

Theorem step_progress :
  forall C h s,
  ~ fault h s C -> C = Cskip \/ exists C' h' s', step h s C h' s' C'.
Proof.
  cmd_induction C; intros h s FAULT.
  (* skip *)
  - by left.
  (* sequential *)
  - assert (H1 : C1 = Cskip \/ ~ C1 = Cskip) by apply classic.
    right. destruct H1 as [H1|H1].
    (* left program [C1] is empty *)
    + clarify. exists C2, h, s. vauto.
    (* left program [C1] is not empty *)
    + assert (H2 : ~ fault h s C1) by (intro H; apply FAULT; vauto).
      apply IH1 in H2. destruct H2 as [H2|H2]; vauto.
      destruct H2 as (C1'&h'&s'&STEP).
      exists (Cseq C1' C2), h', s'. vauto.
  (* assignment *)
  - right. exists Cskip, h, (sUpdate s x (expr_eval E s)).
    constructor.
  (* heap reading *)
  - right. cut (exists v, h (expr_eval E s) = Some v).
    + intro H1. destruct H1 as (v&H1).
      exists Cskip, h, (sUpdate s x v). vauto.
    + rewrite <- option_not_none.
      intro H1. apply FAULT. vauto.
  (* heap writing *)
  - right. cut (exists v, h (expr_eval E1 s) = Some v).
    + intro H1. destruct H1 as (v&H1).
      exists Cskip, (hUpdate h (expr_eval E1 s) (Some (expr_eval E2 s))), s.
      by apply step_write with v.
    + rewrite <- option_not_none.
      intro H. apply FAULT. vauto.
  (* if-then-else *)
  - assert (H1 : cond_eval B s = true \/ cond_eval B s = false)
      by apply cond_eval_excl.
    right. destruct H1 as [H1|H1].
    + exists C1, h, s. vauto.
    + exists C2, h, s. vauto.
  (* while *)
  - right. exists (Cite B (Cseq C (Cwhile B C)) Cskip), h, s. vauto.
  (* parallel composition *)
  - right.
    cut ((~ cmd_locked C2 /\ exists C1' h' s', step h s C1 h' s' C1') \/
         (~ cmd_locked C1 /\ exists C2' h' s', step h s C2 h' s' C2') \/
          C1 = Cskip /\ C2 = Cskip).
    (* progress for all three cases in the cut *)
    + intro H. destruct H as [H|[H|H]].
      (* [C1] makes a step *)
      * destruct H as (H&C1'&h'&s'&STEP).
        exists (Cpar C1' C2), h', s'. vauto.
      (* [C2] makes a step *)
      * destruct H as (H&C2'&h'&s'&STEP).
        exists (Cpar C1 C2'), h', s'. vauto.
      (* [C1] and [C2] have both terminated *)
      * destruct H as (H1&H2). clarify.
        exists Cskip, h, s. vauto.
    (* one of the three cases in the cut must hold *)
    + assert (H1 : C1 = Cskip \/ ~ C1 = Cskip) by apply classic.
      assert (H2 : C2 = Cskip \/ ~ C2 = Cskip) by apply classic.
      desf.
      (* [C1] and [C2] have both terminated *)
      * by repeat right.
      (* [C2] has terminated, [C1] has not *)
      * left. split. intro H3. inv H3.
        apply imply_and_or with (C1 = Cskip); vauto.
        apply IH1. intro FAULT'.
        apply FAULT. vauto.
      (* [C1] has terminated, [C2] has not *)
      * right. left. split.
        ** intro H3. inv H3.
        ** apply imply_and_or with (C2 = Cskip); vauto.
           apply IH2. intro FAULT'.
           apply FAULT. vauto.
      (* [C1] and [C2] have both not terminated *)
      * assert (H3 : cmd_locked C1 \/ ~ cmd_locked C1) by apply classic.
        destruct H3 as [H3|H3].
        (* [C1] is locked *)
        ** assert (H : ~ cmd_locked C2). {
            intro H4. apply FAULT. vauto. }
           left. split. auto.
           apply imply_and_or with (C1 = Cskip); vauto.
           apply IH1. intro FAULT'.
           apply FAULT. vauto.
        (* [C1] is not locked *)
        ** right. left. split. auto.
           apply imply_and_or with (C2 = Cskip); vauto.
           apply IH2. intro FAULT'.
           apply FAULT. vauto.
  (* heap (de)allocation *)
  - right. cut (exists l, h l = None).
    + intro H. destruct H as (l&H).
      exists Cskip, (hUpdate h l (Some (expr_eval E s))), (sUpdate s x l). vauto.
    + apply NNPP. intro H. apply FAULT. vauto.
  - right. exists Cskip,
      (hUpdate h (expr_eval E s) None), s. vauto.
  (* atomics *)
  - right. exists (Cinatom C), h, s. vauto.
  - assert (H : C = Cskip \/ ~ C = Cskip) by apply classic.
    destruct H as [H|H].
    (* [C] has terminated *)
    + clarify. right. exists Cskip, h, s. vauto.
    (* [C] has not terminated *)
    + cut (~ fault h s C).
      * intro H1. apply IH in H1.
        destruct H1 as [H1|H1]; vauto.
        destruct H1 as (C'&h'&s'&STEP).
        right. exists (Cinatom C'), h', s'. vauto.
      * intro H1. apply FAULT. vauto.
  (* process init *)
  - right. exists Cskip, h, s. vauto.
  (* actions *)
  - right. exists (Cinact PMnone C), h, s. vauto.
  - assert (H : C = Cskip \/ ~ C = Cskip) by apply classic.
    right. destruct H as [H|H].
    (* [C] has terminated *)
    + clarify. exists Cskip, h, s.
      destruct m. vauto.
    (* [C] has not terminated *)
    + cut (~ fault h s C).
      * intro H1. apply IH in H1.
        destruct H1 as [H1|H1]; vauto.
        destruct H1 as (C'&h'&s'&STEP).
        exists (Cinact m C'), h', s'.
        destruct m. vauto.
      * intro H1. apply FAULT. vauto.
  (* process end *)
  - right. exists Cskip, h, s. vauto.
  (* querying *)
  - right. exists Cskip, h, s. vauto.
Qed.


(** ** Ghost operational semantics *)

(** The _ghost operational semantics_ of (ghost) programs is the
    lock-step execution of the (ordinary) operational semantics of
    programs and the execution of all its process-algebraic models. *)

(** Ghost commands are programs that maintain some extra metadata.
    In particular, every partially executed action program holds
    (1) the corresponding process identifier, (2) the action that is
    being executed, and (3) a _snapshot_ of the heap made when the
    action block started to be executed. *)

Inductive GhostMetadata :=
  | GMdata(pid : Val)(a : Act)(v : Val)(hs : Heap).

Add Search Blacklist "GhostMetadata_rect".
Add Search Blacklist "GhostMetadata_ind".
Add Search Blacklist "GhostMetadata_rec".
Add Search Blacklist "GhostMetadata_sind".

Definition GhostCmd : Type := Cmd GhostMetadata.

Inductive gstep : Heap -> ProcMap -> Store -> Store -> GhostCmd ->
                  Heap -> ProcMap -> Store -> Store -> GhostCmd -> Prop :=
  (* sequential *)
  | gstep_seq_l h pm s g C :
    gstep h pm s g (Cseq Cskip C) h pm s g C
  | gstep_seq_r h pm s g C1 C2 h' pm' s' g' C1' :
    gstep h pm s g C1 h' pm' s' g' C1' ->
    gstep h pm s g (Cseq C1 C2) h' pm' s' g' (Cseq C1' C2)
  (* assignment *)
  | gstep_assign h pm s g x E :
    let v := expr_eval E s in
    gstep h pm s g (Cass x E) h pm (sUpdate s x v) g Cskip
  (* heap reading *)
  | gstep_read h pm s g x E v :
    h (expr_eval E s) = Some v ->
    gstep h pm s g (Cread x E) h pm (sUpdate s x v) g Cskip
  (* heap writing *)
  | gstep_write h pm s g E1 E2 v :
    let l := expr_eval E1 s in
    let v' := expr_eval E2 s in
    h l = Some v ->
    gstep h pm s g (Cwrite E1 E2) (hUpdate h l (Some v')) pm s g Cskip
  (* if-then-else *)
  | gstep_ite_t h pm s g B C1 C2 :
    cond_eval B s = true ->
    gstep h pm s g (Cite B C1 C2) h pm s g C1
  | gstep_ite_f h pm s g B C1 C2 :
    cond_eval B s = false ->
    gstep h pm s g (Cite B C1 C2) h pm s g C2
  (* while *)
  | gstep_while h pm s g B C :
    gstep h pm s g (Cwhile B C) h pm s g (Cite B (Cseq C (Cwhile B C)) Cskip)
  (* heap (de)alloc *)
  | gstep_alloc h pm s g x E l :
    let v : Val := expr_eval E s in
    h l = None ->
    gstep h pm s g (Calloc x E) (hUpdate h l (Some v)) pm (sUpdate s x l) g Cskip
  | gstep_dispose h pm s g E :
    let l := expr_eval E s in
    gstep h pm s g (Cdispose E) (hUpdate h l None) pm s g Cskip
  (* atomics *)
  | gstep_atom h pm s g C :
    gstep h pm s g (Catomic C) h pm s g (Cinatom C)
  | gstep_inatom_l h pm s g C h' pm' s' g' C' :
    gstep h pm s g C h' pm' s' g' C' ->
    gstep h pm s g (Cinatom C) h' pm' s' g' (Cinatom C')
  | gstep_inatom_r h pm s g :
    gstep h pm s g (Cinatom Cskip) h pm s g Cskip
  (* parallel *)
  | gstep_par_l h pm s g C1 C2 h' pm' s' g' C1' :
    gstep h pm s g C1 h' pm' s' g' C1' ->
    ~ cmd_locked C2 ->
    gstep h pm s g (Cpar C1 C2) h' pm' s' g' (Cpar C1' C2)
  | gstep_par_r h pm s g C1 C2 h' pm' s' g' C2' :
    gstep h pm s g C2 h' pm' s' g' C2' ->
    ~ cmd_locked C1 ->
    gstep h pm s g (Cpar C1 C2) h' pm' s' g' (Cpar C1 C2')
  | gstep_par_done h pm s g :
    gstep h pm s g (Cpar Cskip Cskip) h pm s g Cskip
  (* processes *)
  | gstep_proc_init h pm s g x Pf E xs f pid :
    pm pid = PEfree ->
    let HP := Pf E in
    let P := pDehybridise HP s in
    let f' := expr_eval_map f s in
    gstep h pm s g (Cproc x Pf E xs f) h (pmUpdate pm pid (PEelem perm_full P xs f')) s (sUpdate g x pid) Cskip
  | gstep_proc_end h pm s g x P xs f :
    let pid := g x in
    pmeBisim (pm pid) (PEelem perm_full P xs f) ->
    pterm P ->
    gstep h pm s g (Cendproc x) h (pmUpdate pm pid PEfree) s g Cskip
  (* actions *)
  | gstep_act h pm s g x a E C :
    let v := expr_eval E s in
    let m := GMdata (g x) a v h in
    gstep h pm s g (Cact x a E C) h pm s g (Cinact m C)
  | gstep_act_l h pm s g m C h' pm' s' g' C' :
    gstep h pm s g C h' pm' s' g' C' ->
    gstep h pm s g (Cinact m C) h' pm' s' g' (Cinact m C')
  | gstep_act_r h pm s g pid a v hs q P P' xs f ps1 ps2 :
    pmeBisim (pm pid) (PEelem q P xs f) ->
      (forall x, In x xs -> hs (f x) = Some (ps1 x)) ->
      (forall x, In x xs -> h (f x) = Some (ps2 x)) ->
    pstep P ps1 (PLact a v) P' ps2 ->
    let pm' := pmUpdate pm pid (PEelem q P' xs f) in
    gstep h pm s g (Cinact (GMdata pid a v hs) Cskip) h pm' s g Cskip
  (* querying *)
  | gstep_query g x pm q P xs f ps P' s h :
    let pid := g x in
    pmeBisim (pm pid) (PEelem q P xs f) ->
    (forall x, In x xs -> h (f x) = Some (ps x)) ->
    pstep P ps PLassert P' ps ->
    let pm' := pmUpdate pm pid (PEelem q P' xs f) in
    gstep h pm s g (Cquery x) h pm' s g Cskip.

Add Search Blacklist "gstep_ind".
Add Search Blacklist "gstep_sind".

(** The reduction rules of the standard operational semantics
    are embedded in the reduction rules of the ghost operational
    semantics, as is shown by the following theorem. *)

Theorem gstep_sim :
  forall C h pm s g C' h' pm' s' g',
  gstep h pm s g C h' pm' s' g' C' ->
  step h s (plain C) h' s' (plain C').
Proof.
  cmd_induction C; intros h pm s g C' h' pm' s' g' STEP;
    simpls; inv STEP; clear STEP; simpls; vauto.
  (* sequential *)
  - constructor. by apply IH1 in H10.
  (* parallel *)
  - constructor. by apply IH1 in H5.
    by rewrite cmd_locked_plain.
  - constructor. by apply IH2 in H5.
    by rewrite cmd_locked_plain.
  (* atomics *)
  - constructor. by apply IH in H4.
  (* actions *)
  - constructor. by apply IH in H10.
Qed.

(** Moreover, the ghost operational semantics can mimick
    the steps of the standard operational semantics
    for any basic program. *)

Theorem step_basic_sim :
  forall C h pm s g C' h' s',
  cmd_basic C ->
  step h s (plain C) h' s' C' ->
  exists C'', gstep h pm s g C h' pm s' g C'' /\ C' = plain C''.
Proof.
  cmd_induction C; intros h pm s g C' h' s' H1 STEP; simpls;
    inv STEP; simpls; vauto; try (by exists Cskip; vauto).
  (* sequential *)
  - apply IH1 with (pm := pm)(g := g) in H7; [|intuition].
    destruct H7 as (C1''&H7&H2).
    exists (Cseq C1'' C2). vauto.
  - symmetry in H3. apply plain_skip in H3. clarify.
    exists C2. vauto.
  (* if-then-else *)
  - exists C1. vauto.
  - exists C2. vauto.
  (* while *)
  - exists (Cite B (Cseq C (Cwhile B C)) Cskip). vauto.
  (* parallel *)
  - apply IH1 with (pm := pm)(g := g) in H4; [|intuition].
    destruct H4 as (C1''&H4&H5).
    exists (Cpar C1'' C2). intuition vauto.
    apply gstep_par_l; auto. intro H5.
    apply H8. by rewrite cmd_locked_plain.
  - apply IH2 with (pm := pm)(g := g) in H4; [|intuition].
    destruct H4 as (C2''&H4&H5).
    exists (Cpar C1 C2''). intuition vauto.
    apply gstep_par_r; auto. intro H5.
    apply H8. by rewrite cmd_locked_plain.
  - symmetry in H3, H4. apply plain_skip in H3.
    apply plain_skip in H4. clarify.
    exists Cskip. intuition vauto.
  (* atomics *)
  - exists (Cinatom C). vauto.
  - apply IH with (pm := pm)(g := g) in H3; vauto.
    destruct H3 as (C''&H3&H4). clarify.
    exists (Cinatom C''). vauto.
  - exists Cskip. split; vauto.
    symmetry in H3. apply plain_skip in H3.
    clarify. vauto.
Qed.

(** Program basicality, well-formedness and process map finiteness
    all remain invariant during ghost program execution. *)

Lemma gstep_basic_pres :
  forall C h pm s g C' h' pm' s' g',
  gstep h pm s g C h' pm' s' g' C' ->
  cmd_basic C ->
  cmd_basic C'.
Proof.
  cmd_induction C; intros h pm s g C' h' pm' s' g' STEP H1;
    inv STEP; clear STEP; simpls; try (intuition vauto; fail).
  (* sequential *)
  - destruct H1 as (H1&H2).
    split; auto. by apply IH1 in H11.
  (* parallel *)
  - destruct H1 as (H1&H2&H3).
    repeat split; auto.
    + by apply IH1 in H6.
    + intros (H4&H5). apply H3. intuition.
  - destruct H1 as (H1&H2&H3).
    repeat split; auto.
    + by apply IH2 in H6.
    + intros (H4&H5). apply H3. intuition.
  (* atomics *)
  - apply IH in H5; vauto.
Qed.

Lemma gstep_wf_pres :
  forall C h pm s g C' h' pm' s' g',
  gstep h pm s g C h' pm' s' g' C' ->
  cmd_wf C ->
  cmd_wf C'.
Proof.
  cmd_induction C; intros h pm s g C' h' pm' s' g' STEP H1;
    inv STEP; clear STEP; simpls; try (intuition vauto; fail).
  (* sequential *)
  - destruct H1 as (H1&H2).
    split; auto. by apply IH1 in H11.
  (* parallel *)
  - destruct H1 as (H1&H2&H3).
    repeat split; auto.
    + by apply IH1 in H6.
    + intros (H4&H5). apply H3. intuition.
  - destruct H1 as (H1&H2&H3).
    repeat split; auto.
    + by apply IH2 in H6.
    + intros (H4&H5). apply H3. intuition.
  (* atomics *)
  - by apply IH in H5.
  - by apply gstep_basic_pres in H11.
Qed.

Lemma gstep_pmFinite_pres :
  forall C h pm s g C' h' pm' s' g',
  gstep h pm s g C h' pm' s' g' C' ->
  pmFinite pm ->
  pmFinite pm'.
Proof.
  cmd_induction C; intros h pm s g C' h' pm' s' g' STEP FIN;
    inv STEP; vauto.
  (* sequential *)
  - by apply IH1 in H10.
  (* parallel *)
  - by apply IH1 in H5.
  - by apply IH2 in H5.
  (* atomics *)
  - by apply IH in H4.
  (* process init *)
  - by apply pmFinite_update.
  (* actions *)
  - by apply IH in H10.
  - by apply pmFinite_update.
  (* querying *)
  - by apply pmFinite_update.
  (* process end *)
  - by apply pmFinite_update.
Qed.

(** The ghost semantics can simulate computation steps
    made with bisimilar process maps. *)

Lemma gstep_procmap_eq :
  forall C h pm1 pm2 s g C' h' pm1' s' g',
    pmBisim pm1 pm2 ->
    gstep h pm1 s g C h' pm1' s' g' C' ->
  exists pm2',
    gstep h pm2 s g C h' pm2' s' g' C' /\
    pmBisim pm1' pm2'.
Proof.
  cmd_induction C; intros h pm1 pm2 s g C' h' pm1' s' g' H1 STEP;
    inv STEP; clear STEP; simpls;
    try (exists pm2; intuition constructor; auto; fail).
  (* sequential *)
  - apply IH1 with (pm2 := pm2) in H11; auto.
    destruct H11 as (pm2'&H2&H3).
    exists pm2'. intuition by constructor.
  (* heap writing *)
  - exists pm2. split; auto.
    apply gstep_write with v. auto.
  (* parallel *)
  - apply IH1 with (pm2 := pm2) in H6; auto.
    destruct H6 as (pm2'&H2&H3).
    exists pm2'. split; vauto.
  - apply IH2 with (pm2 := pm2) in H6; auto.
    destruct H6 as (pm2'&H2&H3).
    exists pm2'. split; vauto.
  (* atomics *)
  - apply IH with (pm2 := pm2) in H5; auto.
    destruct H5 as (pm2'&H2&H3).
    exists pm2'. split; vauto.
  (* process init *)
  - rename P0 into P'.
    exists (pmUpdate pm2 pid (PEelem perm_full P' xs f')).
    split. constructor; auto.
    by apply pmBisim_free with pm1.
    by rewrite H1.
  (* actions *)
  - apply IH with (pm2:=pm2) in H11; auto.
    destruct H11 as (pm2'&H2&H3).
    exists pm2'. split; vauto.
  - subst pm'.
    exists (pmUpdate pm2 pid (PEelem q P' xs f)).
    split; vauto.
    + apply gstep_act_r with P ps1 ps2; auto.
      red in H1. by rewrite <- H1.
    + intro pid'. unfold pmUpdate, update. desf.
  (* querying *)
  - rename pid0 into pid'.
    exists (pmUpdate pm2 pid (PEelem q P' xs f)).
    split; vauto.
    + apply gstep_query with P ps; auto.
      by rewrite <- H1.
    + subst pm'. by rewrite H1.
  (* process end *)
  - rename pid0 into pid'.
    exists (pmUpdate pm2 pid' PEfree). split; vauto.
    + apply gstep_proc_end with P xs f; vauto.
      subst pid'. rewrite <- H0. symmetry. by apply H1.
    + intro pid''. unfold pmUpdate, update. desf.
Qed.

(** The sets of free and modified variables do not grow
    during program ghost execution. *)

Lemma gstep_fv_mod_g :
  forall C h pm s g C' h' pm' s' g' x,
  gstep h pm s g C h' pm' s' g' C' ->
  ~ cmd_mod C x -> g x = g' x.
Proof.
  cmd_induction C; intros h pm s g C' h' pm' s' g' y STEP H2;
    inv STEP; simpls.
  (* sequential *)
  - apply IH1 with (x := y) in H11; vauto.
    intro. apply H2. by left.
  (* parallel *)
  - apply IH1 with (x := y) in H6. vauto.
    intro. apply H2. by left.
  - apply IH2 with (x := y) in H6; vauto.
    intro. apply H2. by right.
  (* atomics *)
  - apply IH with (x := y) in H5; vauto.
  (* processes *)
  - intuition vauto.
    unfold sUpdate, update. desf.
  (* actions *)
  - apply IH with (x := y) in H11; desf.
Qed.

Lemma gstep_fv_mod :
  forall C h pm s g C' h' pm' s' g',
  gstep h pm s g C h' pm' s' g' C' ->
    (forall x, cmd_fv C' x -> cmd_fv C x) /\
    (forall x, cmd_mod C' x -> cmd_mod C x) /\
    (forall x, ~ cmd_mod C x -> s x = s' x) /\
    (forall x, ~ cmd_mod C x -> g x = g' x).
Proof.
  intros C h pm s g C' h' pm' s' g' STEP.
  generalize STEP. intro STEP'.
  apply gstep_sim, step_fv_mod in STEP.
  repeat rewrite <- cmd_fv_plain in STEP.
  repeat rewrite <- cmd_mod_plain in STEP.
  destruct STEP as (F1&F2&F3).
  repeat split; vauto. intros x H.
  apply gstep_fv_mod_g with (x := x) in STEP'; vauto.
Qed.

(** Program ghost execution commutes with store agreement. *)

Lemma gstep_agree :
  forall C h pm s1 s2 g C' h' pm' s1' g' (phi : Var -> Prop),
    (forall x, cmd_fv C x -> phi x) ->
    (forall x, phi x -> s1 x = s2 x) ->
    gstep h pm s1 g C h' pm' s1' g' C' ->
  exists s2',
    (forall x, phi x -> s1' x = s2' x) /\
    gstep h pm s2 g C h' pm' s2' g' C'.
Proof.
  cmd_induction C; intros h pm s1 s2 g C' h' pm' s1' g' phi H1 H2 STEP;
    inv STEP; clear STEP; simpls;
    try (exists s2; intuition vauto; fail).
  (* sequential *)
  - apply IH1 with (s2:=s2)(phi:=phi) in H12; auto.
    destruct H12 as (s2'&H3&H4).
    exists s2'. split; vauto.
  (* assignment *)
  - exists (sUpdate s2 x (expr_eval E s2)).
    split; vauto. intros y H3.
    unfold sUpdate, update.
    destruct (var_eq_dec x y); auto. clarify.
    rewrite <- expr_agree with (s1:=s1); auto.
    red. intros x H4. apply H2, H1. by right.
  (* heap reading *)
  - rewrite expr_agree with (s2:=s2) in H12; vauto.
    exists (sUpdate s2 x v). split; vauto.
    intros y H3. unfold sUpdate, update.
    destruct (var_eq_dec x y); vauto.
    by apply H2. red. intros y H4.
    apply H2, H1. by right.
  (* heap writing *)
  - subst l l0 v' v'0.
    exists s2. split; vauto.
    rewrite expr_agree with (s2:=s2) in H12; vauto.
    repeat rewrite expr_agree with (s1:=s1')(s2:=s2); vauto.
    red. ins. apply H2, H1. by right.
    red. ins. apply H2, H1. by left.
    red. ins. apply H2, H1. by left.
  (* if-then-else *)
  - exists s2. split; vauto. constructor.
    rewrite <- cond_agree with (s1:=s1'); auto.
    red. ins. apply H2, H1. by left.
  - exists s2. split; vauto. constructor.
    rewrite <- cond_agree with (s1:=s1'); auto.
    red. ins. apply H2, H1. by left.
  (* parallel *)
  - apply IH1 with (s2:=s2)(phi:=phi) in H7; vauto.
    destruct H7 as (s2'&H3&H4).
    exists s2'. split; vauto.
    intros x H3. apply H1. by left.
  - apply IH2 with (s2:=s2)(phi:=phi) in H7; vauto.
    destruct H7 as (s2'&H3&H4).
    exists s2'. split; vauto.
    intros x H3. apply H1. by right.
  (* heap (de)allocation *)
  - subst v. rewrite expr_agree with (s2:=s2).
    exists (sUpdate s2 x l). split; vauto.
    intros y H3. unfold sUpdate, update.
    destruct (var_eq_dec x y); vauto.
    by apply H2. red. intros y H3.
    apply H2, H1. by right.
  - subst l l0. exists s2. split; vauto.
    rewrite expr_agree with (s2:=s2); vauto.
    red. ins. by apply H2, H1.
  (* atomic programs *)
  - apply IH with (s2:=s2)(phi:=phi) in H6; vauto.
    destruct H6 as (s2'&H3&H4).
    exists s2'. split; vauto.
  (* processes *)
  - subst f' f'0. exists s2. split; vauto.
    subst P0 HP0 P.
    rewrite pDehybridise_agree with (s2:=s2); vauto.
    2:{ red. intros y H3. apply H2, H1.
        repeat right. by exists E. }
    rewrite expr_map_agree with (s3:=s2); vauto.
    intros y H4. apply H2, H1. right. right. by left.
  (* actions *)
  - exists s2. split; auto. subst m v.
    rewrite expr_agree with (s2:=s2); [|auto].
    apply gstep_act. red. intros y H3.
    apply H2. apply H1. right. by left.
  - apply IH with (s2:=s2)(phi:=phi) in H12; vauto.
    destruct H12 as (s2'&H3&H4).
    exists s2'. split; vauto.
Qed.

Lemma gstep_agree_g :
  forall C h pm s g1 g2 C' h' pm' s' g1' (phi : Var -> Prop),
    (forall x, cmd_fv C x -> phi x) ->
    (forall x, phi x -> g1 x = g2 x) ->
    gstep h pm s g1 C h' pm' s' g1' C' ->
  exists g2',
    (forall x, phi x -> g1' x = g2' x) /\
    gstep h pm s g2 C h' pm' s' g2' C'.
Proof.
  cmd_induction C; intros h pm s g1 g2 C' h' pm' s' g1' phi H1 H2 STEP;
    inv STEP; clear STEP; simpls;
    try (exists g2; intuition vauto; fail).
  (* sequential *)
  - apply IH1 with (g2:=g2)(phi:=phi) in H12; auto.
    destruct H12 as (g2'&H3&H4).
    exists g2'. split; vauto.
  (* parallel *)
  - apply IH1 with (g2:=g2)(phi:=phi) in H7; vauto.
    destruct H7 as (g2'&H3&H4).
    exists g2'. split; vauto.
    intros x H. apply H1. by left.
  - apply IH2 with (g2:=g2)(phi:=phi) in H7; vauto.
    destruct H7 as (g2'&H3&H4).
    exists g2'. split; vauto.
    intros x H. apply H1. by right.
  (* atomics *)
  - apply IH with (g2:=g2)(phi:=phi) in H6; vauto.
    destruct H6 as (g2'&H3&H4).
    exists g2'. intuition vauto.
  (* process init *)
  - exists (sUpdate g2 x pid).
    split; vauto. intros y H3.
    unfold sUpdate, update.
    destruct (var_eq_dec x y); auto.
  (* actions *)
  - exists g2. split; auto. subst m v.
    rewrite H2; [|auto]. apply gstep_act.
  - apply IH with (g2:=g2)(phi:=phi) in H12; vauto.
    destruct H12 as (g2'&H3&H4).
    exists g2'. intuition vauto.
  (* querying *)
  - exists g2. intuition. subst pm'0.
    subst pid pid0 pid1.
    rewrite H2 in *; vauto; apply H1; vauto.
  (* process end *)
  - subst pid pid0.
    exists g2. split; vauto.
    rewrite H2 in *; vauto; apply H1; auto.
Qed.

(** The following lemma is for later convenience. *)

Lemma gstep_agree_sim :
  forall C h pm s1 s2 g C' h' pm' s1' s2' g',
    (forall x, cmd_fv C x -> s1 x = s2 x) ->
    (forall x, cmd_fv C x -> s1' x = s2' x) ->
  step h s1 (plain C) h' s1' (plain C') ->
  gstep h pm s2 g C h' pm' s2' g' C' ->
  gstep h pm s1 g C h' pm' s1' g' C'.
Proof.
  cmd_induction C; intros h pm s1 s2 g C' h' pm' s1' s2' g' F1 F2 STEP GSTEP;
    inv STEP; clear STEP; inv GSTEP; clear GSTEP; simpls;
    try (desf; intuition vauto; fail).
  (* sequential *)
  - inv H5.
  - rename C1'0 into C1''.
    apply IH1 with (s1:=s1)(s1':=s1') in H12; vauto.
    intros x H. apply F1. by left.
    intros x H. apply F2. by left.
  - symmetry in H2. apply plain_skip in H2.
    clarify. inv H12.
  (* if-then-else *)
  - constructor. rewrite cond_agree with (s2 := s2'); auto.
    red. intros x H. apply F1. by left.
  - constructor. rewrite cond_agree with (s2 := s2'); auto.
    red. intros x H. apply F1. by left.
  (* parallel *)
  - rename C1'0 into C1''. apply gstep_par_l; auto.
    apply IH1 with s2 s2'; vauto.
    intros x H. apply F1. by left.
    intros x H. apply F2. by left.
  - simpls. vauto. by apply step_neg_C in H6.
  - simpls. vauto. by apply step_neg_C in H6.
  - apply gstep_par_r; auto.
    apply IH2 with s2 s2'; vauto.
    intros x H. apply F1. by right.
    intros x H. apply F2. by right.
  (* heap allocation *)
  - subst v0. clear H6.
    assert (H1 : sUpdate s1 x l x = sUpdate s2 x l0 x). {
      apply F2. by left. }
    unfold sUpdate, update in H1.
    destruct (var_eq_dec x x) as [_|H2]; vauto.
    rewrite <- expr_agree with (s1 := s1).
    by constructor. red.
    intros y H. apply F1. by right.
  (* atomics *)
  - rename C'1 into C'. constructor.
    apply IH with s2 s2'; vauto.
  (* processes *)
  - subst f' f'0. clear H4. subst P0 HP0 P.
    rewrite <- pDehybridise_agree with (s1:=s1'); vauto.
    2:{ red. intros y H3. apply F2.
        repeat right. by exists E. }
    rewrite <- expr_map_agree with (s1:=s1'); vauto.
    intros y H. apply F2. right. right. by left.
  (* actions *)
  - clear H3. subst m v.
    rewrite expr_agree with (s2:=s1').
    + apply gstep_act.
    + red. intros y H1. symmetry. apply F2.
      right. by left.
  - rename C'1 into C'. constructor.
    apply IH with s2 s2'; vauto.
Qed.

(** Ghost steps in basic programs do not affect
    the ghost components [pm] and [g]. *)

Lemma gstep_basic_ghostdata_pres :
  forall C h pm s g C' h' pm' s' g',
  cmd_basic C ->
  gstep h pm s g C h' pm' s' g' C' ->
  pm = pm' /\ g = g'.
Proof.
  cmd_induction C; intros h pm s g C' h' pm' s' g' BASIC STEP;
    vauto; inv STEP; vauto.
  (* sequential *)
  - apply IH1 in H10; intuition vauto.
    simpl in BASIC. desf.
  (* parallel *)
  - apply IH1 in H5; intuition vauto.
    simpl in BASIC. desf.
  - apply IH2 in H5; intuition vauto.
    simpl in BASIC. desf.
  (* atomics *)
  - apply IH in H4; vauto.
Qed.


(** *** Ghost fault semantics *)

(** The ghost fault semantics defines the notions of data-races
    and memory-safety, likewise to [fault], as well as all necessary
    conditions for a configuration in the ghost semantics to make
    progress (see [gstep_progress] for the proof). *)

Inductive gfault : Heap -> ProcMap -> Store -> Store -> GhostCmd -> Prop :=
  (* heap reading *)
  | gfault_read h pm s g x E :
    h (expr_eval E s) = None ->
    gfault h pm s g (Cread x E)
  (* heap writing *)
  | gfault_write h pm s g E1 E2 :
    h (expr_eval E1 s) = None ->
    gfault h pm s g (Cwrite E1 E2)
  (* heap allocation *)
  | gfault_alloc h pm s g x E :
    (~ exists l, h l = None) ->
    gfault h pm s g (Calloc x E)
  (* heap deallocation *)
  | gfault_dispose h pm s g E :
    h (expr_eval E s) = None ->
    gfault h pm s g (Cdispose E)
  (* sequential *)
  | gfault_seq h pm s g C1 C2 :
    gfault h pm s g C1 ->
    gfault h pm s g (Cseq C1 C2)
  (* atomics *)
  | gfault_atom h pm s g C :
    gfault h pm s g C ->
    gfault h pm s g (Cinatom C)
  (* parallel *)
  | gfault_par_l h pm s g C1 C2 :
    gfault h pm s g C1 ->
    ~ cmd_locked C2 ->
    gfault h pm s g (Cpar C1 C2)
  | gfault_par_r h pm s g C1 C2 :
    gfault h pm s g C2 ->
    ~ cmd_locked C1 ->
    gfault h pm s g (Cpar C1 C2)
  | gfault_par_deadlock h pm s g C1 C2 :
    cmd_locked C1 ->
    cmd_locked C2 ->
    gfault h pm s g (Cpar C1 C2)
  (* actions *)
  | gfault_act_step h pm s g m C :
    gfault h pm s g C ->
    gfault h pm s g (Cinact m C)
  | gfault_act_end_1 h pm s g pid a v hs :
    (~ pmeOcc (pm pid)) ->
    gfault h pm s g (Cinact (GMdata pid a v hs) Cskip)
  | gfault_act_end_2 h pm s g pid a v hs q P xs f :
    pmeBisim (pm pid) (PEelem q P xs f) ->
    (exists x, In x xs /\ hs (f x) = None) ->
    gfault h pm s g (Cinact (GMdata pid a v hs) Cskip)
  | gfault_act_end_3 h pm s g pid a v hs q P xs f :
    pmeBisim (pm pid) (PEelem q P xs f) ->
    (exists x, In x xs /\ h (f x) = None) ->
    gfault h pm s g (Cinact (GMdata pid a v hs) Cskip)
  | gfault_act_end_4 h pm s g pid a v hs q P xs f ps1 ps2 :
    pmeBisim (pm pid) (PEelem q P xs f) ->
      (forall x, In x xs -> hs (f x) = Some (ps1 x)) ->
      (forall x, In x xs -> h (f x) = Some (ps2 x)) ->
      (~ exists P', pstep P ps1 (PLact a v) P' ps2) ->
    gfault h pm s g (Cinact (GMdata pid a v hs) Cskip)
  (* processes *)
  | gfault_proc_init h pm s g x P E xs f :
    (~ exists pid, pm pid = PEfree) ->
    gfault h pm s g (Cproc x P E xs f)
  | gfault_proc_end_1 h pm s g x :
    ~ pmeEntire (pm (g x)) ->
    gfault h pm s g (Cendproc x)
  | gfault_proc_end_2 h pm s g x P xs f :
    pmeBisim (pm (g x)) (PEelem perm_full P xs f) ->
    ~ pterm P ->
    gfault h pm s g (Cendproc x)
  (* querying *)
  | gfault_query_1 h pm s g x :
    let pid := g x in
    (~ pmeOcc (pm pid)) ->
    gfault h pm s g (Cquery x)
  | gfault_query_2 h pm s g x q P xs f :
    let pid := g x in
    pmeBisim (pm pid) (PEelem q P xs f) ->
    (exists y, In y xs /\ h (f y) = None) ->
    gfault h pm s g (Cquery x)
  | gfault_query_3 h pm s g x q P xs f ps :
    let pid := g x in
    pmeBisim (pm pid) (PEelem q P xs f) ->
      (forall x, In x xs -> h (f x) = Some (ps x)) ->
      (~ exists P', pstep P ps (PLassert) P' ps) ->
    gfault h pm s g (Cquery x)
  (* data races *)
  | gfault_race_l h pm s g C1 C2 :
    ~ cmd_locked C1 ->
    ~ cmd_locked C2 ->
    ~ disjoint (cmd_writes C1 s) (cmd_acc C2 s) ->
    gfault h pm s g (Cpar C1 C2)
  | gfault_race_r h pm s g C1 C2 :
    ~ cmd_locked C1 ->
    ~ cmd_locked C2 ->
    ~ disjoint (cmd_acc C1 s) (cmd_writes C2 s) ->
    gfault h pm s g (Cpar C1 C2).

Add Search Blacklist "gfault_ind".
Add Search Blacklist "gfault_sind".

(** The program fault semantics is embedded
    in the ghost fault semantics. *)

Theorem fault_emb :
  forall C h pm s g,
  fault h s (plain C) ->
  gfault h pm s g C.
Proof.
  cmd_induction C; intros h pm s g FAULT; simpls;
    inv FAULT; clear FAULT; vauto.
  (* sequential *)
  - constructor. by apply IH1.
  (* parallel *)
  - apply gfault_par_l.
    + by apply IH1.
    + by rewrite <- cmd_locked_plain.
  - apply gfault_par_r.
    + by apply IH2.
    + by rewrite <- cmd_locked_plain.
  - apply gfault_par_deadlock; by rewrite <- cmd_locked_plain.
  (* data races *)
  - apply gfault_race_l.
    + intro H2. apply H1. by rewrite cmd_locked_plain.
    + intro H2. apply H4. by rewrite cmd_locked_plain.
    + intro H2. apply H5. rewrite cmd_writes_plain.
      by rewrite cmd_acc_plain.
  - apply gfault_race_r.
    + intro H2. apply H1. by rewrite cmd_locked_plain.
    + intro H2. apply H4. by rewrite cmd_locked_plain.
    + intro H2. apply H5. rewrite cmd_writes_plain.
      by rewrite cmd_acc_plain.
  (* atomics *)
  - constructor. by apply IH.
  (* actions *)
  - constructor. by apply IH.
Qed.

(** The following theorem shows that ghost reduction steps are
    _progressive_ for non-faulty programs. Being progressive means
    that any ghost configuration that does not fault has either
    terminated or can make another computation step. *)

Lemma heap_procvar_cover :
  forall (xs : list ProcVar)(h : Heap)(f : ProcVar -> Val),
    (forall x, In x xs -> h (f x) <> None) ->
  exists g : ProcVar -> Val,
    forall x, In x xs -> h (f x) = Some (g x).
Proof.
  induction xs as [|x xs IH]; intros h f H1.
  (* nil case *)
  - simpls. exists (fun _ => val_unit).
    intros x H2. contradiction.
  (* cons case *)
  - specialize IH with h f.
    cut (forall x, In x xs -> h (f x) <> None).
    + intros H2. apply IH in H2.
      destruct H2 as (g&H2).
      cut (exists v, h (f x) = Some v).
      * intro H3. destruct H3 as (v&H3).
        exists (update procvar_eq_dec g x v).
        intros y H4. unfold update. desf.
        simpls. desf. by apply H2.
      * rewrite <- option_not_none.
        apply H1. vauto.
    + intros y H2. apply H1. simpls. intuition.
Qed.

Theorem gstep_progress :
  forall C h pm s g,
  ~ gfault h pm s g C ->
  C = Cskip \/ exists C' h' pm' s' g', gstep h pm s g C h' pm' s' g' C'.
Proof.
  cmd_induction C; intros h pm s g FAULT.
  (* empty programs *)
  - by left.
  (* sequential *)
  - cut (C1 = Cskip \/ ~ C1 = Cskip); [|apply classic].
    intros [H | H]; right.
    (* left program [C1] is empty *)
    + clarify. exists C2, h, pm, s, g. vauto.
    (* left program [C1] is not empty *)
    + assert (H1 : ~ gfault h pm s g C1). {
      intro H1. apply FAULT. vauto. }
      apply IH1 in H1.
      destruct H1 as [H1 | H1]; vauto.
      destruct H1 as (C1'&h'&pm'&s'&g'&STEP).
      exists (Cseq C1' C2), h', pm', s', g'. vauto.
  (* local assignment *)
  - right. exists Cskip, h, pm, (sUpdate s x (expr_eval E s)), g. vauto.
  (* heap reading *)
  - right. cut (exists v, h (expr_eval E s) = Some v).
    + intro H1. destruct H1 as (v&H1).
      exists Cskip, h, pm, (sUpdate s x v), g. vauto.
    + rewrite <- option_not_none.
      intro H1. apply FAULT. vauto.
  (* heap writing *)
  - right. cut (exists v, h (expr_eval E1 s) = Some v).
    + intro H1. destruct H1 as (v&H1).
      exists Cskip, (hUpdate h (expr_eval E1 s) (Some (expr_eval E2 s))), pm, s, g.
      by apply gstep_write with v.
    + rewrite <- option_not_none.
      intro H. apply FAULT. vauto.
  (* if-then-else *)
  - right. cut (cond_eval B s = true \/ cond_eval B s = false).
    + intro H1. destruct H1 as [H1 | H1].
      exists C1, h, pm, s, g. vauto.
      exists C2, h, pm, s, g. vauto.
    + rewrite <- Bool.not_true_iff_false.
      apply classic.
  (* while-loops *)
  - right. exists (Cite B (Cseq C (Cwhile B C)) Cskip), h, pm, s, g. vauto.
  (* parallel composition *)
  - right.
    cut ((~ cmd_locked C2 /\ exists C1' h' pm' s' g', gstep h pm s g C1 h' pm' s' g' C1') \/
         (~ cmd_locked C1 /\ exists C2' h' pm' s' g', gstep h pm s g C2 h' pm' s' g' C2') \/
          C1 = Cskip /\ C2 = Cskip).
    (* progress for all three cases in the cut *)
    + intro H. destruct H as [H | [H | H]].
      (* [C1] makes a step *)
      * destruct H as (H&C1'&h'&pm'&s'&g'&STEP).
        exists (Cpar C1' C2), h', pm', s', g'. vauto.
      (* [C2] makes a step *)
      * destruct H as (H&C2'&h'&pm'&s'&g'&STEP).
        exists (Cpar C1 C2'), h', pm', s', g'. vauto.
      (* [C1] and [C2] have both terminated *)
      * destruct H as (H1&H2). clarify.
        exists Cskip, h, pm, s, g. vauto.
    (* one of the three cases in the cut must hold *)
    + cut (C1 = Cskip \/ ~ C1 = Cskip); [|apply classic].
      cut (C2 = Cskip \/ ~ C2 = Cskip); [|apply classic].
      intros H1 H2. desf.
      (* [C1] and [C2] have both terminated *)
      * by repeat right.
      (* [C1] has terminated, [C2] has not *)
      * right. left. split.
        intro H2. inv H2.
        apply imply_and_or with (C2 = Cskip); vauto.
        apply IH2. intro FAULT'.
        apply FAULT. by constructor.
      (* [C2] has terminated, [C1] has not *)
      * left. split. intro H3. inv H3.
        apply imply_and_or with (C1 = Cskip); vauto.
        apply IH1. intro FAULT'.
        apply FAULT. by constructor.
      (* [C1] and [C2] have both not terminated *)
      * cut (cmd_locked C1 \/ ~ cmd_locked C1); [|apply classic].
        intro H3. destruct H3 as [H3 | H3].
        (* [C1] is locked *)
        ** assert (H4 : ~ cmd_locked C2). {
           intro H4. apply FAULT. by constructor. }
           left. split. auto.
           apply imply_and_or with (C1 = Cskip); vauto.
           apply IH1. intro FAULT'.
           apply FAULT. by constructor.
        (* [C1] is not locked *)
        ** right. left. split. auto.
           apply imply_and_or with (C2 = Cskip); vauto.
           apply IH2. intro FAULT'.
           apply FAULT. by constructor.
  (* heap allocation *)
  - right. cut (exists l, h l = None).
    + intro H. destruct H as (l&H).
      exists Cskip, (hUpdate h l (Some (expr_eval E s))), pm, (sUpdate s x l), g.
      by constructor.
    + apply NNPP. intro H.
      apply FAULT. by constructor.
  (* heap disposal *)
  - right.
    exists Cskip, (hUpdate h (expr_eval E s) None), pm, s, g.
    constructor.
  (* atomic block - init *)
  - right. exists (Cinatom C), h, pm, s, g. constructor.
  (* atomic block - step *)
  - right. cut (C = Cskip \/ ~ C = Cskip); [|apply classic].
    intro H. destruct H as [H | H].
    (* [C] has terminated *)
    + clarify. exists Cskip, h, pm, s, g. vauto.
    (* [C] has not terminated *)
    + cut (~ gfault h pm s g C).
      * intro H1. apply IH in H1.
        destruct H1 as [H1 | H1]; vauto.
        destruct H1 as (C'&h'&pm'&s'&g'&STEP).
        exists (Cinatom C'), h', pm', s', g'. vauto.
      * intro H1. apply FAULT. vauto.
  (* process - init *)
  - right. cut (exists pid, pm pid = PEfree).
    + intro H. destruct H as (pid&H).
      pose (HP := Pf E).
      pose (P := pDehybridise HP s).
      pose (f' := expr_eval_map f s).
      pose (pmv := PEelem perm_full P xs f').
      exists Cskip, h, (pmUpdate pm pid pmv), s, (sUpdate g x pid).
      by constructor.
    + apply NNPP. intro H.
      apply FAULT. by constructor.
  (* action - init *)
  - set (v := expr_eval E s).
    set (m := GMdata (g x) a v h).
    right. exists (Cinact m C), h, pm, s, g. vauto.
  (* action - step *)
  - right. cut (C = Cskip \/ ~ C = Cskip); [|apply classic].
    intro H. destruct H as [H|H].
    (* [C] has terminated *)
    + clarify. destruct m as [pid a v hs].
      assert (K1 : pmeOcc (pm pid)). {
        apply NNPP. intro K1. apply FAULT. vauto. }
      apply pmeOcc_destruct in K1.
      destruct K1 as (q&P&xs&F&K1).
      assert (K2 : exists ps1, forall x : ProcVar, In x xs -> hs (F x) = Some (ps1 x)). {
        apply heap_procvar_cover.
        intros x K2 K3. apply FAULT.
        apply gfault_act_end_2 with (q := q)(P := P)(xs := xs)(f := F); vauto.
        by rewrite K1. }
      assert (K3 : exists ps2, forall x : ProcVar, In x xs -> h (F x) = Some (ps2 x)). {
        apply heap_procvar_cover.
        intros x K3 K4. apply FAULT.
        apply gfault_act_end_3 with (q := q)(P := P)(xs := xs)(f := F); vauto.
        by rewrite K1. }
      destruct K2 as (ps1&K2).
      destruct K3 as (ps2&K3).
      assert (K4 : exists P', pstep P ps1 (PLact a v) P' ps2). {
        apply NNPP. intro K4. apply FAULT.
        apply gfault_act_end_4 with q P xs F ps1 ps2; vauto.
        by rewrite K1. }
      destruct K4 as (P'&K4).
      pose (pm' := pmUpdate pm pid (PEelem q P' xs F)).
      exists Cskip, h, pm', s, g.
      apply gstep_act_r with P ps1 ps2; vauto.
      by rewrite K1.
    (* [C] has not terminated *)
    + cut (~ gfault h pm s g C).
      * intro H1. apply IH in H1.
        destruct H1 as [H1 | H1]; vauto.
        destruct H1 as (C'&h'&pm'&s'&g'&STEP).
        exists (Cinact m C'), h', pm', s', g'. vauto.
      * intro H1. apply FAULT. vauto.
  (* querying *)
  - right. pose (pid := g x).
    assert (K1 : pmeOcc (pm pid)). {
      apply NNPP. intro K1. apply FAULT. vauto. }
    apply pmeOcc_destruct in K1.
      destruct K1 as (q&P&xs&F&K1).
    assert (K2 : exists ps, forall x, In x xs -> h (F x) = Some (ps x)). {
      apply heap_procvar_cover.
      intros y K3 K4. apply FAULT.
      apply gfault_query_2 with (q:=q)(P:=P)(xs:=xs)(f:=F); vauto.
      subst pid. by rewrite K1. }
    destruct K2 as (ps&K2).
    assert (K3 : exists P', pstep P ps (PLassert) P' ps). {
      apply NNPP. intro K3. apply FAULT.
      apply gfault_query_3 with q P xs F ps; vauto.
      subst pid. by rewrite K1. }
    destruct K3 as (P'&K3).
    pose (pm' := pmUpdate pm pid (PEelem q P' xs F)).
    exists Cskip, h, pm', s, g.
    apply gstep_query with P ps; vauto.
    subst pid. by rewrite K1.
  (* process - end *)
  - right. pose (pid := g x).
    exists Cskip, h, (pmUpdate pm pid PEfree), s, g.
    assert (H1 : pmeEntire (pm pid)). {
      apply NNPP. intro H. apply FAULT. vauto. }
    apply pmeEntire_content in H1.
    destruct H1 as (P&xs&f&H1).
    assert (H2 : pterm P). {
      apply NNPP. intro H. apply FAULT. subst pid.
      apply gfault_proc_end_2 with P xs f; vauto.
      rewrite H1. auto. }
    apply gstep_proc_end with P xs f; vauto.
    subst pid. by rewrite H1.
Qed.

(** The faulting of ghost programs is stable under replacement
    of process maps with bisimilar ones, as well as replacement of
    (ghost) stores with stores that agree on all variables
    occuring freely in the program. *)

Lemma gfault_pmBisim :
  forall C h pm1 pm2 s g,
  pmBisim pm1 pm2 -> gfault h pm1 s g C -> gfault h pm2 s g C.
Proof.
  cmd_induction C; intros h pm1 pm2 s g EQ FAULT; simpls;
    inv FAULT; clear FAULT; vauto.
  (* sequential *)
  - constructor. by apply IH1 with pm1.
  (* parallel *)
  - apply gfault_par_l. by apply IH1 with pm1.
    intro H1. by apply H6.
  - apply gfault_par_r. by apply IH2 with pm1.
    intro H1. by apply H6.
  (* atomics *)
  - constructor. by apply IH with pm1.
  (* process init *)
  - constructor. intro H.
    apply H4. destruct H as (pid&H).
    exists pid. apply pmBisim_free with pm2; auto.
    by symmetry.
  (* actions *)
  - constructor. by apply IH with pm1.
  - apply gfault_act_end_1. intro H1.
    red in EQ. red in EQ. specialize EQ with pid.
    rewrite <- EQ in H1. congruence.
  - destruct H6 as (x&H1&H2).
    red in EQ. red in EQ.
    specialize EQ with pid.
    rewrite H5 in EQ.
    unfold pmeBisim in EQ.
    remember (pm2 pid) as pm2v.
    destruct pm2v as [q' P' xs' f'| |]; vauto.
    desf. apply gfault_act_end_2 with q' P' xs' f'; vauto.
    + by rewrite Heqpm2v.
    + exists x. split; vauto.
      apply map_eq_In with (x0 := x) in EQ2; vauto.
      by rewrite <- EQ2.
  - destruct H6 as (x&H1&H2).
    red in EQ. red in EQ.
    specialize EQ with pid.
    rewrite H5 in EQ.
    unfold pmeBisim in EQ.
    remember (pm2 pid) as pm2v.
    destruct pm2v as [q' P' xs' f'| |]; vauto.
    desf. apply gfault_act_end_3 with q' P' xs' f'; vauto.
    + by rewrite Heqpm2v.
    + exists x. split; vauto.
      apply map_eq_In with (x0 := x) in EQ2; vauto.
      by rewrite <- EQ2.
  - red in EQ. red in EQ.
    specialize EQ with pid.
    rewrite H1 in EQ.
    unfold pmeBisim in EQ.
    remember (pm2 pid) as pm2v.
    destruct pm2v as [q' P' xs' f'| |]; vauto. desf.
    apply gfault_act_end_4 with q' P' xs' f' ps1 ps2; vauto.
    + by rewrite Heqpm2v.
    + intros x H3.
      apply map_eq_In with (x0 := x) in EQ2; vauto.
      rewrite <- EQ2. by apply H2.
    + intros x H3.
      apply map_eq_In with (x0 := x) in EQ2; vauto.
      rewrite <- EQ2. by apply H7.
    + intros H3. destruct H3 as (P''&H3).
      inv EQ0. clear EQ0. destruct H as (D1&D2&D3&D4).
      apply D4 in H3. destruct H3 as (Q&H3&H4).
      apply H8. exists Q. done.
  (* querying *)
  - apply gfault_query_1. intro H1.
    apply H4. by rewrite EQ.
  - destruct H5 as (y&H1&H2).
    red in EQ. red in EQ.
    specialize EQ with pid.
    rewrite H0 in EQ.
    unfold pmeBisim in EQ.
    remember (pm2 pid) as pm2v.
    destruct pm2v as [q' P' xs' f'| |]; vauto.
    desf. apply gfault_query_2 with q' P' xs' f'; vauto.
    + by rewrite Heqpm2v.
    + exists y. split; vauto.
      apply map_eq_In with (x0 := y) in EQ2; vauto.
      by rewrite <- EQ2.
  - red in EQ. red in EQ.
    specialize EQ with pid.
    rewrite H0 in EQ.
    unfold pmeBisim in EQ.
    remember (pm2 pid) as pm2v.
    destruct pm2v as [q' P' xs' f'| |]; vauto. desf.
    apply gfault_query_3 with q' P' xs' f' ps; vauto.
    + by rewrite Heqpm2v.
    + intros y H3.
      apply map_eq_In with (x0:=y) in EQ2; vauto.
      rewrite <- EQ2. by apply H1.
    + intros H3. destruct H3 as (P''&H3).
      inv EQ0. clear EQ0. destruct H as (D1&D2&D3&D4).
      apply D4 in H3. destruct H3 as (Q&H3&H4).
      apply H6. exists Q. done.
  (* processes *)
  - apply gfault_proc_end_1.
    red in EQ. red in EQ. specialize EQ with (g x).
    by rewrite <- EQ.
  - generalize EQ. intro EQ'.
    red in EQ. red in EQ.
    specialize EQ with (g x).
    rewrite H0 in EQ.
    unfold pmeBisim in EQ.
    remember (pm2 (g x)) as pm2v.
    destruct pm2v as [q' P' xs' f'| |]; vauto.
    desf. apply gfault_proc_end_2 with P' xs' f'; auto.
    + red in EQ'. red in EQ'.
      specialize EQ' with (g x).
      rewrite <- EQ', H0. vauto.
    + intro H. apply H5.
      inv EQ0. clear EQ0. destruct H1 as (D1&D2&D3&D4).
      by apply D1.
Qed.

Add Parametric Morphism : gfault
  with signature eq ==> pmBisim ==> eq ==> eq ==> eq ==> iff
    as gfault_pmBisim_mor.
Proof.
  intros h pm1 pm2 H1 s g C. split; intro H2.
  by apply gfault_pmBisim with pm1.
  apply gfault_pmBisim with pm2; auto.
  by symmetry.
Qed.

(** Ghost faults are dependent on variables
    occuring freely inside programs. *)

Lemma gfault_agree :
  forall C h pm s1 s2 g,
  sAgree (cmd_fv C) s1 s2 -> gfault h pm s1 g C -> gfault h pm s2 g C.
Proof.
  cmd_induction C; intros h pm s1 s2 g AGR FAULT; simpls;
    inv FAULT; clear FAULT; vauto.
  (* sequential *)
  - constructor. apply IH1 with s1; vauto.
    intros x H1. apply AGR. by left.
  (* heap reading *)
  - constructor.
    rewrite <- expr_agree with (s1:=s1); auto.
    unfold sAgree. intros y H.
    apply AGR. by right.
  (* heap writing *)
  - constructor.
    rewrite <- expr_agree with (s1:=s1); auto.
    unfold sAgree. intros x H.
    apply AGR. by left.
  (* parallel *)
  - apply sAgree_split in AGR.
    destruct AGR as (AGR1&AGR2).
    apply gfault_par_l; vauto.
    apply IH1 with s1; auto.
  - apply sAgree_split in AGR.
    destruct AGR as (AGR1&AGR2).
    apply gfault_par_r; vauto.
    apply IH2 with s1; auto.
  (* data races *)
  - apply gfault_race_l; auto.
    intro H2. apply H7. red. intros l F1 F2.
    apply sAgree_split in AGR.
    destruct AGR as (AGR1&AGR2).
    rewrite cmd_writes_agree with (s4:=s2) in F1; auto.
    rewrite cmd_acc_agree with (s4 := s2) in F2; auto.
    by apply H2 with l.
  - apply gfault_race_r; auto.
    intro H2. apply H7. red. intros l F1 F2.
    apply sAgree_split in AGR.
    destruct AGR as (AGR1&AGR2).
    rewrite cmd_acc_agree with (s4:=s2) in F1; auto.
    rewrite cmd_writes_agree with (s4:=s2) in F2; auto.
    by apply H2 with l.
  (* heap disposal *)
  - constructor.
    rewrite <- expr_agree with (s1:=s1); auto.
  (* atomics *)
  - constructor. apply IH with s1; auto.
  (* actions *)
  - constructor. apply IH with s1; auto.
Qed.

Lemma gfault_agree_g :
  forall C h pm s g1 g2,
  sAgree (cmd_fv C) g1 g2 -> gfault h pm s g1 C -> gfault h pm s g2 C.
Proof.
  cmd_induction C; intros h pm s g1 g2 AGR FAULT; simpls;
    inv FAULT; clear FAULT; vauto.
  (* sequential *)
  - apply sAgree_split in AGR.
    destruct AGR as (H1&H2).
    constructor. apply IH1 with g1; auto.
  (* parallel *)
  - apply sAgree_split in AGR.
    destruct AGR as (H1&H2).
    apply gfault_par_l; auto.
    apply IH1 with g1; auto.
  - apply sAgree_split in AGR.
    destruct AGR as (H1&H2).
    apply gfault_par_r; vauto.
    apply IH2 with g1; auto.
  (* atomics *)
  - constructor. apply IH with g1; auto.
  (* actions *)
  - constructor. apply IH with g1; auto.
  (* querying *)
  - apply gfault_query_1. intro H1. apply H4.
    rewrite <- AGR in H1; vauto.
  - destruct H5 as (y&H6&H7).
    apply gfault_query_2 with q P xs f; vauto.
    rewrite <- AGR; vauto.
  - apply gfault_query_3 with q P xs f ps; vauto.
    rewrite <- AGR; vauto.
  (* processes *)
  - apply gfault_proc_end_1.
    rewrite <- AGR; vauto.
  - apply gfault_proc_end_2 with P xs f; vauto.
    rewrite <- AGR; vauto.
Qed.

End Programs.
