Require Import List.
Require Import Arith.
Require Import ZArith.
Require Import Zwf.
Require Import Coq.Program.Equality.
Require Import Classical.
Require Import ClassicalDescription.
Require Import Sequences.

Ltac inv H := inversion H; clear H; subst.
Ltac omegaContradiction := elimtype False; omega.
Open Scope Z_scope.

(** * Part 1. The IMP language and its semantics *)

Definition ident := nat.

Definition eq_ident: forall (x y: ident), {x=y}+{x<>y} := eq_nat_dec.

Inductive expr : Type :=
  | Evar: ident -> expr
  | Econst: Z -> expr
  | Eadd: expr -> expr -> expr
  | Esub: expr -> expr -> expr.

Inductive bool_expr : Type :=
  | Bequal: expr -> expr -> bool_expr
  | Bless: expr -> expr -> bool_expr.

Inductive cmd : Type :=
  | Cskip: cmd
  | Cassign: ident -> expr -> cmd
  | Cseq: cmd -> cmd -> cmd
  | Cifthenelse: bool_expr -> cmd -> cmd -> cmd
  | Cwhile: bool_expr -> cmd -> cmd.

(** Execution states, associating values to variables. *)

Definition state := ident -> Z.

Definition initial_state: state := fun (x: ident) => 0.

Definition update (s: state) (x: ident) (n: Z) : state :=
  fun y => if eq_ident x y then n else s y.

(** Evaluation of expressions. *)

Fixpoint eval_expr (s: state) (e: expr) {struct e} : Z :=
  match e with
  | Evar x => s x
  | Econst n =>  n
  | Eadd e1 e2 => eval_expr s e1 + eval_expr s e2
  | Esub e1 e2 => eval_expr s e1 - eval_expr s e2
  end.

Definition eval_bool_expr (s: state) (b: bool_expr) : bool :=
  match b with
  | Bequal e1 e2 =>
      if Z_eq_dec (eval_expr s e1) (eval_expr s e2) then true else false
  | Bless e1 e2 =>
      if Z_lt_dec (eval_expr s e1) (eval_expr s e2) then true else false
  end.

(** Using the semantics of expressions: to evaluate a given expression *)

Eval compute in (
  let x : ident := O in
  let s : state := update initial_state x 12 in
  eval_expr s (Eadd (Evar x) (Econst 1))).

(** Using the semantics of expressions: 
    to reason symbolically over a given expression *)

Remark expr_add_pos:
  forall s x, s x >= 0 -> eval_expr s (Eadd (Evar x) (Econst 1)) > 0.
Proof.
  simpl. 
  intros. omega.
Qed.

(** Using the semantics of expressions: to show a "meta" property *)

Fixpoint is_free (x: ident) (e: expr) {struct e} : Prop :=
  match e with
  | Evar y => x = y
  | Econst n => False
  | Eadd e1 e2 => is_free x e1 \/ is_free x e2
  | Esub e1 e2 => is_free x e1 \/ is_free x e2
  end.

Lemma eval_expr_domain:
  forall s1 s2 e,
  (forall x, is_free x e -> s1 x = s2 x) ->
  eval_expr s1 e = eval_expr s2 e.
Proof.
  induction e; simpl; intros.
  auto.
  auto.
  f_equal; auto. 
  f_equal; auto.
Qed.

(** ** Reduction semantics *)

Inductive red: cmd * state -> cmd * state -> Prop :=

  | red_assign: forall x e s,
      red (Cassign x e, s) (Cskip, update s x (eval_expr s e))

  | red_seq_left: forall c1 c2 s c1' s',
      red (c1, s) (c1', s') ->
      red (Cseq c1 c2, s) (Cseq c1' c2, s')

  | red_seq_skip: forall c s,
      red (Cseq Cskip c, s) (c, s)

  | red_if_true: forall s b c1 c2,
      eval_bool_expr s b = true ->
      red (Cifthenelse b c1 c2, s) (c1, s)

  | red_if_false: forall s b c1 c2,
      eval_bool_expr s b = false ->
      red (Cifthenelse b c1 c2, s) (c2, s)

  | red_while_true: forall s b c,
      eval_bool_expr s b = true ->
      red (Cwhile b c, s) (Cseq c (Cwhile b c), s)

  | red_while_false: forall b c s,
      eval_bool_expr s b = false ->
      red (Cwhile b c, s) (Cskip, s).

Lemma red_deterministic:
  forall cs cs1, red cs cs1 -> forall cs2, red cs cs2 -> cs1 = cs2.
Proof.
  induction 1; intros cs2 RED; inv RED; auto; try congruence.
  generalize (IHred _ H4). congruence.
  inv H. 
  inv H3. 
Qed.

(** The three possible outcomes of execution. *)

Definition terminates (c: cmd) (s s': state) : Prop :=
  star red (c, s) (Cskip, s').

Definition diverges (c: cmd) (s: state) : Prop :=
  infseq red (c, s).

Definition goes_wrong (c: cmd) (s: state) : Prop :=
  exists c', exists s',
  star red (c, s) (c', s') /\ c' <> Cskip /\ irred red (c', s').

(** ** Natural semantics, terminating case *)

Inductive exec: state -> cmd -> state -> Prop :=
  | exec_skip: forall s,
      exec s Cskip s

  | exec_assign: forall s x e,
      exec s (Cassign x e) (update s x (eval_expr s e))

  | exec_seq: forall s c1 c2 s1 s2,
      exec s c1 s1 -> exec s1 c2 s2 ->
      exec s (Cseq c1 c2) s2

  | exec_if: forall s be c1 c2 s',
      exec s (if eval_bool_expr s be then c1 else c2) s' ->
      exec s (Cifthenelse be c1 c2) s'

  | exec_while_loop: forall s be c s1 s2,
      eval_bool_expr s be = true ->
      exec s c s1 -> exec s1 (Cwhile be c) s2 ->
      exec s (Cwhile be c) s2

  | exec_while_stop: forall s be c,
      eval_bool_expr s be = false ->
      exec s (Cwhile be c) s.

(** Termination in natural semantics implies termination in reduction semantics. *)

Remark star_red_seq_left:
  forall c s c' s' c2,
  star red (c, s) (c', s') ->
  star red (Cseq c c2, s) (Cseq c' c2, s').
Proof.
  intros. dependent induction H. constructor.
  destruct b. econstructor. apply red_seq_left; eauto. eauto. 
Qed. 

Lemma exec_terminates:
  forall s c s', exec s c s' -> terminates c s s'.
Proof.
  unfold terminates. induction 1.
(* Cskip *)
  apply star_refl.
(* Cassign *)
  apply star_one. apply red_assign. auto.
(* Cseq *)
  apply star_trans with (Cseq Cskip c2, s1). 
  apply star_red_seq_left. auto. 
  apply star_step with (c2, s1). apply red_seq_skip. auto.
(* Cifthenelse *)
  apply star_step with ((if eval_bool_expr s be then c1 else c2), s). 
  case_eq (eval_bool_expr s be); intro.
  apply red_if_true; auto. apply red_if_false; auto.
  auto.
(* Cwhile loop *)
  apply star_step with (Cseq c (Cwhile be c), s).
  apply red_while_true. auto.
  apply star_trans with (Cseq Cskip (Cwhile be c), s1).
  apply star_red_seq_left. auto. 
  apply star_step with (Cwhile be c, s1). apply red_seq_skip. auto.
(* Cwhile stop *)
  apply star_one. apply red_while_false. auto.
Qed.

(** Termination in reduction semantics implies termination in natural semantics. *)

Lemma red_preserves_exec:
  forall c s c' s', red (c, s) (c', s') ->
  forall sfinal, exec s' c' sfinal -> exec s c sfinal.
Proof.
  intros until s'; intro RED. dependent induction RED; intros.
(* assign *)
  inv H. apply exec_assign. auto.
(* seq left *)
  inv H. apply exec_seq with s1. eapply IHRED; eauto. auto.
(* seq skip *)
  apply exec_seq with s'. apply exec_skip. auto.
(* ifthenelse true *)
  apply exec_if. rewrite H; auto.
(* ifthenelse false *)
  apply exec_if. rewrite H; auto.
(* while true *)
  inv H0. apply exec_while_loop with s1. auto. auto. auto.
(* while false *)
  inv H0. apply exec_while_stop. auto.
Qed.

Lemma terminates_exec:
  forall s c s', terminates c s s' -> exec s c s'.
Proof.
  unfold terminates. intros. dependent induction H.
(* base case *)
  apply exec_skip.
(* step case *)
  destruct b. eapply red_preserves_exec; eauto. 
Qed.

(** ** Coinductive natural semantics for divergence *)

CoInductive execinf: state -> cmd -> Prop :=
  | execinf_seq_left: forall s c1 c2,
      execinf s c1 ->
      execinf s (Cseq c1 c2)

  | execinf_seq_right: forall s c1 c2 s1,
      exec s c1 s1 -> execinf s1 c2 ->
      execinf s (Cseq c1 c2)

  | execinf_if: forall s b c1 c2,
      execinf s (if eval_bool_expr s b then c1 else c2) ->
      execinf s (Cifthenelse b c1 c2)

  | execinf_while_body: forall s b c,
      eval_bool_expr s b = true ->
      execinf s c ->
      execinf s (Cwhile b c)

  | execinf_while_loop: forall s b c s1,
      eval_bool_expr s b = true ->
      exec s c s1 -> execinf s1 (Cwhile b c) ->
      execinf s (Cwhile b c).

(** Divergence in natural semantics implies divergence in reduction semantics. *)

Lemma execinf_red_step:
  forall c s,
  execinf s c -> exists c', exists s', red (c, s) (c', s') /\ execinf s' c'.
Proof.
  induction c; intros s EXECINF; inv EXECINF.
(* seq left *)
  destruct (IHc1 _ H1) as [c' [s' [A B]]]. 
  exists (Cseq c' c2); exists s'; split.
  apply red_seq_left; auto. 
  apply execinf_seq_left; auto.
(* seq right *)
  generalize (exec_terminates _ _ _ H2). unfold terminates. intro. inv H.
  exists c2; exists s1; split. apply red_seq_skip. auto.
  destruct b as [c' s']. exists (Cseq c' c2); exists s'; split.
  apply red_seq_left; auto.
  apply execinf_seq_right with s1. apply terminates_exec. auto. auto.
(* ifthenelse *)
  exists (if eval_bool_expr s b then c1 else c2); exists s; split.
  case_eq (eval_bool_expr s b); intro.
  apply red_if_true; auto. apply red_if_false; auto.
  auto.
(* while body *)
  exists (Cseq c (Cwhile b c)); exists s; split.
  apply red_while_true; auto. 
  apply execinf_seq_left; auto.
(* while loop *)
  exists (Cseq c (Cwhile b c)); exists s; split.
  apply red_while_true; auto.
  apply execinf_seq_right with s1. auto. auto.
Qed.

Lemma execinf_diverges:
  forall c s, execinf s c -> diverges c s.
Proof.
  cofix COINDHYP; intros.
  destruct (execinf_red_step c s H) as [c' [s' [A B]]].
  apply infseq_step with (c', s'). auto.
  apply COINDHYP. auto.
Qed.

(** Divergence in reduction semantics implies divergence in natural semantics. *)

Lemma diverges_star_inv:
  forall c s c' s',
  diverges c s -> star red (c, s) (c', s') -> diverges c' s'.
Proof.
  intros. apply infseq_star_inv with (c, s); auto. 
  intros; eapply red_deterministic; eauto.
Qed.

Lemma diverges_seq_inversion:
  forall s c1 c2,
  diverges (Cseq c1 c2) s ->
  diverges c1 s 
  \/ exists s', star red (c1, s) (Cskip, s') /\ diverges c2 s'.
Proof.
  intros. 
  destruct (infseq_or_finseq red (c1, s)) as [DIV1 | [[c' s'] [RED1 IRRED1]]].
  left; auto.
  assert (star red (Cseq c1 c2, s) (Cseq c' c2, s')). apply star_red_seq_left; auto.
  assert (c' = Cskip).
    assert (diverges (Cseq c' c2) s'). eapply diverges_star_inv; eauto.
   inv H1. inv H2. elim (IRRED1 _ H7). auto.
  subst c'.
  assert (star red (Cseq c1 c2, s) (c2, s')).
    eapply star_trans; eauto. apply star_one. apply red_seq_skip. 
  right. exists s'; split. auto. eapply diverges_star_inv; eauto.
Qed.

Lemma diverges_while_inversion:
  forall b c s,
  diverges (Cwhile b c) s ->
  eval_bool_expr s b = true /\
  (diverges c s \/ 
   exists s', star red (c, s) (Cskip, s') /\ diverges (Cwhile b c) s').
Proof.
  intros. inv H. inv H0.
  split. auto. apply diverges_seq_inversion. auto.
  inv H1. inv H.
Qed.

Lemma diverges_execinf:
  forall c s, diverges c s -> execinf s c.
Proof.
  cofix COINDHYP. intros. destruct c.
(* skip: impossible *)
  inv H. inv H0.
(* assign: impossible *)
  inv H. inv H0. inv H1. inv H.
(* seq *)
  destruct (diverges_seq_inversion _ _ _ H) as [DIV1 | [s' [RED1 DIV2]]]. 
  apply execinf_seq_left. apply COINDHYP. auto.
  apply execinf_seq_right with s'. apply terminates_exec. auto. 
  apply COINDHYP. auto.
(* if then else *)
  inv H. inv H0.
  apply execinf_if. rewrite H6. apply COINDHYP. auto.
  apply execinf_if. rewrite H6. apply COINDHYP. auto.
(* while *)
  destruct (diverges_while_inversion _ _ _ H) as [EVAL [DIV1 | [s' [RED1 DIV2]]]].
  apply execinf_while_body. auto. apply COINDHYP. auto.
  apply execinf_while_loop with s'. auto. apply terminates_exec. auto. apply COINDHYP. auto.
Qed.

(** ** Definitional interpreter *)

Inductive result: Type :=
  | Bot: result
  | Res: state -> result.

Definition bind (r: result) (f: state -> result) : result :=
  match r with
  | Res s => f s
  | Bot => Bot
  end.

Fixpoint interp (n: nat) (c: cmd) (s: state) {struct n} : result :=
  match n with
  | O => Bot
  | S n' =>
      match c with
      | Cskip => Res s
      | Cassign x e => Res (update s x (eval_expr s e))
      | Cseq c1 c2 =>
          bind (interp n' c1 s) (fun s1 => interp n' c2 s1)
      | Cifthenelse b c1 c2 =>
          interp n' (if eval_bool_expr s b then c1 else c2) s
      | Cwhile b c1 =>
          if eval_bool_expr s b
          then bind (interp n' c1 s) (fun s1 => interp n' (Cwhile b c1) s1)
          else Res s
      end
  end.

(** A sample program and its execution.  The program computes
  the quotient and remainder of variables [a] and [b].  In concrete
  syntax:
<<
       r := a; q := 0;
       while b < r + 1 do r := r - b; q := q + 1 done
>>
*)

Open Scope nat_scope.

Definition va : ident := 0.
Definition vb : ident := 1.
Definition vq : ident := 2.
Definition vr : ident := 3.

Open Scope Z_scope.

Definition prog :=
  Cseq (Cassign vr (Evar va))
  (Cseq (Cassign vq (Econst 0))
   (Cwhile (Bless (Evar vb) (Eadd (Evar vr) (Econst 1)))
      (Cseq (Cassign vr (Esub (Evar vr) (Evar vb)))
            (Cassign vq (Eadd (Evar vq) (Econst 1)))))).

Definition prog_init_state := update (update initial_state va 13) vb 3.

Definition test_prog :=
  match interp 100 prog prog_init_state with
  | Res s => Some(s vq)
  | Bot => None
  end.

Eval compute in test_prog.

(** The natural ordering over results. *)

Definition res_le (r1 r2: result) := r1 = Bot \/ r1 = r2.

(** The [interp] function is monotone in [n] with respect to this ordering. *)

Remark bind_mon:
  forall r1 f1 r2 f2,
  res_le r1 r2 -> (forall s, res_le (f1 s) (f2 s)) ->
  res_le (bind r1 f1) (bind r2 f2).
Proof.
  unfold res_le; intros. destruct H. 
  subst r1. simpl. auto.
  subst r1. destruct r2; simpl; auto. 
Qed.

Open Scope nat_scope.

Lemma interp_mon:
  forall n n' c s, n <= n' -> res_le (interp n c s) (interp n' c s).
Proof.
  induction n; intros; simpl.
  red; auto.
  destruct n'. omegaContradiction. assert (n <= n') by omega. simpl. 
  destruct c.
(* skip *)
  red; auto.
(* assign *)
  red; auto.
(* seq *)
  apply bind_mon. auto. intros; auto.
(* ifthenelse *)
  auto.
(* while *)
  destruct (eval_bool_expr s b). 
  apply bind_mon; auto.
  red; auto.
Qed.

Corollary interp_Res_stable:
  forall n n' c s s',
  n <= n' -> interp n c s = Res s' -> interp n' c s = Res s'.
Proof.
  intros. 
  destruct (interp_mon n n' c s H); congruence.
Qed.

(** It follows an equivalence between termination according to the natural semantics
  and the fact that [interp n c s] returns [Res] for a suitably large [n]. *)

Remark bind_Res_inversion:
  forall r f s, bind r f = Res s -> exists s1, r = Res s1 /\ f s1 = Res s.
Proof.
  unfold bind; intros. 
  destruct r; try congruence. exists s0; auto.
Qed.

Lemma interp_exec:
  forall n c s s', interp n c s = Res s' -> exec s c s'.
Proof.
  induction n; intros until s'; simpl.
  congruence.
  destruct c.
(* skip *)
  intros. inv H. apply exec_skip.
(* expr *)
  intros. inv H. apply exec_assign.
(* seq *)
  intro. destruct (bind_Res_inversion _ _ _ H) as [s1 [EQ1 EQ2]]. 
  apply exec_seq with s1; auto.
(* ifthenelse *)
  intros. apply exec_if. auto.
(* while *)
  case_eq (eval_bool_expr s b); intros.
  destruct (bind_Res_inversion _ _ _ H0) as [s1 [EQ1 EQ2]].
  apply exec_while_loop with s1; auto.  
  inv H0. apply exec_while_stop. auto. 
Qed.

Require Import Max.
Hint Resolve le_max_l le_max_r.

Lemma exec_interp:
  forall s c s', exec s c s' -> exists n, interp n c s = Res s'.
Proof.
  induction 1.
(* skip *)
  exists 1%nat; auto.
(* assign *)
  exists 1%nat; simpl. auto.
(* seq *)
  destruct IHexec1 as [n1 I1]. destruct IHexec2 as [n2 I2]. 
  exists (S (max n1 n2)). simpl. 
  rewrite (interp_Res_stable n1 (max n1 n2) c1 s s1); auto. simpl.
  rewrite (interp_Res_stable n2 (max n1 n2) c2 s1 s2); auto.
(* ifthenelse *)
  destruct IHexec as [n I]. exists (S n); simpl. auto. 
(* while loop *)
  destruct IHexec1 as [n1 I1]. destruct IHexec2 as [n2 I2]. 
  exists (S (max n1 n2)). simpl. rewrite H.
  rewrite (interp_Res_stable n1 (max n1 n2) c s s1); auto. simpl.
  apply interp_Res_stable with n2; auto. 
(* while stop *)
  exists 1%nat; simpl. rewrite H. auto. 
Qed.

Corollary exec_interp_either:
  forall s c s' n, exec s c s' -> interp n c s = Bot \/ interp n c s = Res s'.
Proof.
  intros. 
  destruct (exec_interp _ _ _ H) as [m I]. 
  destruct (le_ge_dec n m). 
  rewrite <- I. change (res_le (interp n c s) (interp m c s)). apply interp_mon; auto.
  right. eapply interp_Res_stable; eauto. 
Qed.

(** Moreover, if [s] diverges according to the natural semantics,
  [interp] always returns [Bot] for all values of [n]. *)

Lemma execinf_interp:
  forall n s c, execinf s c -> interp n c s = Bot.
Proof.
  induction n; intros; simpl.
  auto.
  inv H. 
(* seq left *)
  rewrite (IHn _ _ H0). auto.
(* seq right *)
  destruct (exec_interp_either _ _ _ n H0); rewrite H. auto.
  simpl. auto. 
(* ifthenelse *)
  auto. 
(* while body *)
  rewrite H0. rewrite (IHn s c0); auto.
(* while loop *)
  rewrite H0.
  destruct (exec_interp_either _ _ _ n H1); rewrite H. auto.
  simpl. auto.
Qed.

(** ** Denotational semantics *)

(** The sequence [n => interp n c s] eventually stabilizes as [n] goes to
  infinity. *)

Lemma interp_limit:
  forall s c, exists r, exists m, forall n, m <= n -> interp n c s = r.
Proof.
  intros. 
  destruct (classic (forall n, interp n c s = Bot)).
  exists Bot; exists 0; auto.
  destruct (not_all_ex_not _ _ H) as [m P].
  exists (interp m c s); exists m; intros.
  destruct (interp_mon m n c s H0). congruence. auto.
Qed.

(** Using an axiom of description, we can define a function associating
  the limit of the sequence [n => interp n c s] to each [c, s].
  This is the denotation of [c] in [s]. *)

Definition interp_limit_dep (s: state) (c: cmd) :
  { r: result | exists m, forall n, m <= n -> interp n c s = r}.
Proof.
  intros. apply constructive_definite_description. 
  destruct (interp_limit s c) as [r X]. 
  exists r. red. split. auto. intros r' X'. 
  destruct X as [m P]. destruct X' as [m' P']. 
  transitivity (interp (max m m') c s). symmetry. auto. auto.
Qed.

Definition denot (c: cmd) (s: state) : result := proj1_sig (interp_limit_dep s c).

Lemma denot_limit:
  forall c s, exists m, forall n, m <= n -> interp n c s = denot c s.
Proof.
  intros. unfold denot. apply proj2_sig.
Qed. 

Lemma denot_charact:
  forall c s m r,
  (forall n, m <= n -> interp n c s = r) ->
  denot c s = r.
Proof.
  intros. destruct (denot_limit c s) as [m' I]. 
  transitivity (interp (max m m') c s). symmetry. apply I; auto. apply H; auto.
Qed.

(** The [denot] function satisfies the expected equations for a denotational semantics. *)

Lemma denot_skip:
  forall s, denot Cskip s = Res s.
Proof.
  intros. apply denot_charact with 1%nat. intros. 
  destruct n. elimtype False; omega. auto. 
Qed.

Lemma denot_assign:
  forall x e s,
  denot (Cassign x e) s = Res (update s x (eval_expr s e)).
Proof.
  intros. apply denot_charact with 1%nat. intros. 
  destruct n. omegaContradiction. auto. 
Qed.

Lemma denot_seq:
  forall c1 c2 s, denot (Cseq c1 c2) s = bind (denot c1 s) (fun s' => denot c2 s').
Proof.
  intros. 
  destruct (denot_limit c1 s) as [m1 I1].
  destruct (denot c1 s); simpl.
  apply denot_charact with (S m1); intros. 
  destruct n. omegaContradiction. simpl. rewrite I1. auto. omega. 
  destruct (denot_limit c2 s0) as [m2 I2].
  apply denot_charact with (S (max m1 m2)). intros. 
  destruct n. omegaContradiction. simpl.
  rewrite I1. simpl. apply I2. 
  apply le_trans with (max m1 m2). auto. omega. 
  apply le_trans with (max m1 m2). auto. omega.
Qed.

Lemma denot_if:
  forall b c1 c2 s, 
  denot (Cifthenelse b c1 c2) s = denot (if eval_bool_expr s b then c1 else c2) s.
Proof.
  intros. 
  destruct (denot_limit (if eval_bool_expr s b then c1 else c2) s) as [m I].
  apply denot_charact with (S m). intros. 
  destruct n. omegaContradiction. simpl. apply I. omega.
Qed.

Lemma denot_while:
  forall b c s,
  denot (Cwhile b c) s =
  if eval_bool_expr s b
  then bind (denot c s) (fun s' => denot (Cwhile b c) s')
  else Res s.
Proof.
  intros. case_eq (eval_bool_expr s b); intros.
  destruct (denot_limit c s) as [m1 I1].
  destruct (denot c s); simpl.
  apply denot_charact with (S m1); intros. 
  destruct n. omegaContradiction. simpl.
  rewrite H. rewrite I1. auto. omega. 
  destruct (denot_limit (Cwhile b c) s0) as [m2 I2].
  apply denot_charact with (S (max m1 m2)). intros. 
  destruct n. omegaContradiction. simpl.
  rewrite H. rewrite I1. simpl. rewrite I2. auto. 
  apply le_trans with (max m1 m2). auto. omega. 
  apply le_trans with (max m1 m2). auto. omega.
  apply denot_charact with 1%nat. intros.
  destruct n. omegaContradiction. simpl. rewrite H. auto.
Qed.

Lemma le_interp_denot:
  forall n c s, res_le (interp n c s) (denot c s).
Proof.
  intros. destruct (denot_limit c s) as [m L]. 
  destruct (le_ge_dec m n). 
  rewrite L; auto. red; auto.
  rewrite <- (L m); auto. apply interp_mon; auto.
Qed.

Lemma denot_while_least_fixed_point:
  forall b c (f: state -> result),
  (forall s,
   f s = if eval_bool_expr s b then bind (denot c s) (fun s' => f s') else Res s) ->
  (forall s, res_le (denot (Cwhile b c) s) (f s)).
Proof.
  intros. 
  assert (forall n s, res_le (interp n (Cwhile b c) s) (f s)).
    induction n; intros; simpl.
    red; auto.
    rewrite H. destruct (eval_bool_expr s0 b). 
    apply bind_mon. apply le_interp_denot. auto. 
    red; auto.
  destruct (denot_limit (Cwhile b c) s) as [m L].
  rewrite <- (L m); auto. 
Qed.

(** Using these equations, we can prove an equivalence result between
- having denotation [Res s'] and terminating on [s'] according to the natural semantics;
- having denotation [Bot] and diverging according to the natural semantics.
*)

Lemma denot_exec:
  forall c s s', denot c s = Res s' -> exec s c s'.
Proof.
  intros. destruct (denot_limit c s) as [n I]. rewrite H in I. 
  apply interp_exec with n. auto. 
Qed.

Lemma exec_denot:
  forall s c s', exec s c s' -> denot c s = Res s'.
Proof.
  induction 1.
(* skip *)
  apply denot_skip.
(* assign *)
  rewrite denot_assign. auto.
(* seq *)
  rewrite denot_seq. rewrite IHexec1; simpl. auto.
(* ifthenelse *)
  rewrite denot_if. auto.
(* while loop *)
  rewrite denot_while. rewrite H. rewrite IHexec1. auto.
(* while stop *)
  rewrite denot_while. rewrite H. auto.
Qed.

Lemma execinf_denot:
  forall s c, execinf s c -> denot c s = Bot.
Proof.
  intros. apply denot_charact with 0. intros. apply execinf_interp; auto. 
Qed.

Lemma denot_execinf:
  forall s c, denot c s = Bot -> execinf s c.
Proof.
  cofix COINDHYP; intros until c.
  destruct c.
(* skip *)
  rewrite denot_skip. congruence.
(* assign *)
  rewrite denot_assign. congruence.
(* seq *)
  rewrite denot_seq. case_eq (denot c1 s); simpl. 
  intros. apply execinf_seq_left. apply COINDHYP; auto.
  intros. apply execinf_seq_right with s0. apply denot_exec; auto. 
  apply COINDHYP; auto.
(* ifthenelse *)
  rewrite denot_if. intro. 
  apply execinf_if. apply COINDHYP. auto.
(* while *)
  rewrite denot_while. case_eq (eval_bool_expr s b); intro.
  case_eq (denot c s); simpl; intros. 
  apply execinf_while_body. auto. 
  apply COINDHYP. auto.
  apply execinf_while_loop with s0. auto. 
  apply denot_exec; auto. 
  apply COINDHYP. auto.
  congruence.
Qed.

(** * Part 2.  Axiomatic semantics and program proof *)

(** Assertions over states. *)

Definition assertion := state -> Prop.

Definition aupdate (P: assertion) (x: ident) (e: expr) : assertion :=
  fun s => P (update s x (eval_expr s e)).

Definition atrue (be: bool_expr) : assertion :=
  fun s => eval_bool_expr s be = true.

Definition afalse (be: bool_expr) : assertion :=
  fun s => eval_bool_expr s be = false.

Definition aand (P Q: assertion) : assertion :=
  fun s => P s /\ Q s.

Definition aor (P Q: assertion) : assertion :=
  fun s => P s \/ Q s.

Definition aimp (P Q: assertion) : Prop :=
  forall s, P s -> Q s.

(** The rules of the axiomatic semantics, defining valid weak Hoare triples
  [{P} c {Q}]. *)

Inductive triple: assertion -> cmd -> assertion -> Prop :=
  | triple_skip: forall P,
      triple P Cskip P

  | triple_assign: forall P x e,
      triple (aupdate P x e) (Cassign x e) P

  | triple_seq: forall c1 c2 P Q R,
      triple P c1 Q -> triple Q c2 R ->
      triple P (Cseq c1 c2) R

  | triple_if: forall be c1 c2 P Q,
      triple (aand (atrue be) P) c1 Q ->
      triple (aand (afalse be) P) c2 Q ->
      triple P (Cifthenelse be c1 c2) Q

  | triple_while: forall be c P,
      triple (aand (atrue be) P) c P ->
      triple P (Cwhile be c) (aand (afalse be) P)

  | triple_consequence: forall c P Q P' Q',
      triple P' c Q' -> aimp P P' -> aimp Q' Q ->
      triple P c Q.

(** Semantic interpretation of weak Hoare triples in terms of concrete executions. *)

CoInductive finally: state -> cmd -> assertion -> Prop :=
  | finally_done: forall s (Q: assertion),
      Q s ->
    (*===============================================*)
      finally s Cskip Q

  | finally_step: forall c s c' s' Q,
      red (c, s) (c', s') -> finally s' c' Q ->
    (*===============================================*)
      finally s c Q.

Definition sem_triple (P: assertion) (c: cmd) (Q: assertion) :=
  forall s, P s -> finally s c Q.

Lemma finally_seq:
  forall c1 c2 s Q R,
  finally s c1 Q -> sem_triple Q c2 R -> finally s (Cseq c1 c2) R.
Proof.
  cofix COINDHYP; intros. 
  inv H.
  apply finally_step with c2 s. apply red_seq_skip. auto. 
  apply finally_step with (Cseq c' c2) s'. 
  apply red_seq_left; auto. apply COINDHYP with Q. auto. auto.
Qed.

Lemma finally_while:
  forall be c P,
  sem_triple (aand (atrue be) P) c P ->
  sem_triple P (Cwhile be c) (aand (afalse be) P).
Proof.
  cofix COINDHYP1; intros.
  red; intros. 
  case_eq (eval_bool_expr s be); intro.
  apply finally_step with (Cseq c (Cwhile be c)) s.
  apply red_while_true; auto.
  assert (forall c' s', 
          finally s' c' P ->
          finally s' (Cseq c' (Cwhile be c)) (aand (afalse be) P)).
    cofix COINDHYP2; intros.
    inv H2.
    apply finally_step with (Cwhile be c) s'. apply red_seq_skip.
    apply COINDHYP1. auto. auto. 
    apply finally_step with (Cseq c'0 (Cwhile be c)) s'0. 
    apply red_seq_left. auto. 
    apply COINDHYP2. auto. 
  apply H2. apply H. split. auto. auto. 

  apply finally_step with Cskip s. 
  apply red_while_false; auto.
  apply finally_done. split. auto. auto.
Qed.

Lemma finally_consequence:
  forall s c Q Q', aimp Q Q' -> finally s c Q -> finally s c Q'.
Proof.
  cofix COINDHYP; intros. inv H0.
  apply finally_done. auto.
  apply finally_step with c' s'. auto. apply COINDHYP with Q; auto.
Qed.

(** Every derivable Hoare triple is semantically valid. *)

Lemma triple_correct:
  forall P c Q, triple P c Q -> sem_triple P c Q.
Proof.
  induction 1.
(* skip *)
  red; intros. apply finally_done. auto.
(* assign *)
  red. intro s. unfold aupdate. intro.
  apply finally_step with Cskip (update s x (eval_expr s e)). apply red_assign. 
  apply finally_done. auto.
(* seq *)
  red; intros. apply finally_seq with Q. apply IHtriple1. auto. auto.
(* ifthenelse *)
  red; intros. case_eq (eval_bool_expr s be); intro.
  apply finally_step with c1 s. apply red_if_true. auto. 
  apply IHtriple1. split. red. auto. auto.
  apply finally_step with c2 s. apply red_if_false. auto. 
  apply IHtriple2. split. red. auto. auto.
(* while *)
  apply finally_while. auto. 
(* consequence *)
  red; intros. apply finally_consequence with Q'. auto. 
  apply IHtriple. auto.
Qed.

(** Axiomatic semantics for strong Hoare triples [[P] c [Q]]. *)

Open Scope Z_scope.

Definition aequal (e: expr) (v: Z) : assertion :=
  fun (s: state) => eval_expr s e = v.
Definition alessthan (e: expr) (v: Z) : assertion :=
  fun (s: state) => 0 <= eval_expr s e < v.

Inductive Triple: assertion -> cmd -> assertion -> Prop :=
  | Triple_skip: forall P,
      Triple P Cskip P

  | Triple_assign: forall P x e,
      Triple (aupdate P x e) (Cassign x e) P

  | Triple_seq: forall c1 c2 P Q R,
      Triple P c1 Q -> Triple Q c2 R ->
      Triple P (Cseq c1 c2) R

  | Triple_if: forall be c1 c2 P Q,
      Triple (aand (atrue be) P) c1 Q ->
      Triple (aand (afalse be) P) c2 Q ->
      Triple P (Cifthenelse be c1 c2) Q

  | Triple_while: forall be c P measure,
      (forall v,
        Triple (aand (atrue be) (aand (aequal measure v) P))
               c
               (aand (alessthan measure v) P)) ->
      Triple P (Cwhile be c) (aand (afalse be) P)

  | Triple_consequence: forall c P Q P' Q',
      Triple P' c Q' -> aimp P P' -> aimp Q' Q ->
      Triple P c Q.

(** Semantic interpretation of strong Hoare triples in terms of concrete executions. *)

Definition sem_Triple (P: assertion) (c: cmd) (Q: assertion) :=
  forall s, P s -> exists s', exec s c s' /\ Q s'.

Lemma Triple_while_correct:
  forall (P: assertion) measure c b,
  (forall v : Z,
   sem_Triple (aand (atrue b) (aand (aequal measure v) P))
              c
              (aand (alessthan measure v) P)) ->
  forall v s,
  eval_expr s measure = v -> P s ->
  exists s', exec s (Cwhile b c) s' /\ (aand (afalse b) P) s'.
Proof.
  intros until v. pattern v. apply (well_founded_ind (Zwf_well_founded 0)). 
  intros. case_eq (eval_bool_expr s b); intros.
  destruct (H x s) as [s1 [A B]].
  split. auto. split. auto. auto.
  red in B. unfold alessthan in B. destruct B. 
  assert (Zwf 0 (eval_expr s1 measure) x). split; omega. 
  destruct (H0 _ H6 s1) as [s2 [C D]]. auto. auto. 
  exists s2; split. eapply exec_while_loop; eauto. auto.
  exists s; split. apply exec_while_stop; auto. split; auto.
Qed.

Lemma Triple_correct:
  forall P c Q, Triple P c Q -> sem_Triple P c Q.
Proof.
  induction 1; red; intros.
(* skip *)
  exists s; split. constructor. auto.
(* assign *)
  exists (update s x (eval_expr s e)); split. constructor. auto.
(* seq *)
  destruct (IHTriple1 s H1) as [s1 [A B]].
  destruct (IHTriple2 s1 B) as [s2 [C D]].
  exists s2; split. econstructor; eauto. auto.
(* ifthenelse *)
  case_eq (eval_bool_expr s be); intros.
  destruct (IHTriple1 s) as [s' [A B]]. split; auto. 
  exists s'; split. constructor. rewrite H2; auto. auto.
  destruct (IHTriple2 s) as [s' [A B]]. split; auto. 
  exists s'; split. constructor. rewrite H2; auto. auto.
(* while *)
  apply Triple_while_correct with measure (eval_expr s measure); auto.
(* consequence *)
  destruct (IHTriple s) as [s' [A B]]. auto. 
  exists s'; split. auto. auto.
Qed.

(** Weakest precondition calculus & verification condition generation *)

Inductive acmd : Type :=
  | Askip
  | Aassign(x: ident)(e: expr)
  | Aseq(a1 a2: acmd)
  | Aifthenelse(b: bool_expr)(ayes ano: acmd)
  | Awhile(b: bool_expr)(P: assertion)(abody: acmd)
  | Aassert(P: assertion).

(** [wp a Q] computes the weakest precondition for command [a] with
    postcondition [Q]. *)

Fixpoint wp (a: acmd) (Q: assertion) {struct a} : assertion :=
  match a with
  | Askip => Q
  | Aassign x e => aupdate Q x e
  | Aseq a1 a2 => wp a1 (wp a2 Q)
  | Aifthenelse b a1 a2 => aor (aand (atrue b) (wp a1 Q)) (aand (afalse b) (wp a2 Q))
  | Awhile b P a1 => P
  | Aassert P => P
  end.

(** [vcg a Q] computes a logical formula which, if true, implies that 
    the triple [{wp a Q} a Q] holds. *)

Fixpoint vcg (a: acmd) (Q: assertion) {struct a} : Prop :=
  match a with
  | Askip => True
  | Aassign x e => True
  | Aseq a1 a2 => vcg a1 (wp a2 Q) /\ vcg a2 Q
  | Aifthenelse b a1 a2 => vcg a1 Q /\ vcg a2 Q
  | Awhile b P a1 =>
      vcg a1 P /\
      aimp (aand (afalse b) P) Q /\
      aimp (aand (atrue b) P) (wp a1 P)
  | Aassert P =>
      aimp P Q
  end.

Definition vcgen (P: assertion) (a: acmd) (Q: assertion) : Prop :=
  aimp P (wp a Q) /\ vcg a Q.

(** Mapping annotated commands back to regular commands. *)

Fixpoint erase (a: acmd) {struct a} : cmd :=
  match a with
  | Askip => Cskip
  | Aassign x e => Cassign x e
  | Aseq a1 a2 => Cseq (erase a1) (erase a2)
  | Aifthenelse b a1 a2 => Cifthenelse b (erase a1) (erase a2)
  | Awhile b P a1 => Cwhile b (erase a1)
  | Aassert P => Cskip
  end.

(** Correctness of [wp] and [vcg]. *)

Lemma vcg_correct:
  forall a Q, vcg a Q -> triple (wp a Q) (erase a) Q.
Proof.
  induction a; simpl; intros.
(* skip *)
  apply triple_skip.
(* assign *)
  apply triple_assign.
(* seq *)
  destruct H. apply triple_seq with (wp a2 Q). auto. auto.
(* ifthenelse *)
  destruct H. 
  apply triple_if.
  apply triple_consequence with (wp a1 Q) Q. auto.
  red. unfold aand, aor, atrue, afalse. intros. intuition.
  congruence.
  red; auto.
  apply triple_consequence with (wp a2 Q) Q. auto.
  red. unfold aand, aor, atrue, afalse. intros. intuition.
  congruence.
  red; auto.
(* while *)
  destruct H as [A [B C]]. 
  apply triple_consequence with P (aand (afalse b) P).
  apply triple_while. 
  apply triple_consequence with (wp a P) P.
  auto. auto. red; auto.
  red; auto. auto. 
(* assertion *)
  apply triple_consequence with Q Q. apply triple_skip. auto. red; auto.
Qed.

Theorem vcgen_correct:
  forall P a Q, vcgen P a Q -> triple P (erase a) Q.
Proof.
  intros. destruct H. 
  apply triple_consequence with (wp a Q) Q. 
  apply vcg_correct; auto. auto. red; auto.
Qed.

(** Example of verification. *)

Open Scope Z_scope.

Definition precondition : assertion :=
  fun s => s va >= 0 /\ s vb > 0.

Definition invariant : assertion :=
  fun s => s vr >= 0 /\ s vb > 0 /\ s va = s vb * s vq + s vr.

Definition postcondition : assertion :=
  fun s => s vq = s va / s vb.

(** The program is the earlier Euclidean division example annotated
    with a loop invariant.
<<
       r := a; q := 0;
       while b < r + 1 do {invariant}  r := r - b; q := q + 1 done
>>
*)
Definition aprog :=
  Aseq (Aassign vr (Evar va))
  (Aseq (Aassign vq (Econst 0))
   (Awhile (Bless (Evar vb) (Eadd (Evar vr) (Econst 1)))
      invariant
      (Aseq (Aassign vr (Esub (Evar vr) (Evar vb)))
            (Aassign vq (Eadd (Evar vq) (Econst 1)))))).

Lemma aprog_correct:
  triple precondition (erase aprog) postcondition.
Proof.
  apply vcgen_correct.
  unfold vcgen. simpl. unfold aimp, aand, afalse, atrue, aupdate; simpl. 
  intuition.
(** 1- invariant holds initially ([r = a] and [q = 0]) *)
  unfold precondition in H. unfold invariant, update; simpl.
  intuition. 
(** 2- invariant and [b >= r+1] imply postcondition *)
  destruct (Z_lt_dec (s vb) (s vr + 1)); try congruence.
  unfold invariant in H1. unfold postcondition. intuition.
  apply Zdiv_unique with (s vr). omega. auto. 
(** 3- invariant is preserved by assignment [r := r - b; q := q + 1] *)
  destruct (Z_lt_dec (s vb) (s vr + 1)); try congruence.
  unfold invariant in H1. unfold invariant, update; simpl. intuition. 
  rewrite H3. ring.
Qed.

(** * Part 3.  Compilation to a virtual machine *)

(** ** The virtual machine *)

(** Instruction set. *)

Inductive instruction: Type :=
  | Iconst(n: Z)
  | Ivar(x: ident)
  | Isetvar(x: ident)
  | Iadd
  | Isub
  | Ibranch(ofs: Z)
  | Ibne(ofs: Z)
  | Ibge(ofs: Z)
  | Ihalt.

Definition code := list instruction.

Definition stack := list Z.

Open Scope Z_scope.

(** Semantics of the virtual machine. *)

Fixpoint code_at (c: code) (pc: Z) {struct c} : option instruction :=
  match c with
  | nil => None
  | i :: c' => if Z_eq_dec pc 0 then Some i else code_at c' (pc - 1)
  end.

(** A virtual machine state is a triple
    (program counter, stack, variable state). *)

Definition machine_state := (Z * stack * state)%type.

Inductive transition (c: code): machine_state -> machine_state -> Prop :=
  | trans_const: forall pc stk s n,
      code_at c pc = Some(Iconst n) ->
      transition c (pc, stk, s) (pc + 1, n :: stk, s)

  | trans_var: forall pc stk s x,
      code_at c pc = Some(Ivar x) ->
      transition c (pc, stk, s) (pc + 1, s x :: stk, s)

  | trans_setvar: forall pc stk s x n,
      code_at c pc = Some(Isetvar x) ->
      transition c (pc, n :: stk, s) (pc + 1, stk, update s x n)

  | trans_add: forall pc stk s n1 n2,
      code_at c pc = Some(Iadd) ->
      transition c (pc, n2 :: n1 :: stk, s) (pc + 1, (n1 + n2) :: stk, s)

  | trans_sub: forall pc stk s n1 n2,
      code_at c pc = Some(Isub) ->
      transition c (pc, n2 :: n1 :: stk, s) (pc + 1, (n1 - n2) :: stk, s)

  | trans_branch: forall pc stk s ofs pc',
      code_at c pc = Some(Ibranch ofs) ->
      pc' = pc + 1 + ofs ->
      transition c (pc, stk, s) (pc', stk, s)

  | trans_bne: forall pc stk s ofs n1 n2 pc',
      code_at c pc = Some(Ibne ofs) ->
      pc' = (if Z_eq_dec n1 n2 then pc + 1 else pc + 1 + ofs) ->
      transition c (pc, n2 :: n1 :: stk, s) (pc', stk, s)

  | trans_bge: forall pc stk s ofs n1 n2 pc',
      code_at c pc = Some(Ibge ofs) ->
      pc' = (if Z_lt_dec n1 n2 then pc + 1 else pc + 1 + ofs) ->
      transition c (pc, n2 :: n1 :: stk, s) (pc', stk, s).

(** Sequences of machine transitions. *)

Definition mach_terminates (c: code) (s_init s_fin: state) :=
  exists pc,
  code_at c pc = Some Ihalt /\
  star (transition c) (0, nil, s_init) (pc, nil, s_fin).

Definition mach_diverges (c: code) (s_init: state) :=
  infseq (transition c) (0, nil, s_init).

Definition mach_goes_wrong (c: code) (s_init: state) :=
  exists pc, exists stk, exists s,
  star (transition c) (0, nil, s_init) (pc, stk, s) /\
  irred (transition c) (pc, stk, s) /\
  (code_at c pc <> Some Ihalt \/ stk <> nil).

(** ** The compilation scheme *)

Fixpoint compile_expr (e: expr): code :=
  match e with
  | Evar x => Ivar x :: nil
  | Econst n => Iconst n :: nil
  | Eadd e1 e2 => compile_expr e1 ++ compile_expr e2 ++ Iadd :: nil
  | Esub e1 e2 => compile_expr e1 ++ compile_expr e2 ++ Isub :: nil
  end.

Definition compile_bool_expr (b: bool_expr) (ofs: Z): code :=
  match b with
  | Bequal e1 e2 => compile_expr e1 ++ compile_expr e2 ++ Ibne ofs :: nil
  | Bless e1 e2 => compile_expr e1 ++ compile_expr e2 ++ Ibge ofs :: nil
  end.

Definition length (c: code) : Z := Z_of_nat (List.length c).

Fixpoint compile_cmd (c: cmd): code :=
  match c with
  | Cskip => nil
  | Cassign x e => compile_expr e ++ Isetvar x :: nil
  | Cseq c1 c2 => compile_cmd c1 ++ compile_cmd c2
  | Cifthenelse b c1 c2 =>
      let code1 := compile_cmd c1 in
      let code2 := compile_cmd c2 in
      compile_bool_expr b (length code1 + 1)
      ++ code1
      ++ Ibranch (length code2)
      :: code2
  | Cwhile b c =>
      let code_c := compile_cmd c in
      let code_b := compile_bool_expr b (length code_c + 1) in
      code_b ++ code_c ++ 
      Ibranch (- (length code_b + length code_c + 1)) :: nil
  end.

Definition compile_program (c: cmd) : code :=
  compile_cmd c ++ Ihalt :: nil.

Lemma length_cons:
  forall i c, length (i :: c) = length c + 1.
Proof.
  intros. unfold length. simpl List.length. rewrite inj_S. auto. 
Qed.

Lemma length_app:
  forall c1 c2, length (c1 ++ c2) = length c1 + length c2.
Proof.
  intros. unfold length. rewrite List.app_length. apply inj_plus. 
Qed.

Lemma length_singleton:
  forall i, length (i :: nil) = 1.
Proof. intros. reflexivity. Qed.

Ltac normalize :=
  repeat (rewrite length_singleton || rewrite length_app || rewrite length_cons);
  repeat rewrite Zplus_assoc.

(** ** Correctness of compilation *)

Lemma code_at_app:
  forall i c2 c1 pc,
  pc = length c1 -> code_at (c1 ++ i :: c2) pc = Some i.
Proof.
  induction c1; intros; subst pc.
  simpl.  auto.
  normalize. simpl. 
  destruct (Z_eq_dec (length c1 + 1) 0).
  unfold length in e. omegaContradiction.
  replace (length c1 + 1 - 1) with (length c1) by omega. auto.
Qed.

(** The code for an expression pushes its value on the stack. *)

Lemma compile_expr_correct:
  forall s e pc stk c1 c2,
  pc = length c1 ->
  star (transition (c1 ++ compile_expr e ++ c2))
       (pc, stk, s) 
       (pc + length (compile_expr e), eval_expr s e :: stk, s).
Proof.
  induction e; intros; simpl.
(* var *)
  apply star_one. apply trans_var. apply code_at_app. auto. 
(* const *)
  apply star_one. apply trans_const. apply code_at_app. auto.
(* add *)
  repeat rewrite app_ass.
  eapply star_trans. apply IHe1. auto. 
  rewrite <- app_ass.
  eapply star_trans. apply IHe2. normalize. omega.
  rewrite <- app_ass.
  apply star_one. normalize.  
  apply trans_add. apply code_at_app. normalize. omega.  
(* sub *)
  repeat rewrite app_ass.
  eapply star_trans. apply IHe1. auto. 
  rewrite <- app_ass.
  eapply star_trans. apply IHe2. normalize. omega. 
  rewrite <- app_ass.
  apply star_one. normalize. 
  apply trans_sub. apply code_at_app. normalize; omega. 
Qed.

(** The code for a boolean expression falls through or branches to [ofs],
  depending on the truth value of the expression. *)

Lemma compile_bool_expr_correct:
  forall s e pc stk ofs c1 c2,
  pc = length c1 ->
  star (transition (c1 ++ compile_bool_expr e ofs ++ c2))
       (pc, stk, s) 
       (pc + length (compile_bool_expr e ofs)
           + (if eval_bool_expr s e then 0 else ofs),
        stk, s).
Proof.
  induction e; intros; simpl.
(* equal *)
  repeat rewrite app_ass.
  eapply star_trans. apply compile_expr_correct. auto. 
  rewrite <- app_ass.
  eapply star_trans. apply compile_expr_correct. normalize. omega. 
  rewrite <- app_ass.
  apply star_one. apply trans_bne with ofs.
  apply code_at_app. normalize; omega.
  normalize. destruct (Z_eq_dec (eval_expr s e) (eval_expr s e0)); omega.
(* less *)
  repeat rewrite app_ass.
  eapply star_trans. apply compile_expr_correct. auto. 
  rewrite <- app_ass.
  eapply star_trans. apply compile_expr_correct. normalize. omega. 
  rewrite <- app_ass.
  apply star_one. apply trans_bge with ofs.
  apply code_at_app. normalize; omega.
  normalize. destruct (Z_lt_dec (eval_expr s e) (eval_expr s e0)); omega.
Qed.

(** The code for a terminating command updates the state as predicted
    by the natural semantics. *)

Lemma compile_cmd_correct_terminating:
  forall s c s', exec s c s' ->
  forall stk pc c1 c2,
  pc = length c1 ->
  star (transition (c1 ++ compile_cmd c ++ c2))
       (pc, stk, s)
       (pc + length (compile_cmd c), stk, s').
Proof.
  induction 1; intros.

(* skip *)
  simpl. rewrite Zplus_0_r. apply star_refl.

(* assign *)
  simpl. rewrite app_ass. eapply star_trans. 
  apply compile_expr_correct. auto.
  rewrite <- app_ass.
  apply star_one. normalize. apply trans_setvar. apply code_at_app. normalize; omega.

(* seq *)
  simpl. repeat rewrite app_ass.
  eapply star_trans. apply IHexec1. auto. 
  rewrite <- app_ass. normalize. apply IHexec2. normalize. omega.

(* ifthenelse *)
  simpl. set (code1 := compile_cmd c1). set (code2 := compile_cmd c2).
  repeat rewrite app_ass.
  eapply star_trans. apply compile_bool_expr_correct. auto.
  rewrite <- app_ass.
  destruct (eval_bool_expr s be).
  (* ifthenelse, true *)
  simpl app.
  eapply star_trans. apply IHexec. normalize. omega.
  rewrite <- app_ass. 
  apply star_one. fold code1. 
  apply trans_branch with (length code2).
  apply code_at_app. normalize. omega.
  normalize. omega. 
  (* ifthenelse, false *)
  rewrite <- app_ass.
  change ((Ibranch (length code2) :: code2) ++ c3)
    with ((Ibranch (length code2) :: nil) ++ code2 ++ c3).
  rewrite <- app_ass. normalize.
  eapply star_trans. apply IHexec. normalize; omega.
  fold code2. rewrite <- Zplus_assoc. 
  replace (1 + length code2) with (length code2 + 1) by omega.
  rewrite Zplus_assoc. apply star_refl.

(* while true *)
  eapply star_trans. 2: eapply IHexec2; auto. 
  simpl. set (code_c := compile_cmd c). 
  set (code_b := compile_bool_expr be (length code_c + 1)).
  repeat rewrite app_ass. 
  eapply star_trans. apply compile_bool_expr_correct. auto. rewrite H.
  fold code_b. normalize. 
  rewrite <- app_ass.
  eapply star_trans. apply IHexec1. normalize. omega. 
  rewrite <- app_ass. simpl. apply star_one.
  apply trans_branch with (- (length code_b + length code_c + 1)).
  apply code_at_app. normalize. fold code_c. omega.
  fold code_c. omega. 

(* while false *)
  simpl. set (code_c := compile_cmd c). 
  set (code_b := compile_bool_expr be (length code_c + 1)).
  repeat rewrite app_ass. 
  eapply star_trans. apply compile_bool_expr_correct. auto. rewrite H.
  fold code_b. normalize. apply star_refl.
Qed.

(** The code for a diverging command performs infinitely many machine transitions. *)

Inductive diverging_state: code -> machine_state -> Prop :=
  | div_state_intro: forall s c c1 c2 pc stk,
      execinf s c -> pc = length c1 ->
      diverging_state (c1 ++ compile_cmd c ++ c2) (pc, stk, s).

Lemma diverging_state_productive:
  forall c s c1 c2 pc stk,
  execinf s c -> pc = length c1 ->
  exists st2, 
     plus (transition (c1 ++ compile_cmd c ++ c2)) (pc, stk, s) st2
  /\ diverging_state (c1 ++ compile_cmd c ++ c2) st2.
Proof.
  induction c; intros until stk; intros EXECINF PC; inv EXECINF.
(* seq left *)
  simpl. repeat rewrite app_ass. apply IHc1. auto. auto.  
(* seq right *)
  simpl.
  elim (IHc2 s1 (c0 ++ compile_cmd c1) c3 (length (c0 ++ compile_cmd c1))
             stk H3 (refl_equal _)).
  intro st2. repeat rewrite app_ass. normalize. intros [A B]. 
  exists st2; split; auto.
  eapply star_plus; eauto. apply compile_cmd_correct_terminating; auto.
(* if then else *)
  simpl. set (code1 := compile_cmd c1). set (code2 := compile_cmd c2).
  repeat rewrite app_ass.
  case_eq (eval_bool_expr s b); intro EBE; rewrite EBE in H1.
  (* ifthenelse, true *)
  destruct (IHc1 s (c0 ++ compile_bool_expr b (length code1 + 1))
                   ((Ibranch (length code2) :: code2) ++ c3)
                   (length c0 + length (compile_bool_expr b (length code1 + 1)))
                   stk)
  as [st2 [A B]]. auto. normalize. auto.
  generalize A; fold code1; repeat rewrite app_ass; normalize. clear A; intro A.
  generalize B; fold code1; repeat rewrite app_ass; normalize. clear B; intro B.
  exists st2; split; auto.
  eapply star_plus. apply compile_bool_expr_correct. auto. 
  rewrite EBE. normalize. rewrite Zplus_0_r. auto. 
  (* ifthenelse, false *)
  destruct (IHc2 s (c0 ++ compile_bool_expr b (length code1 + 1)
                    ++ code1 ++ Ibranch (length code2) :: nil)
                   c3
                   (length c0 + 
                    length (compile_bool_expr b (length code1 + 1)) +
                    length code1 + 1)
                   stk)
  as [st2 [A B]]. auto. normalize. auto.
  generalize A; fold code2; repeat rewrite app_ass; normalize. clear A; intro A.
  generalize B; fold code2; repeat rewrite app_ass; normalize. clear B; intro B.
  exists st2; split; auto.
  eapply star_plus. apply compile_bool_expr_correct. auto. 
  rewrite EBE. normalize. auto.
(* while body *)
  simpl. set (code_c := compile_cmd c). 
  set (code_b := compile_bool_expr b (length code_c + 1)).
  repeat rewrite app_ass. simpl.
  destruct (IHc s (c1 ++ code_b)
                  (Ibranch (- (length code_b + length code_c + 1)) :: c2)
                  (length c1 + length code_b)
                  stk)
  as [st2 [A B]]. auto. normalize; auto.
  generalize A; fold code_c; repeat rewrite app_ass; normalize. clear A; intro A.
  generalize B; fold code_c; repeat rewrite app_ass; normalize. clear B; intro B.
  exists st2; split; auto. 
  eapply star_plus. apply compile_bool_expr_correct. auto. rewrite H2. 
  rewrite Zplus_0_r. auto.

(* while loop *)
  exists (length c1, stk, s1); split.
  simpl. set (code_c := compile_cmd c). 
  set (code_b := compile_bool_expr b (length code_c + 1)).
  set (ofs := - (length code_b + length code_c + 1)).
  repeat rewrite app_ass. simpl.
  eapply star_plus. apply compile_bool_expr_correct. auto. rewrite H1.
  rewrite Zplus_0_r. 
  rewrite <- app_ass. fold code_b.
  eapply star_plus. apply compile_cmd_correct_terminating. eauto. normalize; auto.
  apply plus_one. rewrite <- app_ass. 
  apply trans_branch with ofs. apply code_at_app. fold code_c. normalize. auto.
  unfold ofs. fold code_c. omega. 
  econstructor; eauto. 
Qed.

Lemma compile_cmd_correct_diverging:
  forall s c , execinf s c ->
  forall pc stk c1 c2,
  pc = length c1 ->
  infseq (transition (c1 ++ compile_cmd c ++ c2)) (pc, stk, s).
Proof.
  intros. apply infseq_coinduction_principle_2 with 
            (X := diverging_state (c1 ++ compile_cmd c ++ c2)). 
  intros. inv H1. apply diverging_state_productive; auto. 
  constructor; auto.
Qed.

(** In conclusion, we obtain the expected forward simulation result
  between IMP programs and their compiled VM code. *)

Theorem compile_program_correct:
  forall c s_init,
  (forall s_fin, terminates c s_init s_fin -> mach_terminates (compile_program c) s_init s_fin)
/\
  (diverges c s_init -> mach_diverges (compile_program c) s_init).
Proof.
  intros. unfold compile_program. set (code_c := compile_cmd c). split; intros.
(* termination *)
  red. exists (length (code_c)); split.
  apply code_at_app. auto.
  change (length code_c)
    with (length (@nil instruction) + length code_c).
  change (code_c ++ Ihalt :: nil) with (nil ++ code_c ++ Ihalt :: nil).
  apply compile_cmd_correct_terminating. apply terminates_exec. auto. auto.
(* divergence *)
  red. 
  change (length code_c)
    with (length (@nil instruction) + length code_c).
  change (code_c ++ Ihalt :: nil) with (nil ++ code_c ++ Ihalt :: nil).
  apply compile_cmd_correct_diverging. apply diverges_execinf. auto. auto.
Qed.

(** * Part 4.  An example of optimizing program transformation: dead code elimination *)

(** Finite sets of variables, from the Coq standard library. *)

Require Import FSets.
Module VS := FSetAVL.Make(Nat_as_OT).
Module VSP := FSetProperties.Properties(VS).
Module VSdecide := FSetDecide.Decide(VS).
Import VSdecide.

(** Computation of free variables. *)

Fixpoint fv_expr (e: expr) : VS.t :=
  match e with
  | Evar x => VS.singleton x
  | Econst n => VS.empty
  | Eadd e1 e2 => VS.union (fv_expr e1) (fv_expr e2)
  | Esub e1 e2 => VS.union (fv_expr e1) (fv_expr e2)
  end.

Definition fv_bool_expr (b: bool_expr) : VS.t :=
  match b with
  | Bequal e1 e2 => VS.union (fv_expr e1) (fv_expr e2)
  | Bless e1 e2 => VS.union (fv_expr e1) (fv_expr e2)
  end.

Fixpoint fv_cmd (c: cmd) : VS.t :=
  match c with
  | Cskip => VS.empty
  | Cassign x e => fv_expr e
  | Cseq c1 c2 => VS.union (fv_cmd c1) (fv_cmd c2)
  | Cifthenelse b c1 c2 => VS.union (fv_bool_expr b) (VS.union (fv_cmd c1) (fv_cmd c2))
  | Cwhile b c => VS.union (fv_bool_expr b) (fv_cmd c)
  end.

(** ** Liveness analysis *)

(** Computing post-fixpoints. *)

Section FIXPOINT.

Variable F: VS.t -> VS.t.
Variable default: VS.t.

Fixpoint iter (n: nat) (x: VS.t) {struct n} : VS.t :=
  match n with
  | O => default
  | S n' =>
      let x' := F x in
      if VS.subset x' x then x else iter n' x'
  end.

Definition niter := 20%nat.

Definition fixpoint : VS.t := iter niter VS.empty.

Lemma fixpoint_charact:
  VS.Subset (F fixpoint) fixpoint \/ fixpoint = default.
Proof.
  unfold fixpoint. generalize niter, VS.empty. induction n; intros; simpl.
  auto.
  case_eq (VS.subset (F t) t); intro. 
  left. apply VS.subset_2. auto.
  apply IHn. 
Qed.

Hypothesis F_stable:
  forall x, VS.Subset x default -> VS.Subset (F x) default.

Lemma fixpoint_upper_bound:
  VS.Subset fixpoint default.
Proof.
  assert (forall n x, VS.Subset x default -> VS.Subset (iter n x) default).
  induction n; intros; simpl.
  red; auto.
  case_eq (VS.subset (F x) x); intro. auto. apply IHn. auto. 
  unfold fixpoint. apply H. apply VSP.subset_empty. 
Qed.

End FIXPOINT.

(** Liveness analysis: [live c a] computes the set of variables live
  "before" [c] as a function of the set [a] of variables live "after". *)

Fixpoint live (c: cmd) (a: VS.t) {struct c} : VS.t :=
  match c with
  | Cskip => a
  | Cassign x e =>
      if VS.mem x a
      then VS.union (VS.remove x a) (fv_expr e)
      else a
  | Cseq c1 c2 => live c1 (live c2 a)
  | Cifthenelse b c1 c2 =>
      VS.union (fv_bool_expr b) (VS.union (live c1 a) (live c2 a))
  | Cwhile b c =>
      let a' := VS.union (fv_bool_expr b) a in
      let default := VS.union (fv_cmd (Cwhile b c)) a in
      fixpoint (fun x => VS.union a' (live c x)) default
  end.

Lemma live_upper_bound:
  forall c a,
  VS.Subset (live c a) (VS.union (fv_cmd c) a).
Proof.
  induction c; intros; simpl.
  fsetdec.
  case_eq (VS.mem i a); intros. fsetdec. fsetdec.
  generalize (IHc1 (live c2 a)). generalize (IHc2 a). fsetdec.
  generalize (IHc1 a). generalize (IHc2 a). fsetdec.
  apply fixpoint_upper_bound. intro x. generalize (IHc x). fsetdec.
Qed.

Lemma live_while_charact:
  forall b c a,
  let a' := live (Cwhile b c) a in
  VS.Subset (fv_bool_expr b) a' /\ VS.Subset a a' /\ VS.Subset (live c a') a'.
Proof.
  intros.
  generalize (fixpoint_charact
    (fun x : VS.t => VS.union (VS.union (fv_bool_expr b) a) (live c x))
          (VS.union (VS.union (fv_bool_expr b) (fv_cmd c)) a)).
  simpl in a'. fold a'. intros [A|A].
  split. generalize A; fsetdec. split; generalize A; fsetdec. 
  split. rewrite A. fsetdec. 
  split. rewrite A. fsetdec.
  eapply VSP.subset_trans. apply live_upper_bound. rewrite A. fsetdec.
Qed.

(** ** Dead code elimination *)

(** Turn assignments [x := e] to dead variables [x] into [skip] statements. *)

Fixpoint dce (c: cmd) (a: VS.t) {struct c}: cmd :=
  match c with
  | Cskip => Cskip
  | Cassign x e => if VS.mem x a then Cassign x e else Cskip
  | Cseq c1 c2 => Cseq (dce c1 (live c2 a)) (dce c2 a)
  | Cifthenelse b c1 c2 =>
      Cifthenelse b (dce c1 a) (dce c2 a)
  | Cwhile b c =>
      Cwhile b (dce c (live (Cwhile b c) a))
  end.

(** Example:
<<
   r := a;                 ===>   r := a;
   q := 0;                        skip;
   while b < r+1 do               while b < r+1 do
     r := r - b;                    r := r - b;
     q := q + 1;                    skip;
   done                           done
>>
if [q] is not live after.  If [q] is live, the program is unchanged.
*)

Eval compute in (dce prog (VS.singleton vr)).

Eval compute in (dce prog (VS.singleton vq)).

(** ** Semantic correctness *)

Definition agree (a: VS.t) (s1 s2: state) : Prop :=
  forall x, VS.In x a -> s1 x = s2 x.

Lemma agree_mon:
  forall a a' s1 s2,
  agree a' s1 s2 -> VS.Subset a a' -> agree a s1 s2.
Proof.
  unfold VS.Subset, agree; intros. auto.
Qed.

Lemma eval_expr_agree:
  forall a s1 s2, agree a s1 s2 ->
  forall e, VS.Subset (fv_expr e) a -> eval_expr s1 e = eval_expr s2 e.
Proof.
  induction e; simpl; intros.
  apply H. generalize H0; fsetdec. 
  auto.
  f_equal. apply IHe1. generalize H0; fsetdec. apply IHe2. generalize H0; fsetdec. 
  f_equal. apply IHe1. generalize H0; fsetdec. apply IHe2. generalize H0; fsetdec. 
Qed.

Lemma eval_bool_expr_agree:
  forall a s1 s2, agree a s1 s2 ->
  forall b, VS.Subset (fv_bool_expr b) a -> eval_bool_expr s1 b = eval_bool_expr s2 b.
Proof.
  induction b; simpl; intros.
  repeat rewrite (eval_expr_agree a s1 s2); auto; generalize H0; fsetdec.
  repeat rewrite (eval_expr_agree a s1 s2); auto; generalize H0; fsetdec.
Qed.

Lemma agree_update_live:
  forall s1 s2 a x v,
  agree (VS.remove x a) s1 s2 ->
  agree a (update s1 x v) (update s2 x v).
Proof.
  intros; red; intros. unfold update. destruct (eq_ident x x0). auto.
  apply H. apply VS.remove_2. auto. auto.
Qed.

Lemma agree_update_dead:
  forall s1 s2 a x v,
  agree a s1 s2 -> ~VS.In x a ->
  agree a (update s1 x v) s2.
Proof.
  intros; red; intros. unfold update. destruct (eq_ident x x0).
  subst x0. contradiction.
  auto.
Qed.

Lemma dce_correct_terminating:
  forall s c s', exec s c s' ->
  forall a s1,
  agree (live c a) s s1 ->
  exists s1', exec s1 (dce c a) s1' /\ agree a s' s1'.
Proof.
  induction 1; intros; simpl.
(* skip *)
  exists s1; split. constructor. auto.
(* assign *)
  simpl in H. case_eq (VS.mem x a); intro EQ; rewrite EQ in H.
  assert (eval_expr s e = eval_expr s1 e). 
    eapply eval_expr_agree; eauto with set. 
  exists (update s1 x (eval_expr s1 e)); split.
  apply exec_assign. rewrite H0. apply agree_update_live.
  eapply agree_mon; eauto with set.
  exists s1; split. 
  apply exec_skip. apply agree_update_dead; auto. 
  red; intro. assert (VS.mem x a = true). apply VS.mem_1; auto. congruence.
(* seq *)
  simpl in H1.
  destruct (IHexec1 _ _ H1) as [s1' [E1 A1]].
  destruct (IHexec2 _ _ A1) as [s2' [E2 A2]].
  exists s2'; split.
  apply exec_seq with s1'; auto.
  auto.
(* ifthenelse *)
  simpl in H0. 
  assert (eval_bool_expr s be = eval_bool_expr s1 be). 
    eapply eval_bool_expr_agree; eauto with set. 
  assert (agree (live (if eval_bool_expr s be then c1 else c2) a) s s1).
    destruct (eval_bool_expr s be); eapply agree_mon; eauto with set.
  destruct (IHexec _ _ H2) as [s1' [E A]].
  exists s1'; split. 
  apply exec_if. rewrite <- H1. destruct (eval_bool_expr s be); auto.
  auto.
(* while true *)
  destruct (live_while_charact be c a) as [P [Q R]]. 
  assert (eval_bool_expr s be = eval_bool_expr s0 be).
    eapply eval_bool_expr_agree; eauto.
  destruct (IHexec1 (live (Cwhile be c) a) s0) as [s1' [E1 A1]]. 
    eapply agree_mon; eauto. 
  destruct (IHexec2 a s1') as [s2' [E2 A2]]. auto. 
  exists s2'; split.
  apply exec_while_loop with s1'. congruence. auto. exact E2. auto.
(* while false *)
  destruct (live_while_charact be c a) as [P [Q R]]. 
  assert (eval_bool_expr s be = eval_bool_expr s1 be).
    eapply eval_bool_expr_agree; eauto.
  exists s1; split.
  apply exec_while_stop. congruence.
  eapply agree_mon; eauto. 
Qed.

Lemma dce_correct_diverging:
  forall s c, execinf s c ->
  forall a s1,
  agree (live c a) s s1 -> execinf s1 (dce c a).
Proof.
  cofix COINDHYP; intros; inv H; simpl.
(* seq left *)
  apply execinf_seq_left. apply COINDHYP with s. auto. auto. 
(* seq right *)
  simpl in H0.
  destruct (dce_correct_terminating _ _ _ H1 _ _ H0) as [s1' [E A]].
  apply execinf_seq_right with s1'. auto. apply COINDHYP with s2; auto.
(* ifthenelse *)
  simpl in H0. 
  assert (eval_bool_expr s b = eval_bool_expr s1 b). 
    eapply eval_bool_expr_agree; eauto with set.
  apply execinf_if. 
  rewrite <- H. destruct (eval_bool_expr s b).
  apply COINDHYP with s; auto. eapply agree_mon; eauto with set.
  apply COINDHYP with s; auto. eapply agree_mon; eauto with set.
(* while body *)
  destruct (live_while_charact b c0 a) as [P [Q R]]. 
  assert (eval_bool_expr s b = eval_bool_expr s1 b).
    eapply eval_bool_expr_agree; eauto.
  apply execinf_while_body. congruence. 
  apply COINDHYP with s. auto. eapply agree_mon; eauto. 
(* while loop *)
  destruct (live_while_charact b c0 a) as [P [Q R]]. 
  assert (eval_bool_expr s b = eval_bool_expr s1 b).
    eapply eval_bool_expr_agree; eauto.
  assert (agree (live c0 (live (Cwhile b c0) a)) s s1).
    eapply agree_mon; eauto.
  destruct (dce_correct_terminating _ _ _ H2 _ _ H4) as [s1' [E A]].
  apply execinf_while_loop with s1'. congruence. exact E. 
  change (execinf s1' (dce (Cwhile b c0) a)).
  apply COINDHYP with s2. auto. auto. 
Qed.
