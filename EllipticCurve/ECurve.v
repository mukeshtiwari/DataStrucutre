Require Import Arith_base.
Require Import Field_tac.
Require Import Ring.
Require Import Eqdep_dec.
(* Require Import FGroup. *)
Require Import List.
(* Require Import UList. *)

(* My attempt to understand and verify elliptic curve cryptography in Coq *)

Section Elliptic.
  (* Field Element*)
  Context (K : Type) (kO kI : K)
          (kplus kmul ksub kdiv : K -> K -> K)
          (kopp kinv : K -> K) (A B : K)
          (is_zero : K -> bool).
  (* K notations *)
  Notation "x + y" := (kplus x y).  Notation "x * y " := (kmul x y). 
  Notation "x - y " := (ksub x y). Notation "- x" := (kopp x).
  Notation "/ x" := (kinv x). Notation "x / y" := (kdiv x y).
  Notation "0" := kO.
  Notation "1" := kI.
  Notation "2" := (1+1).
  Notation "3" := (1+1+1).

  (* Non singularity *)
  Notation "4" := (2 * 2).
  Notation "27" := (3 * 3 * 3).

  (* elliptic curve theory *)
  (* https://coq.inria.fr/library/Coq.setoid_ring.Field_theory.html# *)
  Record ell_theory : Prop :=
    make_ell_theory {
        Kfth : field_theory kO kI kplus kmul ksub kopp kdiv kinv (@eq K);
        NonSingular : 4 * A * A * A + 27 * B * B <> 0;
        one_not_zero : 1 <> 0;
        two_not_zero : 2 <> 0;
        is_zero_correct : forall k : K, is_zero k = true <-> k = 0
      }.

  Context (Eth : ell_theory).

  Fixpoint pow (k : K) (n : nat) : K :=
    match n with
    | O => 1
    | 1 => k
    | S n' => k * pow k n'
    end.

  Notation "x ^ y" := (pow x y).

  Theorem pow_S : forall k n, k ^ (S n) = k * k ^ n.
  Proof.
    intros k n.
    case n; simpl; auto.
    rewrite Eth.(Kfth).(F_R).(Rmul_comm).
    rewrite Eth.(Kfth).(F_R).(Rmul_1_l).
    auto.
  Qed.

  Require Import Coq.NArith.Nnat.
  Lemma Kpower_theory : Ring_theory.power_theory 1 kmul (eq (A := K)) BinNat.nat_of_N pow.
  Proof.
    constructor.
    intros r n; case n; simpl; auto.
    intros p; elim p using BinPos.Pind; auto.
    intros p0 H.
    rewrite Pnat.nat_of_P_succ_morphism;
      rewrite pow_S.
    rewrite (Ring_theory.pow_pos_succ (Eqsth K) (rmul_ext3_Proper (Eq_ext kplus kmul kopp))); auto.
    rewrite H; auto.
    intros x y z.
    rewrite Eth.(Kfth).(F_R).(Rmul_assoc). auto.
  Qed.

  Ltac iskpow_coef t :=
    match t with
    | (S ?x) => iskpow_coef x
    | O => true
    | _ => false
    end.

  Ltac kpow_tac t :=
    match iskpow_coef t with
    | true => constr:(BinNat.N_of_nat t)
    | _ => constr:(NotConstant)
    end.

  Add Field Kfth : Eth.(Kfth) (power_tac Kpower_theory [kpow_tac]).

  Let Kdiv_def := (Fdiv_def Eth.(Kfth)).

  Lemma Kinv_ext : forall p q, p = q -> /p = /q.
  Proof.
    intros p q H. rewrite H. auto.
  Qed.

  Let Ksth := (Eqsth K).
  Let Keqe := (Eq_ext kplus kmul kopp).
  Let AFth := Field_theory.F2AF Ksth Keqe Eth.(Kfth).
  Let Kmorph := InitialRing.gen_phiZ_morph Ksth Keqe (F_R Eth.(Kfth)).

  Hint Resolve one_not_zero two_not_zero.

  Notation "x ?0" := (is_zero x) (at level 10).

  Fixpoint n2k (n : nat) : K :=
    match n with
    | O => kO
    | 1 => kI
    | S n' => 1 + n2k n'
    end.

  Coercion N2k := n2k.

  Theorem Kdiff_2_0 : (2 : K) <> 0.
  Proof.
    apply two_not_zero; auto.
  Qed.

  Hint Resolve Kdiff_2_0.

  Theorem Keq_minus_eq : forall x y, x - y = 0 -> x = y.
  Proof.
    intros x y H.
    apply trans_equal with (y + (x - y)); try ring.
    rewrite H; ring.
  Qed.

  Theorem Keq_minus_eq_inv : forall x y, x = y -> x - y = 0.
  Proof.
    intros x y H. rewrite H. ring.
  Qed.

  Theorem Kdiff_diff_minus_eq : forall x y, x <> y -> x - y <> 0.
  Proof.
    intros x y H. unfold not in *.
    intros. apply Keq_minus_eq in H0.
    abstract congruence.
  Qed.

  Hint Resolve Kdiff_diff_minus_eq.

  Theorem Kmult_integral :
    forall x y, x * y = 0 -> x = 0 \/ y = 0.
  Proof.
    intros x y H.
    generalize (Eth.(is_zero_correct) x); case (is_zero x); intros (H1, H2);
      auto; right.
    apply trans_equal with ((/x) * (x * y)); try field.
    intros H3. pose proof (H2 H3). abstract congruence.
    rewrite H; ring.
  Qed.

  Theorem Kmult_integral_contrapositive:
    forall x y, x <> 0 -> y <> 0 -> x * y <> 0.
  Proof.
    intros x y H1 H2 H3.
    case (Kmult_integral _ _ H3); auto.
  Qed.
  Hint Resolve Kmult_integral_contrapositive.

  Theorem Kmult_eq_compat_l: forall x y z, y = z -> x * y = x * z.
  Proof.
    intros x y z H; rewrite H; ring.
  Qed.

  Theorem Keq_opp_is_zero: forall x, x = - x -> x = 0.
  Proof.
    intros x H.
    case (Kmult_integral (1+1 : K) x); simpl; auto.
    apply trans_equal with (x + x); simpl; try ring.
    rewrite H at 1; ring.
    intros H1; case two_not_zero; auto.
  Qed.

  Theorem Kdiv_inv_eq_0:
    forall x y, x / y = 0 -> y <> 0 -> x = 0.
  Proof.
    intros x y H1 H2.
    apply trans_equal with (y * (x / y)); try field; auto.
    rewrite H1; ring.
  Qed.


  Theorem is_zero_diff: forall x y, (x - y) ?0 = true -> x = y.
  Proof.
    intros x y H.
    apply trans_equal with (y + (x - y)); try ring.
    case (Eth.(is_zero_correct) (x - y)); intros H1 H2.
    apply H1 in H; rewrite H; ring.
  Qed.


  Theorem is_zero_diff_inv: forall x y, x = y -> (x - y) ?0 = true.
  Proof.
    intros x y H; rewrite H.
    case (Eth.(is_zero_correct) (y - y)); intros H1 H2.
    apply H2; ring.
  Qed.


  Theorem Ksqr_eq :
    forall x y, x^2 = y^2 -> x = y \/ x = -y.
  Proof.
    intros x y H. case (Kmult_integral (x - y) (x + y)); auto.
    ring [H].
    intros H1; left; apply trans_equal with (y + (x - y)); try ring.
    rewrite H1; ring.
    intros H1; right; apply trans_equal with (-y + (x + y)); try ring.
    rewrite H1; try ring.
  Qed.


  Theorem diff_rm_quo: forall x y, x/y <> 0 -> y<>0 -> x <> 0.
  Proof.
    intros x y H H0 H1.  case H. field [H1]; auto.
  Qed.

  Ltac dtac H :=
    match type of H with
      ?X <> 0 =>
      field_simplify X in H
    end; [
      match type of H with
        ?X/?Y <> 0 =>
        cut (X <> 0);
        [clear H; intros H | apply diff_rm_quo with Y; auto]
      end
    | auto].

  
  
  Inductive elt : Type :=
  | Inf_elt : elt
  | Curve_elt x y : y^2 = x^3 + A * x + B -> elt.

  Definition Kdec : forall a b : K, {a = b} + {a <> b}.
  Proof.
    intros a b; case_eq ((a - b) ?0); intros H.
    left. apply is_zero_diff. auto.
    right; intros H1; rewrite is_zero_diff_inv in H;
      abstract congruence.
  Defined.

  Theorem curve_elt_irr: forall x1 x2 y1 y2 H1 H2,
      x1 = x2 -> y1 = y2 -> Curve_elt x1 y1 H1 = Curve_elt x2 y2 H2.
  Proof.
    intros x1 x2 y1 y2 H1 H2 H3 H4.
    subst.
    rewrite (fun H => eq_proofs_unicity H H1 H2); auto.
    intros x y; case (Kdec x y); intros H3; [left | right]; auto.
  Qed.

  Theorem curve_elt_irr1: forall x1 x2 y1 y2 H1 H2,
      x1 = x2 -> (x1 = x2 -> y1 = y2) -> Curve_elt x1 y1 H1 = Curve_elt x2 y2 H2.
  Proof.
    intros x1 x2 y1 y2 H1 H2 H3 H4.
    apply curve_elt_irr; auto.
  Qed.

  Notation "x ?= y" := (Kdec x y) (at level 70).

  Definition ceqb: forall a b: elt, {a = b} + {a<>b}.
  Proof.
    intros a b. case a; case b; auto;
                  try (intros x y e; right; intros H; abstract congruence).
    intros x y e x0 y0 e0. case (Kdec x x0); intros H.
    case (Kdec y y0); intros H1.
    left; apply curve_elt_irr; auto. 
    right; intros H2; injection H2; intros H3 H4;
      subst; abstract congruence.
    right; intros H2; injection H2; intros H3 H4;
      subst; abstract congruence.
  Qed.

  Theorem is_zero_true: forall e, is_zero e = true -> e = 0.
  Proof.
    intro e; generalize (Eth.(is_zero_correct) e); case is_zero; auto;
      intros (H,_); auto.
  Qed.


  Theorem is_zero_false: forall e, is_zero e = false -> e <> 0.
    intro e; generalize (Eth.(is_zero_correct) e); case is_zero; auto;
      intros (_,H); auto.
    intros; discriminate.
    intros _ H1; generalize (H H1); discriminate.
  Qed.

  Lemma opp_lem:
    forall x y,
      y ^ 2 = x ^ 3 + A * x + B -> (- y) ^ 2  = x ^ 3 + A * x + B.
  Proof.
    intros x y H.
    ring [H].
  Qed.

  Definition opp : elt -> elt.
    refine (fun p => match p with
                  | Inf_elt => Inf_elt
                  | Curve_elt x y H => Curve_elt x (-y) _
                  end).
    apply opp_lem; auto.
  Defined.

  Theorem opp_opp: forall p, opp (opp p) = p.
  Proof.
    intros p; case p; simpl; auto.
    intros x y e. apply curve_elt_irr; ring.
  Qed.


  (* if x1 and x2 are same then either it's same point or opposite point *)
  Theorem curve_elt_opp:
    forall x1 x2 y1 y2 H1 H2,
      x1 = x2 -> Curve_elt x1 y1 H1 = Curve_elt x2 y2 H2
                \/ Curve_elt x1 y1 H1 = opp (Curve_elt x2 y2 H2).
  Proof.
    intros x1 x2 y1 y2 H1 H2 H3.
    case (Kmult_integral (y1 - y2) (y1 + y2)); try intros H4.
    ring_simplify.
    ring [H1 H2 H3].
    left. apply curve_elt_irr; auto.
    apply Keq_minus_eq. auto.
    right. unfold opp. apply curve_elt_irr. auto.
    apply Keq_minus_eq. rewrite <- H4. ring.
  Qed.

  Lemma add_lem1: forall x1 y1,
      y1 <> 0 ->
      y1 ^ 2 = x1 ^ 3 + A * x1 + B ->
      let l := (3 * x1 * x1 + A) / (2 * y1) in
      let x3 := l ^ 2 - 2 * x1  in
      (- y1 - l * (x3 - x1)) ^ 2 = x3 ^ 3 + A * x3 + B.
  Proof.
    intros x1 y1 H1 H2 l x3; unfold x3, l.
    field [H2].
    auto.
  Qed.

  (* line passing through two points on curve intersects at third *)
  Lemma add_lem2: forall x1 y1 x2 y2,
      x1 <> x2 ->
      y1 ^ 2 = x1 ^ 3 + A * x1 + B ->
      y2 ^ 2 = x2 ^ 3 + A * x2 + B ->
      let l := (y2 - y1) / (x2 - x1) in
      let x3 := l ^ 2 - x1 - x2 in
      (- y1 - l * (x3 - x1)) ^ 2 = x3 ^ 3 + A * x3 + B.
  Proof.
    intros x1 y1 x2 y2 H H1 H2 l x3; unfold x3, l.
    field [H1 H2]; auto.
  Qed.

  Lemma add_zero : forall x1 x2 y1 y2,
      x1 = x2 ->
      y1 ^ 2 = x1 ^ 3 + A * x1 + B ->
      y2 ^ 2 = x2 ^ 3 + A * x2 + B ->
      y1 <> -y2 -> y1 = y2.
  Proof.
    intros x1 x2 y1 y2 H H1 H2 H3; subst x2.
    case (@Kmult_integral (y1 - y2) (y1 + y2));
      try (intros H4; apply Keq_minus_eq; auto).
    ring [H1 H2].
    case H3; apply Keq_minus_eq; rewrite <- H4;
      ring.
  Qed.

  Lemma add_zero_diff : forall x1 x2 y1 y2,
      x1 = x2 ->
      y1 ^ 2 = x1 ^ 3 + A * x1 + B ->
      y2 ^ 2 = x2 ^ 3 + A * x2 + B ->
      y1 <> -y2 -> y1 <> 0.
  Proof.
    intros x1 x2 y1 y2 H H1 H2 H3 H4.
    pose proof (add_zero _ _ _ _ H H1 H2 H3) as H5.
    case H3. rewrite <- H5. ring [H4].
  Qed.
  