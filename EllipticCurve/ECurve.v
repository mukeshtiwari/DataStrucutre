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


  (* Addition of points *)
  Definition add : elt -> elt -> elt.
    refine (fun p1 p2 =>
              match p1 with
              | Inf_elt => p2
              | Curve_elt x1 y1 H1 =>
                match p2 with
                | Inf_elt => p1
                | Curve_elt x2 y2 H2 =>
                  if x1 ?= x2 then
                    if (y1 ?= -y2) then
                      Inf_elt
                    else
                      let l := (3 * x1 * x1 + A) / (2 * y1) in
                      let x3 := l ^ 2 - 2 * x1 in
                      Curve_elt x3 (-y1 - l * (x3 - x1)) _
                  else
                    let l := (y2 - y1) / (x2 - x1) in
                    let x3 := l ^ 2 - x1 - x2 in
                    Curve_elt x3 (-y1 - l * (x3 - x1)) _
                end
              end).
    apply add_lem1; auto.
    apply (@add_zero_diff x1 x2 y1 y2); auto.
    apply (@add_lem2 x1 y1 x2 y2); auto.
  Defined.

 
    
  Ltac kauto :=
    auto;
    match goal with
      H : ~ ?A, H1 : ?A |- _ => case H; auto
    end.

  Ltac ksplit :=
    let h := fresh "KD" in
    case Kdec; intros h; try (case h; kauto; fail).

  Theorem add_case: forall P,
      (forall p, P Inf_elt p p) ->
      (forall p, P p Inf_elt p) ->
      (forall p, P p (opp p) Inf_elt) ->
      (forall p1 x1 y1 H1 p2 x2 y2 H2 l,
          p1 = (Curve_elt x1 y1 H1) -> p2 = (Curve_elt x2 y2 H2) ->
          p2 = add p1 p1 -> y1<>0 ->
          l = (3 * x1 * x1 + A) / (2 * y1) ->
          x2 = l ^ 2 - 2 * x1 -> y2 = - y1 - l * (x2 - x1) ->
          P p1 p1 p2) ->
      (forall p1 x1 y1 H1 p2 x2 y2 H2 p3 x3 y3 H3 l,
          p1 = (Curve_elt x1 y1 H1) -> p2 = (Curve_elt x2 y2 H2) ->
          p3 = (Curve_elt x3 y3 H3) -> p3 = add p1 p2 ->
          x1 <> x2 ->
          l = (y2 - y1) / (x2 - x1) ->
          x3 = l ^ 2 - x1 - x2 -> y3 = -y1 - l * (x3 - x1) ->
          P p1 p2 p3)->
      forall p q, P p q (add p q).
  Proof.
    intros P H1 H2 H3 H4 H5 p q; case p; case q; auto.
    intros x2 y2 e2 x1 y1 e1; unfold add.
    repeat ksplit.
    replace (Curve_elt x2 y2 e2) with
        (opp (Curve_elt x1 y1 e1)); auto; simpl.
    apply curve_elt_irr; auto; ring [KD0].
    assert (HH: y1 <> 0).
    apply (@add_zero_diff x1 x2 y1 y2); auto.
    replace (Curve_elt x2 y2 e2) with
        (Curve_elt x1 y1 e1); auto.
    eapply H4; eauto; simpl; repeat ksplit;
      try apply curve_elt_irr; auto.
    case HH; apply  Keq_opp_is_zero; auto.
    apply curve_elt_irr; auto.
    case (@Kmult_integral (y1 - y2) (y1 + y2)); try intros HH1.
    ring [e1 e2 KD].
    apply Keq_minus_eq; auto.
    case KD0; apply Keq_minus_eq; ring_simplify; auto.
    eapply H5; eauto; simpl; repeat ksplit.
    apply curve_elt_irr; auto.
  Qed.
  
  Theorem add_casew: forall P,
      (forall p, P Inf_elt p p) ->
      (forall p, P p Inf_elt p) ->
      (forall p, P p (opp p) Inf_elt) ->
      (forall p1 x1 y1 H1 p2 x2 y2 H2 p3 x3 y3 H3 l,
          p1 = (Curve_elt x1 y1 H1) -> p2 = (Curve_elt x2 y2 H2) ->
          p3 = (Curve_elt x3 y3 H3) -> p3 = add p1 p2 -> p1 <> opp p2 ->
          ((x1 = x2 /\ y1 = y2 /\ l = (3 * x1 * x1 + A) / (2 * y1)) \/
           (x1 <> x2 /\ l = (y2 - y1) / (x2 - x1))
          ) ->
          x3 = l ^ 2 - x1 - x2 -> y3 = -y1 - l * (x3 - x1) ->
          P p1 p2 p3)->
      forall p q, P p q (add p q).
    intros; apply add_case; auto.
    intros; eapply X2; eauto.
    rewrite H; simpl; intros tmp; case H4; injection tmp;
      apply Keq_opp_is_zero.
    ring [H6].
    intros; eapply X2; eauto.
    rewrite H; rewrite H0; simpl; intros tmp; case H6;
      injection tmp; auto.
  Qed.
  
  Definition is_tangent p1 p2 :=
    p1 <> Inf_elt /\ p1 = p2 /\ p1 <> opp p2.
  
  Definition is_generic p1 p2 :=
    p1 <> Inf_elt /\ p2 <> Inf_elt /\
    p1 <> p2 /\ p1 <> opp p2.
  
  Definition is_gotan p1 p2 :=
    p1 <> Inf_elt /\ p2 <> Inf_elt /\  p1 <> opp p2.
  
  Ltac kcase X Y :=
    pattern X, Y, (add X Y); apply add_case; auto;
    clear X Y.
  
  Ltac kcasew X Y :=
    pattern X, Y, (add X Y); apply add_casew; auto;
    clear X Y.
  
  Theorem spec1_assoc:
    forall p1 p2 p3,
      is_generic p1 p2 ->
      is_generic p2 p3 ->
      is_generic (add p1 p2) p3 ->
      is_generic  p1 (add p2 p3) ->
      add p1 (add p2 p3) = add (add p1 p2) p3.
    intros p1 p2; kcase p1 p2.
    intros p p3  _ _ (HH, _); case HH; auto.
    intros p3 _ _ _ p4 _ _ _ _ _ _ _ _ _ _ _ p5 (_, (_, (HH, _)));
      case HH; auto.
    intros p1 x1 y1 H1 p2 x2 y2 H2 p4 x4 y4 H4 l
           Hp Hp2 Hp4 Hp4b Hx Hl Hx4 Hy4 p3.
    generalize Hp2 Hp4b; clear Hp2 Hp4b; kcase p2 p3.
    intros; discriminate.
    intros p _ _ _ (_,(HH, _)); case HH; auto.
    intros p _ _ _ (_,(_,(_,HH)));  case HH; rewrite opp_opp; auto.
    intros p2 _ _ _ p3 _ _ _ _ _ _ _ _ _ _ _ _ _ _ (_, (_, (HH, _)));
      case HH; auto.
    intros p2 x2b y2b H2b p3 x3 y3 H3 p5 x5 y5 H5 l1.
    intros Hp2; pattern p2 at 2; rewrite Hp2; clear Hp2.
    intros Hp3 Hp5 Hp5b Hd Hl1 Hx5 Hy5 tmp.
    injection tmp; intros; subst y2b x2b; clear tmp H2b.
    generalize Hp Hp5 Hp5b Hp4b H6 H9;
      clear Hp Hp5 Hp5b Hp4b H6 H9.
    kcase p1 p5.
    intros; discriminate.
    intros; discriminate.
    intros p _ _ _ _ _ (_,(_,(_,HH))); case HH; rewrite opp_opp;
      auto.
    intros p1 _ _ _ p5 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (_,(_,(HH,_)));
      case HH; auto.
    intros p1 x1b y1b H1b.
    intros p5b x5b y5b H5b p6 x6 y6 H6 l2.
    intros Hp1; pattern p1 at 2; rewrite Hp1; clear Hp1.
    intros Hp5; pattern p5b at 2; rewrite Hp5; clear Hp5.
    intros Hp6 _ Hd2 Hl2 Hx6 Hy6.
    intros tmp; injection tmp; intros HH1 HH2; subst y1b x1b;
      clear tmp H1b.
    intros tmp; injection tmp; intros HH1 HH2; subst y5b x5b;
      clear tmp H5b.
    intros _ Hp4b _ _.
    generalize Hp3 Hp4 Hp4b H7 H8; clear Hp3 Hp4 Hp4b H7 H8.
    kcase p4 p3.
    intros; discriminate.
    intros; discriminate.
    intros p _ _ _ _ (_, (_, (_,HH))); case HH; rewrite opp_opp;
      auto.
    intros p3 _ _ _ p4 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (_,(_,(HH, _)));
      case HH; auto.
    intros p4b x4b y4b H4b p3b x3b y3b H3b p7 x7 y7 H7
           l3.
    intros Hp4b; pattern p4b at 2; rewrite Hp4b; clear Hp4b.
    intros Hp3b; pattern p3b at 2; rewrite Hp3b; clear Hp3b.
    intros Hp7 _ Hd3 Hl3 Hx7 Hy7.
    intros tmp; injection tmp; intros HH1 HH2; subst y3b x3b;
      clear tmp H3b.
    intros tmp; injection tmp; intros HH1 HH2; subst y4b x4b;
  clear tmp H4b.
    intros _ _ _.
    subst p6 p7; apply curve_elt_irr; clear H6 H7;
      apply Keq_minus_eq; clear H4 H5; subst.
    Time field [H1 H2 H3]; auto; repeat split; auto.
    intros VV; field_simplify_eq[H1 H2] in VV.
    case Hd3; symmetry; apply Keq_minus_eq;
      field_simplify_eq [H1 H2]; auto.
    intros VV; field_simplify_eq[H1 H2] in VV.
    case Hd2; symmetry; apply Keq_minus_eq;
      field_simplify_eq [H1 H2]; auto.
    Time field [H1 H2 H3]; auto; repeat split; auto.
    intros VV; field_simplify_eq[H1 H2] in VV.
    case Hd3; symmetry; apply Keq_minus_eq;
      field_simplify_eq [H1 H2]; auto.
    intros VV; field_simplify_eq[H1 H2] in VV.
    case Hd2; symmetry; apply Keq_minus_eq;
      field_simplify_eq [H1 H2]; auto.
  Qed.

  Theorem spec2_assoc:
    forall p1 p2 p3,
      is_generic p1 p2 ->
      is_tangent p2 p3 ->
      is_generic (add p1 p2) p3 ->
      is_generic  p1 (add p2 p3) ->
      add p1 (add p2 p3) = add (add p1 p2) p3.
    intros p1 p2; kcase p1 p2.
    intros p p3  _ _ (HH, _); case HH; auto.
    intros p3 _ _ _ p4 _ _ _ _ _ _ _ _ _ _ _ p5 (_, (_, (HH, _)));
      case HH; auto.
    intros p1 x1 y1 H1 p2 x2 y2 H2 p4 x4 y4 H4 l
           Hp Hp2 Hp4 Hp4b Hx Hl Hx4 Hy4 p3.
    generalize Hp2 Hp4b; clear Hp2 Hp4b.
    kcase p2 p3.
    intros; discriminate.
    intros p _ _ _ _ (_, (HH, _)); case HH; auto.
    intros p _ _ _ _ _ (_, (HH, _)); case HH; auto.
    intros p2 x2b y2b H2b p5 x5 y5 H5 l1.
    intros Hp2b.
    intros Hp5 Hp5b Hd Hl1 Hx5 Hy5 Hp2.
    rewrite Hp2 in Hp2b.
    injection Hp2b; intros HH HH1; subst y2b x2b; clear Hp2b.
    generalize Hp Hp5 Hp5b; clear Hp Hp5 Hp5b.
    kcase p1 p5.
    intros; discriminate.
    intros; discriminate.
    intros p _ _ _ _ _ _ _ (_,(_,(_,HH)));
      case HH; rewrite opp_opp; auto.
    intros p1 _ _ _ p5 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (_,(_,(HH,_)));
      case HH; auto.
    intros p1 x1b y1b H1b.
    intros p5b x5b y5b H5b p6 x6 y6 H6 l2.
    intros Hp1; pattern p1 at 2; rewrite Hp1; clear Hp1.
    intros Hp5; pattern p5b at 2; rewrite Hp5; clear Hp5.
    intros Hp6 _ Hd2 Hl2 Hx6 Hy6.
    intros tmp; injection tmp; intros HH1 HH2; subst y1b x1b;
      clear tmp H1b.
    intros tmp; injection tmp; intros HH1 HH2; subst y5b x5b;
      clear tmp H5b.
    intros _ Hp4b _ _.
    generalize Hp2 Hp4 Hp4b; clear Hp2 Hp4 Hp4b.
    kcase p4 p2.
    intros; discriminate.
    intros; discriminate.
    intros p _ _ _ (_, (_, (_,HH))); case HH; rewrite opp_opp;
      auto.
    intros p3 _ _ _ p4 _ _ _ _ _ _ _ _ _ _ _ _ _ _ (_,(_,(HH, _)));
      case HH; auto.
    intros p4b x4b y4b H4b p3b x3b y3b H3b p7 x7 y7 H7
           l3.
    intros Hp4b; pattern p4b at 2; rewrite Hp4b; clear Hp4b.
    intros Hp3b; pattern p3b at 2; rewrite Hp3b; clear Hp3b.
    intros Hp7 _ Hd3 Hl3 Hx7 Hy7.
    intros tmp; injection tmp; intros HH1 HH2; subst y3b x3b;
      clear tmp H3b.
    intros tmp; injection tmp; intros HH1 HH2; subst y4b x4b;
      clear tmp H4b.
    intros _ _ _.
    subst p6 p7; apply curve_elt_irr; clear H6 H7 H2b;
      apply Keq_minus_eq; clear H4 H5; subst.
    Time field [H1 H2]; auto; repeat split; auto.
    intros VV; field_simplify_eq[H1 H2] in VV.
    case Hd3; symmetry; apply Keq_minus_eq;
      field_simplify_eq [H1 H2]; auto.
    intros VV; field_simplify_eq[H1 H2] in VV.
    case Hd2; symmetry; apply Keq_minus_eq;
      field_simplify_eq [H1 H2]; auto.
    Time field [H1 H2]; auto; repeat split; auto.
    intros VV; field_simplify_eq[H1 H2] in VV.
    case Hd3; symmetry; apply Keq_minus_eq;
      field_simplify_eq [H1 H2]; auto.
    intros VV; field_simplify_eq[H1 H2] in VV.
    case Hd2; symmetry; apply Keq_minus_eq;
      field_simplify_eq [H1 H2]; auto.
    intros p3 x3 y3 H3 p5 x5 y5 H5 p6 x6 y6 H6 l1
           Hp3 Hp5 _ _ Hd  _ _ _ _ _ _.
    rewrite Hp3; rewrite Hp5; intros (_, (HH,_));
      case Hd; injection HH; auto.
    Time Qed.


  Theorem spec3_assoc:
    forall p1 p2 p3,
      is_generic p1 p2 ->
      is_tangent p2 p3 ->
      is_generic (add p1 p2) p3 ->
      is_tangent  p1 (add p2 p3) ->
      add p1 (add p2 p3) = add (add p1 p2) p3.
    intros p1 p2.
    kcase p1 p2.
    intros p p3  _ _ (HH, _); case HH; auto.
    intros p3 _ _ _ p4 _ _ _ _ _ _ _ _ _ _ _ p5 (_, (_, (HH, _)));
      case HH; auto.
    intros p1 x1 y1 H1 p2 x2 y2 H2 p4 x4 y4 H4 l
           Hp Hp2 Hp4 Hp4b Hx Hl Hx4 Hy4 p3.
    generalize Hp2 Hp4b; clear Hp2 Hp4b.
    kcase p2 p3.
    intros; discriminate.
    intros p _ _ _ _ (_, (HH, _)); case HH; auto.
    intros p _ _ _ (_ ,(_ , HH)); case HH; rewrite opp_opp; auto.
    intros p2 x2b y2b H2b p5 x5 y5 H5 l1.
    intros Hp2b.
    intros Hp5 Hp5b Hd Hl1 Hx5 Hy5 Hp2.
    rewrite Hp2 in Hp2b.
    injection Hp2b; intros HH HH1; subst y2b x2b; clear Hp2b H2b.
    generalize Hp Hp5 Hp5b; clear Hp Hp5 Hp5b.
    kcase p1 p5.
    intros; discriminate.
    intros; discriminate.
    intros p _ _ _ _ _ _ _ (_, (_,HH)); case HH; rewrite opp_opp;
      auto.
    intros p1 x1b y1b H1b.
    intros p6 x6 y6 H6 l2.
    intros Hp1; pattern p1 at 3 4; rewrite Hp1; clear Hp1.
    intros Hp6 _ Hd2 Hl2 Hx6 Hy6.
    intros tmp; injection tmp; intros HH1 HH2; subst y1b x1b;
      clear tmp.
    intros tmp; injection tmp; intros HH1 HH2.
    subst y5 x5; clear tmp H5.
    rename HH1 into Hy1; rename HH2 into Hx1.
    generalize Hp2 Hp4; clear Hp2 Hp4.
    kcase p4 p2.
    intros; discriminate.
    intros; discriminate.
    intros p _ _ _ _ _ _ (_, (_, (_, HH))); case HH; rewrite opp_opp;
      auto.
    intros p3 _ _ _ p4 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
           (_,(_,(HH, _))); case HH; auto.
    intros p4b x4b y4b H4b p2b x2b y2b H2b.
    intros p7 x7 y7 H7 l3.
    intros Hp4b; pattern p4b at 2; rewrite Hp4b; clear Hp4b.
    intros Hp2b; pattern p2b at 2; rewrite Hp2b; clear Hp2b.
    intros Hp7 _ Hd1 Hl3 Hx7 Hy7.
    intros tmp; injection tmp; intros HH1 HH2; subst y2b x2b;
      clear tmp H2b.
    intros tmp; injection tmp; intros HH1 HH2; subst y4b x4b;
      clear tmp H4b.
    intros _ _ _ _ _ _.
    subst p6 p7; apply curve_elt_irr; clear H6 H7;
      apply Keq_minus_eq; clear H4 H1b; subst.
    Time field [H2]; auto; repeat split; auto;
      intros HH; field_simplify_eq in HH; auto.
    case Hx; symmetry; apply Keq_minus_eq.
    field_simplify_eq; auto.
    case Hd1; symmetry; apply Keq_minus_eq;
      field_simplify_eq; repeat split; auto.
    intros HH1; ring_simplify in HH1; auto.
    case Hx; symmetry; apply Keq_minus_eq.
    field_simplify_eq; auto.
    case Hd2; apply Keq_minus_eq;
      field_simplify_eq; auto.
    Time field [H2]; auto; repeat split; auto;
      intros HH; field_simplify_eq in HH; auto.
    case Hx; symmetry; apply Keq_minus_eq.
    field_simplify_eq; auto.
    case Hd1; symmetry; apply Keq_minus_eq;
      field_simplify_eq; repeat split; auto.
    intros HH1; ring_simplify in HH1; auto.
    case Hx; symmetry; apply Keq_minus_eq.
    field_simplify_eq; auto.
    case Hd2; apply Keq_minus_eq;
      field_simplify_eq; auto.
    intros p1b x1b y1b H1b.
    intros p5b x5b y5b H5b.
    intros p3 x3 y3 H3 l2.
    intros Hp1b; pattern p1b at 2 5; rewrite Hp1b; clear Hp1b.
    intros Hp5b; pattern p5b at 2 4; rewrite Hp5b; clear Hp5b.
    intros Hp3 _; rewrite Hp3; clear Hp3.
    intros Hx1 _ _ _.
    intros tmp; injection tmp; intros HH1 HH2; subst y1b x1b;
      clear tmp.
    intros tmp; injection tmp; intros HH1 HH2; subst y5b x5b;
      clear tmp.
    intros _ _ _ _ _ (_,(HH, _)); case Hx1; injection HH;
      auto.
    intros p2b x2b y2b H2b.
    intros p3 x3 y3 H3.
    intros p5 x5 y5 H5 l2.
    intros Hp2b; pattern p2b at 2 5; rewrite Hp2b; clear Hp2b.
    intros Hp3; rewrite Hp3; clear Hp3.
    intros _ _ Hx1 _ _ _.
    intros tmp; injection tmp; intros HH1 HH2; subst y2b x2b;
      clear tmp.
    intros _ _ (_,(HH, _)); case Hx1; injection HH; auto.
    Time Qed.

(***********************************************************)
(*                                                         *)
(*      inf_elt is the zero                                *)
(*                                                         *)
(***********************************************************)

  Theorem add_0_l: forall p, add Inf_elt p = p.
  Proof.
    auto.
  Qed.

  Theorem add_0_r: forall p, add p Inf_elt = p.
  Proof.
    intros p; case p; auto.
  Qed.


(***********************************************************)
(*                                                         *)
(*      opp is the opposite                                *)
(*                                                         *)
(***********************************************************)

  Theorem add_opp: forall p, add p (opp p) = Inf_elt.
  Proof.
    intros p; case p; unfold add; simpl; auto.
    intros x1 y1 H1.
    repeat ksplit.
    case KD0; ring.
  Qed.


  Theorem add_comm: forall p1 p2, add p1 p2 = add p2 p1.
  Proof.
    intros p1 p2; case p1.
    rewrite add_0_r; rewrite add_0_l; auto.
    intros x1 y1 H1; case p2.
    rewrite add_0_r; rewrite add_0_l; auto.
    intros x2 y2 H2; simpl; repeat ksplit.
    case KD2; ring [KD0].
    case KD0; ring [KD2].
    assert (H3 := add_zero _ _ _ _ KD H1 H2 KD0).
    apply curve_elt_irr; subst x2 y2; auto.
    case KD; auto.
    case KD; auto.
    apply curve_elt_irr; field; auto.
  Qed.

  Theorem aux1: forall x1 y1 x2 y2,
      y1 ^ 2 = x1 ^ 3 + A * x1 + B -> y2 ^ 2 = x2 ^ 3 + A * x2 + B ->
      x1 <> x2 ->  y2 = 0 -> ((y2 - y1) / (x2 - x1))^2 - x1 - x2 = x2 -> False.
  Proof.
    intros x1 y1 x2 y2 H H1 H2 H3 H4.
    subst y2.
    assert (Hu : x2 ^ 3 = -(A * x2 + B)).
    apply trans_equal with
        ((x2 ^ 3 + A * x2 + B) - (A * x2 + B)); try ring.
    rewrite <- H1; ring.
    assert (H5:= (Keq_minus_eq_inv _ _ H4)); clear H4.
    field_simplify_eq [H Hu] in H5; auto.
    generalize (Kmult_eq_compat_l x2 _ _ H5); rename H5 into H4.
    replace (x2 * 0) with 0; try ring; intros H5.
    field_simplify_eq [Hu] in H5.
    generalize H5; clear H5.
    match goal with |- (?X = _ -> _) => replace X with ((x2 - x1) * (2* A *x2 + 3* B));
                                       try ring end.
    intros tmp; case (Kmult_integral _ _ tmp); clear tmp; intros HH2.
    case H2; apply sym_equal; apply Keq_minus_eq; auto.
    generalize (Kmult_eq_compat_l ((2 * A )^3) _  _ (sym_equal H1)).
    replace ((2 * A)^3 * 0 ^ 2) with 0; try (ring).
    intros H5; ring_simplify in H5; auto.
    match type of H5 with  (?X + ?Y + _ = _) =>
                           let x := (constr:(2 * A * x2)) in
                           ((replace Y with (x ^ 3) in H5; try ring);
                            (replace X with (4 * A^3 * x) in H5; try ring);
                            replace x with (-(3) * B) in H5) end.
    2: apply sym_equal; apply Keq_minus_eq; apply trans_equal with (2:= HH2); ring.
    ring_simplify in H5; auto.
    match type of Eth.(NonSingular) with ?X <> 0 =>
                                         case (@Kmult_integral (-B) X); try intros HH3;
                                           try (case NonSingular; auto; fail) end.
    rewrite <- H5; ring.
    assert (HH3b : B = 0).
    replace B with (-(-B)); try ring; rewrite HH3; ring.
    case (@Kmult_integral 2 (A * x2)); try intros HH4; auto.
    apply trans_equal with (2:= HH2).
    rewrite HH3b; ring.
    case (Kmult_integral _ _  HH4); try intros HH5; auto.
    case Eth.(NonSingular); rewrite HH3b; rewrite HH5; simpl; ring.
    ring_simplify [HH5] in H4; auto.
    case (@Kmult_integral A  x1); try intros HH6; auto.
    apply trans_equal with (2 := H4); rewrite HH3b; ring.
    case Eth.(NonSingular); rewrite HH3b; rewrite HH6; ring.
    case H2; rewrite HH6; auto.
  Qed.

  
  Theorem uniq_zero: forall p1 p2, add p1 p2 = p2 -> p1 = Inf_elt.
  Proof.
    intros p1 p2; kcase p1 p2.
    intros p; case p; simpl; auto; intros; discriminate.
    intros.
    subst p1 p2; injection H8; intros H9 H10.
    generalize (Keq_minus_eq_inv _ _ H7); clear H7; intros H7.
    ring_simplify [H9 H10] in H7.
    case (Kmult_integral _ _ H7); auto; intros H11.
    case Kdiff_2_0; auto.
    case H4; auto.
    intros p1 x1 y1 H1 p2 x2 y2 H2 p3 x3 y3 H3 l Hp1 Hp2 Hp3 Hp3b Hd Hl Hx3 Hy3 Hp.
    apply False_ind.
    subst p2; subst p3; injection Hp; clear p1 Hp1 Hp Hp3b; intros.
    case (@aux1 x1 y1 x2 y2); auto.
    generalize (Keq_minus_eq_inv _ _ Hy3); rewrite Hl;
      rewrite H; rewrite H0; clear Hy3; intros Hy3.
    field_simplify_eq in Hy3; auto.
    assert (HH: 2 * y2 * (x2 - x1) = 0).
    rewrite Hy3; ring.
    clear Hy3; rename HH into Hy3.
    case (Kmult_integral _ _ Hy3); auto; clear Hy3; intros Hy3.
    case (Kmult_integral _ _ Hy3); auto; clear Hy3; intros Hy3.
    case Kdiff_2_0; auto.
    case Hd.
    symmetry; apply Keq_minus_eq; auto.
    rewrite <- Hl; rewrite <- Hx3; auto.
  Qed.


  Theorem uniq_opp: forall p1 p2, add p1 p2 = Inf_elt -> p2 = opp p1.
  Proof.
    intros p1 p2; kcase p1 p2.
    intros p H; rewrite H; auto.
    intros; subst; discriminate.
    intros; subst; discriminate.
  Qed.


  Theorem opp_0: opp (Inf_elt) = Inf_elt.
  Proof.
    auto.
  Qed.

  Theorem opp_add: forall p1 p2, opp (add p1 p2) = add (opp p1) (opp p2).
  Proof.
    intros p1 p2; case p1.
    rewrite opp_0; repeat rewrite add_0_l; auto.
    intros x1 y1 H1; case p2.
    rewrite opp_0; repeat rewrite add_0_r; auto.
    intros x2 y2 H2; simpl; repeat ksplit; simpl.
    case KD1; ring [KD0].
    case KD0; apply trans_equal with (-(-y1));
      try ring; rewrite KD1; ring.
    assert (HH:= add_zero_diff _ _ _ _ KD H1 H2 KD0).
    apply curve_elt_irr; try field; repeat split; auto;
      intros HH1; case HH; symmetry; apply Keq_minus_eq;
        ring_simplify; auto.
    apply curve_elt_irr; try field; auto.
  Qed.

  Theorem compat_add_opp: forall p1 p2,
      add p1 p2 = add p1 (opp p2) ->  ~ p1 = opp p1 -> p2 = opp p2.
  Proof.
    intros p1 p2; kcase p1 p2.
    intros p H H1; case H1.
    apply uniq_opp.
    pattern p at 2; rewrite <- opp_opp; auto.
    intros p1 x1 y1 H1 p2 x2 y2 H2 l Hp1 Hp2 Hp2b Hy Hl Hx2 Hy2 He1 He2.
    apply uniq_opp.
    rewrite <- Hp2b; rewrite He1; rewrite add_opp; auto.
    intros p1 x1 y1 H1 p2 x2 y2 H2 p3 x3 y3 H3 l Hp1 Hp2 Hp3 Hp3b Hx12
           Hl Hx3 Hy3 Hp3bb Hd.
    generalize Hp3bb; clear Hp3bb.
    subst p1 p2 p3; simpl; repeat ksplit.
    intros tmp; injection tmp; clear tmp.
    rewrite Hx3; rewrite Hl; intros _ HH.
    assert (HH1:= (Keq_minus_eq_inv _ _ HH)).
    field_simplify_eq in HH1; auto.
    case (Kmult_integral _ _ HH1); try intros HH2; auto.
    case (Kmult_integral _ _ HH2); try intros HH3; auto.
    assert (HH8: 2 * 2 = 0).
    replace (2*2) with (-(-(2 * 2))); try ring
    ; try rewrite HH3; ring.
    case (Kmult_integral _ _ HH8); try intro H9;
      case Kdiff_2_0; auto.
    intros; apply curve_elt_irr; try rewrite HH3;
      intros; ring.
    case Hd; simpl; apply curve_elt_irr; ring[HH2].
  Qed.

  Theorem compat_add_triple: forall p,
      p <> opp p -> add p p <> opp p -> add (add p p) (opp p) = p.
  Proof.
    intro p.
    set (p1 := (add p p)).
    set (p2 := opp p).
    cut (p1 = add p p); auto.
    cut (p2 = opp p); auto.
    kcase p1 p2.
    intros p1 Hp1; subst p1.
    intros; symmetry; apply uniq_opp; auto.
    intros p1 H1 _ H2 _; case H2.
    rewrite <- (opp_opp p); rewrite <- H1; auto.
    intros p1 H1 H2 H3 H4.
    assert (H5: p = p1).
    rewrite <- (opp_opp p); rewrite <- H1; rewrite opp_opp; auto.
    subst p1.
    symmetry; apply uniq_zero with p; auto.
    intros; case H11; auto.
    case p; clear p.
    intros; subst p2; discriminate.
    intros x y H.
    set (p := (Curve_elt x y H)).
    intros p1 x1 y1 H1 p2 x2 y2 H2 p3 x3 y3 H3 l Hp1 Hp2 Hp3 Hp3b
           Hx12 Hl Hx3 Hy3 He1 He2 He3 He4.
    generalize He1; unfold p; rewrite Hp2;
      simpl; intros tmp; injection tmp; clear tmp.
    intros; subst x2 y2.
    rewrite Hp3.
    case (curve_elt_opp _ _ _ _ H3 H); auto.
    rewrite Hx3; rewrite Hl.
    generalize He2; unfold p; simpl; repeat ksplit.
    rewrite Hp1; intros; discriminate.
    rewrite Hp1; intros tmp; injection tmp; intros; subst x1 y1.
    set (l1 := (3 * x * x + A) / (2 * y)).
    field; repeat split; auto.
    rewrite <- Hp3; fold p; intros HH.
    absurd (p1 = Inf_elt).
    rewrite Hp1; intros; discriminate.
    apply uniq_zero with p2.
    rewrite <- Hp3b; rewrite He1; auto.
  Qed.

  Theorem add_opp_double_opp: forall p1 p2,
      add p1 p2 = opp p1 -> p2 = add (opp p1) (opp p1).
    intros p1 p2; intros H1.
    case (ceqb p1 (opp p1)); intros H2.
    pattern (opp p1) at 1; rewrite <- H2.
    rewrite add_opp; apply uniq_zero with p1.
    rewrite add_comm; rewrite H1; auto.
    rewrite <-opp_add.
    assert (H: (p2 = add (opp p1) (opp p1)) \/ (p2 = opp (add (opp p1) (opp p1)))).
    rewrite <- opp_add; rewrite opp_opp.
    generalize H1 H2; clear H1 H2; kcase p1 p2.
    intros p H2 H1; case H1; auto.
    intros p H2 H1; rewrite opp_add; rewrite <- H2; auto.
    intros p1 x1 y1 H1 p2 x2 y2 H2 l Hp1 Hp2 Hp2b Hy1 _ _ _ He1 He2.
    rewrite <- Hp2b; rewrite He1; rewrite opp_opp; auto.
    intros p1 x1 y1 H1 p2 x2 y2 H2 p3 x3 y3 H3 l Hp1 Hp2 Hp3 Hp3b
           Hx12 Hl Hx3 Hy3 He1 He2.
    assert (Hy1: y1 <> 0).
    intros HH; case He2; rewrite Hp1; simpl; apply curve_elt_irr;
      ring[HH].
    assert (Hy2: -y1 <> 0).
    intros Hy2; case Hy1; apply trans_equal with (-(-y1));
      try ring; rewrite Hy2; ring.
    generalize He1; clear He1.
    rewrite Hp1; rewrite Hp2; rewrite Hp3; simpl; repeat ksplit.
    case Hy1; apply Keq_opp_is_zero; auto.
    intros tmp; injection tmp; intros; subst x3 y3; clear tmp Hp1 Hp2 Hp3.
    assert (tmp: forall P Q, P \/ Q -> Q \/ P).
    intuition.
    apply tmp; apply curve_elt_opp; clear tmp.
    rewrite Hl in H0.
    assert (HH1:= (Keq_minus_eq_inv _ _ H0)); clear H0.
    field_simplify_eq [H1 H2] in HH1; auto.
    match type of HH1 with ?XX = 0 =>
                           assert (HH2: 2 * y2 * y1 = XX + 2 * y2 * y1);
                             try (rewrite HH1; ring); clear HH1; rename HH2 into HH1;
                               ring_simplify in HH1
    end.
    match type of HH1 with _ = ?X =>
                           assert (HH2: 4 * y2^2 * y1^2 = X * X);
                             [rewrite <- HH1;ring | clear HH1; rename HH2 into HH1]
    end.
    assert (HH2:= Keq_minus_eq_inv _ _ HH1); clear HH1;
      rename HH2 into HH1.
    ring_simplify [H1 H2] in HH1.
    assert (HH2:
              (x2 - (((3 * x1* x1  + A)/(2*-y1))^2 -2 * x1)) * (x2 -x1)^2 = 0).
    field_simplify_eq [H1]; auto.
    apply trans_equal with (2 := HH1); ring.
    clear HH1; rename HH2 into HH1.
    case (Kmult_integral _ _ HH1); intros HH2.
    apply Keq_minus_eq; auto.
    rewrite <- HH2; field; auto; split; auto.
    simpl in HH2; auto.
    case (Kmult_integral _ _ HH2); intros; case Hx12;
      symmetry; apply Keq_minus_eq; auto.
    case H; auto; intros H3.
    rewrite <- opp_add in H3; auto.
    rewrite opp_add in H3; rewrite opp_opp in H3.
    case (ceqb (add p1 p1) (opp p1)); intros H4.
    rewrite H3; rewrite H4.
    rewrite <- H1; rewrite H3; rewrite H4.
    rewrite add_opp; auto.
    rewrite <- H3.
    apply compat_add_opp with p1; auto.
    apply trans_equal with (opp(add (add p1 p1) (opp p1))).
    rewrite compat_add_triple; auto.
    rewrite <- H3; rewrite opp_add; rewrite opp_opp.
    apply add_comm.
  Qed.


  Theorem cancel:
    forall p1 p2 p3, add p1 p2 = add p1 p3 -> p2 = p3.
    intros p1 p2; pattern p1, p2, (add p1 p2);
      apply add_casew; clear p1 p2.
    intros; subst; auto.
    intros p p1 H; symmetry; apply uniq_zero with p.
    rewrite add_comm; auto.
    intros; symmetry; apply uniq_opp; auto.
    intros p1 x1 y1 H1 p2 x2 y2 H2 p4 x4 y4 H4 l
           Hp1 Hp2 Hp4 Hp4b Hd1 Hl1 Hx4 Hy4 p3.
    generalize Hp1 Hp4b Hd1; clear Hp1 Hp4b Hd1.
    rewrite Hp4; clear Hp4.
    pattern p1, p3, (add p1 p3);
      apply add_casew; clear p1 p3.
    intros; discriminate.
    intros p He1 He2 _ He3.
    apply uniq_zero with p.
    rewrite add_comm; rewrite <- He2; auto.
    intros; discriminate.
    intros p1 x1b y1b H1b p3 x3 y3 H3 p5 x5 y5 H5 l'.
    intros Hp1b Hp3 Hp5 Hp5b Hd1 Hl' Hx5 Hy5 He1 He2 Hd2 He3.
    rewrite He3 in He2; rewrite Hp5b in He2.
    rewrite He1 in Hp1b; injection Hp1b; clear Hp1b.
    intros; subst x1b y1b.
    generalize He3; rewrite Hp5.
    intros tmp; injection tmp; intros HH HH1; clear tmp.
    rewrite Hp5b in He3.
    generalize Hy5; clear Hy5.
    rewrite <- HH; rewrite <- HH1; rewrite Hy4; clear HH Hy4.
    intros HH2; generalize (Keq_minus_eq_inv _ _ HH2); clear HH2.
    intros HH2; ring_simplify in HH2.
    case (@Kmult_integral (l' - l) (x4 - x1));
      try (clear HH2; intros HH2).
    rewrite <- HH2; ring.
    generalize HH1; subst x4 x5; clear HH1.
    rewrite (Keq_minus_eq _ _ HH2).
    intros HH; generalize (Keq_minus_eq_inv _ _ HH);
      clear HH; intros HH; ring_simplify in HH.
    case (curve_elt_opp _ _ _ _ H2 H3).
    symmetry; apply Keq_minus_eq; rewrite <- HH; ring.
    subst p2 p3; auto.
    rewrite <- Hp2; rewrite <- Hp3; intros HH1.
    case (ceqb p1 (opp p1)); intros HH3.
    case Hl1; clear Hl1.
    intros (Hx1, (Hy1, _)).
    case Hd1; rewrite <- HH1; rewrite He1; rewrite Hp2;
      apply curve_elt_irr; auto; clear Hd1.
    intros (Hdx1, Hl2); rewrite Hl2 in HH2; clear Hl2.
    case Hl'; clear Hl'.
    intros (Hx1, (Hy1, _)).
    case Hd2; rewrite HH1; rewrite opp_opp.
    rewrite He1; rewrite Hp3;
      apply curve_elt_irr; auto; clear Hd1.
    intros (Hdx3, Hl2); rewrite Hl2 in HH2; clear Hl2.
    generalize HH1; rewrite Hp2; rewrite Hp3; simpl; clear HH1.
    intros tmp; injection tmp.
    intros; apply curve_elt_irr; auto.
    subst x3 y2.
    field_simplify_eq in HH2; auto.
    case (Kmult_integral _ _ HH2); try intros HHx; auto.
    case Kdiff_2_0; auto.
    ring [HHx].
    rewrite <- (opp_opp p3); rewrite <- HH1.
    apply compat_add_opp with p1; auto.
    pattern p2 at 2; rewrite HH1; rewrite opp_opp; auto.
    case (curve_elt_opp _ _ _ _ H4 H1);
      try apply Keq_minus_eq; auto; rewrite He3; rewrite <- He1;
        intros HH3.
    apply trans_equal with Inf_elt; [idtac | symmetry];
      apply uniq_zero with p1; rewrite add_comm; auto.
    rewrite <- He2; auto.
    apply trans_equal with (add (opp p1) (opp p1));
      [idtac | symmetry]; apply add_opp_double_opp; auto.
    rewrite <- He2; auto.
  Qed.

  Theorem add_minus_id: forall p1 p2, (add (add p1 p2) (opp p2)) = p1.
    intros p1 p2.
    case (ceqb (add p1 p2) (opp p2)).
    intros Hp12; rewrite Hp12; symmetry;
      apply add_opp_double_opp; rewrite add_comm; auto.
    pattern p1, p2, (add p1 p2); apply add_case; clear p1 p2.
    intros; rewrite add_opp; auto.
    intros; rewrite add_0_r; auto.
    intros; rewrite opp_opp; auto.
    intros p1 x1 y1 H1 p2 x2 y2 H2 l Hp1 Hp2 Hp3 Hd
           Hl Hx2 Hy2 Hp12.
    rewrite Hp3.
    apply compat_add_triple; auto.
    rewrite Hp1; simpl; intros tmp; case Hd;
      injection tmp; intros; apply Keq_opp_is_zero; auto.
    rewrite <- Hp3; auto.
    intros p1 x1 y1 H1 p2 x2 y2 H2 p3 x3 y3 H3 l Hp1
           Hp2 Hp3 Hp3b Hx1 Hl Hx3 Hy3.
    generalize Hp2 Hp3 Hp3b; clear Hp2 Hp3 Hp3b.
    pattern p2 at 1 2; rewrite <- (opp_opp p2).
    pattern p3, (opp p2), (add p3 (opp p2)).
    apply add_case.
    intros; discriminate.
    intros; discriminate.
    intros; symmetry; apply uniq_zero with p.
    pattern p at 1; rewrite <- (opp_opp p); auto.
    intros; case n; auto.
    intros p4 x4 y4 H4 p5 x5 y5 H5 p6 x6 y6 H6 l0.
    intros Hp4; rewrite Hp4; clear Hp4.
    intros Hp5; rewrite Hp5; clear Hp5.
    intros Hp6 _; rewrite Hp6; clear Hp6.
    intros Hx Hl0 Hx6 Hy6.
    intros tmp; injection tmp; intros HH1 HH2; clear tmp.
    assert (y5 = - y2).
    rewrite <- HH1; ring.
    subst y5 x5; clear HH1.
    intros tmp; injection tmp; intros HH1 HH2; subst y4 x4;
      clear tmp.
    intros _ _.
    subst p1; apply curve_elt_irr; clear H6 H5 H4 H3;
      subst;
      apply Keq_minus_eq; field [H1 H2]; split; auto;
        intros HH; case Hx;
          ring_simplify [H1 H2] in HH;
          symmetry; apply Keq_minus_eq; field_simplify_eq [H1 H2];
            auto.
  Qed.


  Theorem add_shift_minus: forall p1 p2 p3, add p1 p2 = p3 -> p1 = add p3 (opp p2).
    intros p1 p2 p3 H.
    apply cancel with (opp (opp p2)).
    repeat rewrite (add_comm (opp (opp p2))).
    rewrite add_minus_id; rewrite opp_opp; auto.
  Qed.

  Theorem degen_assoc:
    forall p1 p2 p3,
      (p1 = Inf_elt \/ p2 = Inf_elt \/ p3 = Inf_elt) \/
      (p1 = opp p2 \/ p2 = opp p3) \/
      (opp p1 = add p2 p3 \/ opp p3 = add p1 p2) ->
      add p1 (add p2 p3) = add (add p1 p2) p3.
    intros p1 p2 p3; intuition; subst;
      repeat (rewrite add_opp || rewrite add_0_r ||
              rewrite add_0_l); auto.
    repeat rewrite (add_comm (opp p2)).
    rewrite add_opp; rewrite (add_comm p2);
      rewrite add_minus_id; auto.
    pattern p3 at 4; rewrite <- opp_opp; rewrite add_minus_id.
    rewrite (add_comm (opp p3));
      rewrite add_opp; rewrite add_0_r; auto.
    rewrite <- H0; rewrite add_opp.
    rewrite <- (opp_opp p1); rewrite H0.
    rewrite opp_add.
    rewrite (add_comm (opp p2)); pattern p2 at 2;
      rewrite <- opp_opp; rewrite add_minus_id.
    rewrite add_comm; auto; rewrite add_opp; auto.
    pattern p3 at 1; rewrite <- opp_opp; rewrite H0.
    rewrite (add_comm p2).
    pattern p2 at 2; rewrite <- opp_opp.
    rewrite opp_add; rewrite add_minus_id; auto.
    rewrite <- H0; rewrite (add_comm (opp p3)).
    repeat rewrite add_opp; auto.
  Qed.

  Theorem spec4_assoc:
    forall p1 p2,
      add p1 (add p2 p2) = add (add p1 p2) p2.
    intros p1 p2.
    case (ceqb p1 Inf_elt); intros H1.
    apply degen_assoc; auto.
    case (ceqb p2 Inf_elt); intros H2.
    apply degen_assoc; auto.
    case (ceqb p2 (opp p2)); intros H3.
    apply degen_assoc; auto.
    case (ceqb p1 (opp p2)); intros H4.
    apply degen_assoc; auto.
    case (ceqb (opp p1) (add p2 p2)); intros H5.
    apply degen_assoc; auto.
    case (ceqb (opp p2) (add p1 p2)); intros H6.
    apply degen_assoc; auto.
    case (ceqb p1 (add p2 p2)); intros H7.
    subst p1; apply spec3_assoc.
    repeat split; auto.
    intros H7; case H2; apply uniq_zero with p2; auto.
    split; auto.
    repeat split; auto.
    intros H7; case H4; apply uniq_opp; rewrite add_comm; auto.
    intros H7; case H1; apply uniq_zero with p2; auto.
    split; auto.
    case (ceqb p2 (add p1 p2)); intros H8.
    pattern p1 at 1; rewrite (uniq_zero _ _ (sym_equal H8)).
    rewrite <- H8; auto.
    case (ceqb p1 p2); intros H9.
    subst p1; apply add_comm.
    apply spec2_assoc; repeat split; auto.
    repeat split; auto.
    repeat split; auto.
    intros H10;  case H4; apply uniq_opp; rewrite add_comm; auto.
    intros H10;  case H3; apply uniq_opp; auto.
    intros H10; case H5; rewrite H10; rewrite opp_opp; auto.
  Qed.

  Theorem add_assoc: forall p1 p2 p3, add p1 (add p2 p3) = add (add p1 p2) p3.
    intros p1 p2 p3.
    case (ceqb p1 Inf_elt); intros H1.
    apply degen_assoc; auto.
    case (ceqb p2 Inf_elt); intros H2.
    apply degen_assoc; auto.
    case (ceqb p3 Inf_elt); intros H3.
    apply degen_assoc; auto.
    case (ceqb p1 p2); intros H4.
    subst p1.
    rewrite add_comm; rewrite (add_comm p2).
    rewrite <- spec4_assoc; rewrite add_comm; auto.
    case (ceqb p1 (opp p2)); intros H5.
    apply degen_assoc; auto.
    case (ceqb p2 p3); intros H6.
    subst p2.
    apply spec4_assoc.
    case (ceqb p2 (opp p3)); intros H7.
    apply degen_assoc; auto.
    case (ceqb (opp p1) (add p2 p3)); intros H8.
    apply degen_assoc; auto.
    case (ceqb (opp p3) (add p1 p2)); intros H9.
    apply degen_assoc; auto.
    case (ceqb p1 (add p2 p3)); intros H10.
    rewrite H10.
    apply cancel with (opp p3).
    rewrite spec4_assoc.
    repeat rewrite (add_comm (opp p3)).
    repeat rewrite add_minus_id; rewrite add_comm; auto.
    case (ceqb p3 (add p1 p2)); intros H11.
    rewrite H11.
    apply cancel with (opp p1).
    rewrite spec4_assoc.
    repeat rewrite (add_comm (opp p1)).
    repeat rewrite (add_comm p1).
    repeat rewrite add_minus_id; rewrite add_comm; auto.
    apply spec1_assoc.
    split; auto.
    split; auto.
    split; auto.
    intros HH; case H5; apply uniq_opp; auto.
    rewrite add_comm; auto.
    repeat split; auto.
    intros HH; case H7; apply uniq_opp; auto.
    rewrite add_comm; auto.
    intros HH; case H8; rewrite HH; rewrite opp_opp; auto.
  Qed.
  




  (* multiplying natural number to point on Curve *)
  Fixpoint point_mult (n : nat) (e : elt) : elt :=
    match n with
    | O => Inf_elt
    | S n' => add e (point_mult n' e)
    end.


  (* (k+j)*H = k*H + j*H *)
  Lemma point_mult_distribute : forall k j e,
      point_mult (k + j) e = add (point_mult k e) (point_mult j e).
  Proof. 
    induction k; simpl; intros; try auto.
    specialize (IHk j e). rewrite IHk.
    pose proof (add_assoc e (point_mult k e) (point_mult j e)).
    rewrite H. auto.
  Qed.


  (* v1 + v2 = v3  =>  v1*H + v2*H = v3*H *)
  Lemma addition_verification :
    forall (v1 v2 v3 : nat) (e : elt),
      Nat.add v1 v2 = v3 -> add (point_mult v1 e) (point_mult v2 e) = point_mult v3 e. 
  Proof.
    intros. pose proof (point_mult_distribute v1 v2 e) as H1.
    rewrite <- H1.  rewrite <- H.
    reflexivity.
  Qed.

  
  
  
    
  