Require Import Coq.ZArith.ZArith.
Require Import Lia. 
Open Scope Z_scope.

Lemma coin_3_5 : forall n : Z, n >= 8 -> exists (x y : Z), 3 * x + 5 * y = n.
Proof.
  destruct n; try lia.
  induction p; intros.
  repeat rewrite Pos2Z.inj_xI in *.
  assert (Ht2 : Z.pos p = 4 \/ Z.pos p = 5 \/
                Z.pos p = 6 \/ Z.pos p = 7 \/ Z.pos p >= 8) by lia.
  ring_simplify (2 * 1 + 1).
  ring_simplify (2 * 2 + 1).
  destruct Ht2.  rewrite H0. exists (-2), 3. ring_simplify. reflexivity.
  destruct H0. rewrite H0.  ring_simplify (2 * 5 + 1).
  exists (-3), 4. lia.
  destruct H0.  rewrite H0. ring_simplify (2 * 6 + 1).
  exists (-4), 5. lia.
  destruct H0.  rewrite H0. ring_simplify (2 * 7 + 1).
  exists (-5), 6. lia.
  apply IHp in H0. destruct H0 as [x [y Ht]].
  ring_simplify in Ht. rewrite <- Ht.
  ring_simplify  (2 * (3 * x + 5 * y) + 1).
  exists (2 * x - 3), (2 * y + 2). lia.


  rewrite Pos2Z.pos_xO in *.
  assert (Ht2 : Z.pos p = 4 \/ Z.pos p = 5 \/ Z.pos p = 6 \/ Z.pos p = 7 \/ Z.pos p >= 8) by lia.
  destruct Ht2.  rewrite H0.  exists 1, 1. lia. 
  destruct H0. rewrite H0. exists 0, 2. lia.
  destruct H0.  rewrite H0. exists 4, 0. lia.
  destruct H0.  rewrite H0. exists 3, 1. lia. 
  apply IHp in H0. destruct H0 as [x [y Ht]].
  rewrite <- Ht.
  ring_simplify  (2 * (3 * x + 5 * y)).
  exists (2 * x), (2 * y). lia.

  (* impossible case *)
  lia.
Qed.

