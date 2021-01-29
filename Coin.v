Require Import Coq.ZArith.ZArith.
Require Import Lia. 
Open Scope Z_scope.

Lemma coin_3_5 : forall n : Z, n >= 8 -> exists (x y : Z), 3 * x + 5 * y = n.
Proof. 
  destruct n; try lia.
  induction p; intros.
  repeat rewrite Pos2Z.inj_xI in *.
  assert (Ht2 : Z.pos p = 4 \/ Z.pos p = 5 \/
                Z.pos p = 6 \/ Z.pos p = 7 \/
                Z.pos p >= 8) by lia.
  destruct Ht2 as [Ht2 | [Ht2 | [Ht2 | [Ht2 | Ht2]]]].
  rewrite Ht2. exists (-2), 3. lia. 
  rewrite Ht2. exists (-3), 4. lia.
  rewrite Ht2. exists (-4), 5. lia.
  rewrite Ht2. exists (-5), 6. lia.
  apply IHp in Ht2.
  destruct Ht2 as [x [y Ht]].
  exists (2 * x - 3), (2 * y + 2). lia.


  rewrite Pos2Z.pos_xO in *.
  assert (Ht2 : Z.pos p = 4 \/ Z.pos p = 5 \/
                Z.pos p = 6 \/ Z.pos p = 7 \/
                Z.pos p >= 8) by lia.
  destruct Ht2 as [Ht2 | [Ht2 | [Ht2 | [Ht2 | Ht2]]]].
  rewrite Ht2. exists 1, 1. lia. 
  rewrite Ht2. exists 0, 2. lia.
  rewrite Ht2. exists 4, 0. lia.
  rewrite Ht2. exists 3, 1. lia. 
  apply IHp in Ht2.
  destruct Ht2 as [x [y Ht]].
  exists (2 * x), (2 * y). lia.

  (* impossible case *)
  lia.
Qed.

