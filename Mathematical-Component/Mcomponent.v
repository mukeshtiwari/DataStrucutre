From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* 
Example Gauss n :
  \sum_ (0 <= i < n .+1) i = (n * (n .+1)) %/ 2.
Proof. *)

Definition repeat_twice (g : nat -> nat) : nat -> nat :=
  fun x => g (g x).

Fixpoint  repeat_ntimes (n : nat) (g : nat -> nat) : nat -> nat :=
  match n with
  | 0 => g
  | p .+1 => fun x => g (repeat_ntimes p g x)
  end.

Eval compute in repeat_twice (fun x => x + 3) 3.
Eval compute in repeat_ntimes 1 (fun x => x + 3) 3.

Lemma repeat_ntimes_twice_connect :
  forall (x : nat) (g : nat -> nat), repeat_twice g x = repeat_ntimes 1 g x.
Proof.
  unfold repeat_twice, repeat_ntimes.
  auto.
Qed.

