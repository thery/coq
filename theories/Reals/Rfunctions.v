(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(*i Some properties about pow and sum have been made with John Harrison i*)
(*i Some Lemmas (about pow and powerRZ) have been done by Laurent Thery i*)

(********************************************************)
(**          Definition of the sum functions            *)
(*                                                      *)
(********************************************************)
Require Export ArithRing.

Require Import Rbase.
Require Export Rpow_def.
Require Export R_Ifp.
Require Export Rbasic_fun.
Require Export R_sqr.
Require Export SplitAbsolu.
Require Export SplitRmult.
Require Export ArithProp.
Require Import Omega.
Require Import Zpower.
Local Open Scope nat_scope.
Local Open Scope R_scope.

(*******************************)
(** * Lemmas about factorial   *)
(*******************************)
(*********)
Lemma INR_fact_neq_0 n : INR (fact n) <> 0.
Proof.
  now intro; apply (not_O_INR (fact n) (fact_neq_0 n)).
Qed.

(*********)
Lemma fact_simpl n : fact (S n) = (S n * fact n)%nat.
Proof.
  reflexivity.
Qed.

(*********)
Lemma simpl_fact n : / INR (fact (S n)) * / / INR (fact n) = / INR (S n).
Proof.
  rewrite fact_simpl, mult_INR; field; split.
  - apply not_O_INR; auto.
  - apply INR_fact_neq_0.
Qed.

(*******************************)
(** *       Power              *)
(*******************************)
(*********)

Lemma pow_O x : x ^ 0 = 1.
Proof.
  ring.
Qed.

Lemma pow_1 x : x ^ 1 = x.
Proof.
  ring.
Qed.

Lemma pow_add x n m : x ^ (n + m) = x ^ n * x ^ m.
Proof.
  induction n as [|n IH]; simpl; auto with real.
  rewrite IH; ring.
Qed.

Lemma Rpow_mult_distr x y n : (x * y) ^ n = x ^ n * y ^ n.
Proof.
  induction n; try ring.
  simpl; ring [IHn].
Qed.

Lemma pow_nonzero x n : x <> 0 -> x ^ n <> 0.
Proof.
  intro Hx; induction n as [|n IH]; simpl.
    now apply R1_neq_R0.
  now intros H; case (Rmult_integral _ _ H); intros H1.
Qed.

Hint Resolve pow_O pow_1 pow_add pow_nonzero: real.

Lemma pow_RN_plus x n m : x <> 0 -> x ^ n = x ^ (n + m) * / x ^ m.
Proof.
  intros Hx; rewrite pow_add; field; auto with real.
Qed.

Lemma pow_lt x n : 0 < x -> 0 < x ^ n.
Proof.
  intros Hx; induction n as [|n IH]; simpl; auto with real.
  replace 0 with (x * 0); auto with real.
Qed.
Hint Resolve pow_lt: real.

Lemma Rlt_pow_R1 x n : 1 < x -> (0 < n)%nat -> 1 < x ^ n.
Proof.
  intros Hx; induction n as [|n IH]; simpl; auto with real.
    now intro H; inversion H.
  intros _.
  destruct n as [|n].
    now ring_simplify.
  apply Rlt_trans with (r2 := x * 1).
    now rewrite Rmult_1_r.
  apply Rmult_lt_compat_l.
    now apply (Rlt_trans _ 1); auto with real.
  apply IH; auto with arith.
Qed.
Hint Resolve Rlt_pow_R1: real.

Lemma Rlt_pow x n m : 1 < x -> (n < m)%nat -> x ^ n < x ^ m.
Proof.
  intros H' H'0; replace m with (m - n + n)%nat.
  - rewrite pow_add.
    replace (x ^ n) with (1 * x ^ n) at 1 by ring.
    apply Rmult_lt_compat_r; auto with real.
    + apply pow_lt.
      apply (Rlt_trans _ 1); auto with real.
    + apply Rlt_pow_R1; auto with arith.
      now apply lt_minus_O_lt.
  - rewrite Nat.sub_add; auto with arith.
Qed.
Hint Resolve Rlt_pow: real.

(*********)
Lemma tech_pow_Rmult x n : x * x ^ n = x ^ S n.
Proof.
  induction n; simpl; trivial.
Qed.

(*********)
Lemma tech_pow_Rplus x a n : x ^ a + INR n * x ^ a = INR (S n) * x ^ a.
Proof.
  rewrite S_INR; ring.
Qed.

Lemma poly n x : 0 < x -> 1 + INR n * x <= (1 + x) ^ n.
Proof.
  intro H; induction n as [|n IH].
    now simpl; rewrite Rmult_0_l, Rplus_0_r; auto with real.
  apply (Rle_trans _ ((1 + x) * (1 + INR n * x))).
  - rewrite S_INR.
    ring_simplify.
    rewrite <- (Rplus_0_l (_ + 1)), !Rplus_assoc.
    apply Rplus_le_compat_r.
    apply Rmult_le_pos; auto with real.
  - unfold pow; fold pow.
    apply Rmult_le_compat_l; auto with real.
    apply Rplus_le_le_0_compat; auto with real.
Qed.

Lemma Power_monotonic x m n :
    Rabs x > 1 -> (m <= n)%nat -> Rabs (x ^ m) <= Rabs (x ^ n).
Proof.
  intros H; induction  n as [| n Hrecn]; intros; inversion H0; auto with real.
  apply (Rle_trans _ (Rabs (x ^ n))).
    now apply Hrecn.
  simpl; rewrite Rabs_mult, Rmult_comm.
  rewrite <- Rmult_1_r at 1.
  apply Rmult_le_compat_l; auto with real.
  apply Rabs_pos.
Qed.

Lemma RPow_abs x n : Rabs x ^ n = Rabs (x ^ n).
Proof.
  induction n as [|n IH]; simpl.
    now rewrite Rabs_pos_eq; auto with real.
  now rewrite Rabs_mult, IH.
Qed.

Lemma Pow_x_infinity x :
    Rabs x > 1 ->
    forall b : R,
      exists N : nat, (forall n:nat, (n >= N)%nat -> Rabs (x ^ n) >= b).
Proof.
  intros Hx b; destruct (archimed (b * / (Rabs x - 1))) as [Ha Hb].
  assert (H0 : 0 < Rabs x - 1) by now apply Rlt_Rminus.
  assert (H1 : exists N : nat, INR N >= b * / (Rabs x - 1)).
  - set (u := up _) in Ha, Hb.
    exists (Z.to_nat u).
    destruct u; simpl; auto with real.
    + now apply Rgt_ge.
    + rewrite INR_IZR_INZ, positive_nat_Z.
      now apply Rgt_ge.
    + apply (Rge_trans _ (IZR (Z.neg p))); auto with real.
      now apply Rgt_ge.
  - destruct H1 as [N HN].
    exists N; intros n Hn; apply Rle_ge.
    apply (Rle_trans _ (Rabs (x ^ N))).
    + apply (Rle_trans _ (1 + INR N * (Rabs x - 1))).
      * apply (Rle_trans _ (INR N * (Rabs x - 1))).
        -- replace b with ((b * / (Rabs x - 1)) * (Rabs x - 1)).
             now apply Rmult_le_compat_r; auto with real.
           field; auto with real.
        -- rewrite <- Rplus_0_l at 1; auto with real.
      * rewrite <- RPow_abs.
        replace (Rabs x) with (1 + (Rabs x - 1)) at 2 by ring.
        apply poly; auto with real.
    + now apply Power_monotonic; auto with arith.
Qed.

Lemma pow_ne_zero n : n <> 0%nat -> 0 ^ n = 0.
Proof.
  destruct n; simpl; intro H; try ring.
  case H; auto.
Qed.

Lemma Rinv_pow x n : x <> 0 -> / x ^ n = (/ x) ^ n.
Proof.
  intros Hx; induction n as [|n IH]; simpl.
    now field.
  rewrite Rinv_mult_distr, IH; auto with real.
Qed.

Lemma pow_lt_1_zero x :
    Rabs x < 1 ->
    forall y : R,
      0 < y ->
      exists N : nat, (forall n:nat, (n >= N)%nat -> Rabs (x ^ n) < y).
Proof.
  intros Hx1; elim (Req_dec x 0); intros Hx y Hy.
    exists 1%nat; intros n Hn.
    now rewrite Hx, pow_ne_zero, Rabs_R0; auto with real; omega.
  assert (H : Rabs (/ x) > 1).
    apply Rlt_gt.
    rewrite Rabs_Rinv; trivial.
    replace 1 with (/ 1) by field.
    apply Rinv_lt_contravar; ring_simplify; auto with real.
    now apply Rabs_pos_lt.
  destruct (Pow_x_infinity _ H (/ y + 1)) as [N HN].
  exists N; intros n Hn.
  rewrite <- Rinv_involutive; auto with real.
  rewrite <- Rinv_involutive at 1;
    [idtac | now apply Rabs_no_R0; apply pow_nonzero].
  apply Rinv_lt_contravar.
  - apply Rmult_lt_0_compat; apply Rinv_0_lt_compat; auto with real.
    rewrite <- RPow_abs.
    apply pow_lt.
    now apply Rabs_pos_lt.
  - apply (Rlt_le_trans _ (/ y + 1)); auto with real.
    rewrite <- Rabs_Rinv.
    rewrite Rinv_pow; auto with real.
    now apply pow_nonzero.
Qed.

Lemma pow_R1 r n : r ^ n = 1 -> Rabs r = 1 \/ n = 0%nat.
Proof.
  intros Hr.
  assert (Hr1 : Rabs r ^ n = 1).
    now rewrite RPow_abs, Hr, Rabs_R1.
  destruct n as [|n]; auto.
  case (Req_dec (Rabs r) 1); auto; intros H'1.
  assert (Hr0 : r <> 0).
    contradict Hr; rewrite Hr, pow_ne_zero; auto with real.
  case (Rdichotomy _ _ H'1); intros H'2.
  - assert (H1 : Rabs (/ r) ^ 0 < Rabs (/ r) ^ S n).
      apply Rlt_pow; auto with arith.
      rewrite Rabs_Rinv; trivial.
      replace 1 with (/ 1) by field.
      apply Rinv_lt_contravar; trivial.
      now ring_simplify; apply Rabs_pos_lt.
    rewrite pow_O, RPow_abs, <- Rinv_pow in H1; trivial.
    rewrite Rabs_Rinv, Hr, Rabs_R1, Rinv_1 in H1.
      now contradict H1; auto with real.
    now rewrite Hr; auto with real.
  - assert (H1 : Rabs r ^ 0 < Rabs r ^ S n).
      now apply Rlt_pow; auto with arith.
    rewrite pow_O, Hr1 in H1; trivial.
    now contradict H1; auto with real.
Qed.

Lemma pow_Rsqr x n : x ^ (2 * n) = (x ^ 2) ^ n.
Proof.
  induction  n as [| n IH].
    now rewrite !pow_O.
  replace (2 * S n)%nat with (S (S (2 * n))) by ring.
  replace (x ^ S (S (2 * n))) with (x * x * x ^ (2 * n)).
    rewrite IH; simpl; ring.
  simpl; ring.
Qed.

Lemma pow_le a n : 0 <= a -> 0 <= a ^ n.
Proof.
  intros; induction n as [| n IH].
    now simpl; auto with real.
  now simpl; apply Rmult_le_pos.
Qed.

(**********)
Lemma pow_1_even n : (-1) ^ (2 * n) = 1.
Proof.
  induction n as [| n IH]; trivial.
  replace (2 * S n)%nat with (2 + 2 * n)%nat by ring.
  rewrite pow_add; rewrite IH; simpl; ring.
Qed.

(**********)
Lemma pow_1_odd n : (-1) ^ S (2 * n) = -1.
Proof.
  replace (S (2 * n)) with (2 * n + 1)%nat by ring.
  rewrite pow_add; rewrite pow_1_even; simpl; ring.
Qed.

(**********)
Lemma pow_1_abs n : Rabs ((-1) ^ n) = 1.
Proof.
  induction  n as [| n IH].
    now simpl; apply Rabs_R1.
  replace (S n) with (n + 1)%nat; [ rewrite pow_add | ring ].
  rewrite Rabs_mult, IH, Rmult_1_l; simpl.
  rewrite Rmult_1_r, Rabs_left; auto with real; ring.
Qed.

Lemma pow_mult x n1 n2 : x ^ (n1 * n2) = (x ^ n1) ^ n2.
Proof.
  intros; induction n2 as [| n2 IH].
    now rewrite Nat.mul_0_r, !pow_O.
  replace (n1 * S n2)%nat with (n1 * n2 + n1)%nat by ring.
  replace (S n2) with (n2 + 1)%nat by ring.
  do 2 rewrite pow_add.
  ring [IH].
Qed.

Lemma pow_incr x y n : 0 <= x <= y -> x ^ n <= y ^ n.
Proof.
  intros [Hx Hy].
  induction  n as [| n IH]; auto with real.
  simpl.
  apply Rle_trans with (y * x ^ n).
    do 2 rewrite <- (Rmult_comm (x ^ n)).
    apply Rmult_le_compat_l; trivial.
    now apply pow_le.
  apply Rmult_le_compat_l; trivial.
  now apply Rle_trans with x.
Qed.

Lemma pow_R1_Rle x k : 1 <= x -> 1 <= x ^ k.
Proof.
  intros Hx.
  induction k as [| k IH]; auto with real.
  apply Rle_trans with (x * 1).
    now rewrite Rmult_1_r.
  simpl; apply Rmult_le_compat_l; trivial.
  apply Rle_trans with 1; auto with real.
Qed.

Lemma Rle_pow x m n : 1 <= x -> (m <= n)%nat -> x ^ m <= x ^ n.
Proof.
  intros Hx Hmn.
  replace n with (n - m + m)%nat;
    [idtac | now rewrite plus_comm, <- le_plus_minus].
  rewrite pow_add.
  rewrite Rmult_comm.
  rewrite <- Rmult_1_r at 1.
  apply Rmult_le_compat_l.
    now apply pow_le; left; apply Rlt_le_trans with 1; [ apply Rlt_0_1 |].
  now apply pow_R1_Rle.
Qed.

Lemma pow1 n : 1 ^ n = 1.
Proof.
  induction n as [| n IH]; auto with real.
  now simpl; rewrite IH, Rmult_1_r.
Qed.

Lemma pow_Rabs x n : x ^ n <= Rabs x ^ n.
Proof.
  induction  n as [| n IH]; auto with real.
  simpl; destruct (Rcase_abs x) as [Hlt|Hle].
    rewrite RPow_abs, <- Rabs_mult.
    now apply RRle_abs.
  rewrite Rabs_pos_eq; auto with real.
Qed.

Lemma pow_maj_Rabs x y n : Rabs y <= x -> y ^ n <= x ^ n.
Proof.
  intros Hyx.
  assert (Hx : 0 <= x).
    apply Rle_trans with (Rabs y); auto with real.
    now apply Rabs_pos.
  apply Rle_trans with (Rabs y ^ n).
    now apply pow_Rabs.
  apply pow_incr; split; auto with real.
  now apply Rabs_pos.
Qed.

(*******************************)
(** *       PowerRZ            *)
(*******************************)
(*i Due to L.Thery i*)

Section PowerRZ.

Local Coercion Z_of_nat : nat >-> Z.

(* the following section should probably be somewhere else, but not sure where *)
Section Z_compl.

Local Open Scope Z_scope.

(* Provides a way to reason directly on Z in terms of nats instead of positive *)
Inductive Z_spec (x : Z) : Z -> Type :=
| ZintNull : x = 0 -> Z_spec x 0
| ZintPos (n : nat) : x = n -> Z_spec x n
| ZintNeg (n : nat) : x = - n -> Z_spec x (- n).

Lemma intP x : Z_spec x x.
Proof.
  destruct x as [|p|p].
  - now apply ZintNull.
  - rewrite <-positive_nat_Z at 2.
    apply ZintPos.
    now rewrite positive_nat_Z.
  - rewrite <-Pos2Z.opp_pos.
    rewrite <-positive_nat_Z at 2.
    apply ZintNeg.
    now rewrite positive_nat_Z.
Qed.

End Z_compl.

Definition powerRZ (x:R) (n:Z) :=
  match n with
    | Z0 => 1
    | Zpos p => x ^ Pos.to_nat p
    | Zneg p => / x ^ Pos.to_nat p
  end.

Local Infix "^Z" := powerRZ (at level 30, right associativity) : R_scope.

Lemma Zpower_NR0 x n : (0 <= x)%Z -> (0 <= Zpower_nat x n)%Z.
Proof.
  induction n; unfold Zpower_nat; simpl; auto with zarith.
Qed.

Lemma powerRZ_O x : x ^Z 0 = 1.
Proof.
  reflexivity.
Qed.

Lemma powerRZ_1 x : x ^Z Z.succ 0 = x.
Proof.
  simpl; auto with real.
Qed.

Lemma powerRZ_NOR x z : x <> 0 -> x ^Z z <> 0.
Proof.
  destruct z; simpl; auto with real.
Qed.

Lemma powerRZ_pos_sub x n m : x <> 0 ->
   x ^Z (Z.pos_sub n m) = x ^ Pos.to_nat n * / x ^ Pos.to_nat m.
Proof.
 intro Hx.
 rewrite Z.pos_sub_spec.
 case Pos.compare_spec; intro H; simpl.
 - subst; auto with real.
 - rewrite Pos2Nat.inj_sub by trivial.
   rewrite Pos2Nat.inj_lt in H.
   rewrite (pow_RN_plus x _ (Pos.to_nat n)) by auto with real.
   rewrite plus_comm, le_plus_minus_r by auto with real.
   rewrite Rinv_mult_distr, Rinv_involutive; auto with real.
 - rewrite Pos2Nat.inj_sub by trivial.
   rewrite Pos2Nat.inj_lt in H.
   rewrite (pow_RN_plus x _ (Pos.to_nat m)) by auto with real.
   rewrite plus_comm, le_plus_minus_r by auto with real.
   reflexivity.
Qed.

Lemma powerRZ_add x n m : x <> 0 -> x ^Z (n + m) = x ^Z n * x ^Z m.
Proof.
  destruct n as [|n|n]; destruct m as [|m|m]; simpl; intros; auto with real.
  - (* + + *)
    rewrite Pos2Nat.inj_add; auto with real.
  - (* + - *)
    now apply powerRZ_pos_sub.
  - (* - + *)
    rewrite Rmult_comm. now apply powerRZ_pos_sub.
  - (* - - *)
    rewrite Pos2Nat.inj_add; auto with real.
    rewrite pow_add; auto with real.
    apply Rinv_mult_distr; apply pow_nonzero; auto.
Qed.
Hint Resolve powerRZ_O powerRZ_1 powerRZ_NOR powerRZ_add: real.

Lemma Zpower_nat_powerRZ n m :
  IZR (Zpower_nat (Z.of_nat n) m) = INR n ^Z Z.of_nat m.
Proof.
  induction m as [|m IH]; simpl; auto with real.
  rewrite SuccNat2Pos.id_succ; simpl.
  replace (Zpower_nat (Z.of_nat n) (S m)) with
          (Z.of_nat n * Zpower_nat (Z.of_nat n) m)%Z; trivial.
  rewrite mult_IZR; auto with real.
  repeat rewrite <- INR_IZR_INZ; simpl.
  rewrite IH; simpl.
  case m; simpl; auto with real.
  now intros m1; rewrite SuccNat2Pos.id_succ; auto.
Qed.

Lemma Zpower_pos_powerRZ n m : IZR (Z.pow_pos n m) = IZR n ^Z Zpos m.
Proof.
  rewrite Zpower_pos_nat; simpl.
  induction (Pos.to_nat m).
    now easy.
  unfold Zpower_nat; simpl.
  rewrite mult_IZR.
  now rewrite <- IHn0.
Qed.

Lemma powerRZ_lt x z : 0 < x -> 0 < x ^Z z.
Proof.
  case z; simpl; auto with real.
Qed.
Hint Resolve powerRZ_lt: real.

Lemma powerRZ_le x z : 0 < x -> 0 <= x ^Z z.
Proof.
  intros Hx; apply Rlt_le; auto with real.
Qed.
Hint Resolve powerRZ_le: real.

Lemma Zpower_nat_powerRZ_absolu n m :
  (0 <= m)%Z -> IZR (Zpower_nat n (Z.abs_nat m)) = IZR n ^Z m.
Proof.
  destruct m as [|p|p]; simpl; auto with zarith.
    intros H'; induction (Pos.to_nat p) as [|m IH]; auto with zarith.
    simpl; rewrite <- IH; simpl; auto with zarith.
    now rewrite <- mult_IZR.
  intros H'; absurd (0 <= Zneg p)%Z; auto with zarith.
Qed.

Lemma powerRZ_R1 n : 1 ^Z n = 1.
Proof.
  case n; simpl; auto.
    intros p; induction (Pos.to_nat p) as [|m IH]; simpl; auto.
    rewrite IH; ring.
  intros p; induction (Pos.to_nat p) as [|m IH]; simpl; auto.
    exact Rinv_1.
  rewrite Rinv_mult_distr; try rewrite Rinv_1; try rewrite IH;
    auto with real.
Qed.

Local Open Scope Z_scope.

Lemma pow_powerRZ r n :
  (r ^ n)%R = powerRZ r (Z_of_nat n).
Proof.
  induction n; [easy|simpl].
  now rewrite SuccNat2Pos.id_succ.
Qed.

Lemma powerRZ_ind (P : Z -> R -> R -> Prop) :
  (forall x, P 0 x 1%R) ->
  (forall x n, P (Z.of_nat n) x (x ^ n)%R) ->
  (forall x n, P ((-(Z.of_nat n))%Z) x (Rinv (x ^ n))) ->
  forall x (m : Z), P m x (powerRZ x m)%R.
Proof.
  intros ? ? ? x m.
  destruct (intP m) as [Hm|n Hm|n Hm].
  - easy.
  - now rewrite <- pow_powerRZ.
  - unfold powerRZ.
    destruct n as [|n]; [ easy |].
    rewrite Nat2Z.inj_succ, <- Zpos_P_of_succ_nat, Pos2Z.opp_pos.
    now rewrite <- Pos2Z.opp_pos, <- positive_nat_Z.
Qed.

Lemma powerRZ_inv x alpha : (x <> 0)%R -> powerRZ (/ x) alpha = Rinv (powerRZ x alpha).
Proof.
  intros; destruct (intP alpha).
  - now simpl; rewrite Rinv_1.
  - now rewrite <-!pow_powerRZ, ?Rinv_pow, ?pow_powerRZ.
  - unfold powerRZ.
    destruct (- n).
    + now rewrite Rinv_1.
    + now rewrite Rinv_pow.
    + now rewrite <-Rinv_pow.
Qed.

Lemma powerRZ_neg x alpha : x <> R0 -> powerRZ x (- alpha) = powerRZ (/ x) alpha.
Proof.
  destruct alpha as [|n|n]; intro H ; simpl.
  - easy.
  - now rewrite Rinv_pow.
  - rewrite Rinv_pow by now apply Rinv_neq_0_compat.
    now rewrite Rinv_involutive.
Qed.

Lemma powerRZ_mult_distr m x y :
  ((0 <= m)%Z \/ (x * y <> 0)%R) ->
           (powerRZ (x*y) m = powerRZ x m * powerRZ y m)%R.
Proof.
  intros Hmxy.
  destruct (intP m) as [ | | n Hm ].
  - now simpl; rewrite Rmult_1_l.
  - now rewrite <- !pow_powerRZ, Rpow_mult_distr.
  - destruct Hmxy as [H|H].
    + assert(m = 0) as -> by now omega.
      now rewrite <- Hm, Rmult_1_l.
    + assert(x <> 0)%R by now intros ->; apply H; rewrite Rmult_0_l.
      assert(y <> 0)%R by now intros ->; apply H; rewrite Rmult_0_r.
      rewrite !powerRZ_neg by assumption.
      rewrite Rinv_mult_distr by assumption.
      now rewrite <- !pow_powerRZ, Rpow_mult_distr.
Qed.

End PowerRZ.

Local Infix "^Z" := powerRZ (at level 30, right associativity) : R_scope.

(*******************************)
(* For easy interface          *)
(*******************************)
(* decimal_exp r z is defined as r 10^z *)

Definition decimal_exp (r:R) (z:Z) : R := (r * 10 ^Z z).


(*******************************)
(** * Sum of n first naturals  *)
(*******************************)
(*********)
Fixpoint sum_nat_f_O (f:nat -> nat) (n:nat) : nat :=
  match n with
    | O => f 0%nat
    | S n' => (sum_nat_f_O f n' + f (S n'))%nat
  end.

(*********)
Definition sum_nat_f (s n:nat) (f:nat -> nat) : nat :=
  sum_nat_f_O (fun x:nat => f (x + s)%nat) (n - s).

(*********)
Definition sum_nat_O (n:nat) : nat := sum_nat_f_O (fun x:nat => x) n.

(*********)
Definition sum_nat (s n:nat) : nat := sum_nat_f s n (fun x:nat => x).

(*******************************)
(** *          Sum             *)
(*******************************)
(*********)
Fixpoint sum_f_R0 (f:nat -> R) (N:nat) : R :=
  match N with
    | O => f 0%nat
    | S i => sum_f_R0 f i + f (S i)
  end.

(*********)
Definition sum_f (s n:nat) (f:nat -> R) : R :=
  sum_f_R0 (fun x:nat => f (x + s)%nat) (n - s).

Lemma GP_finite x n :
    sum_f_R0 (fun n:nat => x ^ n) n * (x - 1) = x ^ (n + 1) - 1.
Proof.
  induction  n as [| n Hrecn]; simpl.
    ring.
  rewrite Rmult_plus_distr_r; rewrite Hrecn; cut ((n + 1)%nat = S n).
  intro H; rewrite H; simpl; ring.
  omega.
Qed.

Lemma sum_f_R0_triangle (x:nat -> R) n :
    Rabs (sum_f_R0 x n) <= sum_f_R0 (fun i:nat => Rabs (x i)) n.
Proof.
  induction n as [|n IH]; simpl.
    unfold Rle; right; reflexivity.
  apply
      (Rle_trans _
        (Rabs (sum_f_R0 x n) + Rabs (x (S n)))
        (sum_f_R0 (fun i:nat => Rabs (x i)) n + Rabs (x (S n)))).
    now apply Rabs_triang.
  now rewrite Rplus_comm;
    rewrite (Rplus_comm _ (Rabs (x (S n))));
      apply Rplus_le_compat_l.
Qed.

(*******************************)
(** *     Distance  in R       *)
(*******************************)

(*********)
Definition R_dist x y : R := Rabs (x - y).

(*********)
Lemma R_dist_pos x y : R_dist x y >= 0.
Proof.
  unfold R_dist; unfold Rabs; case (Rcase_abs (x - y));
    intro l.
  unfold Rge; left; apply (Ropp_gt_lt_0_contravar (x - y) l).
  trivial.
Qed.

(*********)
Lemma R_dist_sym x y : R_dist x y = R_dist y x.
Proof.
  unfold R_dist; intros; split_Rabs; try ring.
  generalize (Ropp_gt_lt_0_contravar (y - x) Hlt0); intro;
    rewrite (Ropp_minus_distr y x) in H; generalize (Rlt_asym (x - y) 0 Hlt);
      intro; unfold Rgt in H; exfalso; auto.
  generalize (minus_Rge y x Hge0); intro; generalize (minus_Rge x y Hge); intro;
    generalize (Rge_antisym x y H0 H); intro; rewrite H1;
      ring.
Qed.

(*********)
Lemma R_dist_refl x y : R_dist x y = 0 <-> x = y.
Proof.
  unfold R_dist; intros; split_Rabs; split; intros.
  rewrite (Ropp_minus_distr x y) in H; symmetry;
    apply (Rminus_diag_uniq y x H).
  rewrite (Ropp_minus_distr x y); generalize (eq_sym H); intro;
    apply (Rminus_diag_eq y x H0).
  apply (Rminus_diag_uniq x y H).
  apply (Rminus_diag_eq x y H).
Qed.

Lemma R_dist_eq x : R_dist x x = 0.
Proof.
  unfold R_dist; intros; split_Rabs; intros; ring.
Qed.

(***********)
Lemma R_dist_tri x y z : R_dist x y <= R_dist x z + R_dist z y.
Proof.
  intros; unfold R_dist; replace (x - y) with (x - z + (z - y));
    [ apply (Rabs_triang (x - z) (z - y)) | ring ].
Qed.

(*********)
Lemma R_dist_plus a b c d : R_dist (a + c) (b + d) <= R_dist a b + R_dist c d.
Proof.
  unfold R_dist;
    replace (a + c - (b + d)) with (a - b + (c - d)).
  exact (Rabs_triang (a - b) (c - d)).
  ring.
Qed.

Lemma R_dist_mult_l a b c : R_dist (a * b) (a * c) = Rabs a * R_dist b c.
Proof.
unfold R_dist. 
rewrite <- Rmult_minus_distr_l, Rabs_mult; reflexivity.
Qed.

(********************************)
(** *     Infinite Sum          *)
(********************************)
(*********)
Definition infinite_sum (s:nat -> R) (l:R) : Prop :=
  forall eps:R,
    eps > 0 ->
    exists N : nat,
      (forall n:nat, (n >= N)%nat -> R_dist (sum_f_R0 s n) l < eps).

(** Compatibility with previous versions *)
Notation infinit_sum := infinite_sum (only parsing).
