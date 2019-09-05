(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

Require Import Rbase.
Require Import Rbasic_fun.
Require Import Rpow_def.
Local Open Scope R_scope.

(****************************************************)
(** Rsqr : some results                             *)
(****************************************************)

Lemma Rsqr_def x : x ^ 2 = x * x.
Proof.
  ring.
Qed.

Lemma Rsqr_neg x : x ^ 2 = (- x) ^ 2.
Proof.
  ring.
Qed.

Lemma Rsqr_mult x y : (x * y) ^ 2 = x ^ 2 * y ^ 2.
Proof.
  ring.
Qed.

Lemma Rsqr_plus x y : (x + y) ^ 2 = x ^ 2 + y ^ 2 + 2 * x * y.
Proof.
  ring.
Qed.

Lemma Rsqr_minus x y : (x - y) ^ 2 = x ^ 2 + y ^ 2 - 2 * x * y.
Proof.
  ring.
Qed.

Lemma Rsqr_neg_minus x y : (x - y) ^ 2 = (y - x) ^ 2.
Proof.
  ring.
Qed.

Lemma Rsqr_0 : 0 ^ 2 = 0.
Proof.
  ring.
Qed.

Lemma Rsqr_1 : 1 ^ 2 = 1.
Proof.
  ring.
Qed.

Lemma Rsqr_gt_0_0 x : 0 < x ^ 2 -> x <> 0.
Proof.
  intros H; red; intro H0; rewrite H0 in H.
  rewrite Rsqr_0 in H; case (Rlt_irrefl 0 H).
Qed.

Lemma Rsqr_pos_lt x : x <> 0 -> 0 < x ^ 2.
Proof.
  intros H; destruct (Rtotal_order 0 x) as [H1 | [H1 | H1]].
  - rewrite Rsqr_def.
    apply Rmult_lt_0_compat; assumption.
  - case H; auto.
  - replace (x ^ 2) with (- x * - x) by ring.
    apply Rmult_lt_0_compat; auto with real.
Qed.

Lemma Rsqr_div x y : y <> 0 -> (x / y) ^ 2 = x ^ 2 / y ^ 2.
Proof.
  intros; field; trivial.
Qed.

Lemma Rsqr_eq_0 x : x ^ 2 = 0 -> x = 0.
Proof.
  apply Rsqr_0_uniq.
Qed.

Lemma Rsqr_minus_plus a b : (a - b) * (a + b) = a ^ 2 - b ^ 2.
Proof.
  ring.
Qed.

Lemma Rsqr_plus_minus a b : (a + b) * (a - b) = a ^ 2 - b ^ 2.
Proof.
  ring.
Qed.

Lemma Rsqr_incr_0_var x y : x ^ 2 <= y ^ 2 -> 0 <= y -> x <= y.
Proof.
  intros Hsq Hy.
  apply Rnot_lt_le; intro H1; case (Rle_not_lt _ _ Hsq).
  assert (H2 : 0 < x) by (apply (Rle_lt_trans  _ y); trivial).
  rewrite !Rsqr_def.
  apply (Rle_lt_trans _ (y * x)); auto with real.
Qed.

Lemma Rsqr_incr_0  x y : x ^ 2 <= y ^ 2 -> 0 <= x -> 0 <= y -> x <= y.
Proof.
  intros; apply Rsqr_incr_0_var; trivial.
Qed.

Lemma Rsqr_incr_1 x y : x <= y -> 0 <= x -> 0 <= y -> x ^ 2 <= y ^ 2.
Proof.
  intros Hxy Hx Hy.
  rewrite !Rsqr_def.
  apply Rmult_le_compat; assumption.
Qed.

Lemma Rsqr_incrst_0 x y : x ^ 2 < y ^ 2 -> 0 <= x -> 0 <= y -> x < y.
Proof.
  intros Hsq Hx Hy.
  apply Rnot_le_lt; intro H1; case (Rlt_not_le _ _ Hsq).
  rewrite !Rsqr_def.
  apply (Rle_trans _ (y * x)); auto with real.
Qed.

Lemma Rsqr_incrst_1 x y : x < y -> 0 <= x -> 0 <= y -> x ^ 2 < y ^ 2.
Proof.
  intros.
  rewrite !Rsqr_def.
  apply Rmult_le_0_lt_compat; assumption.
Qed.

Lemma Rsqr_neg_pos_le_0 x y : x ^ 2 <= y ^ 2 -> 0 <= y -> - y <= x.
Proof.
  intros Hsq Hy.
  intros; destruct (Rcase_abs x) as [Hlt|Hle].
  apply Rnot_lt_le; intro H1; case (Rle_not_lt _ _ Hsq).
  - rewrite (Rsqr_neg x).
    apply Rsqr_incrst_1; auto with real.
    replace y with (- - y) by ring; auto with real.
  - apply (Rle_trans _ 0); auto with real.
Qed.

Lemma Rsqr_neg_pos_le_1 x y : - y <= x -> x <= y -> 0 <= y -> x ^ 2 <= y ^ 2.
Proof.
  intros H H0 H1; destruct (Rcase_abs x) as [Hlt|Hle].
  - apply Ropp_lt_gt_contravar, Rlt_le in Hlt; rewrite Ropp_0 in Hlt.
    apply Ropp_le_ge_contravar, Rge_le in H; rewrite Ropp_involutive in H.
    rewrite (Rsqr_neg x); apply Rsqr_incr_1; assumption.
  - apply Rge_le in Hle; apply Rsqr_incr_1; assumption.
Qed.

Lemma neg_pos_Rsqr_le x y : - y <= x -> x <= y -> x ^ 2 <= y ^ 2.
Proof.
  intros H H0; destruct (Rcase_abs x) as [Hlt|Hle].
  - apply Ropp_lt_gt_contravar, Rlt_le in Hlt; rewrite Ropp_0 in Hlt.
    apply Ropp_le_ge_contravar, Rge_le in H; rewrite Ropp_involutive in H.
    assert (0 <= y) by (apply Rle_trans with (-x); assumption).
    rewrite (Rsqr_neg x); apply Rsqr_incr_1; assumption.
  - apply Rge_le in Hle.
    assert (0 <= y) by (apply Rle_trans with x; assumption).
    apply Rsqr_incr_1; assumption.
Qed.

Lemma Rsqr_abs x : x ^ 2 = (Rabs x) ^ 2.
Proof.
  unfold Rabs; case (Rcase_abs x); intro;
    [ apply Rsqr_neg | reflexivity ].
Qed.

Lemma Rsqr_le_abs_0 x y : x ^ 2 <= y ^ 2 -> Rabs x <= Rabs y.
Proof.
  intros; apply Rsqr_incr_0; repeat rewrite <- Rsqr_abs;
    [ assumption | apply Rabs_pos | apply Rabs_pos ].
Qed.

Lemma Rsqr_le_abs_1 x y : Rabs x <= Rabs y -> x ^ 2 <= y ^ 2.
Proof.
  intros; rewrite (Rsqr_abs x); rewrite (Rsqr_abs y);
    apply (Rsqr_incr_1 (Rabs x) (Rabs y) H (Rabs_pos x) (Rabs_pos y)).
Qed.

Lemma Rsqr_lt_abs_0 x y : x ^ 2 < y ^ 2 -> Rabs x < Rabs y.
Proof.
  intros; apply Rsqr_incrst_0; repeat rewrite <- Rsqr_abs;
    [ assumption | apply Rabs_pos | apply Rabs_pos ].
Qed.

Lemma Rsqr_lt_abs_1 x y : Rabs x < Rabs y -> x ^ 2 < y ^ 2.
Proof.
  intros; rewrite (Rsqr_abs x); rewrite (Rsqr_abs y);
    apply (Rsqr_incrst_1 (Rabs x) (Rabs y) H (Rabs_pos x) (Rabs_pos y)).
Qed.

Lemma Rsqr_inj x y : 0 <= x -> 0 <= y -> x ^ 2 = y ^ 2 -> x = y.
Proof.
  intros; generalize (Rle_le_eq (x ^ 2) (y ^ 2)); intro; elim H2; intros _ H3;
    generalize (H3 H1); intro; elim H4; intros; apply Rle_antisym;
      apply Rsqr_incr_0; assumption.
Qed.

Lemma Rsqr_eq_abs_0 x y : x ^ 2 = y ^ 2 -> Rabs x = Rabs y.
Proof.
  intros; unfold Rabs; case (Rcase_abs x) as [Hltx|Hgex];
    case (Rcase_abs y) as [Hlty|Hgey];
    apply Rsqr_inj; auto with real;
    rewrite <- ! Rsqr_neg; trivial.
Qed.

Lemma Rsqr_eq_asb_1 x y : Rabs x = Rabs y -> x ^ 2 = y ^ 2.
Proof.
  intro H; assert (H0 : (Rabs x) ^ 2 = (Rabs y) ^ 2).
    rewrite H; reflexivity.
  repeat rewrite <- Rsqr_abs in H0; assumption.
Qed.

Lemma triangle_rectangle x y z :
    0 <= z -> x ^ 2 + y ^ 2 <= z ^ 2 -> - z <= x <= z /\ - z <= y <= z.
Proof.
  intros Hz Ht; split.
  - assert (H : x ^ 2 <= z ^ 2) by
      (apply (Rplus_le_reg_pos_r _ (y ^ 2)); auto with real).
    split; [apply Rsqr_neg_pos_le_0 | apply Rsqr_incr_0_var]; trivial.
  - assert (H : y ^ 2 <= z ^ 2).
      (apply (Rplus_le_reg_pos_r _ (x ^ 2)); auto with real;
       rewrite Rplus_comm; auto with real).
    split; [apply Rsqr_neg_pos_le_0 | apply Rsqr_incr_0_var]; trivial.
Qed.

Lemma triangle_rectangle_lt x y z :
    x ^ 2 + y ^ 2 < z ^ 2 -> Rabs x < Rabs z /\ Rabs y < Rabs z.
Proof.
  intros; split;
    [ generalize (Rplus_lt_reg_pos_r (x ^ 2) (y ^ 2) (z ^ 2) (Rle_0_sqr y) H);
      intro; apply Rsqr_lt_abs_0; assumption
      | rewrite Rplus_comm in H;
        generalize (Rplus_lt_reg_pos_r (y ^ 2) (x ^ 2) (z ^ 2) (Rle_0_sqr x) H);
          intro; apply Rsqr_lt_abs_0; assumption ].
Qed.

Lemma triangle_rectangle_le x y z :
    x ^ 2 + y ^ 2 <= z ^ 2 -> Rabs x <= Rabs z /\ Rabs y <= Rabs z.
Proof.
  intros; split;
    [ generalize (Rplus_le_reg_pos_r (x ^ 2) (y ^ 2) (z ^ 2) (Rle_0_sqr y) H);
      intro; apply Rsqr_le_abs_0; assumption
      | rewrite Rplus_comm in H;
        generalize (Rplus_le_reg_pos_r (y ^ 2) (x ^ 2) (z ^ 2) (Rle_0_sqr x) H);
          intro; apply Rsqr_le_abs_0; assumption ].
Qed.

Lemma Rsqr_inv x : x <> 0 -> (/ x) ^ 2 = / x ^ 2.
Proof.
  intros; field; trivial.
Qed.

Lemma canonical_Rsqr (a : nonzeroreal) (b c x : R) :
    a * x ^ 2 + b * x + c =
    a * (x + b / (2 * a)) ^ 2 + (4 * a * c - b ^ 2) / (4 * a).
Proof.
  intros.
  field.
  apply a.
Qed.

Lemma Rsqr_eq x y : x ^ 2 = y ^ 2 -> x = y \/ x = - y.
Proof.
  intros H; assert (H1 : Rabs x = Rabs y) by (apply Rsqr_eq_abs_0; trivial).
  unfold Rabs in H1; do 2 destruct Rcase_abs in H1; (left; ring [H1]) || (right ; ring [H1]).
Qed.
