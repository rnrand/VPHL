(** * Unit Interval Lemmas *)

Require Export Reals.
Require Export Psatz.

Open Scope R_scope.

Lemma mult_by_lt_1 : forall a b c,
  0 < a < 1 ->
  0 < b < 1 ->
  0 < c < 1 -> 
  a = b*c ->
  a < b.
Proof.
  intros.
  assert (c < 1). lra.
  assert (/ 1 <  / c). apply Rinv_lt_contravar; lra.  
  assert (a * / 1 < a * / c). apply Rmult_lt_compat_l; lra.
  assert (a * / 1 < b * c * / c). rewrite <- H2. assumption. 
  rewrite Rmult_assoc in H6. 
  rewrite Rinv_r in H6; lra.
Qed.

Lemma plus_by_gt_0 : forall a b c,
  0 < c < 1 ->
  a = b + c ->
  b < a.
Proof.
  intros.
  rewrite H0.
  lra.
Qed.  

Lemma one_minus_p : forall a,
  0 < a < 1 ->
  0 < 1 - a < 1.
Proof.
  intro. lra.
Qed.

Lemma negation_flip : forall a b,
  a < b ->
  (1-a) > (1-b).
Proof.
  intros.
  apply Ropp_gt_contravar in H.
  apply Rplus_gt_compat_l with (r:=1) in H.
  unfold Rminus; assumption.
Qed.

Lemma divide_by_lt : forall a b,
  0 < a < 1 ->
  0 < b < 1 ->
  a < b ->
  0 < a / b < 1.
Proof.
  intros.
  apply Rmult_lt_compat_r with (r:= /b) in H1.
  rewrite Rinv_r in H1; try lra.
  assert (0 < a * / b). apply Rmult_lt_0_compat; try lra.
  apply Rinv_0_lt_compat; lra.
  lra.
  apply Rinv_0_lt_compat; lra.
Qed.

Lemma mult_stable: forall a b,
  0 < a < 1 ->
  0 < b < 1 ->
  0 < a * b < 1.
Proof. 
  intros. 
  assert (0<a*b).
  apply Rmult_lt_0_compat; lra.
  assert (a*b < 1*1).
  apply Rmult_gt_0_lt_compat; lra.
  lra.
Qed.

Lemma mult_lt_0_compat : forall p a,
  0 < p < 1 ->
  (0 < a <-> 0 < p * a).
Proof.
  split; intros.
  + apply Rmult_lt_0_compat; lra.
  + apply Rlt_gt in H0.
    apply Rmult_gt_compat_l with (r:=/p) in H0.
    rewrite <- Rmult_assoc in H0.
    rewrite Rinv_l in H0; lra.
    apply Rinv_0_lt_compat. lra.
Qed.

Lemma mult_le_0_compat : forall p a,
  0 < p < 1 ->
  (0 <= a <-> 0 <= p * a).
Proof.
  split; intros.
  + apply Rmult_le_pos; lra.
  + apply Rle_ge in H0.
    apply Rmult_ge_compat_l with (r:=/p) in H0.
    rewrite <- Rmult_assoc in H0.
    rewrite Rinv_l in H0; lra.
    destruct H. 
    apply Rinv_0_lt_compat in H. lra.
Qed.

Lemma in_0_1_open : forall p a b,
  0 < p < 1 ->
  0 < a < 1 ->
  0 < b < 1 ->
  0 < p * a + (1 - p) * b < 1.
Proof.
  intros.
  destruct H.
  apply conj.
  + apply Rplus_lt_0_compat.
    apply Rmult_lt_0_compat; lra. 
    apply Rmult_lt_0_compat; lra. 
  + destruct Rle_or_lt with (r1:=a) (r2:=b).
    - assert (p * b + (1 - p) * b < 1). lra. 
      assert (p * a <= p * b). 
      eapply Rmult_le_compat_l; lra.
      lra.
    - assert (p * a + (1 - p) * a < 1). lra. 
      assert ((1- p) * b <= (1 - p) * a). 
      eapply Rmult_le_compat_l; lra.
      lra.
Qed.

Lemma in_0_1_closed : forall p a b,
  0 < p < 1 ->
  0 <= a <= 1 ->
  0 <= b <= 1 ->
  0 <= p * a + (1 - p) * b <= 1.
Proof.
  intros.
  destruct H.
  apply conj.
  + apply Rplus_le_le_0_compat.
    apply Rmult_le_pos; lra.
    apply Rmult_le_pos; lra.
  + destruct Rle_or_lt with (r1:=a) (r2:=b).
    - assert (p * b + (1 - p) * b <= 1). lra. 
      assert (p * a <= p * b). 
      eapply Rmult_le_compat_l; lra.
      lra.
    - assert (p * a + (1 - p) * a <= 1). lra. 
      assert ((1- p) * b <= (1 - p) * a). 
      eapply Rmult_le_compat_l; lra.
      lra.
Qed.

Lemma sum_to_0 : forall p a b,
 0 < p < 1 ->
 0 <= a <= 1 ->
 0 <= b <= 1 ->
( p * a + (1-p) * b = 0 <-> (a = 0 /\ b = 0) ).
Proof. 
  split; intros.
  + assert (0 * a <= p * a). 
    apply Rmult_le_compat_r; lra. rewrite Rmult_0_l in H3.
    assert (0 * b <= (1-p) * b). 
      apply Rmult_le_compat_r; lra. rewrite Rmult_0_l in H4.
    assert  (p * a = 0). lra.
    assert ((1 - p) * b = 0). lra.
    split.
    apply Rmult_integral in H5. lra.
    apply Rmult_integral in H6. lra.
  + destruct H2.
    rewrite H2, H3.
    lra.
Qed.


Lemma sum_to_1 : forall p a b,
 0 < p < 1 ->
 0 <= a <= 1 ->
 0 <= b <= 1 ->
( p * a + (1-p) * b = 1 <-> (a = 1 /\ b = 1) ).
Proof.
  split; intros.
  + destruct H.
    assert (a < 1 \/ a = 1). lra.
    assert (b < 1 \/ b = 1). lra.
    destruct H4, H5.
  (* First 3 cases contradict premise H *)
    - apply Rmult_lt_compat_l with (r:=p) in H4; trivial.
      rewrite Rmult_1_r in H4.
      apply Rmult_lt_compat_l with (r:=(1-p)) in H5; try lra.
    - apply Rmult_lt_compat_l with (r:=p) in H4; trivial.
      rewrite Rmult_1_r in H4.
      rewrite H5 in H2. rewrite Rmult_1_r in H2.
      lra.
    - apply Rmult_lt_compat_l with (r:=(1-p)) in H5; try lra.
      rewrite Rmult_1_r in H5.
      rewrite H4 in H2. rewrite Rmult_1_r in H2.
      lra.
    - lra.
  + destruct H2.
    rewrite H2, H3.
    lra.
Qed.

(* Connected to some_state_true *)

Lemma sum_to_gt_0 : forall p a b,
 0 < p < 1 ->
 0 <= a <= 1 ->
 0 <= b <= 1 ->
( 0 < p * a + (1-p) * b <-> (0 < a \/ 0 < b) ).
Proof.
  split; intros.
  + assert (0 < p * a \/ 0 < (1-p) * b). lra.
    destruct H3.
    - left.
      apply mult_lt_0_compat with (p:=p) (a:=a); assumption.
    - right.
      apply mult_lt_0_compat with (p:=(1-p)) (a:=b); lra.
  + destruct H2.
    - apply mult_lt_0_compat with (p:=p) in H2; trivial.
      destruct H1.
      apply mult_le_0_compat with (p:=(1-p)) in H1; lra.
    - apply mult_lt_0_compat with (p:=(1-p)) in H2; try lra.
      destruct H0.
      apply mult_le_0_compat with (p:=p) in H0; try lra.
Qed.
    
(*

Lemma sum_to_lt_1 : forall p a b,
 0 < p < 1 ->
 0 <= a <= 1 ->
 0 <= b <= 1 ->
( p * a + (1-p) * b < 1 <-> (a < 1 \/ b < 1) ).

*)

Lemma scale_eq : forall p a,
  0 < p < 1 ->
  p * a + (1 - p) * a = a.
Proof.
  intros.
  lra.
Qed.

Lemma scale_lt : forall p a b r,
  0 < p < 1 ->
  a < r ->
  b < r ->
  p * a + (1 - p) * b < r.
Proof.
  intros.
  rewrite <- scale_eq with (p:=p); trivial.
  apply Rplus_lt_compat. 
  - apply Rmult_lt_compat_l; lra.
  - apply Rmult_lt_compat_l; lra.  
Qed.

Lemma scale_gt : forall p a b r,
  0 < p < 1 ->
  a > r ->
  b > r ->
  p * a + (1 - p) * b > r.
Proof.
  intros.
  rewrite <- scale_eq with (p:=p); trivial.
  apply Rplus_gt_compat. 
  - apply Rmult_gt_compat_l; lra.
  - apply Rmult_gt_compat_l; lra.  
Qed.

