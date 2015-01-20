(** * Reasoning About Distributions *)

Require Export Intervals.

Inductive dist T:Type : Type :=
  | Unit : T -> dist T
  | Combine : forall (p:R), 0 < p < 1 -> dist T -> dist T -> dist T.

Arguments Unit {T} _.
Arguments Combine {T} p v d1 d2.

Notation "~ X" := (fun t => negb (X t)). 
Notation "X1 && X2 " := (fun t => andb (X1 t) (X2 t)).
Notation "X1 || X2 " := (fun t => orb (X1 t) (X2 t)).

Fixpoint probability {T:Type} (d:dist T) (X: T -> bool): R :=
  match d with
  | Unit t => if X t then 1 else 0
  | Combine p v d1 d2 =>
    p * (probability d1 X) + (1-p) * (probability d2 X)
  end.

Notation "'Pr' X 'in' d"  := (probability d X) (at level 40).

(** ** Basic Theorems of Probability Theory *)

(** Lemma 2.4: Normality *)
Theorem pr_normality : forall {T:Type} (d : dist T) X,
  0 <= Pr X in d <= 1.
Proof.
  intros.
  induction d as [t |].
  + simpl.
    destruct (X t); lra.
  + simpl.
    apply in_0_1_closed. assumption.
    apply IHd1.
    apply IHd2.
Qed.

(** Lemma 2.5: Tautology *)
Lemma pr_tautology : forall {T:Type} (d : dist T) X,
  (forall t, X t = true) ->
  Pr X in d = 1.
Proof.
  intros.
  induction d as [t |].
  + simpl.
    rewrite H.
    reflexivity.
  + simpl in *.
    rewrite IHd1, IHd2.
    lra.
Qed.

(** Lemma 2.6: Contradiction *)
Lemma pr_contradiction : forall {T:Type} (d : dist T) X,
  (forall t, X t = false) ->
  Pr X in d = 0.
Proof.
  intros.
  induction d as [t |].
  + simpl.
    rewrite H.
    reflexivity.
  + simpl in *.
    rewrite IHd1, IHd2.
    lra.
Qed.

(** Lemma 2.7 Equivalence *)
Lemma pr_equivalence: forall {T:Type} (d : dist T) X X',
  (forall t, X t = X' t) ->
  Pr X in d = Pr X' in d.
Proof. 
  intros.
  induction d.
  simpl.
  rewrite H.
  reflexivity.
  simpl.
  rewrite IHd1, IHd2.
  reflexivity.
Qed.

Lemma pr_totality : forall {T:Type} (d : dist T) X, 
  probability d X + probability d (~X) = 1.
Proof.
  intros.
  induction d.
  + simpl. 
    destruct (X t); simpl; lra.
  + simpl in *.
    rewrite <- Rplus_assoc.
    rewrite Rplus_assoc with (r1 := p * (Pr X in d1)) 
                             (r2 := (1 - p) * (Pr X in d2)) 
                             (r3 := p * (Pr ~X in d1)).
    rewrite Rplus_comm with (r1 := (1 - p) * (Pr X in d2)) 
                            (r2 := p * (Pr ~X in d1)).
    rewrite <- Rplus_assoc.
    rewrite Rplus_assoc.
    rewrite <- Rmult_plus_distr_l.
    rewrite <- Rmult_plus_distr_l.
    rewrite IHd1.
    rewrite IHd2.
    lra.
Qed.

(** Lemma 2.8: Complement *)
Lemma pr_complement : forall {T:Type} (d : dist T) X, 
  Pr (~X) in d = 1 - Pr X in d.
Proof.
  intros.
  specialize (pr_totality d X). intros Eq.
  lra.
Qed.

(** Lemma 2.9: Disjunction *)
Lemma pr_disjunction : forall {T:Type} (d : dist T) X1 X2, 
  Pr (X1 || X2) in d = Pr X1 in d + Pr X2 in d - Pr (X1 && X2) in d.
Proof.
  induction d; intros.
  + simpl in *.
    destruct (X1 t), (X2 t); simpl; lra. 
  + simpl in *.
    rewrite IHd1; trivial.
    rewrite IHd2; trivial.
    lra.
Qed.  

Lemma pr_addition : forall {T:Type} (d : dist T) X1 X2, 
  (forall t, (X1 && X2) t = false) ->
  Pr (X1 || X2) in d = Pr X1 in d + Pr X2 in d.
Proof.
  intros.
  rewrite <- Rminus_0_r. 
  replace 0 with (Pr (X1 && X2) in d).
  Focus 2.  apply pr_contradiction. assumption.
  apply pr_disjunction.
Qed.

(** ** Rules for Bounding Probabilities *)

Lemma pr_union_bound : forall {T:Type} (d : dist T) X1 X2, 
  Pr (X1 || X2) in d <= Pr X1 in d + Pr X2 in d.
Proof.
  intros.
  specialize (pr_disjunction d X1 X2); intros.
  specialize (pr_normality d (X1 && X2)); intros.
  lra.
Qed.

Lemma pr_weaken : forall {T:Type} (d : dist T) X X', 
  (forall t, X t = true -> X' t = true) ->
  Pr X in d <= Pr X' in d.  
Proof.
  intros.
  induction d.
  + simpl.
    specialize (H t).
    destruct (X t), (X' t); try lra.
    assert (false=true) as contra by (apply H; reflexivity).
    inversion contra.
  + simpl.
    apply Rmult_le_compat_l with (r:=p) in IHd1; try lra.
    apply Rmult_le_compat_l with (r:=(1-p)) in IHd2; lra.
Qed.    

Lemma pr_strengthen : forall {T:Type} (d : dist T) X X', 
  (forall t, X' t = true -> X t = true) ->
  Pr X in d >= Pr X' in d.  
Proof.
  intros.
  induction d.
  + simpl.
    specialize (H t).
    destruct (X t), (X' t); try lra.
    assert (false=true) as contra by (apply H; reflexivity).
    inversion contra.
  + simpl.
    apply Rmult_ge_compat_l with (r:=p) in IHd1; try lra.
    apply Rmult_ge_compat_l with (r:=(1-p)) in IHd2; lra.
Qed.   

Lemma pr_disj_ge_l : forall {T:Type} (d : dist T) X1 X2,
  Pr (X1 || X2) in d >= Pr X1 in d.
Proof.
  intros; simpl.
  apply pr_strengthen.
  simpl; intros.
  destruct (X1 t), (X2 t); trivial; inversion H.
Qed.

Lemma pr_disj_ge_r : forall {T:Type} (d : dist T) X1 X2,
  Pr (X1 || X2) in d >= Pr X2 in d.
Proof.
  intros; simpl.
  apply pr_strengthen.
  simpl; intros.
  destruct (X1 t), (X2 t); trivial; inversion H.
Qed.


Lemma pr_conj_le_l : forall {T:Type} (d : dist T) X1 X2,
  Pr (X1 && X2) in d <= Pr X1 in d.
Proof.
  intros; simpl.
  apply pr_weaken.
  simpl; intros.
  destruct (X1 t), (X2 t); trivial; inversion H.
Qed.

Lemma pr_conj_le_r : forall {T:Type} (d : dist T) X1 X2,
  Pr (X1 && X2) in d <= Pr X2 in d.
Proof.
  intros; simpl.
  apply pr_weaken.
  simpl; intros.
  destruct (X1 t), (X2 t); trivial; inversion H.
Qed.

Lemma pr_ge_bound : forall {T:Type} (d : dist T) X1 X2 p1 p2,
  (forall t, (X1 && X2) t = false) ->
  Pr X1 in d >= p1 ->
  Pr X2 in d >= p2 ->
  p1 + p2 = 1 ->
  Pr X1 in d = p1 /\ Pr X2 in d = p2.
Proof. 
  intros.
  specialize (pr_addition d X1 X2 H); intros.
  assert (Pr (X1 || X2) in d >= p1 + p2) by lra.
  specialize (pr_normality d (X1 || X2)). intros.
  lra.
Qed.

(** *** The base states are deterministic *)

Theorem pr_unit : forall {T:Type} (t:T) X,
  Pr X in (Unit t) = 0 \/ Pr X in (Unit t) = 1.
Proof.
  intros.
  simpl.
  destruct (X t); lra.
Qed.

(** *** Combining and Splitting Distributions *)

(** Lemma 2.10: Combine *)
Lemma pr_combine : forall {T:Type} (d1 d2 : dist T) X p v r,
  Pr X in d1 = r -> 
  Pr X in d2 = r ->
  Pr X in Combine p v d1 d2 = r.
Proof.
  intros.
  simpl in *.
  rewrite H, H0.
  lra.
Qed.

(** Lemma 2.11: Split (0) *)
Lemma pr_split_0 : forall {T:Type} (d1 d2 : dist T) X p v,
  Pr X in Combine p v d1 d2 = 0 ->
  Pr X in d1 = 0 /\ Pr X in d2 = 0.  
Proof.
  intros.
  apply sum_to_0 with (p:=p); trivial; try apply pr_normality.
Qed.  

(** Lemma 2.11: Split (1) *)
Lemma pr_split_1 : forall {T:Type} (d1 d2 : dist T) X p v,
  Pr X in Combine p v d1 d2 = 1 ->
  Pr X in d1 = 1 /\ Pr X in d2 = 1.  
Proof.
  intros.
  apply sum_to_1 with (p:=p); trivial; try apply pr_normality.
Qed.  


(** *** Useful Rules for Zero and One *)

Lemma pr_complement_1 : forall {T:Type} (d : dist T) X, 
  Pr X in d = 1 <-> Pr (~X) in d = 0.
Proof. intros. rewrite pr_complement. lra. Qed.

Lemma pr_complement_0 : forall {T:Type} (d : dist T) X, 
  Pr X in d = 0 <-> Pr (~X) in d = 1.
Proof. intros. rewrite pr_complement. lra. Qed.

Lemma pr_weaken_1: forall {T:Type} (d : dist T) X X',
  (forall t, X t = true -> X' t = true) ->
  Pr X in d = 1 ->
  Pr X' in d = 1.  
Proof.
  intros.
  induction d. 
  + simpl in *.
    destruct (X t) eqn:Eqx, (X' t) eqn:Eqx'; trivial.
    apply H in Eqx. rewrite Eqx in Eqx'. inversion Eqx'. 
  + apply pr_split_1 in H0 as (H1 & H2).
    simpl. rewrite IHd1, IHd2; trivial. lra.
Qed.

Lemma pr_strengthen_0: forall {T:Type} (d : dist T) X X',
  (forall t, X' t = true -> X t = true) ->
  Pr X in d = 0 ->
  Pr X' in d = 0.  
Proof.
  intros.
  induction d. 
  + simpl in *.
    destruct (X t) eqn:Eqx, (X' t) eqn:Eqx'; trivial.
    apply H in Eqx'. rewrite Eqx in Eqx'. inversion Eqx'. 
  + apply pr_split_0 in H0 as (H1 & H2).
    simpl. rewrite IHd1, IHd2; trivial. lra.
Qed.

Lemma pr_conj_0_l : forall {T:Type} (d : dist T) X1 X2, 
  Pr X1 in d = 0 -> Pr (X1 && X2) in d = 0. 
Proof.
  intros.
  specialize (pr_conj_le_l d X1 X2).
  specialize (pr_normality d (X1 && X2)).
  intros.
  lra.
Qed.

Lemma pr_conj_0_r : forall {T:Type} (d : dist T) X1 X2, 
  Pr X2 in d = 0 -> Pr (X1 && X2) in d = 0. 
Proof.
  intros.
  specialize (pr_conj_le_r d X1 X2).
  specialize (pr_normality d (X1 && X2)).
  intros.
  lra.
Qed.

Lemma pr_conj_1_l : forall {T:Type} (d : dist T) X1 X2, 
  Pr X1 in d = 1 -> Pr (X1 && X2) in d = Pr X2 in d. 
Proof.
  intros.
  induction d.
  + simpl in *.
    destruct (X1 t), (X2 t); trivial; lra. 
  + simpl.
    simpl in H.
    apply sum_to_1 in H; trivial; try apply pr_normality. 
    destruct H.
    rewrite IHd1, IHd2; trivial.
Qed.

Lemma pr_conj_1_r : forall {T:Type} (d : dist T) X1 X2, 
  Pr X2 in d = 1 -> Pr (X1 && X2) in d = Pr X1 in d. 
Proof.
  intros.
  rewrite pr_equivalence with (X' := (X2 && X1)).
  apply pr_conj_1_l. assumption.
  intros.
  destruct (X1 t), (X2 t); reflexivity.
Qed.

Lemma pr_conj_1 : forall {T:Type} (d : dist T) X1 X2, 
  Pr X1 in d = 1 -> 
  Pr X2 in d = 1 ->
  Pr (X1 && X2) in d = 1. 
Proof.
  intros.
  rewrite <- H.
  apply pr_conj_1_r.
  assumption.
Qed.





