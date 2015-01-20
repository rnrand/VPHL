(** * VPHL: A Verified Probabilistic Hoare Logic *)

Require Export PrImp.
Require Export Coq.Program.Equality.
Require Export Coq.Logic.FunctionalExtensionality.

(** ** Hoare Expressions
      Hexps are the fundamental assertions of our Hoare Logic.
**)

Inductive hexp : Type :=
  | HEq : bexp -> R -> hexp
  | HLt : bexp -> R -> hexp
  | HGt : bexp -> R -> hexp
  | HAnd : hexp -> hexp -> hexp
  | HOr : hexp -> hexp -> hexp.

(** Useful Abbreviations *)
Definition HLe b r: hexp := HOr (HLt b r) (HEq b r).
Definition HGe b r: hexp := HOr (HGt b r) (HEq b r).
Definition HNe b r: hexp := HOr (HLt b r) (HGt b r).

Fixpoint HNot hx :=
  match hx with 
  | HEq b p => HNe b p
  | HLt b p => HGe b p 
  | HGt b p => HLe b p 
  | HAnd h1 h2 => HOr (HNot h1) (HNot h2)
  | HOr h1 h2 => HAnd (HNot h1) (HNot h2)
  end.  

Definition HIf P1 P2 : hexp := HOr (HNot P1) P2.
Definition HTrue y := HEq (BId y) 1.
Definition HFalse y := HEq (BId y) 0.

(** *** Evaluation *)
Fixpoint heval (dst : dstate) (h: hexp) {struct h}: Prop :=
  match h with
  | HEq b p => Prb b in dst = p
  | HLt b p => Prb b in dst < p 
  | HGt b p => Prb b in dst > p 
  | HAnd h1 h2 => (heval dst h1) /\ (heval dst h2)
  | HOr h1 h2 => (heval dst h1) \/ (heval dst h2)
  end.

Lemma HGe_simpl: forall mst b p, heval mst (HGe b p) = (Prb b in mst >= p).
Proof. reflexivity. Qed.

Lemma HLe_simpl: forall mst b p, heval mst (HLe b p) = (Prb b in mst <= p).
Proof. reflexivity. Qed.

Lemma HNe_simpl: forall mst b p, heval mst (HNe b p) <-> (Prb b in mst <> p).
Proof. unfold not. split; intros.
       simpl in *. lra.
       simpl. lra.
Qed.

Definition h_implies (P Q : hexp)  : Prop :=
  forall dst, heval dst P -> heval dst Q.

Notation "P ->> Q" :=
  (h_implies P Q) (at level 80) : hoare_spec_scope.

Open Scope hoare_spec_scope.

Notation "P <<->> Q" :=
  (P ->> Q /\ Q ->> P) (at level 80) : hoare_spec_scope.

(** ** Hoare Triples *)

Definition hoare_triple
           (P:hexp) (c:com) (Q:hexp) : Prop :=
  forall dst dst',
       c / dst || dst'  ->
       heval dst P ->
       heval dst' Q.

Notation "{{ P }} c {{ Q }}" :=
  (hoare_triple P c Q) (at level 90, c at next level)
  : hoare_spec_scope.

Theorem hoare_post_true : forall (P Q : hexp) c,
  (forall dst, heval dst Q) ->
  {{P}} c {{Q}}.
Proof.
  intros P Q c H. unfold hoare_triple.
  intros dst dst' mcom HP.
  apply H.  Qed.

Theorem hoare_pre_false : forall (P Q : hexp) c,
  (forall dst, ~(heval dst P)) ->
  {{P}} c {{Q}}.
Proof.
  intros P Q c H. unfold hoare_triple.
  intros dst dst' mcom HP.
  unfold not in H. apply H in HP.
  inversion HP.  Qed.

(** ** Hoare Consequence Rules: Largely preserved from Software Foundations *)

Theorem hoare_consequence_pre : forall (P P' Q : hexp) c,
  {{P'}} c {{Q}} ->
  P ->> P' ->
  {{P}} c {{Q}}.
Proof.
  intros P P' Q c Hhoare Himp.
  intros dst dst' Hc HP. apply (Hhoare dst dst'). 
  assumption. apply Himp. assumption. Qed.

Theorem hoare_consequence_post : forall (P Q Q' : hexp) c,
  {{P}} c {{Q'}} ->
  Q' ->> Q ->
  {{P}} c {{Q}}.
Proof.
  intros P Q Q' c Hhoare Himp.
  intros dst dst' Hc HP. 
  apply Himp.
  apply (Hhoare dst dst'). 
  assumption. assumption. Qed.

Theorem hoare_consequence : forall (P P' Q Q' : hexp) c,
  {{P'}} c {{Q'}} ->
  P ->> P' ->
  Q' ->> Q ->
  {{P}} c {{Q}}.
Proof.
  intros P P' Q Q' c Hht HPP' HQ'Q.
  apply hoare_consequence_pre with (P' := P').
  apply hoare_consequence_post with (Q' := Q').
  assumption. assumption. assumption.  Qed.


(** ** Restricted Assertions
   
Certain Restricted Hoare Assertions enable us to reason from distributions
   to sub-distributions, and vice-versa 

*)

Inductive non_disjunctive : hexp -> Prop := 
  | nd_eq : forall b p, non_disjunctive (HEq b p)
  | nd_lt : forall b p, non_disjunctive (HLt b p)
  | nd_gt : forall b p, non_disjunctive (HGt b p)
  | nd_conj : forall h1 h2, 
      non_disjunctive h1 -> 
      non_disjunctive h2 -> 
      non_disjunctive (HAnd h1 h2).

(** Lemma 4.1 *)
Lemma non_disjunctive_combine: forall P dst1 dst2 p v,
  non_disjunctive P -> 
  heval dst1 P ->
  heval dst2 P ->
  heval (Combine p v dst1 dst2) P.
Proof.
  intros.  
  induction H as [ | | | P1 P2 nd1 IH1 nd2 IH2]; simpl. 
  + simpl in *.
    rewrite H0, H1; lra.
  + apply scale_lt; assumption.
  + apply scale_gt; assumption.
  + destruct H0, H1.
    split.
    apply IH1; assumption.
    apply IH2; assumption.
Qed.

Inductive non_probabilistic : hexp -> Prop :=
  | np_0 : forall b, non_probabilistic (HEq b 0)
  | np_1 : forall b, non_probabilistic (HEq b 1)
  | np_conj : forall h1 h2, 
      non_probabilistic h1 -> 
      non_probabilistic h2 -> 
      non_probabilistic (HAnd h1 h2)
  | np_disj : forall h1 h2, 
      non_probabilistic h1 -> 
      non_probabilistic h2 -> 
      non_probabilistic (HOr h1 h2).

(** Lemma 4.2 *)
Lemma non_probabilistic_split : forall P p v dst1 dst2,
  non_probabilistic P ->
  heval (Combine p v dst1 dst2) P ->
  (heval dst1 P /\ heval dst2 P).
Proof.
  intros P p v dst1 dst2 np.
  induction np.
  + apply pr_split_0.
  + apply pr_split_1.
  + simpl; intuition.
  + simpl; intuition.
Qed.

Inductive deterministic : hexp -> Prop :=
  | det_lit : forall b, deterministic (HEq b 1)
  | det_conj : forall h1 h2, 
      deterministic h1 -> 
      deterministic h2 -> 
      deterministic (HAnd h1 h2).

(** Lemma 4.3 (1) *)
Lemma deterministic_combine : forall P p v dst1 dst2,
  deterministic P ->
  heval dst1 P -> 
  heval dst2 P ->
  heval (Combine p v dst1 dst2) P.
Proof.
  intros P p v dst1 dst2 np.
  induction np.
  + apply pr_combine.
  + simpl; intuition.
Qed.

(** Lemma 4.3 (2) *)
Lemma deterministic_split : forall P p v dst1 dst2,
  deterministic P ->
  heval (Combine p v dst1 dst2) P ->
  heval dst1 P /\ heval dst2 P.
Proof.
  intros P p v dst1 dst2 np.
  induction np.
  + apply pr_split_1.
  + simpl; intuition.
Qed.

(* ####################################################### *)
(** * DST Equivalence:

   Since every distribution over states functions as a probability measure
   over assertions, we should have a notion of distribution equivalence.

   Note that since dsts are represented in tree form, and represent multisets of
   states and weights, the actual representations of equivalent dsts can vary widely
   (eg. any distribution can be expressed via an arbitrarily large tree).

**)

Definition dst_equiv (dst dst' : dstate) : Prop :=
  forall b, Prb b in dst = Prb b in dst'.

Notation "a '==' b" := (dst_equiv a b) (at level 50).

Lemma dst_equiv_eq : forall st1 st2,
  Unit st1 == Unit st2 ->
  st1 = st2.
Proof.
  intros.
  apply injective_projections.
  + apply functional_extensionality.
    intros.
    specialize (H (BEq (AId x) (ANum (fst st1 x)))).
    simpl in H.
    rewrite <- beq_nat_refl in H.
    destruct (beq_nat (fst st2 x) (fst st1 x)) eqn:Eq.
    apply beq_nat_true in Eq.
    symmetry.
    assumption.
    lra.
  + apply functional_extensionality.
    intros.
    specialize (H (BId x)).
    simpl in H.
    destruct (snd st1 x), (snd st2 x); trivial; lra.
Qed.

Lemma dst_equiv_refl : forall dst, dst == dst.
Proof. unfold dst_equiv. reflexivity. Qed.

Lemma dst_equiv_symm : forall dst1 dst2, dst1 == dst2 -> dst2 == dst1.
Proof. unfold dst_equiv. auto. Qed.

Lemma dst_equiv_trans : forall dst1 dst2 dst3, 
  dst1 == dst2 -> dst2 == dst3 -> dst1 == dst3. 
Proof. unfold dst_equiv. intros. rewrite H. apply H0. Qed.

(* Necessary? *)
Lemma dst_equiv_split : forall b p v dst11 dst10 dst21 dst20,
  (Combine p v dst11 dst10) == (Combine p v dst21 dst20) ->
  Prb b in dst11 = 1 ->
  Prb b in dst10 = 0 ->
  Prb b in dst21 = 1 ->
  Prb b in dst20 = 0 ->
  dst11 == dst21 /\ dst10 == dst20.
Proof.
  intros.
  unfold dst_equiv in *.
  split.
  + intros.
    specialize (H (BAnd b0 b)).
    simpl in *.
    rewrite pr_conj_1_r in H; trivial.
    rewrite pr_conj_0_r in H; trivial.
    rewrite pr_conj_1_r in H; trivial.
    rewrite pr_conj_0_r in H; trivial.
    rewrite Rmult_0_r in H.
    rewrite 2 Rplus_0_r in H.
    apply Rmult_eq_reg_l with (r:=p); lra.
  + intros.
    specialize (H (BAnd b0 (BNot b))).
    apply prb_complement_1 in H0.
    apply prb_complement_0 in H1.
    apply prb_complement_1 in H2.
    apply prb_complement_0 in H3.
    simpl in H.
    rewrite pr_conj_0_r in H; trivial.
    rewrite pr_conj_1_r in H; trivial.
    rewrite pr_conj_0_r in H; trivial.
    rewrite pr_conj_1_r in H; trivial.
    rewrite Rmult_0_r in H.
    rewrite 2 Rplus_0_l in H.
    apply Rmult_eq_reg_l with (r:=(1-p)); lra.
Qed.

Lemma dst_equiv_combine : forall p v dst11 dst12 dst21 dst22,
  dst11 == dst21 -> 
  dst12 == dst22 ->
  (Combine p v dst11 dst12) == (Combine p v dst21 dst22).
Proof. unfold dst_equiv. intros. simpl. rewrite H, H0. reflexivity. Qed.

Lemma dst_equiv_unit_split : forall st p v dst1 dst2,
  (Combine p v dst1 dst2) == (Unit st) <-> 
  dst1 == (Unit st) /\ dst2 == (Unit st).
Proof.
  unfold dst_equiv.
  simpl.
  split; intros.
  + split.
    - intros.
      specialize (H b).
      destruct (beval b st) eqn:Eq.
      apply sum_to_1 in H; try lra; try apply pr_normality.
      apply sum_to_0 in H; try lra; try apply pr_normality.
    - intros.
      specialize (H b).
      destruct (beval b st) eqn:Eq.
      apply sum_to_1 in H; try lra; try apply pr_normality.
      apply sum_to_0 in H; try lra; try apply pr_normality.
  + destruct H as [H1 H2].
    rewrite H1, H2.
    lra.
Qed.

(**
   The following lemmas assume we have the proof terms v'. 
   We could give the proof terms explicitly i.e. one_minus_p p v 
*)

(** Lemma 2.1 Distribution Commutativity *)
Lemma dst_comm : forall p v v' dst1 dst2,
  (Combine p v dst1 dst2) == (Combine (1-p) v' dst2 dst1). 
Proof. unfold dst_equiv. simpl. intros. lra. Qed.  

(** Lemma 2.2 Distribution Associativity *)
Lemma dst_assoc : forall p q v v' w w' dst1 dst2 dst3,
  Combine q w (Combine p v dst1 dst2) dst3 == 
  Combine (p*q) w' dst1 (Combine (q*(1-p)/(1-p*q)) v' dst2 dst3).
Proof.
  unfold dst_equiv.
  intros.
  simpl.
  rewrite ! Rmult_plus_distr_l.
  replace (q * (p * (Prb b in dst1))) with (p * q * (Prb b in dst1)) by lra.
  unfold Rdiv.
  rewrite <- 3 Rmult_assoc.
  rewrite Rinv_r_simpl_m. 2:lra.
  rewrite <- Rplus_assoc.
  rewrite <- Rmult_assoc.
  assert (H:(1 - p * q) * (1 - q * (1 - p) * / (1 - p * q)) = (1-q)). 
  2: rewrite H; reflexivity. 
  unfold Rminus.
  rewrite ! Rmult_plus_distr_l.
  rewrite <- ! Ropp_mult_distr_l_reverse.
  rewrite <- ! Rmult_assoc.
  rewrite Rinv_r_simpl_m. 2:lra.
  rewrite ! Rmult_1_r.
  lra.
Qed.

(** Lemma 2.3 Distribution Merge *)
Lemma dst_merge : forall p q r u v w u' v' w' dst1 dst2 dst3 dst4, 
  Combine p u (Combine q v dst1 dst2) (Combine r w dst3 dst4) == 
  Combine (p*q + (1-p)*r) u' 
                        (Combine ((p*q)/(p*q + (1-p)*r)) v' dst1 dst3) 
                        (Combine (p*(1-q)/ (1 - (p*q + (1-p)*r))) w' dst2 dst4).
Proof.
  unfold dst_equiv; intros.
  simpl.
  unfold Rdiv.
  rewrite ! Rmult_plus_distr_l.
  rewrite <- ! Rmult_assoc.
  rewrite <- ! Rplus_assoc.
  assert (H: (p * q + (1 - p) * r) * p * q * / (p * q + (1 - p) * r) = p * q).
    rewrite Rmult_comm.
    rewrite <- ! Rmult_assoc.
    rewrite <- Rinv_l_sym; lra.
  rewrite H. clear H.
  assert (H: (1 - (p * q + (1 - p) * r)) * p * (1 - q) * / (1 - (p * q + (1 - p) * r)) = p * (1-q)).
    rewrite Rmult_comm.
    rewrite <- ! Rmult_assoc.
    rewrite <- Rinv_l_sym; lra.
  rewrite H. clear H.
  assert (H: (p * q + (1 - p) * r) * (1 - p * q * / (p * q + (1 - p) * r)) = (1-p) * r).
    unfold Rminus.    
    rewrite ! Rmult_plus_distr_l.
    rewrite Rmult_1_r.
    rewrite <- ! Ropp_mult_distr_l_reverse.
    rewrite <- ! Rmult_assoc.
    rewrite Rmult_comm with (r2:=/ (p * q + (1 + - p) * r)).
    rewrite <- ! Rmult_assoc.
    rewrite <- Rinv_l_sym; lra.
  rewrite H. clear H.
  assert(H: (1 - (p * q + (1 - p) * r)) *
  (1 - p * (1 - q) * / (1 - (p * q + (1 - p) * r))) = (1-p)*(1-r)).
    unfold Rminus.    
    rewrite ! Rmult_plus_distr_l.
    rewrite Rmult_1_r.
    rewrite <- ! Ropp_mult_distr_l_reverse.
    rewrite <- ! Rmult_assoc.
    rewrite Rinv_r_simpl_m; lra.
  rewrite H. clear H.
  lra.
Qed.    

(** Updating at the root or leaves is equivalent *)
Lemma prob_update_equiv : forall dst x p v,
  prob_update dst x p v == 
  Combine p v (dist_update dst x (ANum 1)) (dist_update dst x (ANum 0)).
Proof.
  unfold dst_equiv; simpl.
  intros.
  induction dst.
  + simpl. reflexivity.
  + simpl.
    rewrite IHdst1, IHdst2.
    lra.
Qed.  

Lemma prob_update_b_equiv : forall dst y p v,
  prob_update_b dst y p v == 
  Combine p v (dist_update_b dst y BTrue) (dist_update_b dst y BFalse).
Proof.
  unfold dst_equiv; simpl.
  intros.
  induction dst.
  + simpl. reflexivity.
  + simpl.
    rewrite IHdst1, IHdst2.
    lra.
Qed.  

(** We can equivalently define dst_equiv over assertions, rather than probabilities. *)
Definition dst_equiv_hexp (dst dst': dstate) : Prop :=
  forall P, heval dst P <-> heval dst' P.

Theorem dst_equiv_iff : forall dst dst',
   dst_equiv dst dst' <-> dst_equiv_hexp dst dst'.
Proof.
  split; intros.
  + induction P; simpl in *; try solve [rewrite H; reflexivity].
    - rewrite IHP1, IHP2.
      reflexivity.
    - rewrite IHP1, IHP2.
      reflexivity.
  + unfold dst_equiv.
    intros.
    destruct H with (P:=(HEq b (Prb b in dst'))) as [ignore solution].
    apply solution.
    reflexivity.
Qed.

Theorem dst_comm_hexp : forall dst1 dst2 p v v',
  dst_equiv_hexp (Combine p v dst1 dst2) (Combine (1-p) v' dst2 dst1).
Proof.
  intros.
  apply dst_equiv_iff.
  apply dst_comm.
Qed.

(** ** The Hoare Skip Rule *)

Theorem hoare_skip : forall P,
     {{P}} Skip {{P}}.
Proof.
  intros P dst dst' step pre.
  apply skip_equiv in step.
  subst.
  assumption.
Qed.

(** ** The Hoare Sequence Rule *)

Theorem hoare_seq : forall P Q R c1 c2,
     {{P}} c1 {{Q}} ->
     {{Q}} c2 {{R}} ->
     {{P}} c1 ;  c2 {{R}}.
Proof.
  intros P Q R c1 c2 hoare1 hoare2 dst dst' step pre.
  apply seq_equiv in step.
  destruct step as (dst0 & step1 & step2).
  apply (hoare2 dst0 dst' step2). 
  apply (hoare1 dst dst0 step1 pre). 
Qed.


(** * Hoare Assignment **)

(** First, we substitute a for X thoughout an arithmetic expression. *)

Fixpoint aexp_sub x a ax {struct ax} : aexp :=
  match ax with
  | ANum n => ANum n
  | AId x' => if beq_aid x x' then a else AId x'
  | APlus a1 a2 => APlus (aexp_sub x a a1) (aexp_sub x a a2)
  | AMinus a1 a2  => AMinus (aexp_sub x a a1) (aexp_sub x a a2)
  | AMult a1 a2 => AMult (aexp_sub x a a1) (aexp_sub x a a2)
  end.

Fixpoint bexp_sub x a bx {struct bx} : bexp :=
  match bx with
  | BTrue       => BTrue
  | BFalse      => BFalse
  | BId y       => BId y
  | BEq a1 a2   => BEq (aexp_sub x a a1) (aexp_sub x a a2)
  | BLe a1 a2   => BLe (aexp_sub x a a1) (aexp_sub x a a2)
  | BNot b1     => BNot (bexp_sub x a b1)
  | BAnd b1 b2  => BAnd (bexp_sub x a b1) (bexp_sub x a b2)
  end.

Fixpoint hexp_sub x a hx {struct hx} : hexp := 
  match hx with
  | HEq b p => HEq (bexp_sub x a b) p
  | HLt b p => HLt (bexp_sub x a b) p
  | HGt b p => HGt (bexp_sub x a b) p 
  | HAnd h1 h2 => HAnd (hexp_sub x a h1) (hexp_sub x a h2)
  | HOr h1 h2 => HOr (hexp_sub x a h1) (hexp_sub x a h2)
  end.

Theorem a_sub_eq : forall x a ax st, 
  aeval (aexp_sub x a ax) st = aeval ax (update st x (aeval a st)).
Proof.
  intros.
  generalize dependent ax.
  induction a.
  + simpl.
    induction ax.
    - simpl. reflexivity.
    - simpl. 
      unfold update.
      destruct (beq_aid x a).
      reflexivity.
      reflexivity.
    - simpl in *. rewrite IHax1. rewrite IHax2. reflexivity.
    - simpl in *. rewrite IHax1. rewrite IHax2. reflexivity.
    - simpl in *. rewrite IHax1. rewrite IHax2. reflexivity.
  + induction ax; try (solve [simpl; rewrite IHax1; rewrite IHax2; reflexivity]).
    - simpl. reflexivity.
    - simpl. 
      unfold update.
      destruct (beq_aid x a0).
      reflexivity.
      reflexivity.
  + induction ax; try (solve [simpl; rewrite IHax1; rewrite IHax2; reflexivity]).
    - simpl. reflexivity.
    - simpl in *. 
      destruct (beq_aid x a) eqn:eq; trivial.
  + induction ax; try (solve [simpl; rewrite IHax1; rewrite IHax2; reflexivity]).
    - simpl. reflexivity.
    - simpl in *. 
      destruct (beq_aid x a) eqn:eq; trivial.
  + induction ax; try (solve [simpl; rewrite IHax1; rewrite IHax2; reflexivity]).
    - simpl. reflexivity.
    - simpl in *. 
      destruct (beq_aid x a) eqn:eq; trivial.
Qed.

Theorem b_sub_eq : forall x a bx st, 
  beval (bexp_sub x a bx) st = beval bx (update st x (aeval a st)).
Proof.
  intros.
  induction bx; simpl; trivial.
  + rewrite 2 a_sub_eq; reflexivity.
  + rewrite 2 a_sub_eq; reflexivity.
  + rewrite IHbx; reflexivity.
  + rewrite IHbx1, IHbx2; reflexivity.
Qed.

Lemma pr_sub: forall x a b dst,
  Prb bexp_sub x a b in dst = Prb b in dist_update dst x a.
Proof.
  intros.
  induction dst.
  + simpl. rewrite b_sub_eq. reflexivity.
  + simpl in *. rewrite IHdst1, IHdst2. reflexivity.
Qed.

Theorem h_sub_eq : forall x a hx dst, 
  heval dst (hexp_sub x a hx) = 
  heval (dist_update dst x a) hx.
Proof.
  intros.
  induction hx.
  +  induction dst; simpl.
     - rewrite b_sub_eq; reflexivity.
     - rewrite 2 pr_sub; reflexivity.
  +  induction dst; simpl.
     - rewrite b_sub_eq; reflexivity.
     - rewrite 2 pr_sub; reflexivity.
  +  induction dst; simpl.
     - rewrite b_sub_eq; reflexivity.
     - rewrite 2 pr_sub; reflexivity.
  + simpl. rewrite IHhx1, IHhx2. reflexivity.
  + simpl. rewrite IHhx1, IHhx2. reflexivity.
Qed.  

(** ** The Hoare Assignment Rule *)

Theorem hoare_asgn : forall Q x a,
  {{hexp_sub x a Q}} (x ::= a) {{Q}}.
Proof.
  intros Q x a dst dst' step pre.
  apply assign_equiv in step.
  subst.
  rewrite <- h_sub_eq.
  assumption.
Qed.

(** The Related Equivalence Rule *)

Lemma update_equiv : forall dst1 dst2 x n,
  dst_equiv dst1 dst2 ->
  dst_equiv (dist_update dst1 x n) (dist_update dst2 x n).
Proof.
  intros.
  rewrite dst_equiv_iff in *.
  unfold dst_equiv_hexp.
  intros.
  rewrite <- 2 h_sub_eq.
  apply H.
Qed.

(** * Boolean Assignment 
      This follows the same structure as above *)

Fixpoint bexp_sub_b y b bx {struct bx} : bexp :=
  match bx with
  | BTrue       => BTrue
  | BFalse      => BFalse
  | BId y'      => if beq_bid y y' then b else BId y'
  | BEq a1 a2   => BEq a1 a2
  | BLe a1 a2   => BLe a1 a2
  | BNot b1     => BNot (bexp_sub_b y b b1)
  | BAnd b1 b2  => BAnd (bexp_sub_b y b b1) (bexp_sub_b y b b2)
  end.

Fixpoint hexp_sub_b y b hx {struct hx} : hexp := 
  match hx with
  | HEq b' p => HEq (bexp_sub_b y b b') p
  | HLt b' p => HLt (bexp_sub_b y b b') p
  | HGt b' p => HGt (bexp_sub_b y b b') p 
  | HAnd h1 h2 => HAnd (hexp_sub_b y b h1) (hexp_sub_b y b h2)
  | HOr h1 h2 => HOr (hexp_sub_b y b h1) (hexp_sub_b y b h2)
  end.

Theorem b_sub_eq_b : forall y b bx st, 
  beval (bexp_sub_b y b bx) st = beval bx (update_b st y (beval b st)).
Proof.
  intros.
  induction bx; simpl; trivial.
  + destruct (beq_bid y b0); trivial.
  + rewrite 2 update_non_interference; reflexivity.
  + rewrite 2 update_non_interference; reflexivity.
  + rewrite IHbx; reflexivity.
  + rewrite IHbx1, IHbx2; reflexivity.
Qed.    

Lemma pr_sub_b: forall y b bx dst,
  Prb bexp_sub_b y b bx in dst = Prb bx in dist_update_b dst y b.
Proof.
  intros.
  induction dst.
  + simpl; rewrite b_sub_eq_b; reflexivity.
  + simpl in *; rewrite IHdst1, IHdst2; reflexivity.
Qed.

Theorem h_sub_eq_b : forall y b hx dst, 
  heval dst (hexp_sub_b y b hx) = 
  heval (dist_update_b dst y b) hx.
Proof.
  intros.
  induction hx.
  +  induction dst; simpl.
     - rewrite b_sub_eq_b; reflexivity.
     - rewrite 2 pr_sub_b; reflexivity.
  +  induction dst; simpl.
     - rewrite b_sub_eq_b; reflexivity.
     - rewrite 2 pr_sub_b; reflexivity.
  +  induction dst; simpl.
     - rewrite b_sub_eq_b; reflexivity.
     - rewrite 2 pr_sub_b; reflexivity.
  + simpl. rewrite IHhx1, IHhx2. reflexivity.
  + simpl. rewrite IHhx1, IHhx2. reflexivity.
Qed.

(** ** The Hoare Boolean Assignment Rule *)

Theorem hoare_asgn_b : forall Q y b,
  {{hexp_sub_b y b Q}} (y :== b) {{Q}}.
Proof.
  intros Q y b dst dst' step pre.
  apply bassign_equiv in step.
  subst.
  rewrite <- h_sub_eq_b.
  assumption.
Qed.

(** The Related Equivalence Rule *)

Lemma update_equiv_b : forall dst1 dst2 y b,
  dst_equiv dst1 dst2 ->
  dst_equiv (dist_update_b dst1 y b) (dist_update_b dst2 y b).
Proof.
  intros.
  rewrite dst_equiv_iff in *.
  unfold dst_equiv_hexp.
  intros.
  rewrite <- 2 h_sub_eq_b.
  apply H.
Qed.

    
(** * Hoare Toss *)

(** ** Hoare Toss Preliminaries: X-freeness

    Let's introduce the idea of X-freeness - a given variable appears nowhere 
    in our Hoare Assertions  *)

Inductive ax_id_free: aexp -> aid -> Prop := 
  | Af_num : forall n x, ax_id_free (ANum n) x
  | Af_id : forall x' x, x<>x' -> ax_id_free (AId x') x
  | Af_plus : forall a1 a2 x, 
              ax_id_free a1 x -> ax_id_free a2 x -> ax_id_free (APlus a1 a2) x
  | Af_minus : forall a1 a2 x, 
              ax_id_free a1 x -> ax_id_free a2 x -> ax_id_free (AMinus a1 a2) x
  | Af_mult : forall a1 a2 x,
              ax_id_free a1 x -> ax_id_free a2 x -> ax_id_free (AMult a1 a2) x.

Inductive bx_id_free: bexp -> aid -> Prop := 
  | Bf_true : forall x, bx_id_free BTrue x
  | Bf_false : forall x, bx_id_free BFalse x
  | Bf_id : forall y x, bx_id_free (BId y) x
  | Bf_eq : forall a1 a2 x, 
              ax_id_free a1 x -> ax_id_free a2 x -> bx_id_free (BEq a1 a2) x
  | Bf_le : forall a1 a2 x, 
              ax_id_free a1 x -> ax_id_free a2 x -> bx_id_free (BLe a1 a2) x
  | Bf_not: forall b x, bx_id_free b x -> bx_id_free (BNot b) x
  | Bf_and : forall b1 b2 x, 
             bx_id_free b1 x -> bx_id_free b2 x -> bx_id_free (BAnd b1 b2) x.

Inductive hx_id_free: hexp -> aid -> Prop := 
  | Hf_eq : forall b p x, bx_id_free b x -> hx_id_free (HEq b p) x
  | Hf_lt : forall b p x, bx_id_free b x -> hx_id_free (HLt b p) x
  | Hf_gt : forall b p x, bx_id_free b x -> hx_id_free (HGt b p) x
  | Hf_and : forall h1 h2 x, 
             hx_id_free h1 x -> hx_id_free h2 x -> hx_id_free (HAnd h1 h2) x
  | Hf_or : forall h1 h2 x, 
             hx_id_free h1 x -> hx_id_free h2 x -> hx_id_free (HOr h1 h2) x.   


(** This wind up being a useful weaker notion of freeness that allows us to use
   earlier results relating to variable substitution. *)

Definition free (Q : hexp) (x : aid) : Prop := forall a, hexp_sub x a Q = Q.

(** We need to show that the weaker form follows from the stronger one. *)

Lemma a_free_eq: forall a x ax, 
  ax_id_free ax x -> aexp_sub x a ax = ax.
Proof.
  intros.  
  induction H; simpl.
  + reflexivity.
  + apply beq_aid_false_iff in H. 
    rewrite H; reflexivity.
  + rewrite IHax_id_free1, IHax_id_free2; reflexivity.
  + rewrite IHax_id_free1, IHax_id_free2; reflexivity.
  + rewrite IHax_id_free1, IHax_id_free2; reflexivity.
Qed.

Lemma b_free_eq: forall a x bx, 
  bx_id_free bx x -> bexp_sub x a bx = bx.
Proof.
  intros.  
  induction H; simpl; trivial.
  + eapply a_free_eq in H. 
    eapply a_free_eq in H0.    
    rewrite H, H0. reflexivity.
  + eapply a_free_eq in H. 
    eapply a_free_eq in H0.    
    rewrite H, H0. reflexivity.
  + rewrite IHbx_id_free. reflexivity.
  + rewrite IHbx_id_free1, IHbx_id_free2. reflexivity.
Qed.

(** These two implication of the above will prove useful shortly. *)

Lemma a_free_imp : forall a x st n,
  ax_id_free a x ->
  aeval a (update st x n) = aeval a st. 
Proof.
  intros.  
  apply a_free_eq with (a:=ANum n) in H.
  replace n with (aeval (ANum n) st) by reflexivity.
  rewrite <- a_sub_eq.
  rewrite H.
  reflexivity.
Qed.  

Lemma b_free_imp : forall b x st n,
  bx_id_free b x ->
  beval b (update st x n) = beval b st. 
Proof.
  intros.  
  apply b_free_eq with (a:=ANum n) in H.
  replace n with (aeval (ANum n) st) by reflexivity.
  rewrite <- b_sub_eq.
  rewrite H.
  reflexivity.
Qed.

Lemma free_eq: forall Q x, 
  hx_id_free Q x -> free Q x.
Proof.
  unfold free.
  intros.
  induction H; simpl.
  + eapply b_free_eq in H. 
    rewrite H. reflexivity.
  + eapply b_free_eq in H. 
    rewrite H. reflexivity.
  + eapply b_free_eq in H. 
    rewrite H. reflexivity.
  + rewrite IHhx_id_free1, IHhx_id_free2. reflexivity.
  + rewrite IHhx_id_free1, IHhx_id_free2. reflexivity.
Qed.

(** A simple consequence of freeness and the hoare_assignment rule : *)

Lemma hoare_asgn_free : forall Q x a, 
  free Q x ->
  {{ Q }} (x ::= a) {{ Q }}.
Proof.
  intros Q x a freeQ dst dst' step pre.
  apply assign_equiv in step.
  subst.
  rewrite <- h_sub_eq.
  unfold free in freeQ.
  rewrite freeQ.
  assumption.
Qed.

(** Conditionals allow us to insert boolean expressions throughout our assertions *)

Fixpoint bicondition01 (hx:hexp) (x:aid) (p:R) : hexp :=
  match hx with
  | HEq b p'   =>  HAnd (HEq (BAnd b (BEq (AId x) (ANum 1%nat))) (p*p')) 
                        (HEq (BAnd b (BEq (AId x) (ANum 0%nat))) ((1-p)*p'))
  | HLt b p'   =>  HAnd (HLt (BAnd b (BEq (AId x) (ANum 1%nat))) (p*p')) 
                        (HLt (BAnd b (BEq (AId x) (ANum 0%nat))) ((1-p)*p'))
  | HGt b p'   =>  HAnd (HGt (BAnd b (BEq (AId x) (ANum 1%nat))) (p*p')) 
                        (HGt (BAnd b (BEq (AId x) (ANum 0%nat))) ((1-p)*p'))
  | HAnd P1 P2 => HAnd (bicondition01 P1 x p) (bicondition01 P2 x p)
  | HOr P1 P2  => HOr (bicondition01 P1 x p) (bicondition01 P2 x p)
end.    

(** Independence rules for tossing a free variable *)

Lemma prob_update_1 : forall dst x b r p v,
  bx_id_free b x ->
  Prb b in dst = r ->
  Prb BAnd b (BEq (AId x) (ANum 1)) in prob_update dst x p v = p * r.
Proof.
  intros.
  generalize dependent r.
  induction dst.
  intros.
  + simpl in *.
    apply b_free_eq with (a := ANum 1) in H. 
    replace 1%nat with (aeval (ANum 1%nat) t) by reflexivity.
    rewrite <- b_sub_eq.
    rewrite H.
    simpl. 
    rewrite beq_aid_refl.
    rewrite <- beq_nat_refl.
    simpl.
    rewrite andb_true_r.
    rewrite andb_false_r.
    rewrite H0.
    lra.
  + intros.
    simpl in *.
    erewrite IHdst1 by reflexivity.
    erewrite IHdst2 by reflexivity.
    rewrite <- 2 Rmult_assoc.
    rewrite Rmult_comm with (r1:=p0) (r2:=p).
    rewrite Rmult_comm with (r1:=(1-p0)) (r2:=p).
    rewrite 2 Rmult_assoc.
    rewrite <- Rmult_plus_distr_l.
    rewrite H0.
    reflexivity.    
Qed.

Lemma prob_update_0 : forall dst x b r p v,
  bx_id_free b x ->
  Prb b in dst = r ->
  Prb BAnd b (BEq (AId x) (ANum 0)) in prob_update dst x p v = (1-p) * r.
Proof.
  intros.
  generalize dependent r.
  induction dst.
  intros.
  + simpl in *.
    apply b_free_eq with (a := ANum 0) in H. 
    replace 0%nat with (aeval (ANum 0%nat) t) by reflexivity.
    rewrite <- b_sub_eq.
    rewrite H.
    simpl. 
    rewrite beq_aid_refl.
    rewrite <- beq_nat_refl.
    simpl.
    rewrite andb_true_r.
    rewrite andb_false_r.
    rewrite H0.
    lra.
  + intros.
    simpl in *.
    erewrite IHdst1 by reflexivity.
    erewrite IHdst2 by reflexivity.
    rewrite <- 2 Rmult_assoc.
    rewrite Rmult_comm with (r1:=p0) (r2:=(1-p)).
    rewrite Rmult_comm with (r1:=(1-p0)) (r2:=(1-p)).
    rewrite 2 Rmult_assoc.
    rewrite <- Rmult_plus_distr_l.
    rewrite H0.
    reflexivity.    
Qed.

(** ** The Hoare Toss Rule *)

Theorem hoare_toss : forall Q x p v, hx_id_free Q x ->
  {{ Q }} x $=(p,v) {{ bicondition01 Q x p }}.
Proof.
  intros Q x p v hfQ dst dst' step pre.
  apply toss_equiv in step; subst.
  specialize (prob_update_0 dst x). intros pu0.
  specialize (prob_update_1 dst x). intros pu1.
  induction Q.
  + simpl in *.  
    inversion hfQ; subst.
    rewrite pu0 with (r:=(Prb b in dst)); trivial.
    rewrite pu1 with (r:=(Prb b in dst)); trivial.
    split; reflexivity.
  + simpl in *.  
    inversion hfQ; subst.
    rewrite pu0 with (r:=(Prb b in dst)); trivial.
    rewrite pu1 with (r:=(Prb b in dst)); trivial.
    split; apply Rmult_lt_compat_l; trivial; lra. 
  + simpl in *.  
    inversion hfQ; subst.
    rewrite pu0 with (r:=(Prb b in dst)); trivial.
    rewrite pu1 with (r:=(Prb b in dst)); trivial.
    split; apply Rmult_gt_compat_l; trivial; lra.
  + simpl.
    inversion hfQ; subst.
    destruct pre.
    split.
    apply IHQ1; assumption.
    apply IHQ2; assumption.
  + simpl.
    inversion hfQ; subst.
    destruct pre.
    left. apply IHQ1; assumption.
    right. apply IHQ2; assumption.
Qed.

(** * BToss *)

(** This follows the same structure as above - though the boolean coin toss 
    operation is the important one in this case. *)

Inductive bx_bid_free: bexp -> bid -> Prop := 
  | Bf_true_b : forall y, bx_bid_free BTrue y
  | Bf_false_b : forall y, bx_bid_free BFalse y
  | Bf_id_b : forall y' y, y<>y' -> bx_bid_free (BId y') y  
  | Bf_eq_b : forall a1 a2 y, bx_bid_free (BEq a1 a2) y
  | Bf_le_b : forall a1 a2 y, bx_bid_free (BLe a1 a2) y
  | Bf_not_b: forall b y, bx_bid_free b y -> bx_bid_free (BNot b) y
  | Bf_and_b : forall b1 b2 y, 
             bx_bid_free b1 y -> bx_bid_free b2 y -> bx_bid_free (BAnd b1 b2) y.

Inductive hx_bid_free: hexp -> bid -> Prop := 
  | Hf_eq_b : forall b p y, bx_bid_free b y -> hx_bid_free (HEq b p) y
  | Hf_lt_b : forall b p y, bx_bid_free b y -> hx_bid_free (HLt b p) y
  | Hf_gt_b : forall b p y, bx_bid_free b y -> hx_bid_free (HGt b p) y
  | Hf_and_b: forall h1 h2 y, 
             hx_bid_free h1 y -> hx_bid_free h2 y -> hx_bid_free (HAnd h1 h2) y
  | Hf_or_b : forall h1 h2 y, 
             hx_bid_free h1 y -> hx_bid_free h2 y -> hx_bid_free (HOr h1 h2) y.   

Definition free_b (Q : hexp) (y : bid) : Prop := forall b, hexp_sub_b y b Q = Q.

Lemma b_free_eq_b: forall y b bx, 
  bx_bid_free bx y -> bexp_sub_b y b bx = bx.
Proof.
  intros.  
  induction H; simpl; trivial.
  + apply beq_bid_false_iff in H.
    rewrite H; reflexivity.
  + rewrite IHbx_bid_free. reflexivity.
  + rewrite IHbx_bid_free1, IHbx_bid_free2. reflexivity.
Qed.

Lemma b_free_imp_b : forall bx y st b,
  bx_bid_free bx y ->
  beval bx (update_b st y b) = beval bx st. 
Proof.
  intros.  
  induction H; simpl; trivial.
  + apply beq_bid_false_iff in H.
    rewrite H; reflexivity.
  + rewrite 2 update_non_interference.
    reflexivity.
  + rewrite 2 update_non_interference.
    reflexivity.
  + rewrite IHbx_bid_free; reflexivity.
  + rewrite IHbx_bid_free1, IHbx_bid_free2; reflexivity.
Qed.

Lemma free_eq_b: forall Q x, 
  hx_bid_free Q x -> free_b Q x.
Proof.
  unfold free_b.
  intros.
  induction H; simpl.
  + eapply b_free_eq_b in H. 
    rewrite H. reflexivity.
  + eapply b_free_eq_b in H. 
    rewrite H. reflexivity.
  + eapply b_free_eq_b in H. 
    rewrite H. reflexivity.
  + rewrite IHhx_bid_free1, IHhx_bid_free2. reflexivity.
  + rewrite IHhx_bid_free1, IHhx_bid_free2. reflexivity.
Qed.

Lemma hoare_asgn_free_b : forall Q y b, 
  free_b Q y ->
  {{ Q }} (y :== b) {{ Q }}.
Proof.
  intros Q y b frQ dst dst' step pre.
  apply bassign_equiv in step; subst.
  rewrite <- h_sub_eq_b.
  unfold free_b in frQ.
  rewrite frQ.
  assumption.
Qed.

Fixpoint bicondition_b (hx:hexp) (y:bid) (p:R) : hexp :=
  match hx with
  | HEq b p'   =>  HAnd (HEq (BAnd b (BId y)) (p*p')) 
                        (HEq (BAnd b (BNot (BId y))) ((1-p)*p'))
  | HLt b p'   =>  HAnd (HLt (BAnd b (BId y)) (p*p')) 
                        (HLt (BAnd b (BNot (BId y))) ((1-p)*p'))
  | HGt b p'   =>  HAnd (HGt (BAnd b (BId y)) (p*p')) 
                        (HGt (BAnd b (BNot (BId y))) ((1-p)*p'))
  | HAnd P1 P2 => HAnd (bicondition_b P1 y p) (bicondition_b P2 y p)
  | HOr P1 P2  => HOr (bicondition_b P1 y p) (bicondition_b P2 y p)
end.    

Lemma prob_update_T : forall dst y b r p v,
  bx_bid_free b y ->
  Prb b in dst = r ->
  Prb BAnd b (BId y) in prob_update_b dst y p v = p * r.
Proof.
  intros.
  generalize dependent r.
  induction dst.
  intros.
  + simpl in *.
    apply b_free_eq_b with (b := BTrue) in H. 
    replace true with (beval BTrue t) by reflexivity.
    rewrite <- b_sub_eq_b.
    rewrite H.
    simpl. 
    rewrite beq_bid_refl.
    rewrite andb_true_r.
    rewrite andb_false_r.
    rewrite H0.
    lra.
  + intros.
    simpl in *.
    erewrite IHdst1 by reflexivity.
    erewrite IHdst2 by reflexivity.
    rewrite <- 2 Rmult_assoc. 
    rewrite Rmult_comm with (r1:=p0) (r2:=p).
    rewrite Rmult_comm with (r1:=(1-p0)) (r2:=p). 
    rewrite 2 Rmult_assoc. 
    rewrite <- Rmult_plus_distr_l. 
    rewrite H0.
    reflexivity.    
Qed.

Lemma prob_update_F : forall dst y b r p v,
  bx_bid_free b y ->
  Prb b in dst = r ->
  Prb BAnd b (BNot (BId y)) in prob_update_b dst y p v = (1 - p) * r.
Proof.
  intros.
  generalize dependent r.
  induction dst.
  intros.
  + simpl in *.
    apply b_free_eq_b with (b := BFalse) in H. 
    replace false with (beval BFalse t) by reflexivity.
    rewrite <- b_sub_eq_b.
    rewrite H.
    simpl. 
    rewrite beq_bid_refl.
    rewrite andb_true_r.
    rewrite andb_false_r.
    rewrite H0.
    lra.
  + intros.
    simpl in *.
    erewrite IHdst1 by reflexivity.
    erewrite IHdst2 by reflexivity.
    rewrite <- 2 Rmult_assoc. 
    rewrite Rmult_comm with (r1:=p0) (r2:=(1-p)).
    rewrite Rmult_comm with (r1:=(1-p0)) (r2:=(1-p)). 
    rewrite 2 Rmult_assoc. 
    rewrite <- Rmult_plus_distr_l. 
    rewrite H0.
    reflexivity.    
Qed.

(** ** The Boolean Toss Hoare Rule *)

Theorem hoare_toss_b : forall Q y p v, hx_bid_free Q y ->
  {{ Q }} y $=[p,v] {{ bicondition_b Q y p }}.
Proof.
  intros Q y p v hfQ dst dst' step pre.
  apply btoss_equiv in step; subst.
  specialize (prob_update_F dst y). intros pu0.
  specialize (prob_update_T dst y). intros pu1.
  induction Q.
  + simpl in *.  
    inversion hfQ; subst.
    rewrite pu0 with (r:=(Prb b in dst)); trivial.
    rewrite pu1 with (r:=(Prb b in dst)); trivial.
    split; reflexivity.
  + simpl in *.  
    inversion hfQ; subst.
    rewrite pu0 with (r:=(Prb b in dst)); trivial.
    rewrite pu1 with (r:=(Prb b in dst)); trivial.
    split; apply Rmult_lt_compat_l; trivial; lra. 
  + simpl in *.  
    inversion hfQ; subst.
    rewrite pu0 with (r:=(Prb b in dst)); trivial.
    rewrite pu1 with (r:=(Prb b in dst)); trivial.
    split; apply Rmult_gt_compat_l; trivial; lra.
  + simpl.
    inversion hfQ; subst.
    destruct pre.
    split.
    apply IHQ1; assumption.
    apply IHQ2; assumption.
  + simpl.
    inversion hfQ; subst.
    destruct pre.
    left. apply IHQ1; assumption.
    right. apply IHQ2; assumption.
Qed.

(** * If Statements *)

(** The traditional Hoare If rule:

                  {{P /\  b}} c1 {{Q}}
                  {{P /\ ~b}} c2 {{Q}}
          ------------------------------------  (traditional hoare if)
          {{P}} IF b THEN c1 ELSE c2 FI {{Q}} 


Our Deterministic If Rule

                  {{P /\  y}} c1 {{Q}}
                  {{P /\ ~y}} c2 {{Q}}
     ------------------------------------------------- (hoare_if_det)
     {{P /\ (y \/ ~y) }} IF y THEN c1 ELSE c2 FI {{Q}} 


Our Probabilistic If Rule

                            0  < p < 1
                         unassigned y c1 c2
                    {{1/p * P1}} c1 {{1/p * Q}}
                {{1/(1-p) * P2}} c2 {{1/(1-p) * Q}}
    -------------------------------------------------------------  (hoare_if_prob)
    {{Pr(y) = p /\ P /\ P2}} IF y THEN c1 ELSE c2 FI {{Q1 /\ Q2}} 

*)

(** Conditioning on a given boolean expression.
    In practice, we care about that boolean being an identifier. *)

Fixpoint condition (hx:hexp) (b':bexp) : hexp :=   
match hx with 
  | HEq b p     =>  HEq (BAnd b b') p
  | HLt b p     =>  HLt (BAnd b b') p
  | HGt b p     =>  HGt (BAnd b b') p
  | HAnd P1 P2  => HAnd (condition P1 b') (condition P2 b')
  | HOr P1 P2   => HOr  (condition P1 b') (condition P2 b')
end.

Definition conditionT hx y := condition hx (BId y).
Definition conditionF hx y := condition hx (BNot (BId y)).

Lemma condition_on_1 : forall P b dst, 
  Prb b in dst = 1 ->
  (heval dst P <-> heval dst (condition P b)).
Proof.
  intros.
  induction P; simpl.
  + rewrite pr_conj_1_r; trivial; reflexivity.
  + rewrite pr_conj_1_r; trivial; reflexivity.
  + rewrite pr_conj_1_r; trivial; reflexivity.
  + rewrite IHP1, IHP2. reflexivity.
  + rewrite IHP1, IHP2. reflexivity.
Qed.

Inductive unassigned: com -> bid -> Prop :=
  | Cf_skip_b' : forall y, unassigned Skip y
  | Cf_ass_b' : forall x a y, unassigned (x::=a) y
  | Cf_bass_b' : forall y' b y, y'<>y -> unassigned (y':== b) y
  | Cf_seq_b' : forall c1 c2 y,  
    unassigned c1 y ->  unassigned c2 y -> unassigned (c1 ; c2) y
  | Cf_if_b' : forall y' c1 c2 y,
    unassigned c1 y -> unassigned c2 y -> unassigned (If y' c1 c2) y
  | Cf_while_b' : forall y' c y, unassigned c y -> unassigned (While y' c) y
  | Cf_toss_b' : forall x p v y, unassigned (x $=(p,v)) y
  | Cf_btoss_b' : forall y' p v y, y'<>y -> unassigned (y' $=[p,v]) y.

Lemma probability_preserved : forall c dst dst' y,  
  unassigned c y ->
  c / dst || dst' ->
  Prb (BId y) in dst = Prb (BId y) in dst'.
Proof.
  intros c dst dst' y na step.
  induction step; trivial.
  + inversion na; subst.
    apply beq_bid_false_iff in H3.
    simpl.
    rewrite H3.
    reflexivity.
  + inversion na.
    rewrite IHstep1; trivial.
    rewrite IHstep2; trivial.
  + inversion na; subst.
    apply IHstep; trivial.
  + inversion na; subst.
    apply IHstep; trivial.
  + inversion na; subst.
    rewrite IHstep1; trivial.
    rewrite IHstep2; trivial.
  + simpl. lra. 
  + inversion na; subst.
    apply beq_bid_false_iff in H2.
    simpl.
    rewrite H2.
    lra.
  + simpl in *.
    rewrite IHstep2; trivial.
    rewrite IHstep1; trivial.
Qed.

(** Scaling Distributions *)

Fixpoint scale P a: hexp :=
  match P with
  | HEq b p => HEq b (a*p)
  | HLt b p => HLt b (a*p)
  | HGt b p => HGt b (a*p)
  | HAnd P1 P2 => HAnd (scale P1 a) (scale P2 a)
  | HOr P1 P2 => HOr (scale P1 a) (scale P2 a)
  end.

(** Lemma 7.2 *)
Lemma scale_equiv_1 : forall P dst1 dst0 b p v,
  Prb b in dst1 = 1 ->
  Prb b in dst0 = 0 ->
  (heval (Combine p v dst1 dst0) (condition P b) <-> heval dst1 (scale P (1/p))).
Proof.
  intros P dst1 dst0 b p v Pr1 Pr0.
  split; intros H.
  + induction P; simpl in *.
    - rewrite pr_conj_1_r in H; trivial.
      rewrite pr_conj_0_r in H; trivial.
      apply Rmult_eq_compat_l with (r:=(1/p)) in H.
      rewrite Rmult_0_r in H.
      rewrite Rplus_0_r in H.    
      unfold Rdiv in *.
      rewrite <- Rmult_assoc in H.
      rewrite Rmult_1_l in H.
      rewrite Rmult_comm with (r1:=/p) (r2:=p) in H.
      rewrite Rinv_r_simpl_r in H; lra.
    - rewrite pr_conj_1_r in H; trivial.
      rewrite pr_conj_0_r in H; trivial.
      apply Rmult_lt_compat_l with (r:=(1/p)) in H.
      rewrite Rmult_0_r in H.
      rewrite Rplus_0_r in H.    
      unfold Rdiv in *.
      rewrite <- Rmult_assoc in H.
      rewrite Rmult_1_l in H.
      rewrite Rmult_comm with (r1:=/p) (r2:=p) in H.
      rewrite Rinv_r_simpl_r in H; lra.    
      destruct v as [gt0 lt1].
      apply Rinv_0_lt_compat in gt0. lra. 
    - rewrite pr_conj_1_r in H; trivial.
      rewrite pr_conj_0_r in H; trivial.
      apply Rmult_gt_compat_l with (r:=(1/p)) in H.
      rewrite Rmult_0_r in H.
      rewrite Rplus_0_r in H.    
      unfold Rdiv in *.
      rewrite <- Rmult_assoc in H.
      rewrite Rmult_1_l in H.
      rewrite Rmult_comm with (r1:=/p) (r2:=p) in H.
      rewrite Rinv_r_simpl_r in H; lra.    
      destruct v as [gt0 lt1].
      apply Rinv_0_lt_compat in gt0. lra. 
    - destruct H as [H1 H2].
      specialize (IHP1 H1); specialize (IHP2 H2).
      split; assumption.
    - destruct H as [H1 | H2].
      specialize (IHP1 H1); left; assumption.
      specialize (IHP2 H2); right; assumption.
  + induction P; simpl in *.
    - rewrite pr_conj_1_r; trivial.
      rewrite pr_conj_0_r; trivial.
      rewrite Rmult_0_r.
      rewrite Rplus_0_r.    
      apply Rmult_eq_compat_l with (r:=p) in H.
      unfold Rdiv in *.
      rewrite Rmult_1_l in H.
      rewrite <- Rmult_assoc in H.
      rewrite Rinv_r_simpl_r in H; lra.
    - rewrite pr_conj_1_r; trivial.
      rewrite pr_conj_0_r; trivial.
      rewrite Rmult_0_r.
      rewrite Rplus_0_r.    
      apply Rmult_lt_compat_l with (r:=p) in H; try lra.
      unfold Rdiv in *.
      rewrite Rmult_1_l in H.
      rewrite <- Rmult_assoc in H.
      rewrite Rinv_r_simpl_r in H; lra.
    - rewrite pr_conj_1_r; trivial.
      rewrite pr_conj_0_r; trivial.
      rewrite Rmult_0_r.
      rewrite Rplus_0_r.    
      apply Rmult_gt_compat_l with (r:=p) in H; try lra.
      unfold Rdiv in *.
      rewrite Rmult_1_l in H.
      rewrite <- Rmult_assoc in H.
      rewrite Rinv_r_simpl_r in H; lra.
    - destruct H as [H1 H2].
      specialize (IHP1 H1); specialize (IHP2 H2).
      split; assumption.
    - destruct H as [H1 | H2].
      specialize (IHP1 H1); left; assumption.
      specialize (IHP2 H2); right; assumption.
Qed.

(** Lemma 7.3 *)
Lemma scale_equiv_0 : forall P dst1 dst0 b p v,
  Prb b in dst1 = 1 ->
  Prb b in dst0 = 0 ->
  (heval (Combine p v dst1 dst0) (condition P (BNot b)) <-> 
   heval dst0 (scale P (1/(1-p)))).
Proof.   
  intros P dst1 dst0 b p v Pr1 Pr0.
  specialize (one_minus_p p v). intros v'.
  specialize (dst_comm_hexp dst1 dst0 p v v'); intros equiv.
  apply prb_complement_0 in Pr0.
  apply prb_complement_1 in Pr1.    
  split; intros H.
  + apply equiv in H.
    apply scale_equiv_1 in H; trivial.
  + apply equiv.
    apply scale_equiv_1; trivial.
Qed.

Lemma scale_1 : forall P, scale P 1 = P.
Proof.
  intros P.
  induction P; simpl; try (rewrite Rmult_1_l; reflexivity).
  + rewrite IHP1, IHP2; reflexivity.
  + rewrite IHP1, IHP2; reflexivity.
Qed.


(** ** Lemma 7.1: Splitting Distributions

   For any distribution dst and proposition b,
   we can split dst into distributions dst1 and dst0 
   where b is true in dst1 and false in dst0. 

   This is crucial for the hoare logic rule for if statements.

   (The second version includes extra information about the equivalence,
    which should become unnecessary if we prove the general dst_equiv rule.)
*)

Theorem fork_on_b : forall dst b p v,
  Prb b in dst = p ->
  exists dst1 dst0, 
  Prb b in dst1 = 1 /\
  Prb b in dst0 = 0 /\ 
  dst_equiv dst (Combine p v dst1 dst0).
Proof. 
  induction dst as [st| q v0 dst1 IH1 dst2 IH2].
  + intros.
    simpl in *. 
    destruct (beval b st); lra.
  + intros.  
    specialize (@pr_normality state dst1 (beval b)). intros temp1.
    specialize (@pr_normality state dst2 (beval b)). intros temp2.    
    assert (i1:Prb b in dst1 = 0 \/ Prb b in dst1 = 1 \/ 0 < Prb b in dst1 < 1). lra.
    assert (i2:Prb b in dst2 = 0 \/ Prb b in dst2 = 1 \/ 0 < Prb b in dst2 < 1). lra.
    clear temp1 temp2.
    simpl in H. 
    destruct i1, i2; try destruct H0; try destruct H1. 
    (* 9 cases, many trivial. *)
    - rewrite H0, H1 in H; lra.
    - rewrite H0, H1 in H.
      assert (p=1-q) by lra. clear H.
      exists dst2, dst1. 
      split; try split; trivial.
      unfold dst_equiv; intros.
      subst.
      apply dst_comm.
    - destruct IH2 with (b:=b) (v:=H1) as [dst21].
      reflexivity.
      destruct H2 as [dst20].
      rewrite H0 in H.
      assert (p = (1-q) * (Prb b in dst2)) by lra.
      exists dst21.
      assert (p < 1 - q).
        apply mult_by_lt_1 with (c:=(Prb b in dst2)); lra. 
      assert (1 - (1 -q) < 1 - p).
        apply negation_flip; lra.
      assert (0 < q / (1-p) < 1) as v_new. 
        apply divide_by_lt; lra.
      clear IH1 IH2 H H4 H5.
      exists (Combine (q / (1-p)) v_new dst1 dst20).
      assert (Prb b in dst2 = p /(1-q)).
        rewrite Rmult_comm in H3.
        apply Rmult_eq_compat_r with (r:= /(1-q)) in H3.  
        rewrite Rmult_assoc in H3.
        rewrite Rinv_r in H3; lra.
      clear H3.
      destruct H2. destruct H3.
      split; try split.
      assumption.
      simpl.
      rewrite H0, H3. lra.
      unfold dst_equiv in *.
      simpl in *.
      intros.
      rewrite H4.
      rewrite H.
      rewrite 2 Rmult_plus_distr_l.
      unfold Rdiv.
      rewrite <- 6 Rmult_assoc.
      rewrite 2 Rinv_r_simpl_m; try lra.
      rewrite <- 2 Rplus_assoc.
      rewrite Rplus_comm with (r1:=p * (Prb b0 in dst21)).
      assert ((1 - q) * ((1 - p * / (1 - q))) = (1 - p) * ((1 - q * / (1 - p)))).
        unfold Rminus.
        rewrite 2 Rmult_plus_distr_l.
        rewrite 2 Rmult_1_r.
        rewrite <- 2 Ropp_mult_distr_l_reverse.
        rewrite <- 2 Rmult_assoc.
        rewrite 2 Rinv_r_simpl_m; try lra.          
      rewrite H5.
      reflexivity.
    - rewrite H0, H1 in H.
      assert (p=q) by lra. clear H.
      exists dst1, dst2. 
      split; try split; trivial.
      unfold dst_equiv; intros.
      subst.
      replace v with v0 by apply proof_irrelevance.
      reflexivity.
    - destruct IH1 with (b:=b) (v:=H0) as [dst11]. reflexivity.
      destruct H2 as [dst10].
      rewrite H1 in H.
      assert (p = q * (Prb b in dst1)) by lra.
      exists dst11.
      assert (p < q).
        apply mult_by_lt_1 with (c:=(Prb b in dst1)); lra. 
      assert (1 - q  < 1 - p).
        apply negation_flip; lra.
      assert (0 < (1-q) / (1-p) < 1) as v_new. 
        apply divide_by_lt; lra.
      clear IH1 IH2 H H4 H5.
      exists (Combine ((1-q) / (1-p)) v_new dst2 dst10).
      assert (Prb b in dst1 = p /q).
        rewrite Rmult_comm in H3.
        apply Rmult_eq_compat_r with (r:= /q) in H3.  
        rewrite Rmult_assoc in H3.
        rewrite Rinv_r in H3; lra.
      clear H3.
      destruct H2. destruct H3.
      split; try split.
      assumption.
      simpl.
      rewrite H1, H3. lra.
      unfold dst_equiv in *.
      simpl in *.
      intros.
      rewrite H4.
      rewrite H.
      rewrite 2 Rmult_plus_distr_l.
      unfold Rdiv.
      rewrite <- 6 Rmult_assoc.
      rewrite 2 Rinv_r_simpl_m; try lra.
      rewrite Rplus_comm with (r1:= (1-q) * (Prb b0 in dst2)).
      rewrite <- Rplus_assoc.
      assert (q * (1 - p */ q) = (1 - p) * (1 - (1 - q) */ (1 - p))).
        unfold Rminus.
        rewrite 2 Rmult_plus_distr_l.
        rewrite 2 Rmult_1_r.
        rewrite <- 2 Ropp_mult_distr_l_reverse.
        rewrite <- 2 Rmult_assoc.
        rewrite 2 Rinv_r_simpl_m; try lra.
      rewrite H5.
      reflexivity.
    - rewrite H0, H1 in H; lra.
    - destruct IH2 with (b:=b) (v:=H1) as [dst21]. reflexivity.
      destruct H2 as [dst20].
      rewrite H0 in H.
      assert (p = q + (1-q) * (Prb b in dst2)) by lra.
      assert (q < p). apply plus_by_gt_0 with (c:=(1 - q) * (Prb b in dst2)); 
        try lra.
        apply mult_stable; lra.
      assert (0 < q /p < 1) as v_new. 
        apply divide_by_lt; lra.
      clear IH1 IH2 H H4.
      exists (Combine (q / p) v_new dst1 dst21).
      exists dst20.
      assert (Prb b in dst2 = (p-q)/(1-q)).
        apply Rplus_eq_compat_l with (r:=-q) in H3.
        rewrite <- Rplus_assoc in H3.
        rewrite Rplus_opp_l in H3.
        rewrite Rplus_0_l in H3.
        apply Rmult_eq_compat_l with (r:= /(1-q)) in H3.  
        rewrite <- Rmult_assoc in H3.
        rewrite Rinv_l in H3; lra.
      clear H3.
      destruct H2. destruct H3.
      split; try split.
      simpl.
      rewrite H0, H2. lra.
      assumption.
      unfold dst_equiv in *.
      simpl in *.
      intros.
      rewrite H4.
      rewrite H.
      rewrite 2 Rmult_plus_distr_l.
      unfold Rdiv.
      rewrite <- 6 Rmult_assoc.
      rewrite 2 Rinv_r_simpl_m; try lra.
      rewrite <- Rplus_assoc.
      assert (p-q = p * (1-q */ p) ).
        unfold Rminus.
        rewrite Rmult_plus_distr_l.
        rewrite Rmult_1_r.
        unfold Rdiv.
        rewrite <- Ropp_mult_distr_l_reverse.
        rewrite <- Rmult_assoc.
        rewrite Rinv_r_simpl_m; try lra.
      assert ((1 - q) * (1 - (p - q) * / (1 - q)) = (1-p)).
        unfold Rminus.
        rewrite Rmult_plus_distr_l.
        rewrite Rmult_1_r.
        rewrite <- Ropp_mult_distr_l_reverse.
        rewrite <- Rmult_assoc.
        rewrite Rinv_r_simpl_m; try lra.
      rewrite H6.
      rewrite H5.
      reflexivity.
    - destruct IH1 with (b:=b) (v:=H0) as [dst11]. reflexivity.
      destruct H2 as [dst10].
      rewrite H1 in H.
      symmetry in H.
      rewrite Rmult_1_r in H.
      assert (1-q < p). apply plus_by_gt_0 with (c:= q * (Prb b in dst1)); try lra.
        apply mult_stable; lra. 
      assert (0 < (1-q)/p < 1) as v_new. 
        apply divide_by_lt; lra.
      clear IH1 IH2 H3.
      exists (Combine ((1-q) / p) v_new dst2 dst11).
      exists dst10.
      assert (Prb b in dst1 = (p+q-1)/q).
        rewrite <- Rplus_comm in H.
        apply Rplus_eq_compat_l with (r:=-(1-q)) in H.
        rewrite <- Rplus_assoc in H.
        rewrite Rplus_opp_l in H.
        rewrite Rplus_0_l in H.
        apply Rmult_eq_compat_r with (r:= /q) in H.  
        rewrite Rinv_r_simpl_m in H; try lra.
      clear H.
      destruct H2. destruct H2.
      split; try split.
      simpl.
      rewrite H, H1. lra.
      assumption.
      unfold dst_equiv in *.
      simpl in *.
      intros.
      rewrite H4.
      rewrite H3.
      rewrite 2 Rmult_plus_distr_l.
      unfold Rdiv.
      rewrite <- 6 Rmult_assoc.
      rewrite 2 Rinv_r_simpl_m; try lra.
      rewrite Rplus_comm.
      rewrite Rplus_assoc.
      assert ((p + q - 1) = (p * (1 - (1 - q) * / p))).
        unfold Rminus.
        rewrite Rmult_plus_distr_l.
        rewrite Rmult_1_r.
        rewrite <- Ropp_mult_distr_l_reverse.
        rewrite <- Rmult_assoc.
        rewrite Rinv_r_simpl_m; try lra.
      assert (q * (1 - (p + q - 1) * / q) = (1-p)).
        unfold Rminus. 
        rewrite Rmult_plus_distr_l.
        rewrite Rmult_1_r.
        rewrite <- Ropp_mult_distr_l_reverse.
        rewrite <- Rmult_assoc.
        rewrite Rinv_r_simpl_m; try lra.
      rewrite H6.
      rewrite H5.
      reflexivity.
    - remember (Prb b in dst1) as p1. 
      symmetry in Heqp1.
      remember (Prb b in dst2) as p2. 
      symmetry in Heqp2.
      destruct IH1 with (b:=b) (p:=p1) (v:=H0) as [dst11]. apply Heqp1.
      destruct IH2 with (b:=b) (p:=p2) (v:=H1) as [dst21]. apply Heqp2.
      destruct H2 as [dst10].
      destruct H3 as [dst20].
      clear IH1 IH2.
      remember H as v_p. clear Heqv_p. symmetry in v_p. 
      remember H as v_np. clear Heqv_np. symmetry in v_np.
      apply plus_by_gt_0 in v_p; try apply mult_stable; try lra.
      remember v_p as temp. clear Heqtemp.
      apply divide_by_lt in v_p; try apply mult_stable; try lra.
      apply Rplus_eq_compat_l with (r:=-(q*p1)) in v_np.
      rewrite <- Rplus_assoc in v_np.
      rewrite Rplus_opp_l in v_np.
      rewrite Rplus_0_l in v_np.
      assert (temp3:  - (q * p1)  + p < 1). 
        rewrite <- Rplus_0_l.
        apply Rplus_lt_compat. 
        apply Ropp_lt_gt_0_contravar. 
        apply Rmult_lt_0_compat; lra. lra.
      apply mult_by_lt_1 in v_np; try lra. (*here*)
      clear temp temp3.
      apply Rplus_lt_compat_l with (r:=(q*p1)) in v_np.
      rewrite <- Rplus_assoc in v_np.
      rewrite Rplus_opp_r in v_np.
      rewrite Rplus_0_l in v_np.
      apply Ropp_lt_contravar in v_np.
      apply Rplus_lt_compat_l with (r:=1) in v_np.
      assert ((1 - p1)*q < 1-p). lra.
      clear v_np. rename H4 into v_np.
      apply divide_by_lt in v_np; try apply mult_stable; try lra.
      exists (Combine (q*p1 / p) v_p dst11 dst21).
      exists (Combine ((1-p1)*q / (1-p)) v_np dst10 dst20).      
      destruct H2, H3. 
      destruct H4, H5.
      split; try split.
      simpl. rewrite H2, H3. lra.
      simpl. rewrite H4, H5. lra.
      unfold dst_equiv in *.
      simpl in *.
      intros.
      rewrite H6.
      rewrite H7.
      rewrite <- H.
      rewrite 4 Rmult_plus_distr_l.
      unfold Rminus.
      unfold Rdiv.
      rewrite <- 12 Rmult_assoc.
      assert ((q * p1 + (1 + - q) * p2) * q * p1 * / (q * p1 + (1 + - q) * p2)
                                                       = q * p1).
        rewrite Rmult_comm.
        rewrite <- 2 Rmult_assoc.
        rewrite Rinv_l; lra.
      rewrite H8. clear H8.
      assert(
          (q * p1 + (1 + - q) * p2) * (1 + - (q * p1 * / (q * p1 + (1 + - q) * p2)))
          = (1 + - q) * p2).
        rewrite Rmult_plus_distr_l.
        rewrite Rmult_1_r.
        rewrite Rmult_comm with (r1:=(q * p1 + (1 + - q) * p2)).
        rewrite Ropp_mult_distr_l_reverse.
        rewrite Rmult_assoc.
        rewrite Rinv_l; try lra.
      rewrite H8. clear H8.
      assert( ((1 + - (q * p1 + (1 + - q) * p2)) * (1 + - p1) * q * 
               / (1 + - (q * p1 + (1 + - q) * p2))) =  q * (1 + - p1)).
        rewrite Rmult_comm. 
        rewrite <- 2 Rmult_assoc.
        rewrite Rinv_l; try lra.
      rewrite H8. clear H8.
      assert( (1 + - (q * p1 + (1 + - q) * p2)) *
              (1 + - ((1 + - p1) * q * / (1 + - (q * p1 + (1 + - q) * p2)))) 
              = (1 + - q) * (1 + - p2)).
        rewrite Rmult_plus_distr_l.
        rewrite Rmult_1_r.
        rewrite Rmult_plus_distr_l.
        rewrite Rmult_1_r.
        rewrite <- 2 Ropp_mult_distr_l_reverse.
        rewrite <- 2 Rmult_assoc. 
        rewrite Rmult_comm with (r2:=/(1 + - (q * p1 + (1 + - q) * p2))).
        rewrite <- 2 Rmult_assoc. 
        rewrite Rinv_l; try lra.
      rewrite H8. clear H8.      
      lra.
Qed.


Theorem fork_on_b_plus : forall c dst dst' b p v,
  c / dst || dst' ->
  Prb b in dst = p ->
  exists dst1 dst0 dst'', 
  Prb b in dst1 = 1 /\
  Prb b in dst0 = 0 /\ 
  dst_equiv dst (Combine p v dst1 dst0) /\
  c / (Combine p v dst1 dst0) || dst'' /\ 
  dst_equiv dst' dst''.
Proof. 
  (* Note: Starred sections denote the proof of the two new conclusions *)
  induction dst as [st| q v0 dst1 IH1 dst2 IH2].
  + intros.
    simpl in *. 
    assert(False) as contra. destruct (beval b st); lra.
    contradiction.
  + intros dst' b p v com prob.  
    specialize (@pr_normality state dst1 (beval b)). intros temp1.
    specialize (@pr_normality state dst2 (beval b)). intros temp2.    
    assert (i1:Prb b in dst1 = 0 \/ Prb b in dst1 = 1 \/ 0 < Prb b in dst1 < 1). lra.
    assert (i2:Prb b in dst2 = 0 \/ Prb b in dst2 = 1 \/ 0 < Prb b in dst2 < 1). lra.
    clear temp1 temp2.
    simpl in prob. 
    destruct i1 as [Pr1 | d1], i2 as [Pr2 | d2]; 
      try destruct d1 as [Pr1 | v1]; try destruct d2 as [Pr2 | v2].
    (* 9 cases, many trivial. *)
    - assert(False) as contra. rewrite Pr1, Pr2 in prob; lra.
      contradiction.
    - apply step_split in com as (dst1' & dst2' & Eq & step1 & step2).
      rewrite Pr1, Pr2 in prob.
      replace (q * 0 + (1-q) * 1) with (1 - q) in prob by lra. 
      symmetry in prob.
      exists dst2, dst1, (Combine p v dst2' dst1').
      split; try split; try split; trivial.
      unfold dst_equiv; intros.
      subst.
      apply dst_comm.
      split.
      * constructor; assumption.
      * unfold dst_equiv.
        subst.
        apply dst_comm.
    - apply step_split in com as (dst1' & dst2' & Eq & step1 & step2).
      specialize (IH2 dst2' b (Prb b in dst2) v2 step2). 
      destruct IH2 as (dst21 & dst20 & dst'' & Pr21 & Pr20 & Eq2 & step' & Eq3).
      reflexivity.
      rewrite Pr1 in prob.
      rewrite Rmult_0_r in prob. rewrite Rplus_0_l in prob. symmetry in prob.
      assert (t1:p < 1 - q). apply mult_by_lt_1 with (c:=(Prb b in dst2)); lra. 
      assert (t2:1 - (1 -q) < 1 - p). apply negation_flip; lra.
      assert (0 < q / (1-p) < 1) as v_new. apply divide_by_lt; lra.
      clear t1 t2.
      exists dst21, (Combine (q / (1-p)) v_new dst1 dst20).
      assert (prob2: Prb b in dst2 = p /(1-q)).
        rewrite Rmult_comm in prob.
        apply Rmult_eq_compat_r with (r:= /(1-q)) in prob.  
        rewrite Rmult_assoc in prob.
        rewrite Rinv_r in prob; lra.
      clear prob. rename prob2 into prob.
      apply step_split in step' as (dst21' & dst20' & Eq1 & step21 & step22).
      exists (Combine p v dst21' (Combine (q / (1 - p)) v_new dst1' dst20')).
      split; try split; try split.
      assumption.
      simpl.
      rewrite Pr1, Pr20. lra.
      unfold dst_equiv in *.
      simpl in *.
      intros.
      rewrite Eq2.
      rewrite prob.
      rewrite 2 Rmult_plus_distr_l.
      unfold Rdiv.
      rewrite <- 6 Rmult_assoc.
      rewrite 2 Rinv_r_simpl_m; try lra.
      rewrite <- 2 Rplus_assoc.
      rewrite Rplus_comm with (r1:=p * (Prb b0 in dst21)).
      assert (H:(1 - q) * ((1 - p * / (1 - q))) = (1 - p) * ((1 - q * / (1 - p)))).
        unfold Rminus.
        rewrite 2 Rmult_plus_distr_l.
        rewrite 2 Rmult_1_r.
        rewrite <- 2 Ropp_mult_distr_l_reverse.
        rewrite <- 2 Rmult_assoc.
        rewrite 2 Rinv_r_simpl_m; try lra.          
      rewrite H.
      reflexivity.
      split.
      * constructor; trivial.
        constructor; trivial.
      *  unfold dst_equiv.
         subst.
         intros.
         simpl.
         rewrite Eq3.
         simpl.
         rewrite prob.
         rewrite 2 Rmult_plus_distr_l.
         unfold Rdiv.
         rewrite <- 6 Rmult_assoc.
         rewrite 2 Rinv_r_simpl_m; try lra.
         rewrite <- 2 Rplus_assoc.
         rewrite Rplus_comm with (r1:=p * (Prb b0 in dst21')).
         assert (H:(1 - q) * ((1 - p * / (1 - q))) = (1 - p)*((1 - q * / (1 - p)))).
           unfold Rminus.
           rewrite 2 Rmult_plus_distr_l.
           rewrite 2 Rmult_1_r.
           rewrite <- 2 Ropp_mult_distr_l_reverse.
           rewrite <- 2 Rmult_assoc.
           rewrite 2 Rinv_r_simpl_m; try lra.          
         rewrite H.
         reflexivity.
    - rewrite Pr1, Pr2 in prob.
      assert (t:p=q) by lra. clear prob. rename t into prob.
      exists dst1, dst2, dst'. 
      split; try split; try split; trivial.
      unfold dst_equiv; intros.
      subst.
      replace v with v0 by apply proof_irrelevance.
      reflexivity.
      split.
      * subst.
        replace v with v0 by apply proof_irrelevance.
        assumption.
      * apply dst_equiv_refl.
    - apply step_split in com.
      destruct com as [x1 com]. destruct com as [x2 com].
      destruct com as [Eq com]. destruct com as [com1 com2].
      destruct IH1 with (b:=b) (v:=v1) (dst':=x1) as [dst11]; trivial.
      destruct H as [dst10].
      rewrite Pr2 in prob.
      assert (p = q * (Prb b in dst1)) by lra.
      exists dst11.
      assert (p < q). apply mult_by_lt_1 with (c:=(Prb b in dst1)); lra. 
      assert (1 - q  < 1 - p). apply negation_flip; lra.
      assert (0 < (1-q) / (1-p) < 1) as v_new. apply divide_by_lt; lra.
      clear IH1 IH2 prob H1 H2.
      exists (Combine ((1-q) / (1-p)) v_new dst2 dst10).
      assert (Prb b in dst1 = p /q).
        rewrite Rmult_comm in H0.
        apply Rmult_eq_compat_r with (r:= /q) in H0.  
        rewrite Rmult_assoc in H0.
        rewrite Rinv_r in H0; lra.
      clear H0.
      destruct H as (dst'' & Pr11 & Pr10 & Eq1 & com & equiv).
      apply step_split in com.
      destruct com as [x11 com]. destruct com as [x10 com].
      destruct com as [Eq2 com]. destruct com as [com21 com20].
      exists (Combine p v x11 (Combine ((1 - q) / (1 - p)) v_new x2 x10)).      
      split; try split; try split.
      assumption.
      simpl.
      rewrite Pr2, Pr10. lra.
      unfold dst_equiv in *.
      simpl in *.
      intros.
      rewrite Eq1.
      rewrite H1.
      rewrite 2 Rmult_plus_distr_l.
      unfold Rdiv.
      rewrite <- 6 Rmult_assoc.
      rewrite 2 Rinv_r_simpl_m; try lra.
      rewrite Rplus_comm with (r1:= (1-q) * (Prb b0 in dst2)).
      rewrite <- Rplus_assoc.
      assert (q * (1 - p */ q) = (1 - p) * (1 - (1 - q) */ (1 - p))).
        unfold Rminus.
        rewrite 2 Rmult_plus_distr_l.
        rewrite 2 Rmult_1_r.
        rewrite <- 2 Ropp_mult_distr_l_reverse.
        rewrite <- 2 Rmult_assoc.
        rewrite 2 Rinv_r_simpl_m; try lra.
      rewrite H.
      reflexivity.
      split.
      * constructor; trivial.
        constructor; trivial.
      * unfold dst_equiv.
        subst.
        intros.
        simpl.
        rewrite equiv.
        simpl.
        rewrite H1.
        rewrite 2 Rmult_plus_distr_l.
        unfold Rdiv.
        rewrite <- 6 Rmult_assoc.
        rewrite 2 Rinv_r_simpl_m; try lra.
        rewrite Rplus_comm with (r1:= (1-q) * (Prb b0 in x2)).
        rewrite <- Rplus_assoc.
        assert (q * (1 - p */ q) = (1 - p) * (1 - (1 - q) */ (1 - p))).
          unfold Rminus.
          rewrite 2 Rmult_plus_distr_l.
          rewrite 2 Rmult_1_r.
          rewrite <- 2 Ropp_mult_distr_l_reverse.
          rewrite <- 2 Rmult_assoc.
          rewrite 2 Rinv_r_simpl_m; try lra.
        rewrite H.
        reflexivity.
    - assert(False) as contra. rewrite Pr1, Pr2 in prob; lra.
      contradiction.
    - rename prob into H, Pr1 into H0, v2 into H1.
      apply step_split in com.
      destruct com as [x1 com]. destruct com as [x2 com].
      destruct com as [Eq com]. destruct com as [com1 com2].
      destruct IH2 with (b:=b) (v:=H1) (dst':=x2) as [dst21]; trivial.
      destruct H2 as [dst20].
      rewrite H0 in H.
      assert (p = q + (1-q) * (Prb b in dst2)) by lra.
      assert (q < p). apply plus_by_gt_0 with (c:=(1 - q) * (Prb b in dst2)); 
        try lra. apply mult_stable; lra.
      assert (0 < q /p < 1) as v_new. apply divide_by_lt; lra.
      clear IH1 IH2 H H4.
      exists (Combine (q / p) v_new dst1 dst21).
      exists dst20.
      assert (Prb b in dst2 = (p-q)/(1-q)).
        apply Rplus_eq_compat_l with (r:=-q) in H3.
        rewrite <- Rplus_assoc in H3.
        rewrite Rplus_opp_l in H3.
        rewrite Rplus_0_l in H3.
        apply Rmult_eq_compat_l with (r:= /(1-q)) in H3.  
        rewrite <- Rmult_assoc in H3.
        rewrite Rinv_l in H3; lra.
      clear H3.
      destruct H2. destruct H2. destruct H3.
      destruct H4. destruct H5 as [com equiv].
      apply step_split in com.
      destruct com as [x21 com]. destruct com as [x20 com].
      destruct com as [Eq2 com]. destruct com as [com21 com20].
      exists (Combine p v (Combine (q / p) v_new x1 x21) x20).      
      split; try split; try split.
      simpl.
      rewrite H0, H2. lra.
      assumption.
      unfold dst_equiv in *.
      simpl in *.
      intros.
      rewrite H4.
      rewrite H.
      rewrite 2 Rmult_plus_distr_l.
      unfold Rdiv.
      rewrite <- 6 Rmult_assoc.
      rewrite 2 Rinv_r_simpl_m; try lra.
      rewrite <- Rplus_assoc.
      assert (p-q = p * (1-q */ p) ).
        unfold Rminus.
        rewrite Rmult_plus_distr_l.
        rewrite Rmult_1_r.
        unfold Rdiv.
        rewrite <- Ropp_mult_distr_l_reverse.
        rewrite <- Rmult_assoc.
        rewrite Rinv_r_simpl_m; try lra.
      assert ((1 - q) * (1 - (p - q) * / (1 - q)) = (1-p)).
        unfold Rminus.
        rewrite Rmult_plus_distr_l.
        rewrite Rmult_1_r.
        rewrite <- Ropp_mult_distr_l_reverse.
        rewrite <- Rmult_assoc.
        rewrite Rinv_r_simpl_m; try lra.
      rewrite H6.
      rewrite H5.
      reflexivity.
      split.
      * constructor; trivial.
        constructor; trivial.
      * unfold dst_equiv.
        subst.
        intros.
        simpl.
        rewrite equiv.
        simpl.
        rewrite H.
        rewrite 2 Rmult_plus_distr_l.
        unfold Rdiv.
        rewrite <- 6 Rmult_assoc.
        rewrite 2 Rinv_r_simpl_m; try lra.
        rewrite <- Rplus_assoc.
        assert (p-q = p * (1-q */ p) ).
          unfold Rminus.
          rewrite Rmult_plus_distr_l.
          rewrite Rmult_1_r.
          unfold Rdiv.
          rewrite <- Ropp_mult_distr_l_reverse.
          rewrite <- Rmult_assoc.
          rewrite Rinv_r_simpl_m; try lra.
        assert ((1 - q) * (1 - (p - q) * / (1 - q)) = (1-p)).
          unfold Rminus.
          rewrite Rmult_plus_distr_l.
          rewrite Rmult_1_r.
          rewrite <- Ropp_mult_distr_l_reverse.
          rewrite <- Rmult_assoc.
          rewrite Rinv_r_simpl_m; try lra.
        rewrite H6.
        rewrite H5.
        reflexivity.
    - rename prob into H, v1 into H0, Pr2 into H1.
      apply step_split in com.
      destruct com as [x1 com]. destruct com as [x2 com].
      destruct com as [Eq com]. destruct com as [com1 com2].
      destruct IH1 with (b:=b) (v:=H0) (dst':=x1) as [dst11]; trivial.
      destruct H2 as [dst10].
      rewrite H1 in H.
      symmetry in H.
      rewrite Rmult_1_r in H.
      assert (1-q < p). apply plus_by_gt_0 with (c:= q * (Prb b in dst1)); try lra.
        apply mult_stable; lra. 
      assert (0 < (1-q)/p < 1) as v_new. 
        apply divide_by_lt; lra.
      clear IH1 IH2 H3.
      exists (Combine ((1-q) / p) v_new dst2 dst11).
      exists dst10.
      assert (Prb b in dst1 = (p+q-1)/q).
        rewrite <- Rplus_comm in H.
        apply Rplus_eq_compat_l with (r:=-(1-q)) in H.
        rewrite <- Rplus_assoc in H.
        rewrite Rplus_opp_l in H.
        rewrite Rplus_0_l in H.
        apply Rmult_eq_compat_r with (r:= /q) in H.  
        rewrite Rinv_r_simpl_m in H; try lra.
      clear H.
      destruct H2. destruct H. destruct H2.
      destruct H4. destruct H5 as [com equiv].
      apply step_split in com.
      destruct com as [x11 com]. destruct com as [x10 com].
      destruct com as [Eq2 com]. destruct com as [com11 com10].
      exists (Combine p v (Combine ((1 - q) / p) v_new x2 x11) x10).
      split; try split; try split.
      simpl.
      rewrite H, H1. lra.
      assumption.
      unfold dst_equiv in *.
      simpl in *.
      intros.
      rewrite H4.
      rewrite H3.
      rewrite 2 Rmult_plus_distr_l.
      unfold Rdiv.
      rewrite <- 6 Rmult_assoc.
      rewrite 2 Rinv_r_simpl_m; try lra.
      rewrite Rplus_comm.
      rewrite Rplus_assoc.
      assert ((p + q - 1) = (p * (1 - (1 - q) * / p))).
        unfold Rminus.
        rewrite Rmult_plus_distr_l.
        rewrite Rmult_1_r.
        rewrite <- Ropp_mult_distr_l_reverse.
        rewrite <- Rmult_assoc.
        rewrite Rinv_r_simpl_m; try lra.
      assert (q * (1 - (p + q - 1) * / q) = (1-p)).
        unfold Rminus. 
        rewrite Rmult_plus_distr_l.
        rewrite Rmult_1_r.
        rewrite <- Ropp_mult_distr_l_reverse.
        rewrite <- Rmult_assoc.
        rewrite Rinv_r_simpl_m; try lra.
      rewrite H6.
      rewrite H5.
      reflexivity.
      split. 
      * constructor; trivial.
        constructor; trivial.
      * unfold dst_equiv.
        subst.
        intros.
        simpl.
        rewrite equiv.
        simpl.
        rewrite H3.
        rewrite 2 Rmult_plus_distr_l.
        unfold Rdiv.
        rewrite <- 6 Rmult_assoc.
        rewrite 2 Rinv_r_simpl_m; try lra.
        rewrite Rplus_comm.
        rewrite Rplus_assoc.
        assert ((p + q - 1) = (p * (1 - (1 - q) * / p))).
          unfold Rminus.
          rewrite Rmult_plus_distr_l.
          rewrite Rmult_1_r.
          rewrite <- Ropp_mult_distr_l_reverse.
          rewrite <- Rmult_assoc.
          rewrite Rinv_r_simpl_m; try lra.
        assert (q * (1 - (p + q - 1) * / q) = (1-p)).
          unfold Rminus. 
          rewrite Rmult_plus_distr_l.
          rewrite Rmult_1_r.
          rewrite <- Ropp_mult_distr_l_reverse.
          rewrite <- Rmult_assoc.
          rewrite Rinv_r_simpl_m; try lra.
        rewrite H6.
        rewrite H5.
        reflexivity.
    - rename prob into H, v1 into H0, v2 into H1.
      apply step_split in com.
      destruct com as [x1 com]. destruct com as [x2 com].
      destruct com as [Eq com]. destruct com as [com1 com2].
      remember (Prb b in dst1) as p1. 
      symmetry in Heqp1.
      remember (Prb b in dst2) as p2. 
      symmetry in Heqp2.
      destruct IH1 with (b:=b) (p:=p1) (v:=H0) (dst':=x1) as [dst11]; trivial.
      destruct IH2 with (b:=b) (p:=p2) (v:=H1) (dst':=x2) as [dst21]; trivial.
      destruct H2 as [dst10].
      destruct H3 as [dst20].
      clear IH1 IH2.
      remember H as v_p. clear Heqv_p. symmetry in v_p. 
      remember H as v_np. clear Heqv_np. symmetry in v_np.
      apply plus_by_gt_0 in v_p; try apply mult_stable; try lra.
      remember v_p as temp. clear Heqtemp.
      apply divide_by_lt in v_p; try apply mult_stable; try lra.
      apply Rplus_eq_compat_l with (r:=-(q*p1)) in v_np.
      rewrite <- Rplus_assoc in v_np.
      rewrite Rplus_opp_l in v_np.
      rewrite Rplus_0_l in v_np.
      assert (temp3:  - (q * p1)  + p < 1). 
        rewrite <- Rplus_0_l.
        apply Rplus_lt_compat. 
        apply Ropp_lt_gt_0_contravar. 
        apply Rmult_lt_0_compat; lra. lra.
      apply mult_by_lt_1 in v_np; try lra. (*here*)
      clear temp temp3.
      apply Rplus_lt_compat_l with (r:=(q*p1)) in v_np.
      rewrite <- Rplus_assoc in v_np.
      rewrite Rplus_opp_r in v_np.
      rewrite Rplus_0_l in v_np.
      apply Ropp_lt_contravar in v_np.
      apply Rplus_lt_compat_l with (r:=1) in v_np.
      assert ((1 - p1)*q < 1-p). lra.
      clear v_np. rename H4 into v_np.
      apply divide_by_lt in v_np; try apply mult_stable; try lra.
      exists (Combine (q*p1 / p) v_p dst11 dst21).
      exists (Combine ((1-p1)*q / (1-p)) v_np dst10 dst20).
      destruct H2, H3. destruct H2, H3. destruct H4, H5.
      destruct H6. destruct H8 as [com equiv1].
      apply step_split in com.
      destruct com as [x11 com]. destruct com as [x10 com].
      destruct com as [Eq1 com]. destruct com as [com11 com10].
      destruct H7. destruct H8 as [com equiv2].
      apply step_split in com.
      destruct com as [x21 com]. destruct com as [x20 com].
      destruct com as [Eq2 com]. destruct com as [com21 com20].
      exists (Combine p v (Combine (q * p1 / p) v_p x11 x21)
                      (Combine ((1 - p1) * q / (1 - p)) v_np x10 x20)).
      split; try split; try split.
      simpl. rewrite H2, H3. lra.
      simpl. rewrite H4, H5. lra.
      unfold dst_equiv in *.
      simpl in *.
      intros.
      rewrite H6.
      rewrite H7.
      rewrite <- H.
      rewrite 4 Rmult_plus_distr_l.
      unfold Rminus.
      unfold Rdiv.
      rewrite <- 12 Rmult_assoc.
      assert ((q * p1 + (1 + - q) * p2) * q * p1 * / (q * p1 + (1 + - q) * p2)
                                                       = q * p1).
        rewrite Rmult_comm.
        rewrite <- 2 Rmult_assoc.
        rewrite Rinv_l; lra.
      rewrite H8. clear H8.
      assert(
          (q * p1 + (1 + - q) * p2) * (1 + - (q * p1 * / (q * p1 + (1 + - q) * p2)))
          = (1 + - q) * p2).
        rewrite Rmult_plus_distr_l.
        rewrite Rmult_1_r.
        rewrite Rmult_comm with (r1:=(q * p1 + (1 + - q) * p2)).
        rewrite Ropp_mult_distr_l_reverse.
        rewrite Rmult_assoc.
        rewrite Rinv_l; try lra.
      rewrite H8. clear H8.
      assert( ((1 + - (q * p1 + (1 + - q) * p2)) * (1 + - p1) * q * 
               / (1 + - (q * p1 + (1 + - q) * p2))) =  q * (1 + - p1)).
        rewrite Rmult_comm. 
        rewrite <- 2 Rmult_assoc.
        rewrite Rinv_l; try lra.
      rewrite H8. clear H8.
      assert( (1 + - (q * p1 + (1 + - q) * p2)) *
              (1 + - ((1 + - p1) * q * / (1 + - (q * p1 + (1 + - q) * p2)))) 
              = (1 + - q) * (1 + - p2)).
        rewrite Rmult_plus_distr_l.
        rewrite Rmult_1_r.
        rewrite Rmult_plus_distr_l.
        rewrite Rmult_1_r.
        rewrite <- 2 Ropp_mult_distr_l_reverse.
        rewrite <- 2 Rmult_assoc. 
        rewrite Rmult_comm with (r2:=/(1 + - (q * p1 + (1 + - q) * p2))).
        rewrite <- 2 Rmult_assoc. 
        rewrite Rinv_l; try lra.
      rewrite H8. clear H8.      
      lra.
      split.
      * constructor; trivial.
        constructor; trivial.
        constructor; trivial.
      * unfold dst_equiv.        
        intros.
        rewrite Eq.
        simpl.
        rewrite equiv1.
        rewrite equiv2.
        rewrite Eq1, Eq2.
        simpl.
        rewrite <-H.
        rewrite 4 Rmult_plus_distr_l.
        unfold Rminus.
        unfold Rdiv.
        rewrite <- 12 Rmult_assoc.
        assert ((q * p1 + (1 + - q) * p2) * q * p1 * / (q * p1 + (1 + - q) * p2)
                                                       = q * p1).
          rewrite Rmult_comm.
          rewrite <- 2 Rmult_assoc.
          rewrite Rinv_l; lra.
        rewrite H8. clear H8.
        assert(
          (q * p1 + (1 + - q) * p2) * (1 + - (q * p1 * / (q * p1 + (1 + - q) * p2)))
          = (1 + - q) * p2).
          rewrite Rmult_plus_distr_l.
          rewrite Rmult_1_r.
          rewrite Rmult_comm with (r1:=(q * p1 + (1 + - q) * p2)).
          rewrite Ropp_mult_distr_l_reverse.
          rewrite Rmult_assoc.
          rewrite Rinv_l; try lra.
        rewrite H8. clear H8.
        assert( ((1 + - (q * p1 + (1 + - q) * p2)) * (1 + - p1) * q * 
               / (1 + - (q * p1 + (1 + - q) * p2))) =  q * (1 + - p1)).
          rewrite Rmult_comm. 
          rewrite <- 2 Rmult_assoc.
          rewrite Rinv_l; try lra.
        rewrite H8. clear H8.
        assert( (1 + - (q * p1 + (1 + - q) * p2)) *
              (1 + - ((1 + - p1) * q * / (1 + - (q * p1 + (1 + - q) * p2)))) 
              = (1 + - q) * (1 + - p2)).
          rewrite Rmult_plus_distr_l.
          rewrite Rmult_1_r.
          rewrite Rmult_plus_distr_l.
          rewrite Rmult_1_r.
          rewrite <- 2 Ropp_mult_distr_l_reverse.
          rewrite <- 2 Rmult_assoc. 
          rewrite Rmult_comm with (r2:=/(1 + - (q * p1 + (1 + - q) * p2))).
          rewrite <- 2 Rmult_assoc. 
          rewrite Rinv_l; try lra.
        rewrite H8. clear H8.      
        lra.
Qed.

Lemma if_steps: forall y c1 c2 dst dst1 dst2,
  c1 / dst || dst1 ->
  c2 / dst || dst2 ->
  exists dst3, (IFB y THEN c1 ELSE c2 FI) / dst || dst3.
Proof. 
  induction dst as [st|]; intros.
  + destruct (snd st y) eqn: Eq.
    - exists dst1.
      apply if_true_lift; trivial.
      simpl.
      rewrite Eq; trivial.
    - exists dst2.
      apply if_false_lift; trivial.
      simpl.
      rewrite Eq; trivial.
  + inversion H; subst.
    inversion H0; subst.
    destruct IHdst1 with (dst2:=dst1') (dst3:=dst1'0) as [dst1'1]; trivial.
    destruct IHdst2 with (dst1:=dst2') (dst3:=dst2'0) as [dst2'1]; trivial.
    exists (Combine p a dst1'1 dst2'1).
    apply E_Lift; assumption.
Qed.    

(** Note: The converse is false, even in a weak form.

i.e.
Conjecture if_steps_rev : forall b c1 c2 dst dst',
  (IFB b THEN c1 ELSE c2 FI) / dst || dst' ->
  exists dst1 dst2, c1 / dst || dst1 \/ c2 / dst || dst2.
      
*)

Theorem hoare_if_true : forall P Q y c1 c2 dst dst',
  Prb (BId y) in dst = 1 ->
  {{conditionT P y}} c1 {{conditionT Q y}} ->
  heval dst (conditionT P y) -> 
  (IFB y THEN c1 ELSE c2 FI) / dst || dst' ->
  heval dst' (conditionT Q y).
Proof.
  intros.
  apply if_true_equiv in H2; trivial.
  eapply H0.
  apply H2.
  assumption.
Qed.

Theorem hoare_if_false : forall P Q y c1 c2 dst dst',
  Prb (BId y) in dst = 0 ->
  {{conditionF P y}} c2 {{conditionF Q y}} ->
  heval dst (conditionF P y) -> 
  (IFB y THEN c1 ELSE c2 FI) / dst || dst' ->
  heval dst' (conditionF Q y).
Proof.
  intros.
  apply if_false_equiv in H2; trivial.
  eapply H0.
  apply H2.
  assumption.
Qed.

(** ** The Deterministic If Rule *)

Theorem hoare_if_det : forall P Q y c1 c2, 
  {{ HAnd P (HTrue y) }} c1 {{ Q }} ->
  {{ HAnd P (HFalse y) }} c2 {{ Q }} ->
  {{ HAnd P (HOr (HTrue y) (HFalse y)) }} (IFB y THEN c1 ELSE c2 FI) {{ Q }}.
Proof.
  intros P Q y c1 c2 hoare1 hoare2 dst dst' step HP. 
  destruct HP as [HP det].
  destruct det as [HT | HF].
  + rewrite <- if_true_equiv in step by assumption.
    apply hoare1 with (dst:=dst); trivial.
    split; assumption.
  + rewrite <- if_false_equiv in step by assumption.
    apply hoare2 with (dst:=dst); trivial.
    split; assumption.
Qed.

(** ** The Probabilistic If Rule  *)

Theorem hoare_if_prob : forall P1 P2 Q1 Q2 c1 c2 y p,
  0 < p < 1 ->
  unassigned c1 y ->
  unassigned c2 y ->
  {{HAnd (scale P1 (1/p)) (HTrue y)}} c1 {{scale Q1 (1/p)}} ->
  {{HAnd (scale P2 (1/(1-p))) (HFalse y)}} c2 {{scale Q2 (1/(1-p))}} ->
  {{HAnd (HEq (BId y) p) (HAnd (conditionT P1 y) (conditionF P2 y))}} 
    (IFB y THEN c1 ELSE c2 FI) {{HAnd (conditionT Q1 y) (conditionF Q2 y)}}.
Proof.
  intros P1 P2 Q1 Q2 c1 c2 y p v cf1 cf2 HP1 HP2 dst dst' step pre.
  destruct pre as (prob & preT & preF).
  simpl in *.
  specialize (fork_on_b_plus (IFB y THEN c1 ELSE c2 FI) dst dst' 
    (BId y) p v step prob). 
  intros (dst1 & dst0 & dst'' & E1 & E0 & Eq & step2 & Eq2).
  rewrite dst_equiv_iff in Eq.
  apply Eq in preT. apply Eq in preF.
  inversion step2; subst. rename H4 into stepT, H5 into stepF, dst2' into dst0'.
  rewrite dst_equiv_iff in Eq2.
  apply if_true_equiv in stepT; trivial.
  apply if_false_equiv in stepF; trivial.
  specialize (probability_preserved c1 dst1 dst1' y cf1 stepT); intros E1'. 
  specialize (probability_preserved c2 dst0 dst0' y cf2 stepF); intros E0'.
  rewrite E1 in E1'; rewrite E0 in E0'. symmetry in E1', E0'.
  split.
  + apply Eq2.
    apply scale_equiv_1; trivial.
    apply scale_equiv_1 in preT; trivial.
    eapply HP1. apply stepT.
    split; assumption. 
  + apply Eq2.
    apply scale_equiv_0; trivial.
    apply scale_equiv_0 in preF; trivial.
    eapply HP2. apply stepF.
    split; assumption. 
Qed.


(** * While Loops *)

(** ** While loop termination *)

Inductive terminates_in : nat -> com -> dstate -> Prop :=
  | term_0 : forall y c dst,
    Prb (BId y) in dst = 0 ->
    terminates_in 0 (WHILE y DO c END) dst
  | term_S : forall n y c dst dst', 
    Prb (BId y) in dst = 1 ->
    c / dst || dst' ->
    terminates_in n (WHILE y DO c END) dst' ->
    terminates_in (S n) (WHILE y DO c END) dst.

Lemma term_combine : forall y c n p v dst1 dst2,
  terminates_in n (WHILE y DO c END) dst1 ->
  terminates_in n (WHILE y DO c END) dst2 ->
  terminates_in n (WHILE y DO c END) (Combine p v dst1 dst2).
Proof.
  induction n; intros p v dst1 dst2 T1 T2.
  + inversion T1; subst.
    inversion T2; subst.
    apply term_0. 
    simpl in *; rewrite H1; rewrite H2; lra.
  + inversion T1; subst. rename dst' into dst1', H2 into Pr1, H3 into step1.
    inversion T2; subst. rename dst' into dst2', H2 into Pr2, H3 into step2.
    apply term_S with (dst':=(Combine p v dst1' dst2')).
    simpl in *; rewrite Pr1; rewrite Pr2; lra.
    apply E_Lift; assumption.
    apply IHn; assumption.
Qed.

Lemma term_split : forall y c n p v dst1 dst2,
  terminates_in n (WHILE y DO c END) (Combine p v dst1 dst2) ->
  terminates_in n (WHILE y DO c END) dst1 /\ 
  terminates_in n (WHILE y DO c END) dst2.
Proof.
  induction n; intros p v dst1 dst2 T.
  + inversion T; subst.
    apply pr_split_0 in H1 as (Pr1 & Pr2).
    split; apply term_0; assumption.
  + inversion T; subst.
    apply pr_split_1 in H2 as (Pr1 & Pr2).
    inversion H3; subst.
    replace v1 with v in * by apply proof_irrelevance. 
    specialize (IHn p v dst1' dst2' H5).
    destruct IHn as [T1 T2].
    split. 
    apply term_S with (dst':=dst1'); trivial.
    apply term_S with (dst':=dst2'); trivial.
Qed.

Lemma while_end : forall y c dst dst',
  WHILE y DO c END / dst || dst' ->
  terminates_in 0 (WHILE y DO c END) dst'.
Proof.
  intros.
  remember (WHILE y DO c END) as com.  
  induction H; try solve [inversion Heqcom]; subst.
  apply term_0; simpl; rewrite H; reflexivity.
  apply IHceval2; assumption.
  apply term_combine.
  apply IHceval1; reflexivity.
  apply IHceval2; reflexivity.
Qed.

Lemma equidistant: forall P y c p v dst1 dst2 m n,
  {{ HAnd P (HTrue y) }} c {{ HAnd P (HOr (HTrue y) (HFalse y)) }} ->
  heval (Combine p v dst1 dst2) (HAnd P (HOr (HTrue y) (HFalse y))) ->
  terminates_in m (WHILE y DO c END) dst1 ->
  terminates_in n (WHILE y DO c END) dst2 ->
  m = n.
Proof.
  intros P y c p v dst1 dst2 m.
  generalize dependent dst2.
  generalize dependent dst1.
  induction m; intros dst1 dst2 n hoare HP term1 term2.
  + destruct HP.
    destruct H0.
    - inversion term1; subst. (* contradiction: y is true in dst1 *)
      simpl in *; apply pr_split_1 in H0; lra. 
    - inversion term2; trivial; subst.
      simpl in *; apply pr_split_0 in H0; lra.
  + inversion term1; subst.
    inversion term2; subst.    
    destruct HP.
    destruct H0.
    (* Two contradiction cases: One branch terminates first. *)
    simpl in *; apply pr_split_1 in H0; lra.
    simpl in *; apply pr_split_0 in H0; lra.    
    assert( heval (Combine p v dst1 dst2) (HAnd P (HTrue y))) as HP2.
      split. destruct HP; assumption. simpl in *; rewrite H1, H2; lra.
    assert (step: c / Combine p  v dst1 dst2 || Combine p v dst' dst'0). 
      apply E_Lift; assumption.
    apply hoare in step.
    apply step in HP2.
    specialize (IHm dst' dst'0 n0 hoare HP2 H5 H8).
    rewrite IHm. 
    reflexivity.
Qed.


(** 
   In principle, we could remove the "non_probabilistic P" hypothesis from the 
   following lemma based on our yet unproven conjecture that every non-deterministic
   invariant that preserves deterministic b implies some deterministic invariant. 

   However, we have yet to prove this (nearly certain) conjecture in Coq.
*) 

Lemma while_terminates : forall P y c dst dst',
  non_probabilistic P ->
  {{ HAnd P (HTrue y) }} c {{ HAnd P (HOr (HTrue y) (HFalse y)) }} ->
  heval dst (HAnd P (HOr (HTrue y) (HFalse y))) ->
  WHILE y DO c END / dst || dst' ->
  exists n, terminates_in n (WHILE y DO c END) dst.
Proof.
  intros.
  remember (WHILE y DO c END) as com.
  induction H2; try solve [inversion Heqcom].
  + exists 0%nat.
    apply term_0.
    simpl; rewrite H2; reflexivity.
  + inversion Heqcom; subst.
    assert (heval (Unit st) (HAnd P (HTrue y))). 
      split. 
      destruct H1; assumption. 
      simpl; rewrite H2; reflexivity. 
    specialize (H0 (Unit st) dst' H2_ H3). 
    specialize (IHceval2 H0 Heqcom). 
    destruct IHceval2 as (n & term).
    exists (S n).
    apply term_S with (dst':=dst'); trivial.
    simpl; rewrite H2; reflexivity. 
  + inversion Heqcom; subst.
    assert (non_probabilistic (HAnd P (HOr (HTrue y) (HFalse y)))).
      constructor. assumption.
      constructor; constructor.
    eapply non_probabilistic_split in H3. 2: apply H1.
    destruct H3.
    destruct IHceval1 as (m & term1); trivial. 
    destruct IHceval2 as (n & term2); trivial. 
    specialize (equidistant P y c p v dst1 dst2 m n H0 H1 term1 term2). intros.
    subst.
    exists n.
    apply term_combine; assumption.
Qed.


(** *** A limited Hoare While Rule *)

Theorem hoare_while_end : forall y c,
  {{ HEq BTrue 1 }} WHILE y DO c END {{ HFalse y }}.
Proof.
  intros y c dst dst' step HP.
  clear HP.
  remember (WHILE y DO c END) as com.
  induction step; inversion Heqcom; subst.
  + simpl.
    rewrite H; reflexivity.
  + apply IHstep2; reflexivity.
  + simpl in *.  
    rewrite IHstep1, IHstep2; trivial.
    lra.
Qed.

(** ** The Hoare While Rule *)

Theorem hoare_while_det: forall P D y c,
  non_probabilistic D ->
  {{HAnd D (HTrue y) }} c {{ HAnd D (HOr (HTrue y) (HFalse y)) }} ->
  {{ HAnd P (HTrue y) }} c {{ P }} ->
  P ->> D -> 
  {{ HAnd P (HOr (HTrue y) (HFalse y)) }} WHILE y DO c END{{HAnd P (HFalse y) }}.
Proof.
  intros P D y c np inv' inv cons dst dst' step pre.
  specialize (while_terminates D y c dst dst'); intros term. 
  destruct term as [n term]; trivial.
    destruct pre. split; try apply cons; assumption.
  remember (WHILE y DO c END) as com.
  induction term; inversion Heqcom; subst.
  + specialize (while_end_equiv y c dst dst' H). intros temp. apply temp in step.
    clear temp. subst.
    split; [destruct pre; assumption | assumption].
  + specialize (while_loop_lift y c dst dst' H step). intros (dst'' & step1 & step2).
    apply IHterm; trivial.
    apply step_deterministic with (dst1:=dst'0) in step1; subst; trivial.
    destruct pre as (HP & HDet). 
    split.
    apply inv with (dst:=dst); trivial.
    split; assumption.
    apply inv' with (dst:=dst); trivial.
    apply cons in HP.
    split; assumption.
Qed.



(** * Alternative If Rules *)

(**

Unscaled If rule


                             c-free c1 c2 x
                             all0 P1 -> all0 Q1
                             all0 P2 -> all0 Q2
                        {{P1 | y}} c1 {{Q1 | y}} 
                        {{P2 | ~y}} c2 {{Q2 | ~y}} 
       ----------------------------------------------------- (hoare unscaled if)     
   {{P1 | y /\ P2 | ~y}} IF y THEN c1 ELSE c2 FI {{Q1 | y /\ Q2 | ~y}}

*)

Inductive com_id_free: com -> aid -> Prop :=
  | Cf_skip : forall x, com_id_free Skip x
  | Cf_ass : forall x' a x, x'<>x -> ax_id_free a x -> com_id_free (x'::=a) x
  | Cf_bass : forall y b x, com_id_free (y:==b) x
  | Cf_seq : forall c1 c2 x, 
             com_id_free c1 x ->  com_id_free c2 x -> com_id_free (c1 ; c2) x
  | Cf_if : forall y c1 c2 x,
             com_id_free c1 x -> com_id_free c2 x -> com_id_free (If y c1 c2) x
  | Cf_while : forall y c x, com_id_free c x -> com_id_free (While y c) x
  | Cf_toss: forall x' p v x, x'<>x -> com_id_free (x' $=(p,v)) x
  | Cf_btoss: forall y p v x, com_id_free (y $=[p,v]) x.

Inductive com_bid_free: com -> bid -> Prop :=
  | Cf_skip_b : forall y, com_bid_free Skip y
  | Cf_ass_b : forall x a y, com_bid_free (x::=a) y
  | Cf_bass_b : forall y' b y, y'<>y -> bx_bid_free b y -> com_bid_free (y':==b) y
  | Cf_seq_b : forall c1 c2 y, 
               com_bid_free c1 y ->  com_bid_free c2 y -> com_bid_free (c1 ; c2) y
  | Cf_if_b : forall y' c1 c2 y, y'<>y ->
              com_bid_free c1 y -> com_bid_free c2 y -> com_bid_free (If y' c1 c2) y
  | Cf_while_b : forall y' c y, y'<>y -> 
                                com_bid_free c y -> com_bid_free (While y' c) y
  | Cf_toss_b : forall x p v y, com_bid_free (x $=(p,v)) y
  | Cf_btoss_b : forall y' p v y, y'<>y -> com_bid_free (y'$=[p,v]) y.

Lemma free_then_unassigned : forall c y,
  com_bid_free c y -> unassigned c y.
Proof.
  intros c y H.
  induction H; subst; try solve [repeat constructor; trivial].
Qed.

Lemma vacuous_P : forall P b dstX dstY, 
  Prb b in dstX = 0 ->
  Prb b in dstY = 0 ->
  heval dstX (condition P b) ->
  heval dstY (condition P b).
Proof.
  intros.
  induction P; simpl in *.
  + rewrite pr_conj_0_r; trivial.
    rewrite pr_conj_0_r in H1; assumption. 
  + rewrite pr_conj_0_r; trivial.
    rewrite pr_conj_0_r in H1; assumption. 
  + rewrite pr_conj_0_r; trivial.
    rewrite pr_conj_0_r in H1; assumption. 
  + inversion H1.
    apply IHP1 in H2.
    apply IHP2 in H3.
    split; assumption.
  + inversion H1.
    apply IHP1 in H2; left; assumption.
    apply IHP2 in H2; right; assumption.
Qed.

(** Lemma 7.4 *)
Lemma vacuous_P_l : forall P b p v dst1 dstX dstY,
  Prb b in dstX = 0 ->
  Prb b in dstY = 0 ->
  heval (Combine p v dst1 dstX) (condition P b) ->
  heval (Combine p v dst1 dstY) (condition P b).
Proof.
  intros.
  induction P; simpl in *.
  + rewrite pr_conj_0_r with (d:=dstY); trivial.
    rewrite pr_conj_0_r with (d:=dstX) in H1; assumption.
  + rewrite pr_conj_0_r with (d:=dstY); trivial.
    rewrite pr_conj_0_r with (d:=dstX) in H1; assumption.
  + rewrite pr_conj_0_r with (d:=dstY); trivial.
    rewrite pr_conj_0_r with (d:=dstX) in H1; assumption.
  + destruct H1.
    apply IHP1 in H1.
    apply IHP2 in H2.
    split; assumption.
  + destruct H1.
    left. apply IHP1. assumption.
    right. apply IHP2. assumption.
Qed.   

(** Lemma 7.5 *)
Lemma vacuous_P_r : forall P b p v dst2 dstX dstY,
  Prb b in dstX = 0 ->
  Prb b in dstY = 0 ->
  heval (Combine p v dstX dst2) (condition P b) ->
  heval (Combine p v dstY dst2) (condition P b).
Proof.
  intros.
  induction P; simpl in *.
  + rewrite pr_conj_0_r; trivial.
    rewrite pr_conj_0_r in H1; assumption. 
  + rewrite pr_conj_0_r; trivial.
    rewrite pr_conj_0_r in H1; assumption. 
  + rewrite pr_conj_0_r; trivial.
    rewrite pr_conj_0_r in H1; assumption. 
  + inversion H1.
    apply IHP1 in H2.
    apply IHP2 in H3.
    split; assumption.
  + inversion H1.
    apply IHP1 in H2; left; assumption.
    apply IHP2 in H2; right; assumption.
Qed.

(** Note: The third case arguably shouldn't exist, but the current format of hexp 
    and heval does prohibit a hexp to have a p \notin [0,1] on the RHS *)

Inductive all_zero: hexp -> Prop :=
  | zero_eq : forall b, all_zero (HEq b 0)
  | zero_lt : forall p b, p > 0 -> all_zero (HLt b p)
  | zero_gt: forall p b, p < 0 -> all_zero (HGt b p)
  | zero_or_l : forall P Q, all_zero P -> all_zero (HOr P Q)
  | zero_or_r : forall P Q, all_zero Q -> all_zero (HOr P Q)
  | zero_and : forall P Q, all_zero P -> all_zero Q -> all_zero (HAnd P Q).

(** Lemma 7.6 *)
Lemma neg_b_all_zero : forall P b dst,
  Prb b in dst = 0 -> 
  (heval dst (condition P b) <-> all_zero P).
Proof.
  intros P b dst Pr0.
  split.
  + intros HP.
    induction P; simpl in *.
    - rewrite pr_conj_0_r in HP; trivial.
      rewrite <- HP.
      constructor.
    - rewrite pr_conj_0_r in HP; trivial.
      constructor.
      assumption.
(* this case is the only reason for zero_gt *)
    - rewrite pr_conj_0_r in HP; trivial. 
      constructor. assumption.
    - destruct HP.
      constructor; auto.
    - destruct HP.
      apply zero_or_l; auto.
      apply zero_or_r; auto.
  + intros Z.
    induction Z; simpl; try rewrite pr_conj_0_r; auto.
Qed.

(** Two additional premutation rules will go here for lack of better location. *)

Lemma dist_update_prob_permute_b : forall dst y1 y2 b p v,
  y1 <> y2 ->
  bx_bid_free b y1 ->
  dist_update_b (prob_update_b dst y1 p v) y2 b 
  = prob_update_b (dist_update_b dst y2 b) y1 p v.
Proof.
  intros.
  induction dst.
  + simpl.
    rewrite 2 b_free_imp_b in * by assumption.
    rewrite update_permute_b; trivial.
    replace (update_b (update_b t y1 false) y2 (beval b t)) with 
            (update_b (update_b t y2 (beval b t)) y1 false).
    reflexivity.
    rewrite update_permute_b; trivial.
    apply beq_bid_false_iff; auto.
    apply beq_bid_false_iff; assumption.
  + simpl.
    rewrite IHdst1.
    rewrite IHdst2.
    reflexivity.
Qed.


Lemma dist_update_b_permute : forall dst y1 y2 b1 b2,
  y1 <> y2 ->
  bx_bid_free b2 y1 ->
  bx_bid_free b1 y2 ->
  dist_update_b (dist_update_b dst y1 b1) y2 b2 =
  dist_update_b (dist_update_b dst y2 b2) y1 b1.
Proof.
  intros.
  induction dst.
  + simpl.
    rewrite 2 b_free_imp_b in * by assumption.
    rewrite update_permute_b; trivial.
    apply beq_bid_false_iff; assumption.
  + simpl.
    rewrite IHdst1.
    rewrite IHdst2.
    reflexivity.
Qed.


Lemma bass_steps : forall c y b dst dst', 
  b = BTrue \/ b = BFalse ->
  com_bid_free c y -> 
  c / dst || dst' ->
  c / (dist_update_b dst y b) || (dist_update_b dst' y b).
Proof.
  intros.
  induction H1.
  +  apply E_Skip.
  + replace (Unit (update st x n)) with (dist_update (Unit st) x (ANum n))
      by reflexivity.
    rewrite dist_update_non_interference; trivial.
    apply E_Assign.
    simpl. rewrite update_non_interference. assumption.
  + inversion H0; subst.
    replace (Unit (update_b st y0 (beval b0 st))) with 
      (dist_update_b (Unit st) y0 b0) by reflexivity.
    rewrite <- dist_update_b_permute; auto.
    apply E_BAssign.
    reflexivity.
    destruct H; subst; constructor.
  + inversion H0; subst.
    apply E_Seq with (dst':=(dist_update_b dst' y b)).
    apply IHceval1; assumption.
    apply IHceval2; assumption.
  + inversion H0; subst.
    apply E_IfTrue.
    simpl.
    assert (y <> y0) by auto.
    apply beq_bid_false_iff in H3.
    rewrite H3; trivial.
    apply IHceval; assumption.
  + inversion H0; subst.
    apply E_IfFalse.
    simpl.
    assert (y <> y0) by auto.
    apply beq_bid_false_iff in H3.
    rewrite H3; trivial.
    apply IHceval; assumption.
  + inversion H0; subst.
    apply E_WhileEnd.
    simpl.
    assert (y <> y0) by auto.
    apply beq_bid_false_iff in H2.
    rewrite H2; trivial.
  + inversion H0; subst.
    apply E_WhileLoop with (dst':=dist_update_b dst' y b).
    simpl.
    assert (y <> y0) by auto.
    apply beq_bid_false_iff in H2.
    rewrite H2; trivial.
    simpl in *.
    apply IHceval1; assumption.
    apply IHceval2; assumption.    
  + replace (Combine p v (Unit (update st x 1)) (Unit (update st x 0)))
       with (prob_update (Unit st) x p v) by reflexivity.
    rewrite prob_update_non_interference; trivial.
    apply E_Toss.
  + inversion H0; subst.
    replace (Combine p v (Unit (update_b st y0 true)) (Unit (update_b st y0 false)))
       with (prob_update_b (Unit st) y0 p v) by reflexivity.
    rewrite dist_update_prob_permute_b; trivial. 
    apply E_BToss.
    destruct H; subst; constructor.
  + simpl. 
    apply E_Lift.
    apply IHceval1; assumption.
    apply IHceval2; assumption.
Qed.
  
(** *** Unscaled If *)

(**  The all_zero hypotheses say if P2's base elements are all Pr(b) = 0, 
     Pr(b) < p (for p>0) and Pr(b) > p (for negative p) the same must be true of Q.
     This rules out the case where b = 1, c2 contains a loop, and Q2 contains 
     a false judgement. (Or the similar case for c1.)                            *)


Theorem hoare_if_unscaled : forall P1 P2 Q1 Q2 c1 c2 y,
  com_bid_free c1 y ->
  com_bid_free c2 y ->
  (all_zero P1 -> all_zero Q1) ->
  (all_zero P2 -> all_zero Q2) ->
  {{conditionT P1 y}} c1 {{conditionT Q1 y}} ->
  {{conditionF P2 y}} c2 {{conditionF Q2 y}} ->
  {{HAnd (conditionT P1 y) (conditionF P2 y)}} (IFB y THEN c1 ELSE c2 FI) 
                           {{HAnd (conditionT Q1 y) (conditionF Q2 y)}}.
Proof.
  intros P1 P2 Q1 Q2 c1 c2 y cf1 cf2 zero1 zero2 HP1 HP2 dst dst' step pre. 
  specialize (pr_normality dst (beval (BId y))); intros temp.
  assert (Prb (BId y) in dst = 1 \/ Prb (BId y) in dst = 0 
                                \/ 0 < Prb (BId y) in dst < 1) as H by lra.
  clear temp.
  destruct H as [Pr1 | H]; [ | destruct H as [Pr0 | v]].
  + simpl.
    destruct pre as [preT preF].
    split.
    - apply hoare_if_true with (P:=P1) (c1:=c1) (c2:=c2) (dst:=dst); assumption. 
    - rewrite <- if_true_equiv in step; trivial. 
      apply free_then_unassigned in cf1.
      specialize (probability_preserved c1 dst dst' y cf1 step); intros Pr1'.
      rewrite Pr1 in Pr1'. symmetry in Pr1'.
      rewrite prb_complement_1 in Pr1.
      unfold conditionF in *.
      apply neg_b_all_zero with (P:=P2) in Pr1; trivial.
      apply Pr1 in preF. 
      specialize (zero2 preF).
      apply neg_b_all_zero; trivial.
      apply pr_complement_1; assumption.
  + simpl.
    destruct pre as [preT preF].
    split.
    - rewrite <- if_false_equiv in step; trivial. 
      apply free_then_unassigned in cf2.
      specialize (probability_preserved c2 dst dst' y cf2 step); intros Pr0'.
      rewrite Pr0 in Pr0'. symmetry in Pr0'.  
      unfold conditionF in *. 
      apply neg_b_all_zero with (P:=P1) in Pr0; trivial.
      apply Pr0 in preT. 
      specialize (zero1 preT).
      apply neg_b_all_zero; assumption.
    - apply hoare_if_false with (P:=P2) (c1:=c1) (c2:=c2) (dst:=dst); assumption.
  + remember (Prb (BId y) in dst) as q. symmetry in Heqq. 
    specialize (fork_on_b_plus (IFB y THEN c1 ELSE c2 FI) dst dst' 
      (BId y) q v step Heqq). 
    intros (dst1 & dst0 & dst'' & E1 & E0 & Eq & step2 & Eq2).
    rewrite dst_equiv_iff in Eq.
    apply Eq in pre.
    destruct pre as [preT preF].
    apply step_split in step2.
    destruct step2 as (dst1' & dst0' & Eqm & stepT & stepF).
    rewrite dst_equiv_iff in Eq2.
    apply Eq2.
    rewrite Eqm.
    apply if_true_equiv in stepT; trivial.
    apply if_false_equiv in stepF; trivial.
    specialize (free_then_unassigned c1 y cf1). intros cf1'.
    specialize (free_then_unassigned c2 y cf2). intros cf2'.
    specialize (probability_preserved c1 dst1 dst1' y cf1' stepT); intros E1'. 
    specialize (probability_preserved c2 dst0 dst0' y cf2' stepF); intros E0'. 
    rewrite E1 in E1'. rewrite E0 in E0'. symmetry in E1', E0'.
    split.
    * assert(H: c1 / (Combine q v dst1 (dist_update_b dst1 y BFalse)) 
                  || (Combine q v dst1' (dist_update_b dst1' y BFalse))).
      apply E_Lift; trivial.
      apply bass_steps; auto.
      unfold hoare_triple in HP1.
      apply HP1 in H; trivial.
      apply vacuous_P_l with (dstX:=dist_update_b dst1' y BFalse); trivial.
      apply dist_update_false.
      apply vacuous_P_l with (dstX:=dst0); trivial.
      apply dist_update_false. 
    * assert(H: c2 / (Combine q v (dist_update_b dst0 y BTrue)) dst0
                  || (Combine q v (dist_update_b dst0' y BTrue)) dst0').
      apply E_Lift; trivial.
      apply bass_steps; auto.
      unfold hoare_triple in HP2.
      eapply HP2 in H.
      apply vacuous_P_r with (dstX:=dist_update_b dst0' y BTrue); trivial.
      apply prb_complement_1. apply dist_update_true. 
      apply prb_complement_1; assumption.
      apply vacuous_P_r with (dstX:=dst1); trivial.
      apply prb_complement_1; assumption.
      apply prb_complement_1.
      apply dist_update_true. 
Qed.      

(** ** The General If Rule *)
(**

General If rule

                         all0 P1 -> all0 Q1
                         all0 P2 -> all0 Q2
                         unassigned y c1 c2
                    {{1/p * P1}} c1 {{1/p * Q}}
                {{1/(1-p) * P2}} c2 {{1/(1-p) * Q}}
    -------------------------------------------------------------  (hoare_if_gen)
    {{Pr(y) = p /\ P /\ P2}} IF y THEN c1 ELSE c2 FI {{Q1 /\ Q2}} 


*)
(** We can remove the HTrue y's without changing the proof of this rule 
    (or much changing its content.) *)

Theorem hoare_if_gen : forall P1 P2 Q1 Q2 c1 c2 y p,
  unassigned c1 y ->
  unassigned c2 y ->
  (all_zero P1 -> all_zero Q1) ->
  (all_zero P2 -> all_zero Q2) ->
  {{HAnd (scale P1 (1/p)) (HTrue y)}} c1 {{scale Q1 (1/p)}} ->
  {{HAnd (scale P2 (1/(1-p))) (HFalse y)}} c2 {{scale Q2 (1/(1-p))}} ->
  {{HAnd (HEq (BId y) p) (HAnd (conditionT P1 y) (conditionF P2 y))}} 
    (IFB y THEN c1 ELSE c2 FI) {{HAnd (conditionT Q1 y) (conditionF Q2 y)}}.
Proof.
  intros P1 P2 Q1 Q2 c1 c2 y p cf1 cf2 zero1 zero2 HP1 HP2 dst dst' step pre.
  destruct pre as (prob & preT & preF).
  specialize (pr_normality dst (beval (BId y))); rewrite prob; intros temp.
  assert (p = 1 \/ p = 0 \/ 0 < p < 1) as H by lra.
  clear temp.
  replace (heval dst (HEq (BId y) p)) with (Prb (BId y) in dst = p) in prob 
                                                                    by reflexivity.
  destruct H as [Pr1 | H]; [ | destruct H as [Pr0 | v]].
  + rewrite Pr1 in *. clear Pr1.
    apply if_true_equiv in step; trivial.
    specialize (probability_preserved c1 dst dst' y cf1 step). intros Pr1'.
    rewrite prob in Pr1'. symmetry in Pr1'.
    split.
    - unfold conditionT in *. 
      rewrite <- condition_on_1 in preT; trivial.
      rewrite <- condition_on_1; trivial.
      replace (1/1) with (1) in HP1 by lra.
      rewrite 2 scale_1 in HP1.
      apply HP1 with (dst:=dst); trivial.
      split; assumption. 
    - unfold conditionF in *.
      apply prb_complement_1 in prob.       
      apply neg_b_all_zero with (P:=P2) in prob.
      apply prob in preF.
      specialize (zero2 preF).
      apply neg_b_all_zero; trivial.
      apply prb_complement_1; assumption.
  + rewrite Pr0 in *. clear Pr0.
    rewrite <- if_false_equiv in step; trivial. 
    specialize (probability_preserved c2 dst dst' y cf2 step); intros Pr0'.
    rewrite prob in Pr0'. symmetry in Pr0'.    
    split.
    - unfold conditionT in *.
      apply neg_b_all_zero with (P:=P1) in prob; trivial.
      apply prob in preT.
      specialize (zero1 preT).
      apply neg_b_all_zero; trivial.
    - unfold conditionF in *.       
      rewrite prb_complement_0 in prob.
      rewrite prb_complement_0 in Pr0'.
      rewrite <- condition_on_1 in preF; trivial.
      rewrite <- condition_on_1; trivial.
      replace (1/(1-0)) with (1) in HP2 by lra.
      rewrite 2 scale_1 in HP2.
      apply HP2 with (dst:=dst); trivial.
      apply prb_complement_0 in prob.
      split; assumption.
  + specialize (fork_on_b_plus (IFB y THEN c1 ELSE c2 FI) dst dst' 
      (BId y) p v step prob). 
    intros (dst1 & dst0 & dst'' & E1 & E0 & Eq & step2 & Eq2).
    rewrite dst_equiv_iff in Eq.
    apply Eq in preT. apply Eq in preF.
    inversion step2; subst. rename dst2' into dst0', H4 into stepT, H5 into stepF. 
    rewrite dst_equiv_iff in Eq2.
    apply if_true_equiv in stepT; trivial.
    apply if_false_equiv in stepF; trivial.
    specialize (probability_preserved c1 dst1 dst1' y cf1 stepT); intros E1'. 
    specialize (probability_preserved c2 dst0 dst0' y cf2 stepF); intros E0'. 
    rewrite E1 in E1'; rewrite E0 in E0'. symmetry in E1', E0'.
    split.
    - apply Eq2.
      apply scale_equiv_1; trivial.
      apply scale_equiv_1 in preT; trivial.
      eapply HP1. apply stepT.
      split; assumption. 
    - apply Eq2.
      apply scale_equiv_0; trivial.
      apply scale_equiv_0 in preF; trivial.
      eapply HP2. apply stepF.
      split; assumption. 
Qed.

(** ** Inverse If Rules:
       We can also move the scaling to the main condition to avoid worrying about
       dividing by zero.

                         unassigned y c1 c2
                       all0 p*P1 -> all0 p*Q1
                   all0 (1-p)*P2 -> all0 (1-p)*Q2
                          {{P1}} c1 {{Q}}
                          {{P2}} c2 {{Q}}
    -------------------------------------------------------------  (hoare_if_gen')
    {{Pr(y) = p /\ p*P /\ P2}} IF y THEN c1 ELSE c2 FI {{p*Q1 /\ (1-p)*Q2}} 

*)

Lemma scale_twice : forall P p q,
  scale (scale P p) q = scale P (p*q).
Proof.
  intros.
  induction P; simpl; try solve [replace (q*(p*r)) with (p*q*r) by lra; reflexivity].
  + rewrite IHP1, IHP2; reflexivity.
  + rewrite IHP1, IHP2; reflexivity.
Qed.
  
Lemma scale_inversion: forall P Q p,
  p <> 0 ->
  (scale P p = Q <-> P = scale Q (1/p)).
Proof.
  intros P Q p NZ.
  split.
  + intros; subst.
    rewrite scale_twice.
    unfold Rdiv.
    rewrite Rmult_1_l.
    rewrite Rinv_r; trivial.
    symmetry; apply scale_1.
  + intros; subst.
    rewrite scale_twice.
    unfold Rdiv.    
    rewrite Rmult_1_l.
    rewrite <- Rinv_l_sym; trivial.
    apply scale_1.
Qed.

Lemma scale_cond : forall P p b,
  scale (condition P b) p = condition (scale P p) b.
Proof.
  intros P p b.
  induction P; simpl; trivial.
  + rewrite IHP1, IHP2; reflexivity.
  + rewrite IHP1, IHP2; reflexivity.
Qed.

Lemma scale_equiv_1' : forall P dst1 dst0 b p v,
  Prb b in dst1 = 1 ->
  Prb b in dst0 = 0 ->
  (heval (Combine p v dst1 dst0) (scale (condition P b) p) <-> heval dst1 P).
Proof.
  intros P dst1 dst0 b p v Pr1 Pr0.
  rewrite scale_cond.
  remember (scale P p) as Q.
  destruct scale_inversion with (P:=P) (Q:=Q) (p:=p). lra.
  symmetry in HeqQ.  
  specialize (H HeqQ).
  rewrite H.
  apply scale_equiv_1; assumption.
Qed.

Lemma scale_equiv_0' : forall P dst1 dst0 b p v,
  Prb b in dst1 = 1 ->
  Prb b in dst0 = 0 ->
  (heval (Combine p v dst1 dst0) (scale (condition P (BNot b)) (1-p)) <-> 
   heval dst0 P).
Proof.
  intros P dst1 dst0 b p v Pr1 Pr0.
  rewrite scale_cond.
  remember (scale P (1-p)) as Q.
  destruct scale_inversion with (P:=P) (Q:=Q) (p:=(1-p)). lra.
  symmetry in HeqQ.  
  specialize (H HeqQ).
  rewrite H.
  apply scale_equiv_0; assumption.
Qed.

(** *** Hoare If Prob Inverse *)

Theorem hoare_if_prob' : forall P1 P2 Q1 Q2 c1 c2 y p,
  0 < p < 1 ->
  unassigned c1 y ->
  unassigned c2 y ->
  {{HAnd P1 (HTrue y)}} c1 {{Q1}} ->
  {{HAnd P2 (HFalse y)}} c2 {{Q2}} ->
  {{HAnd (HEq (BId y) p) (HAnd (scale (conditionT P1 y) p) 
                               (scale (conditionF P2 y) (1-p)))}} 
    (IFB y THEN c1 ELSE c2 FI) {{HAnd (scale (conditionT Q1 y) p)
                                      (scale (conditionF Q2 y) (1-p)) }}.
Proof.
  intros P1 P2 Q1 Q2 c1 c2 y p v cf1 cf2 HP1 HP2 dst dst' step pre.
  destruct pre as (prob & preT & preF).
  simpl in *.
  specialize (fork_on_b_plus (IFB y THEN c1 ELSE c2 FI) dst dst' 
    (BId y) p v step prob). 
  intros (dst1 & dst0 & dst'' & E1 & E0 & Eq & step2 & Eq2).
  rewrite dst_equiv_iff in Eq.
  apply Eq in preT. apply Eq in preF.
  inversion step2; subst. rename H4 into stepT, H5 into stepF, dst2' into dst0'.
  rewrite dst_equiv_iff in Eq2.
  apply if_true_equiv in stepT; trivial.
  apply if_false_equiv in stepF; trivial.
  specialize (probability_preserved c1 dst1 dst1' y cf1 stepT); intros E1'. 
  specialize (probability_preserved c2 dst0 dst0' y cf2 stepF); intros E0'.
  rewrite E1 in E1'; rewrite E0 in E0'. symmetry in E1', E0'.
  split.
  + apply Eq2.
    apply scale_equiv_1'; trivial.
    apply scale_equiv_1' in preT; trivial.
    eapply HP1. apply stepT.
    split; assumption. 
  + apply Eq2.
    apply scale_equiv_0'; trivial.
    apply scale_equiv_0' in preF; trivial.
    eapply HP2. apply stepF.
    split; assumption. 
Qed.

(** *** Hoare If General Inverse *)

Theorem hoare_if_gen' : forall P1 P2 Q1 Q2 c1 c2 y p,
  unassigned c1 y ->
  unassigned c2 y ->
  (all_zero (scale P1 p) -> all_zero (scale Q1 p)) ->
  (all_zero (scale P2 (1-p)) -> all_zero (scale Q2 (1-p))) ->
  {{HAnd P1 (HTrue y)}} c1 {{Q1}} ->
  {{HAnd P2 (HFalse y)}} c2 {{Q2}} ->
  {{HAnd (HEq (BId y) p) (HAnd (scale (conditionT P1 y) p) 
                               (scale (conditionF P2 y) (1-p)))}} 
    (IFB y THEN c1 ELSE c2 FI) {{HAnd (scale (conditionT Q1 y) p)
                                      (scale (conditionF Q2 y) (1-p)) }}.
Proof.
  intros P1 P2 Q1 Q2 c1 c2 y p cf1 cf2 zero1 zero2 HP1 HP2 dst dst' step pre.
  destruct pre as (prob & preT & preF).
  specialize (pr_normality dst (beval (BId y))); rewrite prob; intros temp.
  assert (p = 1 \/ p = 0 \/ 0 < p < 1) as H by lra.
  clear temp.
  replace (heval dst (HEq (BId y) p)) with (Prb (BId y) in dst = p) in prob 
                                                                    by reflexivity.
  destruct H as [Pr1 | H]; [ | destruct H as [Pr0 | v]].
  + rewrite Pr1 in *. clear Pr1.
    apply if_true_equiv in step; trivial.
    specialize (probability_preserved c1 dst dst' y cf1 step). intros Pr1'.
    rewrite prob in Pr1'. symmetry in Pr1'.
    split.
    - unfold conditionT in *. 
      rewrite scale_1 in preT.
      rewrite <- condition_on_1 in preT; trivial.
      rewrite scale_1.
      rewrite <- condition_on_1; trivial.
      apply HP1 with (dst:=dst); trivial.
      split; assumption. 
    - unfold conditionF in *.
      apply prb_complement_1 in prob.       
      apply neg_b_all_zero with (P:=(scale P2 (1-1))) in prob.
      rewrite <- scale_cond in prob.
      apply prob in preF.
      specialize (zero2 preF).
      rewrite scale_cond.
      apply neg_b_all_zero; trivial.
      apply prb_complement_1; assumption.
  + rewrite Pr0 in *. clear Pr0.
    rewrite <- if_false_equiv in step; trivial. 
    specialize (probability_preserved c2 dst dst' y cf2 step); intros Pr0'.
    rewrite prob in Pr0'. symmetry in Pr0'.    
    split.
    - unfold conditionT in *.
      apply neg_b_all_zero with (P:=(scale P1 0)) in prob; trivial.
      rewrite <- scale_cond in prob.
      apply prob in preT.
      specialize (zero1 preT).
      rewrite scale_cond.
      apply neg_b_all_zero; trivial.
    - unfold conditionF in *.       
      rewrite prb_complement_0 in prob.
      rewrite prb_complement_0 in Pr0'.
      rewrite scale_cond in preF.
      rewrite <- condition_on_1 in preF; trivial.
      rewrite scale_cond.
      rewrite <- condition_on_1; trivial.
      replace (1/(1-0)) with (1) in HP2 by lra.
      rewrite Rminus_0_r in *.
      rewrite scale_1 in *.
      apply HP2 with (dst:=dst); trivial.
      apply prb_complement_0 in prob.
      split; assumption.
  + specialize (fork_on_b_plus (IFB y THEN c1 ELSE c2 FI) dst dst' 
      (BId y) p v step prob). 
    intros (dst1 & dst0 & dst'' & E1 & E0 & Eq & step2 & Eq2).
    rewrite dst_equiv_iff in Eq.
    apply Eq in preT. apply Eq in preF.
    inversion step2; subst. rename dst2' into dst0', H4 into stepT, H5 into stepF. 
    rewrite dst_equiv_iff in Eq2.
    apply if_true_equiv in stepT; trivial.
    apply if_false_equiv in stepF; trivial.
    specialize (probability_preserved c1 dst1 dst1' y cf1 stepT); intros E1'. 
    specialize (probability_preserved c2 dst0 dst0' y cf2 stepF); intros E0'. 
    rewrite E1 in E1'; rewrite E0 in E0'. symmetry in E1', E0'.
    split.
    - apply Eq2.
      apply scale_equiv_1'; trivial.
      apply scale_equiv_1' in preT; trivial.
      eapply HP1. apply stepT.
      split; assumption. 
    - apply Eq2.
      apply scale_equiv_0'; trivial.
      apply scale_equiv_0' in preF; trivial.
      eapply HP2. apply stepF.
      split; assumption. 
Qed.


(** * Generalizing the While rule *)

(** *** Two useful While Equivalences *)

Lemma while_embed : forall y c dst dst',
  WHILE y DO c END / dst || dst' <->
  IFB y THEN WHILE y DO c END ELSE Skip FI / dst || dst'.
Proof.
  split; intros.
  + remember (WHILE y DO c END) as com.
    induction H; inversion Heqcom; subst.
    - apply if_false_equiv.
      simpl; rewrite H; reflexivity.
      apply E_Skip.
    - apply if_true_equiv.
      simpl; rewrite H; reflexivity.
      apply E_WhileLoop with (dst':=dst'); assumption.
    - apply E_Lift; [apply IHceval1 | apply IHceval2]; assumption.
  + remember (IFB y THEN WHILE y DO c END ELSE Skip FI) as com.
    induction H; inversion Heqcom; subst.
    - assumption.
    - inversion H0; subst.
      apply E_WhileEnd; assumption.
    - apply E_Lift; [apply IHceval1 | apply IHceval2]; assumption.
Qed.

Lemma while_embed_special : forall y y' c dst dst',
  (((y':==BId y); WHILE y DO c END) / dst || dst' <->
  ((y':==BId y); IFB y' THEN WHILE y DO c END ELSE Skip FI) / dst || dst').
Proof.
  split; intros H.
  + apply seq_equiv in H as (dst'0 & step & step').
    apply seq_lift with (dst':=dst'0).
    assumption.
    assert (heval dst'0 (HEq (BIff (BId y) (BId y')) 1)).
      eapply hoare_asgn_b.
      apply step.
      simpl.
      rewrite beq_bid_refl.
      simpl.
      apply pr_tautology; intros st.
      destruct (beq_bid y' y); simpl; destruct (snd st y); reflexivity.
    simpl in H.
    clear step dst. rename step' into step.
    remember (WHILE y DO c END) as com.
    induction step; inversion Heqcom; subst.
    - apply if_false_lift.
      simpl in *. 
      destruct (snd st y') eqn:Eq.
      rewrite H0 in H. simpl in H. lra.
      reflexivity.
      apply E_Skip.
    - apply if_true_lift.
      simpl in *. 
      destruct (snd st y') eqn:Eq.
      reflexivity.
      rewrite H0 in H. simpl in H. lra.
      apply E_WhileLoop with (dst':=dst'); assumption.
    - apply pr_split_1 in H.
      destruct H.
      apply E_Lift; [apply IHstep1 | apply IHstep2]; assumption.
  + apply seq_equiv in H as (dst'0 & step & step').
    apply seq_lift with (dst':=dst'0).
    assumption.
    assert (heval dst'0 (HEq (BIff (BId y) (BId y')) 1)).
      eapply hoare_asgn_b.
      apply step.
      simpl.
      rewrite beq_bid_refl.
      apply pr_tautology; intros st.
      destruct (beq_bid y' y); simpl; destruct (snd st y); reflexivity. 
    simpl in H.
    clear step dst. rename step' into step.
    remember (IFB y' THEN WHILE y DO c END ELSE Skip FI) as com.
    induction step; inversion Heqcom; subst.
    - assumption.
    - inversion step; subst.
      apply E_WhileEnd. 
      simpl in *. 
      destruct (snd st y); trivial.
      rewrite H0 in H; simpl in H; lra.
    - apply pr_split_1 in H.
      destruct H.
      apply E_Lift; [apply IHstep1 | apply IHstep2]; trivial.
Qed.

Lemma sub_over_condition : forall P b y b',
hexp_sub_b y b' (condition P b) = condition (hexp_sub_b y b' P) (bexp_sub_b y b' b).
Proof.
  intros.
  induction P; try solve [unfold condition; reflexivity].
  + simpl.
    rewrite IHP1, IHP2.
    reflexivity.
  + simpl.
    rewrite IHP1, IHP2.
    reflexivity.
Qed.

(* *** An extension of the WHILE rule for a probabilistic guard 

  P1' can in principle be replaced by (scale P1' (1/p)) throughout
*)

Theorem hoare_while_prob : forall P1 D P2 c y y' p, 
  0 < p < 1 -> 
  y' <> y ->
  hx_bid_free P1 y' ->
  hx_bid_free P2 y' ->
  com_bid_free c y' ->
  non_probabilistic D ->
  {{HAnd (scale P1 (1/p)) (HTrue y)}} c {{ scale P1 (1/p) }} ->
  {{HAnd D (HTrue y)}} c {{ HAnd D (HOr (HTrue y) (HFalse y)) }} ->
  scale P1 (1/p) ->> D -> 
  {{ HAnd (HEq (BId y) p) (HAnd (conditionT P1 y) (conditionF P2 y)) }} 
  y':==(BId y); WHILE y DO c END
  {{ HAnd (HAnd (conditionT P1 y') (conditionF P2 y')) (HFalse y) }}.
Proof.
  intros P1 D P2 c y y' p v neq hf1' hf2' cf' np inv' inv cons dst dst' step HP. 
  split.
  Focus 2.
    apply seq_equiv in step as (dst'0 & step & step'). 
    eapply hoare_while_end. 
    apply step'.
    apply prb_true.
  apply free_eq_b in hf1'. apply free_eq_b in hf2'.
  rewrite while_embed_special in step ; trivial.
  generalize dependent HP. generalize dependent step.
  generalize dependent dst'. generalize dependent dst.
  apply hoare_seq with 
    (Q:= (HAnd (HEq (BId y') p) (HAnd (conditionT (HAnd P1 (HEq (BId y) p)) y') 
                                      (conditionF P2 y')))).  
  + eapply hoare_consequence_pre.
    apply hoare_asgn_b.
    intros dst (Prp & HPT & HPF).
    simpl in *.
    unfold conditionT, conditionF.
    rewrite 2 sub_over_condition; simpl.
    apply beq_bid_false_iff in neq. rewrite neq.
    rewrite beq_bid_refl.
    rewrite hf1', hf2'.
    intuition.
    rewrite <- Prp; apply pr_equivalence.
    intros. simpl. destruct (snd t y); reflexivity.
  + eapply hoare_if_prob with (c1:=WHILE y DO c END) (c2:=Skip) (p:=p); trivial.
    repeat constructor. 
    apply free_then_unassigned; assumption.
    constructor.
    eapply hoare_consequence.
    apply hoare_while_det with (P:=(scale P1 (1 / p))) (D:=D); trivial.
    simpl. intros dst H. destruct H as ((H1 & H2) & H3). 
    split; trivial.
    left. unfold Rdiv in H2. rewrite Rmult_comm in H2. rewrite <- Rmult_assoc in H2. 
          rewrite Rinv_r_simpl_m in H2. apply H2. lra.
    intros dst H. destruct H; assumption. 
    eapply hoare_consequence_pre.
    apply hoare_skip.
    intros dst H. destruct H; assumption. 
Qed.    

(** ** The "General" Hoare While Rule *)

Theorem hoare_while_gen : forall P1 D P2 c y y' p, 
  y' <> y ->
  hx_bid_free P1 y' ->
  hx_bid_free P2 y' ->
  com_bid_free c y' ->
  non_probabilistic D ->
  {{HAnd (scale P1 (1/p)) (HTrue y)}} c {{ scale P1 (1/p) }} ->
  {{HAnd D (HTrue y)}} c {{ HAnd D (HOr (HTrue y) (HFalse y)) }} ->
  scale P1 (1/p) ->> D -> 
  {{ HAnd (HEq (BId y) p) (HAnd (conditionT P1 y) (conditionF P2 y)) }} 
  y':==(BId y); WHILE y DO c END
  {{ HAnd (HAnd (conditionT P1 y') (conditionF P2 y')) (HFalse y) }}.
Proof.
  intros P1 D P2 c y y' p neq hf1' hf2' cf' np inv' inv cons dst dst' step HP. 
  split.
  Focus 2.
    apply seq_equiv in step as (dst'0 & step & step'). 
    eapply hoare_while_end. 
    apply step'.
    apply prb_true.
  apply free_eq_b in hf1'. apply free_eq_b in hf2'.
  rewrite while_embed_special in step ; trivial.
  generalize dependent HP. generalize dependent step.
  generalize dependent dst'. generalize dependent dst.
  apply hoare_seq with 
    (Q:= (HAnd (HEq (BId y') p) (HAnd (conditionT (HAnd P1 (HEq (BId y) p)) y') 
                                      (conditionF P2 y')))).  
  + eapply hoare_consequence_pre.
    apply hoare_asgn_b.
    intros dst (Prp & HPT & HPF).
    simpl in *.
    unfold conditionT, conditionF.
    rewrite 2 sub_over_condition; simpl.
    apply beq_bid_false_iff in neq. rewrite neq.
    rewrite beq_bid_refl.
    rewrite hf1', hf2'.
    intuition.
    rewrite <- Prp; apply pr_equivalence.
    intros. simpl. destruct (snd t y); reflexivity.
  + assert (p = 0 \/ p <> 0) as H by lra.
    destruct H as [Z | NZ]. 
    - intros dst dst' step (Pry & ((HPEq & HPT) & HPF)).
      simpl in *.
      rewrite Z in Pry.
      rewrite <- if_false_equiv in step; trivial.
      apply skip_equiv in step. subst.
      intuition.
    - eapply hoare_if_gen with (c1:=WHILE y DO c END) (c2:=Skip) (p:=p); trivial.
      repeat constructor. 
      apply free_then_unassigned; assumption.
      constructor.
      intros H; inversion H; assumption. 
      eapply hoare_consequence.
      apply hoare_while_det with (P:=(scale P1 (1 / p))) (D:=D); trivial.
      simpl. intros dst H. destruct H as ((H1 & H2) & H3). 
      split; trivial.
      left. unfold Rdiv in H2. rewrite Rmult_comm in H2. 
            rewrite <- Rmult_assoc in H2. rewrite Rinv_r_simpl_m in H2. 
            apply H2. assumption.
    intros dst H. destruct H; assumption. 
    eapply hoare_consequence_pre.
    apply hoare_skip.
    intros dst H. destruct H; assumption. 
Qed.    