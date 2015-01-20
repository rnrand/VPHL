(** * PrImp: A Simple Probabilistic Imperative Language *)

Require Export SfLib.
Require Export Distributions.
Require Export Coq.Logic.ProofIrrelevance.

(* ################################################### *)
(** ** Arithmetic and Boolean Expressions  *)

Open Scope nat_scope.

Inductive aexp : Type :=
  | ANum : nat -> aexp
  | AId : aid -> aexp             
  | APlus : aexp -> aexp -> aexp
  | AMinus : aexp -> aexp -> aexp
  | AMult : aexp -> aexp -> aexp.

Fixpoint aeval (a : aexp) (st:state) : nat :=
  match a with
  | ANum n => n
  | AId x => (fst st) x                                    
  | APlus a1 a2 => (aeval a1 st) + (aeval a2 st)
  | AMinus a1 a2  => (aeval a1 st) - (aeval a2 st)
  | AMult a1 a2 => (aeval a1 st) * (aeval a2 st)
  end.

Inductive bexp : Type :=
  | BTrue : bexp
  | BFalse : bexp
  | BId : bid -> bexp
  | BEq : aexp -> aexp -> bexp
  | BLe : aexp -> aexp -> bexp
  | BNot : bexp -> bexp
  | BAnd : bexp -> bexp -> bexp.

(** Useful Abbreviations *)
Definition BLt a1 a2: bexp := BLe (APlus a1 (ANum 1)) a2.
Definition BGt a1 a2: bexp := BNot (BLe a1 a2).
Definition BGe a1 a2: bexp := BNot (BLt a1 a2).
Definition BOr b1 b2: bexp := BNot (BAnd (BNot b1) (BNot b2)).
Definition BIff b1 b2 : bexp := BOr (BAnd b1 b2) (BAnd (BNot b1) (BNot b2)).

Fixpoint beval (b : bexp) (st:state) : bool :=
  match b with
  | BTrue       => true
  | BFalse      => false
  | BId y       => (snd st) y
  | BEq a1 a2   => beq_nat (aeval a1 st) (aeval a2 st)
  | BLe a1 a2   => ble_nat (aeval a1 st) (aeval a2 st)
  | BNot b1     => negb (beval b1 st)
  | BAnd b1 b2  => andb (beval b1 st) (beval b2 st)
  end.

(* ################################################### *)
(** ** State Distributions  *)

Open Scope R_scope.

Definition dstate : Type := dist state. 

Definition empty_dstate : dstate := Unit empty_state.

Notation "'Prb' b 'in' dst"  := (Pr (beval b) in dst) (at level 40).


(** *** Translating the bexp connectives *)

Lemma bor_eq : forall b1 b2 dst,
  Prb (BOr b1 b2) in dst = 
  Pr ((fun st => beval b1 st) || (fun st => beval b2 st)) in dst.
Proof. 
  simpl.
  induction dst.
  + simpl.   
    destruct (beval b1 t), (beval b2 t); reflexivity.
  + simpl.
    rewrite IHdst1.
    rewrite IHdst2.
    reflexivity.  
Qed.

Lemma biff_imp : forall dst b1 b2,
  Prb (BIff b1 b2) in dst = 1 ->
  Prb b1 in dst = Prb b2 in dst.
Proof.
  intros.
  induction dst. 
  + simpl in *.
    destruct (beval b1 t), (beval b2 t); trivial.
    simpl in H. lra.
  + apply pr_split_1 in H as (H1 & H2).
    simpl.
    rewrite IHdst1; trivial.
    rewrite IHdst2; trivial.
Qed.

(** *** Special Cases of ProbTheory Specific to State Distributions *)

Lemma prb_true: forall dst, Prb BTrue in dst = 1.
Proof. intros. apply pr_tautology. reflexivity. Qed.

Lemma prb_false: forall dst, Prb BFalse in dst = 0. 
Proof. intros. apply pr_contradiction. reflexivity. Qed.

Lemma prb_complement_1 : forall dst b, Prb b in dst = 1 <-> Prb (BNot b) in dst = 0.
Proof. intros. rewrite pr_complement_1. reflexivity. Qed.

Lemma prb_complement_0 : forall dst b, Prb b in dst = 0 <-> Prb (BNot b) in dst = 1.
Proof. intros. rewrite pr_complement_0. reflexivity. Qed.

(* ################################################### *)
(** ** Updating Distributions *)


Fixpoint dist_update (dst : dstate) (x: aid) (a : aexp) : dstate :=
  match dst with
  | Unit st => Unit (update st x (aeval a st))
  | Combine p v dst1 dst2 =>
    Combine p v (dist_update dst1 x a) (dist_update dst2 x a)
  end.

Fixpoint dist_update_b (dst : dstate) (y: bid) (b : bexp) : dstate :=
  match dst with
  | Unit st => Unit (update_b st y (beval b st))
  | Combine p v dst1 dst2 =>
    Combine p v (dist_update_b dst1 y b) (dist_update_b dst2 y b)
  end.


Fixpoint prob_update (dst : dstate) (x:aid) (p:R) (v:0<p<1) : dstate :=
  match dst with
  | Unit st => Combine p v (Unit (update st x 1)) (Unit (update st x 0))
  | Combine p0 v0 dst1 dst2 =>
    Combine p0 v0 (prob_update dst1 x p v) (prob_update dst2 x p v)
  end.

Fixpoint prob_update_b (dst : dstate) (y:bid) (p:R) (v:0<p<1) : dstate :=
  match dst with
  | Unit st => Combine p v (Unit (update_b st y true)) 
                           (Unit (update_b st y false))
  | Combine p0 v0 dst1 dst2 =>
    Combine p0 v0 (prob_update_b dst1 y p v) (prob_update_b dst2 y p v)
  end.

Lemma dist_update_true : forall dst y,
  Prb (BId y) in (dist_update_b dst y BTrue) = 1.
Proof.
  intros.
  induction dst.
  + simpl.
    rewrite beq_bid_refl.
    reflexivity.
  + simpl in *.
    rewrite IHdst1, IHdst2.
    lra.
Qed.

Lemma dist_update_false : forall dst y,
  Prb (BId y) in (dist_update_b dst y BFalse) = 0.
Proof.
  intros. 
  induction dst.
  + simpl.
    rewrite beq_bid_refl.
    reflexivity.
  + simpl in *.
    rewrite IHdst1, IHdst2.
    lra.
Qed.


(** *** Non-interference Rules of Updates  *)

Theorem update_non_interference : forall st a y b,
  aeval a (update_b st y b) = aeval a st. 
Proof.
  intros.
  induction a; trivial.
  + simpl. rewrite IHa1, IHa2. reflexivity.
  + simpl. rewrite IHa1, IHa2. reflexivity.
  + simpl. rewrite IHa1, IHa2. reflexivity.
Qed.

Lemma dist_update_non_interference: forall dst x y a b,
  b = BTrue \/ b = BFalse ->
  dist_update_b (dist_update dst x a) y b =  
  dist_update (dist_update_b dst y b) x a.
Proof.
  intros.
  destruct H; subst.
  + induction dst; simpl.
    - rewrite update_non_interference.
      rewrite update_interpermute; reflexivity.
    - rewrite IHdst1, IHdst2; reflexivity.
  + induction dst; simpl.
    - rewrite update_non_interference.
      rewrite update_interpermute; reflexivity.
    - rewrite IHdst1, IHdst2; reflexivity.
Qed.

Lemma prob_update_non_interference: forall dst x y b p v,
  b = BTrue \/ b = BFalse ->
  dist_update_b (prob_update dst x p v) y b =  
  prob_update (dist_update_b dst y b) x p v.
Proof.
  intros.
  destruct H; subst.
  + induction dst; simpl.
    - rewrite update_interpermute; reflexivity.
    - rewrite IHdst1, IHdst2; reflexivity.
  + induction dst; simpl.
    - rewrite update_interpermute; reflexivity.
    - rewrite IHdst1, IHdst2; reflexivity.
Qed.

(* ####################################################### *)
(** ** Commands *)

Inductive com : Type :=
  | Skip : com
  | Assign : aid -> aexp -> com
  | BAssign : bid -> bexp -> com
  | Seq : com -> com -> com
  | If : bid -> com -> com -> com
  | While : bid -> com -> com  
  | Toss : forall p:R, 0 < p < 1 -> aid -> com
  | BToss : forall p:R, 0 < p < 1 -> bid -> com.

(** Notations *) 

Notation "x '::=' a" :=
  (Assign x a) (at level 60).
Notation "y ':==' b" :=
  (BAssign y b) (at level 60).
Notation "c1 ; c2" :=
  (Seq c1 c2) (at level 80, right associativity).
Notation "'WHILE' x 'DO' c 'END'" :=
  (While x c) (at level 80, right associativity).
Notation "'IFB' y 'THEN' c1 'ELSE' c2 'FI'" :=
  (If y c1 c2) (at level 80, right associativity).
Notation "x '$=(' p ',' v ')'" :=
  (Toss p v x) (at level 60, right associativity).
Notation "y '$=[' p ',' v ']'" :=
  (BToss p v y) (at level 60, right associativity).

Reserved Notation "mc '/' dst '||' dst'" (at level 40, dst at level 39).

Inductive ceval : com -> dstate -> dstate -> Prop :=
  | E_Skip : forall st,
      Skip / Unit st || Unit st
  | E_Assign  : forall st x a n,
      aeval a st = n ->
      (x ::= a) / Unit st || Unit (update st x n)
  | E_BAssign  : forall st y b b0,
      beval b st = b0 ->
      (y :== b) / Unit st || Unit (update_b st y b0)
  | E_Seq : forall st dst' dst'' c1 c2,
      c1 / Unit st  || dst' ->
      c2 / dst' || dst'' ->
      (c1 ; c2) / Unit st || dst''
  | E_IfTrue : forall st dst' y c1 c2,
      snd st y = true ->
      c1 / Unit st || dst' ->
      (IFB y THEN c1 ELSE c2 FI) / Unit st || dst'
  | E_IfFalse : forall st dst' y c1 c2,
      snd st y = false ->
      c2 / (Unit st) || dst' ->
      (IFB y THEN c1 ELSE c2 FI) / Unit st || dst'
  | E_WhileEnd : forall st y c,
      snd st y = false ->
      (WHILE y DO c END) / Unit st || Unit st
  | E_WhileLoop : forall st dst' dst'' y c,
      snd st y = true ->
      c / (Unit st) || dst' ->
      (WHILE y DO c END) / dst' || dst'' ->
      (WHILE y DO c END) / Unit st || dst''
  | E_Toss : forall st x p v,
       (x $=(p,v)) / Unit st || 
         Combine p v (Unit (update st x 1)) (Unit (update st x 0))
  | E_BToss : forall st y p v,
      (y $=[p,v]) / Unit st || 
         Combine p v (Unit (update_b st y true)) (Unit (update_b st y false))
  | E_Lift  : forall dst1 dst1' dst2 dst2' c p v,
      c / dst1 || dst1' ->
      c / dst2 || dst2' ->
      c / Combine p v dst1 dst2 || Combine p v dst1' dst2'

  where "c '/' dst '||' dst'" := (ceval c dst dst').

(** Lemma 3.2: Step Determinism *)
Lemma step_deterministic : forall c dst dst1 dst2,
  c / dst || dst1 ->
  c / dst || dst2 ->
  dst1 = dst2.
Proof.
  intros c dst dst1 dst2 step1 step2.
  generalize dependent dst2. 
  induction step1; intros. 
  + inversion step2. reflexivity.
  + inversion step2; subst; reflexivity.
  + inversion step2; subst; reflexivity. 
  + inversion step2; subst.
    apply IHstep1_1 in H2. subst.
    apply IHstep1_2 in H4. subst.
    reflexivity.
  + inversion step2; subst.
    apply IHstep1 in H6. assumption.
    rewrite H in H5. inversion H5.  
  + inversion step2; subst.
    rewrite H in H5. inversion H5.
    apply IHstep1 in H6. assumption.
  + inversion step2; subst.
    reflexivity.
    rewrite H in H3. inversion H3.
  + inversion step2; subst.
    rewrite H in H4. inversion H4.
    apply IHstep1_2.
    specialize (IHstep1_1 dst'0 H4).
    subst. assumption.
  + inversion step2; subst.
    replace v1 with v by (apply proof_irrelevance).    
    reflexivity.
  + inversion step2; subst.
    replace v1 with v by (apply proof_irrelevance).    
    reflexivity.
  + inversion step2; subst.
    replace v1 with v by (apply proof_irrelevance).    
    apply IHstep1_1 in H4.
    apply IHstep1_2 in H5.
    subst. reflexivity.
Qed.    

(** Commands take Combinations only to Combinations 
    This follow directly from our definitions, but is useful in place of doing inversion. *)

(** Lemma 3.1: Decomposition *)
Lemma step_split : forall c p v dst1 dst2 dst',
  c / Combine p v dst1 dst2 || dst' ->
  (exists dst1' dst2', dst' = Combine p v dst1' dst2' /\
   c / dst1 || dst1' /\ c / dst2 || dst2').
Proof.
  intros. 
  inversion H; subst. 
  exists dst1', dst2'.
  replace v1 with v by apply proof_irrelevance.
  split; [reflexivity | split; assumption].
Qed.

(* ####################################################### *)
(** ** Applying Commands Over Distributions *)

Lemma skip_lift : forall dst, Skip / dst || dst.
Proof.
  induction dst.
  apply E_Skip.
  apply E_Lift; assumption.
Qed.  

Lemma skip_equiv : forall dst dst', Skip / dst || dst' <-> dst' = dst.  
Proof.
  intros dst dst'.
  split.
  + intros step.
    specialize (skip_lift dst); intros step'.
    apply step_deterministic with (dst1:=dst) in step; subst; trivial.
  + intros; subst.
    apply skip_lift.
Qed.

Lemma seq_lift : forall c1 c2 dst dst' dst'', 
  c1 / dst || dst' ->
  c2 / dst' || dst'' ->
  (c1 ; c2) / dst || dst''.
Proof.
  intros c1 c2 dst.
  induction dst as [st | ].
  + intros dst' dst'' step1 step2.
    apply E_Seq with (dst':=dst'); assumption.
  + intros dst' dst'' step1 step2.
    inversion step1; subst.
    inversion step2; subst.
    replace v0 with a in * by (apply proof_irrelevance). clear v0.
    replace v1 with a in * by (apply proof_irrelevance). clear v1.
    constructor.
    apply IHdst1 with (dst':=dst1'); assumption. 
    apply IHdst2 with (dst':=dst2'); assumption. 
Qed.  

Lemma seq_equiv : forall c1 c2 dst dst'',
  (c1 ; c2) / dst || dst'' <-> 
  (exists dst', c1 / dst || dst' /\ c2 / dst' || dst'').
Proof.
  intros c1 c2 dst dst''.
  split. 
  2: intros (dst' & step1 & step2); apply seq_lift with (dst':=dst'); assumption.
  generalize dependent dst''; induction dst as [st | ].
  + intros dst'' step.
    inversion step; subst.
    exists dst'; auto.
  + intros dst' step.    
    inversion step; subst.
    replace v0 with a by (apply proof_irrelevance).    
    specialize (IHdst1 dst1' H4). destruct IHdst1 as (dst1m & step11 & step12).
    specialize (IHdst2 dst2' H5). destruct IHdst2 as (dst2m & step21 & step22).
    exists (Combine p a dst1m dst2m).
    split; constructor; assumption.
Qed.    

Lemma assign_lift: forall x a dst, (x::=a) / dst || dist_update dst x a.
Proof. 
  intros x a dst.
  induction dst.
  apply E_Assign; reflexivity.
  simpl.
  apply E_Lift; assumption.
Qed.

Lemma assign_equiv : forall x a dst dst', 
  (x::=a) / dst || dst' <-> dst' = dist_update dst x a.  
Proof.
  intros x a dst dst'.
  split.
  + intros step.
    specialize (assign_lift x a dst); intros step'.
    apply step_deterministic with (dst1:=dst') in step'; assumption.
  + intros; subst.
    apply assign_lift.
Qed.

Lemma bassign_lift : forall y b dst, (y:==b) / dst || dist_update_b dst y b.
Proof. 
  intros y b dst.
  induction dst.
  apply E_BAssign; reflexivity.
  simpl.
  apply E_Lift; assumption.
Qed.

Lemma bassign_equiv : forall y b dst dst', 
  (y:==b) / dst || dst' <-> dst' = dist_update_b dst y b.  
Proof.
  intros y b dst dst'.
  split.
  + intros step.
    specialize (bassign_lift y b dst); intros step'.
    apply step_deterministic with (dst1:=dst') in step'; assumption.
  + intros; subst.
    apply bassign_lift.
Qed.

Lemma toss_lift : forall x p v dst,  x $=(p,v) / dst || prob_update dst x p v.
Proof.
  intros x p v dst.
  induction dst.
  apply E_Toss.
  simpl.
  apply E_Lift; assumption.
Qed.

Lemma toss_equiv: forall x p v dst dst', 
  (x $=(p,v)) / dst || dst' <-> dst' = prob_update dst x p v.
Proof.
  intros x p v dst dst'.
  split.
  + intros step.
    specialize (toss_lift x p v dst); intros step'.
    apply step_deterministic with (dst1:=dst') in step'; assumption.
  + intros; subst.
    apply toss_lift.
Qed.  

Lemma btoss_lift : forall y p v dst,  y $=[p,v] / dst || prob_update_b dst y p v.
Proof.
  intros y p v dst.
  induction dst.
  apply E_BToss.
  simpl.
  apply E_Lift; assumption.
Qed.
    
Lemma btoss_equiv: forall y p v dst dst', 
  (y $=[p,v]) / dst || dst' <-> dst' = prob_update_b dst y p v.
Proof.
  intros y p v dst dst'.
  split.
  + intros step.
    specialize (btoss_lift y p v dst); intros step'.
    apply step_deterministic with (dst1:=dst') in step'; assumption.
  + intros; subst.
    apply btoss_lift.
Qed.  

Lemma if_true_lift: forall y c1 c2 dst dst',
  Prb (BId y) in dst = 1 ->
  c1 / dst || dst' -> 
  IFB y THEN c1 ELSE c2 FI / dst || dst'.
Proof.
  induction dst; intros.
  + apply E_IfTrue; trivial.
    simpl in H.
    destruct (snd t y); trivial.
    lra.
  + apply pr_split_1 in H as (Pr1 & Pr2); trivial.
    inversion H0; subst.
    replace v0 with a in * by apply proof_irrelevance. clear v0.
    apply E_Lift.
    apply IHdst1; assumption.
    apply IHdst2; assumption.
Qed.
  
Lemma if_true_equiv : forall y c1 c2 dst dst',
  Prb (BId y) in dst = 1 ->
  (c1 / dst || dst' <-> IFB y THEN c1 ELSE c2 FI / dst || dst').
Proof.
  split.
  intros; apply if_true_lift; trivial.
  generalize dependent dst'.
  induction dst; intros.
  + inversion H0; subst.
    assumption.
    simpl in H.
    rewrite H6 in H.
    lra.
  + apply pr_split_1 in H as (Pr1 & Pr2); trivial.
    inversion H0; subst.
    replace v0 with a in * by apply proof_irrelevance. clear v0.
    apply E_Lift.
    apply IHdst1; assumption.
    apply IHdst2; assumption.
Qed.
    
Lemma if_false_lift : forall y c1 c2 dst dst',
  Prb (BId y) in dst = 0 ->
  c2 / dst || dst' -> 
  IFB y THEN c1 ELSE c2 FI / dst || dst'.
Proof. 
  induction dst; intros.
  + apply E_IfFalse; trivial.
    simpl in H.
    destruct (snd t y); trivial.
    lra.
  + apply pr_split_0 in H as (Pr1 & Pr2); trivial.
    inversion H0; subst.
    subst.
    replace v0 with a in * by apply proof_irrelevance. clear v0.
    apply E_Lift.    
    apply IHdst1; assumption.
    apply IHdst2; assumption.
Qed.

Lemma if_false_equiv : forall y c1 c2 dst dst',
  Prb (BId y) in dst = 0 ->
  (c2 / dst || dst' <-> IFB y THEN c1 ELSE c2 FI / dst || dst').
Proof.
  split.
  apply if_false_lift; trivial.
  generalize dependent dst'.
  induction dst; intros.
  + inversion H0; subst.
    simpl in H.
    rewrite H6 in H.
    lra.
    assumption.
  + apply pr_split_0 in H as (Pr1 & Pr2); trivial.
    inversion H0; subst.
    replace v0 with a in * by apply proof_irrelevance. clear v0.
    apply E_Lift.    
    apply IHdst1; assumption.
    apply IHdst2; assumption.
Qed.

Lemma if_equiv : forall y c1 c2 dst1 dst2 dst1' dst2' p v,
  Prb (BId y) in dst1 = 1 ->
  Prb (BId y) in dst2 = 0 ->
  (c1 / dst1 || dst1' /\ c2 / dst2 || dst2' <->
  (IFB y THEN c1 ELSE c2 FI) / Combine p v dst1 dst2 || Combine p v dst1' dst2').
Proof.
  intros.
  split.
  + intros.
    destruct H1.
    apply E_Lift.
    apply if_true_lift; assumption.
    apply if_false_lift; assumption.
  + intros.
    inversion H1; subst.
    split.
    eapply if_true_equiv.
    apply H.
    apply H5.
    eapply if_false_equiv.
    apply H0.
    apply H9.
Qed.    


Lemma while_end_lift : forall y c dst,
  Prb (BId y) in dst = 0 ->
  (WHILE y DO c END) / dst || dst.
Proof.
  intros.
  induction dst.
  + apply E_WhileEnd.
    simpl in H.
    destruct (snd t y); [lra | reflexivity].
  + apply pr_split_0 in H; trivial. 
    destruct H as [H H0].
    apply E_Lift.
    apply IHdst1; assumption.
    apply IHdst2; assumption.
Qed.

Lemma while_end_equiv : forall y c dst dst',
  Prb (BId y) in dst = 0 ->
  ((WHILE y DO c END) / dst || dst' <-> dst' = dst).
Proof.
  intros.
  split.
  + intros step.
    specialize (while_end_lift y c dst H); intros step'.
    apply step_deterministic with (dst1:=dst) in step; subst; trivial.
  + intros; subst.
    apply while_end_lift; trivial.
Qed.

Lemma while_loop_lift : forall y c dst dst'',
  Prb (BId y) in dst = 1 ->
  (WHILE y DO c END) / dst || dst'' ->
  exists dst', c / dst || dst' /\ (WHILE y DO c END) / dst' || dst''.
Proof.
  intros y c dst dst'' Pr1 step.
  + remember (WHILE y DO c END) as com.
    induction step; inversion Heqcom; subst.
    - simpl in Pr1.
      rewrite H in Pr1; lra.
    - exists dst'; split; assumption.
    - apply pr_split_1 in Pr1 as (Pr1 & Pr2); trivial.
      specialize (IHstep1 Pr1 H).
      specialize (IHstep2 Pr2 H).
      destruct IHstep1 as (dst1'' & step1' & while1). 
      destruct IHstep2 as (dst2'' & step2' & while2). 
      exists (Combine p v dst1'' dst2'').
      split.
      apply E_Lift; assumption.
      apply E_Lift; assumption.
Qed.
  
Lemma while_loop_equiv : forall y c dst dst'',
  Prb (BId y) in dst = 1 ->
  ((WHILE y DO c END) / dst || dst'' <->
   exists dst', c / dst || dst' /\ (WHILE y DO c END) / dst' || dst'').
Proof.
  intros y c dst dst'' Pr1.
  split.
  apply while_loop_lift; assumption.
  + intros (dst' & step & step').
    generalize dependent dst''.  generalize dependent dst'.
    induction dst.
    - intros.
      apply E_WhileLoop with (dst':=dst'); trivial.
      simpl in Pr1.      
      destruct (snd t y); trivial; lra.
    - intros.
      apply pr_split_1 in Pr1 as (Pr1 & Pr2); trivial.
      inversion step; subst.
      inversion step'; subst.      
      replace v0 with a in * by apply proof_irrelevance. clear v0.
      replace v1 with a in * by apply proof_irrelevance. clear v1.
      apply E_Lift.
      apply IHdst1 with (dst':=dst1'); trivial.
      apply IHdst2 with (dst':=dst2'); trivial.
Qed.      
