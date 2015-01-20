(** * SfLib: Modified From the Software Foundations Library 

These are the basic notions that will go into our development.

We introduce identifiers and states, and discuss their properties.

This file in particular, as well as core part PrImp.v were based upon 
Pierce et al's Software Foundations, available at:
http://www.cis.upenn.edu/~bcpierce/sf/current/index.html
*)

(** Imports and basic notions *)

Require Omega. 
Require Export Bool.
Require Export Arith.
Require Export Arith.EqNat.  (* Contains [beq_nat], among other things *)
Require Export Coq.Logic.FunctionalExtensionality.

Require String. Open Scope string_scope.

Fixpoint ble_nat (n m : nat) : bool :=
  match n with
  | O => true
  | S n' =>
      match m with
      | O => false
      | S m' => ble_nat n' m'
      end
  end.

(** Arithmetic Identifiers *)

Inductive aid : Type := Aid : nat -> aid.

Definition beq_aid (i1 i2 : aid) := 
  match (i1, i2) with (Aid n1, Aid n2) => beq_nat n1 n2 end.

Theorem beq_aid_refl : forall i, beq_aid i i = true.
Proof. intros. destruct i. symmetry. apply beq_nat_refl. Qed.

Theorem beq_aid_eq : forall i1 i2, beq_aid i1 i2 = true -> i1 = i2.
Proof.
  intros i1 i2 H. destruct i1; destruct i2.
  symmetry in H. apply beq_nat_eq in H; subst; reflexivity.
Qed.

Theorem beq_aid_false_iff : forall i1 i2, beq_aid i1 i2 = false <-> i1 <> i2.
Proof.
  split.
  intros H eq. rewrite eq in H. rewrite beq_aid_refl in H. inversion H.
  intros H. destruct i1; destruct i2. apply beq_nat_false_iff. auto.
Qed.

(** Boolean Identifiers *)

Inductive bid : Type := Bid : nat -> bid.

Definition beq_bid (i1 i2 : bid) := 
  match (i1, i2) with (Bid n1, Bid n2) => beq_nat n1 n2 end.

Theorem beq_bid_refl : forall i, beq_bid i i = true.
Proof. intros. destruct i. symmetry. apply beq_nat_refl. Qed.

Theorem beq_bid_eq : forall i1 i2, beq_bid i1 i2 = true -> i1 = i2.
Proof.
  intros i1 i2 H. destruct i1; destruct i2.
  symmetry in H; apply beq_nat_eq in H; subst; reflexivity.
Qed.

Theorem beq_bid_false_iff : forall i1 i2, beq_bid i1 i2 = false <-> i1 <> i2.
Proof.
  split.
  intros H eq. rewrite eq in H. rewrite beq_bid_refl in H. inversion H.
  intros H. destruct i1; destruct i2. apply beq_nat_false_iff. auto.
Qed.

(* ####################################################### *)
(** ** States *)

(** A _state_ represents the current values of all the variables at
    some point in the execution of a program. *)
(** For simplicity (to avoid dealing with partial functions), we
    let the state be defined for _all_ variables, even though any
    given program is only going to mention a finite number of them. *)

Definition state := ((aid -> nat) * (bid -> bool))%type. 

Definition empty_state : state :=
  (fun _ => 0, fun _ => false). 

Definition update (st : state) (x : aid) (n : nat) : state :=
  (fun x' => if beq_aid x x' then n else (fst st) x', snd st). 

Definition update_b (st : state) (y : bid) (b : bool) : state :=
  (fst st, fun y' => if beq_bid y y' then b else (snd st) y'). 

(** Properties of [update]. *)

Theorem update_eq : forall n x st, fst (update st x n) x = n.
Proof. intros; unfold update; simpl; rewrite beq_aid_refl; reflexivity. Qed.

Theorem update_neq : forall x2 x1 n st,
  beq_aid x2 x1 = false -> fst (update st x2 n) x1 = (fst st x1).
Proof.
  intros x2 x1 n st Hneq; simpl.
  unfold update.
  rewrite -> Hneq.
  reflexivity. 
Qed.

Theorem update_same : forall n1 x1 st,
  fst st x1 = n1 -> update st x1 n1 = st.
Proof.
  intros n1 x1 st Heq; simpl.
  apply injective_projections; trivial.
  apply functional_extensionality; intros.
  unfold update. subst. simpl.
  destruct (beq_aid x1 x) eqn:Eq; trivial.
  apply beq_aid_eq in Eq. subst. reflexivity.
Qed.

Theorem update_permute : forall n1 n2 x1 x2 st,
  beq_aid x2 x1 = false ->
  update (update st x2 n1) x1 n2 = update (update st x1 n2) x2 n1.
Proof.
  intros n1 n2 x1 x2 st H; simpl.
  apply injective_projections; trivial.
  apply functional_extensionality; intros.
  simpl.
  destruct (beq_aid x1 x) eqn:Eq1, (beq_aid x2 x) eqn:Eq2; trivial.
  apply beq_aid_eq in Eq1; apply beq_aid_eq in Eq2.
  apply beq_aid_false_iff in H.
  subst.
  contradict H. reflexivity.
Qed.

Theorem update_permute_b : forall b1 b2 y1 y2 st,
  beq_bid y2 y1 = false ->
  update_b (update_b st y2 b1) y1 b2 = update_b (update_b st y1 b2) y2 b1.
Proof.
  intros b1 b2 y1 y2 st H; simpl.
  apply injective_projections; trivial.
  apply functional_extensionality; intros.
  simpl.
  destruct (beq_bid y1 x) eqn:Eq1, (beq_bid y2 x) eqn:Eq2; trivial.
  apply beq_bid_eq in Eq1; apply beq_bid_eq in Eq2.
  apply beq_bid_false_iff in H.
  subst.
  contradict H. reflexivity.
Qed.

(** The following is trivial due to the non-conflicting nature of our updates, 
  but worth expressing explicitly. (In fact, reflexivity alone can prove this.) *)

Theorem update_interpermute : forall x y n b st,
  update_b (update st x n) y b = update (update_b st y b) x n.
Proof.
  intros.
  apply injective_projections; reflexivity.
Qed.