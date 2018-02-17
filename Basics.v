Inductive day : Type :=
| monday : day
| tuesday : day
| wednesday : day
| thursday : day
| friday : day
| saturday : day
| sunday : day.


Definition next_weekday (d : day) : day :=
  match d with
  | monday => tuesday
  | tuesday => wednesday
  | wednesday => thursday
  | thursday => friday
  | friday => saturday
  | saturday => sunday
  | sunday => monday
  end.

Inductive bool : Type :=
| true : bool
| false : bool.

Definition negb (b : bool) : bool :=
  match b with
  | true => false
  | false => true
  end.

Definition andb (b1 : bool) (b2 : bool) :=
  match b1 with
  | true => b2
  | false => false
  end.

Definition orb (b1 : bool) (b2 : bool) :=
  match b1 with
  | true => true
  | false => b2
  end.

Fixpoint evenb (n:nat) : bool :=
  match n with
  | O        => true
  | S O      => false
  | S (S n') => evenb n'
  end.

Eval simpl in (next_weekday (next_weekday saturday)).

Example test_orb1: (orb true false) = true.
Proof. simpl. reflexivity. Qed.
Example test_orb2: (orb false false) = false.
Proof. simpl. reflexivity. Qed.
Example test_orb3: (orb false true ) = true.
Proof. simpl. reflexivity. Qed.
Example test_orb4: (orb true true ) = true.
Proof. simpl. reflexivity. Qed.

Definition nandb (b1 : bool) (b2 : bool) : bool :=
  match b1, b2 with
  | true, true => false
  | false, true => true
  | true, false => true
  | false, false => true
  end.

Example test_nandb1: (nandb true false) = true.
Proof. simpl. reflexivity. Qed.
Example test_nandb2: (nandb false false) = true.
Proof. simpl. reflexivity. Qed.
Example test_nandb3: (nandb false true) = true.
Proof. simpl. reflexivity. Qed.
Example test_nandb4: (nandb true true) = false.
Proof. simpl. reflexivity. Qed.

Check (negb true).
Check negb.

Theorem plus_0_n : forall n : nat, 0 + n = n.
Proof.
  simpl. reflexivity. Qed.

Eval simpl in (forall n : nat, n + 0 = n).
Eval simpl in (forall n : nat, 0 + n = n).

Fixpoint beq_nat (n m : nat) : bool :=
  match n with
  | O => match m with
         | O => true
         | S m' => false
         end
  | S n' => match m with
            | O => false
            | S m' => beq_nat n' m'
            end
  end.

Theorem plus_0_n'' : forall n : nat, 0 + n = n.
Proof.
  intros n. reflexivity. Qed.

Theorem plus_id_example : forall n m : nat,
    n = m ->
    n + n = m + m.
Proof.
  intros n m. intros H. rewrite -> H.
  reflexivity. Qed.

Theorem plus_id_exercise : forall n m o : nat,
    n = m -> m = o -> n + m = m + o.
Proof.
  intros m n o. intros H. intros I.
  rewrite -> H. rewrite -> I.
  reflexivity.
Qed.

Theorem mult_0_plus : forall n m : nat,
  (0 + n) * m = n * m.
Proof.
  intros n m.
  rewrite -> plus_O_n.
  reflexivity.
Qed.

Theorem plus_1_n : forall n : nat, 1 + n = S n.
Proof.
  intros n. reflexivity.
Qed.

Theorem mult_1_plus : forall n m : nat,
    (1 + n) * m = m + (n * m).
Proof.
  intros n m.
  rewrite -> plus_1_n.
  reflexivity.
Qed.

Theorem plus_1_neq_0_firsttry : forall n : nat,
    beq_nat (n + 1) 0 = false.
Proof.
  intros n. destruct n as [| n'].
  reflexivity.
  reflexivity.
Qed.

Theorem negb_involutive : forall b : bool,
    negb (negb b) = b.
Proof.
  intros b. destruct b.
  reflexivity.
  reflexivity.
Qed.

Theorem zero_nbeq_plus_1 : forall n : nat,
    beq_nat 0 (n + 1) = false.
Proof.
  intros n. destruct n as [O | S n'].
  reflexivity.
  reflexivity.
Qed.


Require String. Open Scope string_scope.

Ltac move_to_top x :=
  match reverse goal with
  | H : _ |- _ => try move x after H
  end.

Tactic Notation "assert_eq" ident(x) constr (v) :=
  let H := fresh in
  assert (x = v) as H by reflexivity;
  clear H.

Tactic Notation "Case_aux" ident(x) constr(name) :=
  first [
    set (x := name); move_to_top x
  | assert_eq x name; move_to_top x
  | fail 1 "because we are working on a different case" ].

Tactic Notation "Case" constr(name) := Case_aux Case name.
Tactic Notation "SCase" constr(name) := Case_aux SCase name.
Tactic Notation "SSCase" constr(name) := Case_aux SSCase name.
Tactic Notation "SSSCase" constr(name) := Case_aux SSSCase name.
Tactic Notation "SSSSCase" constr(name) := Case_aux SSSSCase name.
Tactic Notation "SSSSSCase" constr(name) := Case_aux SSSSSCase name.
Tactic Notation "SSSSSSCase" constr(name) := Case_aux SSSSSSCase name.
Tactic Notation "SSSSSSSCase" constr(name) := Case_aux SSSSSSSCase name.

Theorem andb_true_elim1 : forall b c : bool,
    andb b c = true -> b = true.
Proof.
  intros b c H.
  destruct b.
  Case "b = true". reflexivity.
  Case "b = false". rewrite <- H. reflexivity.
Qed.

Theorem andb_true_elim2 : forall b c : bool,
    andb b c = true -> c = true.
Proof.
  intros [] [].
  - reflexivity.
  - simpl. intros H. rewrite -> H. reflexivity.
  - reflexivity.
  - simpl. intros H. rewrite -> H. reflexivity.
Qed.

Theorem plus_0_r : forall n : nat, n + 0 = n.
Proof.
  intros n. induction n as [| n'].
  Case "n = 0". reflexivity.
  Case "n = S n". simpl. rewrite -> IHn'. reflexivity.
Qed.


Theorem minus_diag : forall n,
    minus n n = 0.
Proof.
  intros n.
  induction n as [| n'].
  Case "n = 0".
    simpl. reflexivity.
  Case "n = S n'".
  simpl. rewrite -> IHn'. reflexivity.
Qed.

Theorem mult_0_r : forall n : nat,
    n * 0 = 0.
Proof.
  intros n.
  induction n as [| n'].
  Case "n = 0".
  simpl.
  reflexivity.
  Case "n = S n'".
  simpl.
  rewrite -> IHn'.
  reflexivity.
Qed.

Theorem plus_n_Sm : forall n m : nat,
    S (n + m) = n + (S m).
Proof.
  intros n m.
  induction n as [| n'].
  Case "n = 0".
  simpl.
  reflexivity.
  Case "n = S n'".
  simpl.
  rewrite -> IHn'.
  reflexivity.
Qed.

Theorem plus_0 : forall n : nat,
    n + 0 = n.
Proof.
  intros n.
  induction n as [| n'].
  Case "n = 0".
  simpl.
  reflexivity.
  Case "n = S n'".
  simpl.
  rewrite -> IHn'.
  reflexivity.
Qed.


Theorem plus_comm : forall n m : nat,
    n + m = m + n.
Proof.
  intros n m.
  induction n as [ | n'].
  Case "n = 0".
  simpl.
  rewrite -> plus_0.
  reflexivity.
  Case "n = S n'".
  simpl.
  rewrite -> IHn'.
  rewrite <- plus_n_Sm.
  reflexivity.
Qed.

Fixpoint double (n : nat) :=
  match n with
  | O => O
  | S n' => S (S (double n'))
  end.

Lemma double_plus : forall n, double n = n + n.
Proof.
  intros n.
  induction n as [ | n'].
  Case "n = 0".
  simpl.
  reflexivity.
  Case "n = S n'".
  simpl.
  rewrite -> IHn'.
  rewrite -> plus_n_Sm.
  reflexivity.
Qed.