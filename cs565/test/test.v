Inductive day : Type :=
| monday : day
| tuesday : day
| wednesday : day
| thursday : day
| friday : day
| saturday : day
| sunday : day.

Definition next_weekday (d:day) : day :=
  match d with
    | monday    => tuesday
    | tuesday   => wednesday
    | wednesday => thursday
    | thursday  => friday
    | friday    => monday
    | saturday  => monday
    | sunday    => monday
  end.

Eval compute in (next_weekday friday).
(* ==> monday : day *)

Eval compute in (next_weekday (next_weekday saturday)).
(* ==> tuesday : day *)

Example test_next_weekday:
  (next_weekday (next_weekday saturday)) = tuesday.

Proof. simpl. reflexivity. Qed.

Definition admit {T: Type} : T.  Admitted.

(* ex1 *)
Definition negb (b:bool) : bool :=
  match b with
    | true => false
    | false => true
  end.

Definition andb (b1:bool) (b2:bool) : bool :=
  match b1 with
    | true => b2
    | false => false
  end.

Definition orb (b1:bool) (b2:bool) : bool :=
  match b1 with
    | true => true
    | false => b2
  end.

Definition nandb (b1:bool) (b2:bool) : bool :=
  match b1 with
    | true => (negb b2)
    | false => true
  end.
    
Example test_nandb1: (nandb true false) = true.
Proof. reflexivity. Qed.
Example test_nandb2: (nandb false false) = true.
Proof. reflexivity. Qed.
Example test_nandb3: (nandb false true) = true.
Proof. reflexivity. Qed.
Example test_nandb4: (nandb true true) = false.
Proof. reflexivity. Qed.

Definition andb3 (b1:bool) (b2:bool) (b3:bool) : bool :=
  match b1 with
    | true => andb b2 b3
    | false => false
  end.

Example test_andb31: (andb3 true true true) = true.
Proof. reflexivity. Qed.
Example test_andb32: (andb3 false true true) = false.
Proof. reflexivity. Qed.
Example test_andb33: (andb3 true false true) = false.
Proof. reflexivity. Qed.
Example test_andb34: (andb3 true true false) = false.
Proof. reflexivity. Qed.

Check andb3.
Check (andb3 true true false).
Check negb.

Definition minustwo (n : nat) : nat :=
  match n with
    | O => O
    | S O => O
    | S (S n') => n'
  end.

Check (S O).
Eval compute in (minustwo 1).
Check O.

Fixpoint evenb (n:nat) : bool :=
  match n with
    | O => true
    | S O => false
    | S (S n') => evenb n'
  end.

Definition oddb (n:nat) : bool := negb (evenb n).

Example test_oddb1: (oddb (S O)) = true.
Proof. reflexivity. Qed.
Example test_oddb2: (oddb (S (S (S (S O))))) = false.
Proof. reflexivity. Qed.

Fixpoint plus (n : nat) (m : nat) : nat :=
  match n with
    | O => m
    | S n' => S (plus n' m)
  end.
Eval compute in (plus (S (S (S O))) (S (S O))).

Fixpoint mult (n m : nat) : nat :=
  match n with
    | O => O
    | S n' => plus m (mult n' m)
  end.

Eval compute in (mult 3 3).

Fixpoint minus (n m:nat) : nat :=
  match n, m with
    | O, _ => O
    | S _, O => n
    | S n', S m' => minus n' m'
  end.

Eval compute in (minus 1 0).
Example test_minus: (minus 1 0) = 1.
Proof. reflexivity. Qed.

Fixpoint exp (base power : nat) : nat :=
  match power with
    | O => S O
    | S power' => mult base (exp base power')
  end.

Example test_exp: (exp 2 3) = 8.
Proof. reflexivity. Qed.

Fixpoint factorial (n:nat) : nat :=
  match n with
    | O => S O
    | S n' => mult n (factorial n')
  end.
Example test_factorial1: (factorial 3) = 6.
Proof. reflexivity. Qed.
Example test_factorial2: (factorial 5) = (mult 10 12).
Proof. reflexivity. Qed.

(*
Notation "x + y" := (plus x y)
                      (at level 50, left associativity)
                    : nat_scope.
Notation "x - y" := (minus x y)
                      (at level 50, left associativity)
                    : nat_scope.
Notation "x × y" := (mult x y)
                      (at level 40, left associativity)
                    : nat_scope.
*)
Check (0 + 1 + 1).

Fixpoint beq_nat (n m : nat) : bool :=
  match n, m with
    | O, O => true
    | O, S _ => false
    | S _, O => false
    | S n', S m' => beq_nat n' m'
  end.

Eval compute in (beq_nat 0 0).
Eval compute in (beq_nat 1 0).
Eval compute in (beq_nat 0 1).
Eval compute in (beq_nat 1 1).

Fixpoint ble_nat (n m : nat) : bool :=
  match n with
    | O => true
    | S n' =>
        match m with
          | O => false
          | S m' => ble_nat n' m'
        end
  end.

Definition blt_nat (n m : nat) : bool :=
  (andb (ble_nat n m) (negb(beq_nat n m))).

Example test_blt_nat1: (blt_nat 2 2) = false.
Proof. reflexivity. Qed.
Example test_blt_nat2: (blt_nat 2 4) = true.
Proof. reflexivity. Qed.
Example test_blt_nat3: (blt_nat 4 2) = false.
Proof. reflexivity. Qed.

Theorem plus_O_n : forall n, 0 + n = n.
Proof. intros n. reflexivity. Qed.

Theorem plus_id_example : forall n m : nat,
                            n = m ->
                            n + n = m + m.
Proof. intros n m. (* move both quantifiers into the context *)
       intros H. (* move the hypothesis into the context *)
       rewrite <- H.
       (* Rewrite the goal using the hypothesis *)
       reflexivity. Qed.

Theorem plus_id_exercise : forall n m o : nat,
                             n = m ->
                             m = o ->
                             n + m = m + o.
Proof.
  intros n m o.
  intros H1 H2.
  rewrite -> H1, H2.
  reflexivity. Qed.

Theorem mult_0_plus : forall n m : nat,
                        (0 + n) * m = n * m.
Proof.
  intros n m.
  rewrite -> plus_O_n.
  reflexivity. Qed.

(* ex2 *)
Theorem plus_1_1 : forall n : nat,
                     1 + n = S n.

Proof.
  intros n. reflexivity. Qed.
  
Theorem mult_S_1 : forall n m : nat,
                     m = S n ->
                     m * (1 + n) = m * m.
Proof.
  intros n m.
  intros H.
  rewrite -> plus_1_1.
  rewrite <- H.
  reflexivity. Qed.

Theorem plus_1_neq_0 : forall n : nat,
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
  intros n. destruct n as [| n'].
  reflexivity.
  reflexivity.
Qed.

Theorem identity_fn_applied_twice :
  forall (f : bool -> bool),
    (forall (x : bool), f x = x) ->
    forall (b : bool), f (f b) = b.
Proof.
  intros f.
  intros H.
  intros b.
  rewrite -> H.
  rewrite -> H.
  reflexivity.
Qed.

Theorem negation_fn_applied_twice :
  forall (f : bool -> bool),
    (forall (x : bool), f x = negb x) ->
    forall (b : bool), f (f b) = b.
Proof.
  intros f.
  intros H.
  intros b. destruct b.
  rewrite -> H.
  rewrite -> H.
  reflexivity.
  rewrite -> H.
  rewrite -> H.
  reflexivity.
Qed.

Theorem andb_eq_orb1 :
  forall (b c : bool),
    (andb b c = orb b c) ->
    b = c.
Proof.
  intros b c. destruct b. destruct c.
  simpl.
  reflexivity.
  simpl.
  intros H.
  rewrite -> H.
  reflexivity.
  simpl.
  intros H.
  rewrite -> H.
  reflexivity.
Qed.

Inductive bin : Type :=
| B0 : bin
| B1 : bin -> bin
| B2 : bin -> bin.

Fixpoint incr (a : bin) : bin :=
  match a with
    | B0 => B2 B0
    | B1 n => B2 n
    | B2 n => B1 (incr n)
  end.


Fixpoint bin_to_nat (a : bin) : nat :=
  match a with
    | B0 => 0
    | B1 n => 2 * (bin_to_nat n)
    | B2 n => 1 + 2 * (bin_to_nat n)
  end.

Eval compute in (bin_to_nat (incr B0)).
Eval compute in (bin_to_nat (incr (B2 B0))).
Eval compute in (bin_to_nat (incr (B1 (B2 B0)))).

Example test_bin_incr1 :
  (bin_to_nat (incr B0)) = (S (bin_to_nat B0)).
Proof. reflexivity. Qed.

Example test_bin_incr2 :
  (bin_to_nat (incr (B1 B0))) = (S (bin_to_nat (B1 B0))).
Proof. reflexivity. Qed.

Example test_bin_incr3 :
  (bin_to_nat (incr (B2 B0))) = (S (bin_to_nat (B2 B0))).
Proof. reflexivity. Qed.

Example test_bin_incr4 :
  (bin_to_nat (incr (B1 (B2 B0)))) = (S (bin_to_nat (B1 (B2 B0)))).
Proof. reflexivity. Qed.

Example test_bin_incr5 :
  (bin_to_nat (incr (incr (B1 B0)))) = (S (S (bin_to_nat (B1 B0)))).
Proof. reflexivity. Qed.

Fixpoint plus' (n : nat) (m : nat) : nat :=
  match n with
    | O => m
    | S n' => S (plus' n' m)
  end.

(*
Fixpoint strange_func (n : nat) : nat :=
  match n with
    | O => strange_func (S O)
    | S n' => O
  end.
*)
Fixpoint strange_func (n : nat) : nat :=
  match n with
    | O => O
    | S n' => strange_func O
  end.
