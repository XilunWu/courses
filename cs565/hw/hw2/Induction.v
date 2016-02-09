Require String. Open Scope string_scope.

Ltac move_to_top x :=
  match reverse goal with
    | H : _ |- _ => try move x after H
  end.

Tactic Notation "assert_eq" ident(x) constr(v) :=
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
  Case "b = true". (* <----- here *)
  reflexivity.
  Case "b = false". (* <---- and here *)
  rewrite <- H.
  reflexivity.
Qed.

Theorem andb_true_elim2 : forall b c : bool,
                            andb b c = true -> c = true.
Proof.
  intros b c H.
  destruct b.
  Case "b = true".
  destruct c.
  SCase "c = true".  
  reflexivity.
  SCase "c = false".
  rewrite <- H.
  reflexivity.
  Case "b = false".
  destruct c.
  SCase "c = true".
  reflexivity.
  SCase "c = false".
  rewrite <- H.
  reflexivity.
Qed.  

Theorem plus_0_r_firsttry : forall n : nat,
                              n + 0 = n.
Proof. intros n. induction n as [| n'].
       Case "n = 0". reflexivity.
       Case "n = S n'". simpl. rewrite -> IHn'. reflexivity.
Qed.

Theorem minus_diag : forall n,
                       minus n n = 0.
Proof.
  intros n. induction n as [| n'].
  Case "n = 0". reflexivity.
  Case "n = S n'". simpl. rewrite -> IHn'. reflexivity.
Qed.

Theorem mult_0_r : forall n : nat,
                     n * 0 = 0.
Proof. intros n. induction n as [| n'].
       Case "n = 0". reflexivity.
       Case "n = S n'". simpl. rewrite -> IHn'. reflexivity.
Qed.

Theorem plus_n_Sm : forall n m : nat,
                      S (n + m) = n + (S m).
Proof. intros n. induction n as [| n'].
       Case "n = 0". simpl. reflexivity.
       Case "n = S n'". simpl. intros m. rewrite -> IHn'.
       reflexivity.
Qed.

(* May not be the best way *)
Theorem plus_comm : forall n m : nat,
                      n + m = m + n.
Proof. intros n. induction n as [| n'].
       Case "n = 0".
       intros m. induction m as [| m'].
       SCase "m = 0". reflexivity.
       SCase "m = S m'". simpl. rewrite <- IHm'. reflexivity.
       Case "n = S n'". intros m. destruct m as [| m'].
       SCase "m = 0". simpl. rewrite -> IHn'. reflexivity.
       SCase "m = S m'". simpl. rewrite -> plus_n_Sm. rewrite -> IHn'. simpl. rewrite -> plus_n_Sm. reflexivity.
Qed.

Theorem plus_assoc : forall n m p : nat,
                       n + (m + p) = (n + m) + p.
Proof.
  intros n. induction n as [| n'].
  Case "n = 0". intros m p. reflexivity.
  Case "n = S n'". simpl. intros m p. rewrite -> IHn'. reflexivity.
Qed.

Fixpoint double (n : nat) :=
  match n with
    | O => O
    | S n' => S (S (double n'))
  end.

Lemma double_plus : forall n : nat,
                      double n = n + n.
Proof.
  intros n. induction n as [| n'].
  Case "n = 0". reflexivity.
  Case "n = S n'". simpl. rewrite -> IHn'. rewrite -> plus_n_Sm.
  reflexivity.
Qed.

(* 
  Exercise: 1 star (destruct_induction)
  Briefly explain the difference between the tactics destruct and induction. 
*)
(* induction introduces the induction hypothesis proven in previous cases which can be used as hypothesis in the following proof case, while destruct doesn't have relationship among cases. *)

Theorem mult_0_plus' : forall n m : nat,
                         (0 + n) * m = n * m.
Proof.
  intros n m.
  assert (H : 0 + n = n).
  (* Note that we could also name the assertion with as just as we did above with destruct and induction, i.e., assert (0 + n = n) as H. *)
  Case "Proof of assertion". reflexivity.
  rewrite -> H.
  reflexivity.
Qed.

Theorem plus_rearrange_firsttry : forall n m p q : nat,
                                    (n + m) + (p + q) = (m + n) + (p + q).
Proof. 
  intros n m p q.
  (* We just need to swap (n + m) for (m + n)...
     it seems like plus_comm should do the trick! *)
  assert (H : n + m = m + n).
  Case "Proof of assertion". rewrite -> plus_comm. reflexivity.
  rewrite -> H.
  reflexivity.
Qed.

Theorem plus_swap : forall n m p : nat,
                      n + (m + p) = m + (n + p).
Proof.
  intros n m p.
  rewrite -> plus_assoc.  
  rewrite -> plus_assoc.
  assert (H : n + m = m + n).
  Case "Proof of assertion". rewrite -> plus_comm. reflexivity.
  rewrite -> H.
  reflexivity.
Qed.

Theorem mult_comm_help : forall m n: nat,
                      m + m * n = m * S n.
Proof.
  intros m. induction m as [| m'].
  Case "m = 0". reflexivity.
  Case "m = S m'".
  intros n.
  simpl.
  rewrite -> plus_swap.
  rewrite -> IHm'.
  reflexivity.
Qed.

Theorem mult_comm : forall m n : nat,
                      m * n = n * m.
Proof.
  intros m. induction m as [| m'].
  Case "m = 0". intros n. rewrite -> mult_0_r. reflexivity.
  Case "m = S m'".
  intros n. simpl. rewrite -> IHm'. rewrite -> mult_comm_help.
  reflexivity.
Qed.

Theorem mult_comm2 : forall m n : nat,
                      m * n = n * m.
Proof.
  intros. induction n as [|n'].
  - Case "n = 0". simpl. rewrite mult_0_r. reflexivity.
  - Case "n = S n'". simpl. rewrite <-IHn'. clear IHn'. induction m as [|m'].
    + SCase "m = 0". simpl. reflexivity.
    + SCase "m = S m'". simpl. rewrite IHm'. rewrite plus_swap. reflexivity.
Qed.

Require Export Basics.

Lemma double_negb : forall n,
                      negb (negb n) = n.
Proof.
  intros n. induction n as [| n'].
  Case "n = O". reflexivity.
  Case "n = S n'". reflexivity.
Qed.

Theorem evenb_n__oddb_Sn : forall n : nat,
                             evenb n = negb (evenb (S n)).
Proof.
  intros n. induction n as [| n'].
  reflexivity.
  assert (H1 : forall n, evenb (S (S n)) = evenb n).
  Case "Proof of assertion". intros n. reflexivity.
  rewrite -> H1.
  assert (H2 : forall n, negb (evenb (S n)) = evenb n).
  intros n. induction n as [| n_1].
  SCase "n = O". reflexivity.
  SCase "n = S n_1". rewrite -> H1. rewrite <- IHn_1. rewrite -> double_negb. reflexivity.
  rewrite <- H2. rewrite -> H1.
  reflexivity.
Qed.

Theorem ble_nat_refl : forall n:nat,
                           true = ble_nat n n.
Proof.
  intros n. induction n as [| n']. reflexivity. simpl. rewrite <- IHn'. reflexivity. Qed.

Theorem zero_nbeq_S : forall n:nat,
                        beq_nat 0 (S n) = false.
Proof. reflexivity. Qed.

Theorem andb_false_r : forall b : bool,
                         andb b false = false.
Proof.
  intros b. destruct b.
  Case "b = true". reflexivity.
  Case "b = false". reflexivity.
Qed.

Theorem plus_ble_compat_l : forall n m p : nat,
                              ble_nat n m = true ->
                              ble_nat (p + n) (p + m) = true.
Proof.
  intros n m p H.
  induction p as [| p'].
  Case "p = 0". simpl. rewrite -> H. reflexivity.
  Case "p = S p'". simpl. rewrite -> IHp'. reflexivity.
Qed.

Theorem S_nbeq_0 : forall n:nat,
                     beq_nat (S n) 0 = false.
Proof. reflexivity. Qed.

Theorem mult_1_l : forall n:nat, 1 * n = n.
Proof.
  intros n. induction n as [| n'].
  Case "n = 0". reflexivity.
  Case "n = S n'". simpl. rewrite -> plus_comm. reflexivity.
Qed.

Theorem all3_spec : forall b c : bool,
                      orb
                        (andb b c)
                        (orb (negb b)
                             (negb c))
                      = true.
Proof.
  intros b c. destruct b.
  Case "b = true". destruct c.
  SCase "c = true". reflexivity.
  SCase "c = false". reflexivity.
  Case "b = false". reflexivity.
Qed.

Theorem mult_plus_distr_r : forall n m p : nat,
                              (n + m) * p = (n * p) + (m * p).
Proof.
  intros n m. induction n as [| n'].
  Case "n = 0". reflexivity.
  Case "n = S n'". simpl. intros p. rewrite -> IHn'. rewrite <- plus_assoc. reflexivity.
Qed.  

Theorem mult_assoc : forall n m p : nat,
                       n * (m * p) = (n * m) * p.
Proof.
  intros n m p.
  induction n as [| n'].
  Case "n = 0". reflexivity.
  Case "n = S n'". simpl. rewrite -> IHn'. rewrite -> mult_plus_distr_r. reflexivity.
Qed.

Theorem beq_nat_refl : forall n : nat,
                         true = beq_nat n n.
Proof.
  intros n. induction n as [| n'].
  reflexivity.
  Case "n = S n'". simpl. rewrite <- IHn'. reflexivity.
Qed.

Theorem plus_swap' : forall n m p : nat,
                       n + (m + p) = m + (n + p).
Proof.
  intros n m p.
  rewrite -> plus_assoc.
  rewrite -> plus_assoc.
  replace (n + m) with (m + n).
  reflexivity.
  Case "Proof of replace". rewrite plus_comm. reflexivity.
Qed.

