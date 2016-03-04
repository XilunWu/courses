(** * MoreCoq: More About Coq's Tactics *)

Require Export Poly.

Theorem silly1 : forall (n m o p : nat),
     n = m  ->
     [n;o] = [n;p] ->
     [n;o] = [m;p].
Proof.
  intros n m o p eq1 eq2.
  rewrite <- eq1.
  apply eq2.  Qed.

Theorem silly2 : forall (n m o p : nat),
     n = m  ->
     (forall (q r : nat), q = r -> [q;o] = [r;p]) ->
     [n;o] = [m;p].
Proof.
  intros n m o p eq1 eq2. 
  apply eq2. apply eq1.  Qed.

Theorem silly2a : forall (n m : nat),
     (n,n) = (m,m)  ->
     (forall (q r : nat), (q,q) = (r,r) -> [q] = [r]) ->
     [n] = [m].
Proof.
  intros n m eq1 eq2.
  apply eq2. apply eq1.  Qed.

Theorem silly_ex : 
     (forall n, evenb n = true -> oddb (S n) = true) ->
     evenb 3 = true ->
     oddb 4 = true.
Proof. intros eq1 eq2. apply eq1. apply eq2. Qed.

Theorem silly3 : forall (n : nat),
     true = beq_nat n 5  ->
     beq_nat (S (S n)) 7 = true.
Proof.
  intros n H.
  symmetry.
  simpl. (* Actually, this [simpl] is unnecessary, since 
            [apply] will perform simplification first. *)
  apply H.  Qed.         

Theorem rev_exercise1 : forall (l l' : list nat),
     l = rev l' ->
     l' = rev l.
Proof.
  intros. rewrite H. symmetry. apply rev_involutive.
Qed.

(** **** Exercise: 1 star, optional (apply_rewrite)  *)
(** Briefly explain the difference between the tactics [apply] and
    [rewrite].  Are there situations where both can usefully be
    applied?
  (* 
Rewrite: rewrite is a tactic replacing part of the goal with left side or right side of an existing lemma/hypothesis.

Apply: apply will examine if the goal's left side and right side equals to those of an existing lemma/hypothesis correspondingly. This examination is done via reflexivity.

There're situations where both can be applied. 
   *)
*)

(* ###################################################### *)
(** * The [apply ... with ...] Tactic *)

(** The following silly example uses two rewrites in a row to
    get from [[a,b]] to [[e,f]]. *)

Example trans_eq_example : forall (a b c d e f : nat),
     [a;b] = [c;d] ->
     [c;d] = [e;f] ->
     [a;b] = [e;f].
Proof.
  intros a b c d e f eq1 eq2. 
  rewrite -> eq1. rewrite -> eq2. reflexivity.  Qed.

(** Since this is a common pattern, we might
    abstract it out as a lemma recording once and for all
    the fact that equality is transitive. *)

Theorem trans_eq : forall (X:Type) (n m o : X),
  n = m -> m = o -> n = o.
Proof.
  intros X n m o eq1 eq2. rewrite -> eq1. rewrite -> eq2. 
  reflexivity.  Qed.

(** Now, we should be able to use [trans_eq] to
    prove the above example.  However, to do this we need
    a slight refinement of the [apply] tactic. *)

Example trans_eq_example' : forall (a b c d e f : nat),
     [a;b] = [c;d] ->
     [c;d] = [e;f] ->
     [a;b] = [e;f].
Proof.
  intros a b c d e f eq1 eq2. 
  apply trans_eq with (m:=[c;d]). apply eq1. apply eq2.   Qed.

(** **** Exercise: 3 stars, optional (apply_with_exercise)  *)
Example trans_eq_exercise : forall (n m o p : nat),
     m = (minustwo o) ->
     (n + p) = m ->
     (n + p) = (minustwo o). 
Proof.
  intros n m o p eq1 eq2. apply trans_eq with (m:=m). apply eq2.
  apply eq1.
Qed.

Theorem eq_add_S : forall (n m : nat),
     S n = S m ->
     n = m.
Proof.
  intros n m eq. inversion eq. reflexivity.  Qed.

Theorem silly4 : forall (n m : nat),
     [n] = [m] ->
     n = m.
Proof.
  intros n o eq. inversion eq. reflexivity.  Qed.

Theorem silly5 : forall (n m o : nat),
     [n;m] = [o;o] ->
     [n] = [m].
Proof.
  intros n m o eq. inversion eq. reflexivity. Qed.

(** **** Exercise: 1 star (sillyex1)  *) 
Example sillyex1 : forall (X : Type) (x y z : X) (l j : list X),
     x :: y :: l = z :: j ->
     y :: l = x :: j ->
     x = y.
Proof.
  intros X x y z l j eq1 eq2.
  inversion eq1. inversion eq2. rewrite H0. reflexivity.
Qed.
  
Theorem silly6 : forall (n : nat),
     S n = O ->
     2 + 2 = 5.
Proof.
  intros n contra. inversion contra. Qed.

Theorem silly7 : forall (n m : nat),
     false = true ->
     [n] = [m].
Proof.
  intros n m contra. inversion contra.  Qed.

(** **** Exercise: 1 star (sillyex2)  *)
Example sillyex2 : forall (X : Type) (x y z : X) (l j : list X),
     x :: y :: l = [] ->
     y :: l = z :: j ->
     x = z.
Proof. intros. inversion H. Qed.

Theorem f_equal : forall (A B : Type) (f: A -> B) (x y: A), 
    x = y -> f x = f y. 
Proof. intros A B f x y eq. rewrite eq.  reflexivity.  Qed. 

(** **** Exercise: 2 stars, optional (practice)  *)
(** A couple more nontrivial but not-too-complicated proofs to work
    together in class, or for you to work as exercises. *)
Theorem beq_nat_0_l : forall n,
   beq_nat 0 n = true -> n = 0.
Proof.
  intros. destruct n. reflexivity.
  inversion H.
Qed.

Theorem beq_nat_0_r : forall n,
   beq_nat n 0 = true -> n = 0.
Proof.
  intros. destruct n. reflexivity.
  inversion H.
Qed.

Theorem S_inj : forall (n m : nat) (b : bool),
     beq_nat (S n) (S m) = b  ->
     beq_nat n m = b. 
Proof.
  intros n m b H. simpl in H. apply H.  Qed.

Theorem silly3' : forall (n : nat),
  (beq_nat n 5 = true -> beq_nat (S (S n)) 7 = true) ->
     true = beq_nat n 5  ->
     true = beq_nat (S (S n)) 7.
Proof.
  intros n eq H.
  symmetry in H. apply eq in H. symmetry in H. 
  apply H.  Qed.
(** **** Exercise: 3 stars (plus_n_n_injective)  *)
(** Practice using "in" variants in this exercise. *)

Theorem plus_n_n_injective : forall n m,
     n + n = m + m ->
     n = m.
Proof.
  intros n. induction n as [| n'].
  - Case "n = O". intros. simpl in H. destruct m.
    + SCase "m = O". reflexivity.
    + SCase "m = S m'". inversion H.
  - Case "n = S n'". intros. destruct m.
    + SCase "m = O". inversion H.
    + SCase "m = S m'". simpl in H. inversion H. rewrite <- plus_n_Sm in H1.
      rewrite <- plus_n_Sm in H1. inversion H1.
      apply IHn' in H2. rewrite H2. reflexivity.
Qed.

Theorem double_injective : forall n m,
     double n = double m ->
     n = m.
Proof.
  intros n. induction n as [| n'].
  Case "n = O". simpl. intros m eq. destruct m as [| m'].
    SCase "m = O". reflexivity.
    SCase "m = S m'". inversion eq. 
  Case "n = S n'". 
    intros m eq.
    destruct m as [| m'].
    SCase "m = O". 
      inversion eq.  
    SCase "m = S m'".  
      apply f_equal. 
      apply IHn'. inversion eq. reflexivity. Qed.

Theorem beq_nat_true : forall n m,
    beq_nat n m = true -> n = m.
Proof.
  intros n. induction n as [| n'].
  Case "n = O". intros m eq. destruct m.
  SCase "m = O". reflexivity.
  SCase "m = S m'". inversion eq.
  Case "n = S n'". intros m eq. destruct m as [| m'].
  SCase "m = O". inversion eq.
  SCase "m = S m'". apply f_equal.
  apply IHn'. inversion eq. reflexivity.
Qed.
  
(** **** Exercise: 2 stars, advanced (beq_nat_true_informal)  *)
(** Give a careful informal proof of [beq_nat_true], being as explicit
    as possible about quantifiers. *)

(*
Theorem: forall n m, if beq_nat n m = true, then n = m.
Proof: 
    By induction on n:
      n = O:
      Destruct on m:
      if m = O. We have beq_nat n m = true and n = m.
      if m = S _. We have beq_nat n m = false.
      Thus we know forall m, if beq_nat O m = true -> O = m.

    Suppose n = S n'. 
      Destruct on m:
      if m = O. We have beq_nat n m = false.
      if m = S m'. Then beq_nat n m = beq_nat n' m'. By the induction hypothesis, we have beq_nat n' m' = true -> n' = m', 
      from which we know beq_nat n m = true -> n = m.

    Qed.
*)
      

(** The strategy of doing fewer [intros] before an [induction] doesn't
    always work directly; sometimes a little _rearrangement_ of
    quantified variables is needed.  Suppose, for example, that we
    wanted to prove [double_injective] by induction on [m] instead of
    [n]. *)

Theorem double_injective_take2_FAILED : forall n m,
     double n = double m ->
     n = m.
Proof.
  intros n m. induction m as [| m'].
  Case "m = O". simpl. intros eq. destruct n as [| n'].
    SCase "n = O". reflexivity.
    SCase "n = S n'". inversion eq. 
  Case "m = S m'". intros eq. destruct n as [| n'].
    SCase "n = O". inversion eq.
    SCase "n = S n'".  apply f_equal.
        (* Stuck again here, just like before. *)
Abort.

(** The problem is that, to do induction on [m], we must first
    introduce [n].  (If we simply say [induction m] without
    introducing anything first, Coq will automatically introduce
    [n] for us!)   *)

(** What can we do about this?  One possibility is to rewrite the
    statement of the lemma so that [m] is quantified before [n].  This
    will work, but it's not nice: We don't want to have to mangle the
    statements of lemmas to fit the needs of a particular strategy for
    proving them -- we want to state them in the most clear and
    natural way. *)

(**  What we can do instead is to first introduce all the
    quantified variables and then _re-generalize_ one or more of
    them, taking them out of the context and putting them back at
    the beginning of the goal.  The [generalize dependent] tactic
    does this. *)

Theorem double_injective_take2 : forall n m,
     double n = double m ->
     n = m.
Proof.
  intros n m. 
  (* [n] and [m] are both in the context *)
  generalize dependent n.
  (* Now [n] is back in the goal and we can do induction on
     [m] and get a sufficiently general IH. *)
  induction m as [| m'].
  Case "m = O". simpl. intros n eq. destruct n as [| n'].
    SCase "n = O". reflexivity.
    SCase "n = S n'". inversion eq.
  Case "m = S m'". intros n eq. destruct n as [| n'].
    SCase "n = O". inversion eq.
    SCase "n = S n'". apply f_equal.
      apply IHm'. inversion eq. reflexivity. Qed.

Theorem length_snoc' : forall (X : Type) (v : X)
                              (l : list X) (n : nat),
     length l = n ->
     length (snoc l v) = S n. 
Proof.
  intros X v l. induction l as [| v' l'].

  Case "l = []". 
    intros n eq. rewrite <- eq. reflexivity.

  Case "l = v' :: l'". 
    intros n eq. simpl. destruct n as [| n'].
    SCase "n = 0". inversion eq.
    SCase "n = S n'".
      apply f_equal. apply IHl'. inversion eq. reflexivity. Qed.

(** It might be tempting to start proving the above theorem
    by introducing [n] and [eq] at the outset.  However, this leads
    to an induction hypothesis that is not strong enough.  Compare
    the above to the following (aborted) attempt: *)

Theorem length_snoc_bad : forall (X : Type) (v : X)
                              (l : list X) (n : nat),
     length l = n ->
     length (snoc l v) = S n. 
Proof.
  intros X v l n eq. induction l as [| v' l'].

  Case "l = []". 
    rewrite <- eq. reflexivity.

  Case "l = v' :: l'". 
    simpl. destruct n as [| n'].
    SCase "n = 0". inversion eq.
    SCase "n = S n'".
      apply f_equal. Abort. (* apply IHl'. *) (* The IH doesn't apply! *)


(** As in the double examples, the problem is that by
    introducing [n] before doing induction on [l], the induction
    hypothesis is specialized to one particular natural number, namely
    [n].  In the induction case, however, we need to be able to use
    the induction hypothesis on some other natural number [n'].
    Retaining the more general form of the induction hypothesis thus
    gives us more flexibility.

    In general, a good rule of thumb is to make the induction hypothesis
    as general as possible. *)

(** **** Exercise: 3 stars (gen_dep_practice)  *)
(** Prove this by induction on [l]. *)

Theorem index_after_last: forall (n : nat) (X : Type) (l : list X),
     length l = n ->
     index n l = None.
Proof.
  intros n X l. generalize dependent n. induction l as [| h l'].
  Case "l = nil".  reflexivity.
  Case "l = h :: l'". intros n. destruct n as [| n'].
  SCase "n = O". intros eq. inversion eq.
  SCase "n = S n'". intros eq. simpl. apply IHl'. inversion eq. reflexivity.
Qed.

(** **** Exercise: 3 stars, advanced, optional (index_after_last_informal)  *)
(** Write an informal proof corresponding to your Coq proof
    of [index_after_last]:
 
     _Theorem_: For all sets [X], lists [l : list X], and numbers
      [n], if [length l = n] then [index n l = None].
 
     _Proof_:
     (* FILL IN HERE *)
[]
*)

(** **** Exercise: 3 stars, optional (gen_dep_practice_more)  *)
(** Prove this by induction on [l]. *)

Theorem length_snoc''' : forall (n : nat) (X : Type) 
                              (v : X) (l : list X),
     length l = n ->
     length (snoc l v) = S n. 
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 3 stars, optional (app_length_cons)  *)
(** Prove this by induction on [l1], without using [app_length]
    from [Lists]. *)

Theorem app_length_cons : forall (X : Type) (l1 l2 : list X) 
                                  (x : X) (n : nat),
     length (l1 ++ (x :: l2)) = n ->
     S (length (l1 ++ l2)) = n.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 4 stars, optional (app_length_twice)  *)
(** Prove this by induction on [l], without using app_length. *)

Theorem app_length_twice : forall (X:Type) (n:nat) (l:list X),
     length l = n ->
     length (l ++ l) = n + n.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)


(** **** Exercise: 3 stars, optional (double_induction)  *)
(** Prove the following principle of induction over two naturals. *)

Theorem double_induction: forall (P : nat -> nat -> Prop), 
  P 0 0 ->
  (forall m, P m 0 -> P (S m) 0) ->
  (forall n, P 0 n -> P 0 (S n)) ->
  (forall m n, P m n -> P (S m) (S n)) ->
  forall m n, P m n.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)


(* ###################################################### *)
(** * Using [destruct] on Compound Expressions *)

(** We have seen many examples where the [destruct] tactic is
    used to perform case analysis of the value of some variable.  But
    sometimes we need to reason by cases on the result of some
    _expression_.  We can also do this with [destruct].

    Here are some examples: *)

Definition sillyfun (n : nat) : bool :=
  if beq_nat n 3 then false
  else if beq_nat n 5 then false
  else false.

Theorem sillyfun_false : forall (n : nat),
  sillyfun n = false.
Proof.
  intros n. unfold sillyfun. 
  destruct (beq_nat n 3).
    Case "beq_nat n 3 = true". reflexivity.
    Case "beq_nat n 3 = false". destruct (beq_nat n 5).
      SCase "beq_nat n 5 = true". reflexivity.
      SCase "beq_nat n 5 = false". reflexivity.  Qed.

(** **** Exercise: 1 star (override_shadow)  *)
Theorem override_shadow : forall (X:Type) x1 x2 k1 k2 (f : nat->X),
  (override (override f k1 x2) k1 x1) k2 = (override f k1 x1) k2.
Proof.
  intros. unfold override.
  destruct (beq_nat k1 k2).
  Case "beq_nat k1 k2 = true". reflexivity.
  Case "beq_nat k1 k2 = false". reflexivity.
Qed.
  (** **** Exercise: 3 stars, optional (combine_split)  *)
(** Complete the proof below *)

Theorem combine_split : forall X Y (l : list (X * Y)) l1 l2,
  split l = (l1, l2) ->
  combine l1 l2 = l.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** Sometimes, doing a [destruct] on a compound expression (a
    non-variable) will erase information we need to complete a proof. *)
(** For example, suppose
    we define a function [sillyfun1] like this: *)

Definition sillyfun1 (n : nat) : bool :=
  if beq_nat n 3 then true
  else if beq_nat n 5 then true
  else false.

(** And suppose that we want to convince Coq of the rather
    obvious observation that [sillyfun1 n] yields [true] only when [n]
    is odd.  By analogy with the proofs we did with [sillyfun] above,
    it is natural to start the proof like this: *)

Theorem sillyfun1_odd_FAILED : forall (n : nat),
     sillyfun1 n = true ->
     oddb n = true.
Proof.
  intros n eq. unfold sillyfun1 in eq.
  destruct (beq_nat n 3).
  (* stuck... *)
Abort.

(** We get stuck at this point because the context does not
    contain enough information to prove the goal!  The problem is that
    the substitution peformed by [destruct] is too brutal -- it threw
    away every occurrence of [beq_nat n 3], but we need to keep some
    memory of this expression and how it was destructed, because we
    need to be able to reason that since, in this branch of the case
    analysis, [beq_nat n 3 = true], it must be that [n = 3], from
    which it follows that [n] is odd.

    What we would really like is to substitute away all existing
    occurences of [beq_nat n 3], but at the same time add an equation
    to the context that records which case we are in.  The [eqn:]
    qualifier allows us to introduce such an equation (with whatever
    name we choose). *)

Theorem sillyfun1_odd : forall (n : nat),
     sillyfun1 n = true ->
     oddb n = true.
Proof.
  intros n eq. unfold sillyfun1 in eq.
  destruct (beq_nat n 3) eqn:Heqe3.
  (* Now we have the same state as at the point where we got stuck
    above, except that the context contains an extra equality
    assumption, which is exactly what we need to make progress. *)
    Case "e3 = true". apply beq_nat_true in Heqe3.
      rewrite -> Heqe3. reflexivity.
    Case "e3 = false".
     (* When we come to the second equality test in the body of the
       function we are reasoning about, we can use [eqn:] again in the
       same way, allow us to finish the proof. *)
      destruct (beq_nat n 5) eqn:Heqe5. 
        SCase "e5 = true".
          apply beq_nat_true in Heqe5.
          rewrite -> Heqe5. reflexivity.
        SCase "e5 = false". inversion eq.  Qed.


(** **** Exercise: 2 stars (destruct_eqn_practice)  *)
Theorem bool_fn_applied_thrice : 
  forall (f : bool -> bool) (b : bool), 
  f (f (f b)) = f b.
Proof.
  intros. destruct b.
  - Case "b = true". destruct (f true) eqn:H1.
    + SCase "(f true) = true". rewrite -> H1. rewrite -> H1. reflexivity.
    + SCase "(f true) = false". destruct (f false) eqn:H2.
      rewrite H1. reflexivity.
      rewrite H2. reflexivity.
  - Case "b = false". destruct (f false) eqn:H3.
    + SCase "(f false) = true". destruct (f true) eqn:H4.
      apply H4.
      apply H3.
    + SCase "(f false) = false". 
      rewrite H3. apply H3.
Qed.

(** **** Exercise: 2 stars (override_same)  *)
Theorem override_same : forall (X:Type) x1 k1 k2 (f : nat->X),
  f k1 = x1 -> 
  (override f k1 x1) k2 = f k2.
Proof.
  intros. unfold override.
  destruct (beq_nat k1 k2) eqn:H1.
  Case "beq_nat k1 k2 = true". rewrite <- H. apply f_equal. apply beq_nat_true. apply H1.
  Case "beq_nat k1 k2 = false". reflexivity.
Qed.
(* ################################################################## *)
(** * Review *)

(** We've now seen a bunch of Coq's fundamental tactics.  We'll
    introduce a few more as we go along through the coming lectures,
    and later in the course we'll introduce some more powerful
    _automation_ tactics that make Coq do more of the low-level work
    in many cases.  But basically we've got what we need to get work
    done.

    Here are the ones we've seen:

      - [intros]: 
        move hypotheses/variables from goal to context 

      - [reflexivity]:
        finish the proof (when the goal looks like [e = e])

      - [apply]:
        prove goal using a hypothesis, lemma, or constructor

      - [apply... in H]: 
        apply a hypothesis, lemma, or constructor to a hypothesis in
        the context (forward reasoning)

      - [apply... with...]:
        explicitly specify values for variables that cannot be
        determined by pattern matching

      - [simpl]:
        simplify computations in the goal 

      - [simpl in H]:
        ... or a hypothesis 

      - [rewrite]:
        use an equality hypothesis (or lemma) to rewrite the goal 

      - [rewrite ... in H]:
        ... or a hypothesis 

      - [symmetry]:
        changes a goal of the form [t=u] into [u=t]

      - [symmetry in H]:
        changes a hypothesis of the form [t=u] into [u=t]

      - [unfold]:
        replace a defined constant by its right-hand side in the goal 

      - [unfold... in H]:
        ... or a hypothesis  

      - [destruct... as...]:
        case analysis on values of inductively defined types 

      - [destruct... eqn:...]:
        specify the name of an equation to be added to the context,
        recording the result of the case analysis

      - [induction... as...]:
        induction on values of inductively defined types 

      - [inversion]:
        reason by injectivity and distinctness of constructors

      - [assert (e) as H]:
        introduce a "local lemma" [e] and call it [H] 

      - [generalize dependent x]:
        move the variable [x] (and anything else that depends on it)
        from the context back to an explicit hypothesis in the goal
        formula 
*)

(* ###################################################### *)
(** * Additional Exercises *)

(** **** Exercise: 3 stars (beq_nat_sym)  *)
Theorem beq_nat_sym : forall (n m : nat),
  beq_nat n m = beq_nat m n.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 3 stars, advanced, optional (beq_nat_sym_informal)  *)
(** Give an informal proof of this lemma that corresponds to your
    formal proof above:

   Theorem: For any [nat]s [n] [m], [beq_nat n m = beq_nat m n].

   Proof:
   (* FILL IN HERE *)
[]
 *)

(** **** Exercise: 3 stars, optional (beq_nat_trans)  *)
Theorem beq_nat_trans : forall n m p,
  beq_nat n m = true ->
  beq_nat m p = true ->
  beq_nat n p = true.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 3 stars, advanced (split_combine)  *)
(** We have just proven that for all lists of pairs, [combine] is the
    inverse of [split].  How would you formalize the statement that
    [split] is the inverse of [combine]? When is this property true?

    Complete the definition of [split_combine_statement] below with a
    property that states that [split] is the inverse of
    [combine]. Then, prove that the property holds. (Be sure to leave
    your induction hypothesis general by not doing [intros] on more
    things than necessary.  Hint: what property do you need of [l1]
    and [l2] for [split] [combine l1 l2 = (l1,l2)] to be true?)  *)

Definition admit {T: Type} : T.  Admitted.

Definition split_combine_statement : Prop :=
(* FILL IN HERE *) admit.

Theorem split_combine : split_combine_statement.
Proof.
(* FILL IN HERE *) Admitted.



(** [] *)

(** **** Exercise: 3 stars (override_permute)  *)
Theorem override_permute : forall (X:Type) x1 x2 k1 k2 k3 (f : nat->X),
  beq_nat k2 k1 = false ->
  (override (override f k2 x2) k1 x1) k3 = (override (override f k1 x1) k2 x2) k3.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 3 stars, advanced (filter_exercise)  *)
(** This one is a bit challenging.  Pay attention to the form of your IH. *)

Theorem filter_exercise : forall (X : Type) (test : X -> bool)
                             (x : X) (l lf : list X),
     filter test l = x :: lf ->
     test x = true.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 4 stars, advanced (forall_exists_challenge)  *)
(** Define two recursive [Fixpoints], [forallb] and [existsb].  The
    first checks whether every element in a list satisfies a given
    predicate:
      forallb oddb [1;3;5;7;9] = true

      forallb negb [false;false] = true
  
      forallb evenb [0;2;4;5] = false
  
      forallb (beq_nat 5) [] = true
    The second checks whether there exists an element in the list that
    satisfies a given predicate:
      existsb (beq_nat 5) [0;2;3;6] = false
 
      existsb (andb true) [true;true;false] = true
 
      existsb oddb [1;0;0;0;0;3] = true
 
      existsb evenb [] = false
    Next, define a _nonrecursive_ version of [existsb] -- call it
    [existsb'] -- using [forallb] and [negb].
 
    Prove theorem [existsb_existsb'] that [existsb'] and [existsb] have
    the same behavior.
*)

(* FILL IN HERE *)
(** [] *)

(** $Date: 2014-12-31 16:01:37 -0500 (Wed, 31 Dec 2014) $ *)



