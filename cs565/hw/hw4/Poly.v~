Require Export Lists.

Inductive list (X:Type) : Type :=
| nil : list X
| cons : X -> list X -> list X.

Check nil.
(* ===> nil : forall X : Type, list X *)
Check nil nat.
(* ===> nil nat : list nat *)
Check cons.
(* ===> nil : forall X : Type, X -> list X -> list X*)
Check cons nat.
(* ===> cons nat : nat -> list nat -> list nat *)
Check (cons nat 2 (cons nat 1 (nil nat))).
Eval compute in (cons nat 2 (cons nat 1 (nil nat))).

Fixpoint length (X:Type) (l:list X): nat :=
  match l with
    | nil => 0
    | cons h t => S (length X t)
  end.

Example test_length1 :
  length nat (cons nat 1 (cons nat 2 (nil nat))) = 2.
Proof. reflexivity. Qed.

Example test_length2 :
  length bool (cons bool true (nil bool)) = 1.
Proof. reflexivity. Qed.


Fixpoint app (X:Type) (l1 l2:list X) : list X :=
  match l1 with
    | nil => l2
    | cons h t => cons X h (app X t l2)
  end.

Fixpoint snoc (X:Type) (l:list X) (v:X) : list X :=
  match l with
    | nil => cons X v (nil X)
    | cons h t => cons X h (snoc X t v)
  end.

Fixpoint rev (X:Type) (l:list X) : list X :=
  match l with
    | nil => nil X
    | cons h t => snoc X (rev X t) h
  end.

Example test_rev1 :
  rev nat (cons nat 1 (cons nat 2 (nil nat)))
  = (cons nat 2 (cons nat 1 (nil nat))).
Proof. reflexivity. Qed.

Example test_rev2:
  rev bool (nil bool) = nil bool.
Proof. reflexivity. Qed.

Module MumbleBaz.

  Inductive mumble : Type :=
  | a : mumble
  | b : mumble -> nat -> mumble
  | c : mumble.
  Inductive grumble (X:Type) : Type :=
  | d : mumble -> grumble X
  | e : X -> grumble X.

  (* d mumble (b a 5)
     d bool (b a 5)
     e bool true
     e mumble (b c 0)
   *)

  Check d mumble (b a 5).
  Check d bool (b a 5).
  Check e bool true.
  Check e mumble (b c 0).

  Inductive baz : Type :=
  | x : baz -> baz
  | y : baz -> bool -> baz.

  (* 0 elements because we can't induce baz from any combination of x and y *)
End MumbleBaz.

Fixpoint app' X l1 l2 : list X :=
  match l1 with
    | nil => l2
    | cons h t => cons X h (app' X t l2)
  end.

Check app'.
(* ===> forall X : Type, list X -> list X -> list X *)
Check app.
(* ===> forall X : Type, list X -> list X -> list X *)

Fixpoint length' (X:Type) (l:list X) : nat :=
  match l with
    | nil => 0
    | cons h t => S (length' _ t)
  end.

Definition list123 :=
  cons nat 1 (cons nat 2 (cons nat 3 (nil nat))).
Definition list123' := cons _ 1 (cons _ 2 (cons _ 3 (nil _))).

Arguments nil {X}.
Arguments cons {X} _ _. (* use underscore for argument position that has no name *)
Arguments length {X} l.
Arguments app {X} l1 l2.
Arguments rev {X} l.
Arguments snoc {X} l v.

Definition list123'' := cons 1 (cons 2 (cons 3 nil)).
Check (length list123'').

Fixpoint length'' {X:Type} (l:list X) : nat :=
  match l with
    | nil => 0
    | cons h t => S (length'' t)
  end.

Check @nil.
Definition mynil' := @nil nat.


Notation "x :: y" := (cons x y)
                       (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y []) ..).
Notation "x ++ y" := (app x y)
                       (at level 60, right associativity).

Fixpoint repeat {X:Type} (n:X) (count:nat) : list X :=
  match count with
    | 0 => nil
    | S n' => n :: (repeat n n')
  end.
Example test_repeat1:
  repeat true 2 = cons true (cons true nil).
Proof. reflexivity. Qed.

Theorem nil_app : forall (X:Type) (l:list X), app [] l = l.
Proof. reflexivity. Qed.

Theorem rev_snoc : forall (X:Type) (v:X) (s:list X),  rev (snoc s v) = v :: (rev s).
Proof. intros. induction s as [|h t].
       Case "s = nil". reflexivity.
       Case "s = h::t". simpl. rewrite IHt. reflexivity.
Qed.

Theorem rev_involutive : forall (X:Type) (l:list X), rev (rev l) = l.
Proof. intros. induction l as [| h t].
       Case "l = nil". reflexivity.
       Case "l = h :: t". simpl. rewrite rev_snoc. rewrite IHt. reflexivity.
Qed.

Theorem snoc_with_append : forall (X:Type) (l1 l2 : list X) (v:X),
                             snoc (l1 ++ l2) v = l1 ++ (snoc l2 v).
Proof. intros. induction l1 as [|h t].
       Case "l1 = nil". reflexivity.
       Case "l1 = h::t". simpl. rewrite IHt. reflexivity.
Qed.

Inductive prod (X Y : Type) : Type :=
  pair : X -> Y -> prod X Y.

Arguments pair {X} {Y} _ _.

Notation "( x , y )" := (pair x y).

Notation "X * Y" := (prod X Y) : type_scope.


Definition fst {X Y : Type} (p : X * Y) : X :=
  match p with (x,y) => x end.

Definition snd {X Y : Type} (p : X * Y) : Y :=
  match p with (x,y) => y end.

Fixpoint combine {X Y : Type} (lx:list X) (ly:list Y) : list (X*Y) :=
  match (lx,ly) with
    | (nil, _) => nil
    | (_, nil) => nil
    | (hx::tx, hy::ty) => (hx, hy) :: (combine tx ty)
  end.

Check combine.
(* ===> list ?134 -> list ?135 -> list (?134 * ?135) *)
Check @combine.
(* ===> forall X Y : Type, list X -> list Y -> list (X * Y) *)
Eval compute in (combine [1;2] [false;false;true;true]).
(* ===> = [(1, false); (2, false)] : list (nat * bool) *)

Fixpoint split {X Y : Type} (p : list (X*Y)) : (list X * list Y) :=
  match p with
    | [] => ([], [])
    | (x, y) :: t => match split t with (xs, ys) => (x::xs, y::ys) end
  end.
Example test_split:
  split [(1,false);(2,false)] = ([1;2],[false;false]).
Proof. reflexivity. Qed.

Inductive option (X:Type) : Type :=
| Some : X -> option X
| None : option X.

Arguments Some {X} _.
Arguments None {X}.

Fixpoint index {X:Type} (n:nat) (l:list X) : option X :=
  match l with
    | [] => @None X
    | a :: l' => if (beq_nat n 0) then Some a else index (pred n) l'
  end.

Example test_index1 : index 0 [4;5;6;7] = Some 4.
Proof. reflexivity. Qed.
Example test_index2 : index 1 [[1];[2]] = Some [2].
Proof. reflexivity. Qed.
Example test_index3 : index 2 [true] = None.
Proof. reflexivity. Qed.

Definition hd_opt {X : Type} (l : list X) : option X :=
  match l with
    | [] => None
    | a :: l' => Some a
  end.
Check @hd_opt.
Example test_hd_opt1 : hd_opt [1;2] = Some 1.
Proof. reflexivity. Qed.
Example test_hd_opt2 : hd_opt [[1];[2]] = Some [1].
Proof. reflexivity. Qed.

Definition doit3times {X:Type} (f: X->X) (n:X) : X := f (f (f n)).
Check @doit3times.
(* ===> doit3times : forall X : Type, (X -> X) -> X -> X *)

Example test_doit3times: doit3times minustwo 9 = 3.
Proof. reflexivity. Qed.

Example test_doit3times': doit3times negb true = false.
Proof. reflexivity. Qed.
Check plus.
(* ==> nat -> nat -> nat *)
Check (plus 3).
(* ==> nat -> nat*)
Definition plus3 := plus 3.
Check plus3.
Example test_plus3 : plus3 4 = 7.
Proof. reflexivity. Qed.
Example test_plus3' : doit3times plus3 0 = 9.
Proof. reflexivity. Qed.
Example test_plus3'' : doit3times (plus 3) 0 = 9.
Proof. reflexivity. Qed.

Definition prod_curry {X Y Z : Type}
           (f: X * Y -> Z) (x:X) (y:Y) : Z := f (x,y).

Definition prod_uncurry {X Y Z : Type}
           (f: X -> Y -> Z) (p : X * Y) : Z := match p with (x,y) => f x y end.

Check @prod_curry.
Check @prod_uncurry.

Theorem uncurry_curry : forall (X Y Z : Type) (f: X -> Y -> Z) x y,
                          prod_curry (prod_uncurry f) x y = f x y.
Proof. reflexivity. Qed.

Theorem curry_uncurry : forall (X Y Z : Type) (f: X * Y -> Z) p,
                          prod_uncurry (prod_curry f) p = f p.
Proof. intros. destruct p as [x y]. reflexivity. Qed.

Fixpoint filter {X:Type} (test: X -> bool) l : list X :=
  match l with
    | [] => []
    | h :: t => if (test h) then h :: (filter test t) else filter test t
  end.

Example test_filter1: filter evenb [1;2;3;4] = [2;4].
Proof. reflexivity. Qed.

Definition length_is_1 {X : Type} (l : list X) : bool :=
  beq_nat (length l) 1.
Example test_filter2:
  filter length_is_1
         [ [1; 2]; [3]; [4]; [5;6;7]; []; [8] ]
  = [ [3]; [4]; [8] ].
Proof. reflexivity. Qed.

Definition countoddmembers' (l:list nat) : nat :=
  length (filter oddb l).

Example test_countoddmembers'1: countoddmembers' [1;0;3;1;4;5] = 4.
Proof. reflexivity. Qed.
Example test_countoddmembers'2: countoddmembers' [0;2;4] = 0.
Proof. reflexivity. Qed.
Example test_countoddmembers'3: countoddmembers' nil = 0.
Proof. reflexivity. Qed.

Example test_anon_fun':
  doit3times (fun n => n * n) 2 = 256.
Proof. reflexivity. Qed.

Example test_filter2':
  filter (fun l => beq_nat (length l) 1)
         [ [1; 2]; [3]; [4]; [5;6;7]; []; [8] ]
  = [ [3]; [4]; [8] ].
Proof. reflexivity. Qed.

Definition filter_even_gt7 (l : list nat) : list nat :=
  filter (fun x => andb (evenb x) (blt_nat 7 x)) l.

Example test_filter_even_gt7_1 :
  filter_even_gt7 [1;2;6;9;10;3;12;8] = [10;12;8].
Proof. reflexivity. Qed.

Example test_filter_even_gt7_2 :
  filter_even_gt7 [5;2;6;19;129] = [].
Proof. reflexivity. Qed.


Definition partition {X:Type} (test: X -> bool) l : (list X * list X) :=
  let lx := filter test l in
  let ly := filter (fun x => negb (test x)) l in
  (lx, ly).
Example test_partition1: partition oddb [1;2;3;4;5] = ([1;3;5], [2;4]).
Proof. reflexivity. Qed.
Example test_partition2: partition (fun x => false) [5;9;0] = ([], [5;9;0]).
Proof. reflexivity. Qed.


Fixpoint map {X Y : Type} (f:X->Y) (l:list X) : list Y :=
  match l with
    | [] => []
    | h :: t => (f h) :: (map f t)
  end.
Example test_map1: map (plus 3) [2;0;2] = [5;3;5].
Proof. reflexivity. Qed.
Example test_map2: map oddb [2;1;2;5] = [false;true;false;true].
Proof. reflexivity. Qed.
Example test_map3:
  map (fun n => [evenb n;oddb n]) [2;1;2;5]
  = [[true;false];[false;true];[true;false];[false;true]].
Proof. reflexivity. Qed.

Theorem map_snoc : forall (X Y : Type) (f: X -> Y) (l:list X) (x:X),
                     map f (snoc l x) = snoc (map f l) (f x).
Proof. intros. induction l as [| h t].
       Case "l = nil". reflexivity.
       Case "l = h :: t". simpl. rewrite IHt. reflexivity.
Qed.
  
Theorem map_rev : forall (X Y : Type) (f: X -> Y) (l:list X),
                    map f (rev l) = rev (map f l).
Proof. intros. induction l as [| h t].
       Case "l = nil". reflexivity.
       Case "l = h :: t". simpl. rewrite map_snoc. rewrite IHt. reflexivity.
Qed.

Fixpoint flat_map {X Y:Type} (f:X -> list Y) (l:list X) : (list Y) :=
  match l with
    | [] => []
    | h :: t => (f h) ++ flat_map f t
  end.
Example test_flat_map1:
  flat_map (fun n => [n;n;n]) [1;5;4]
  = [1; 1; 1; 5; 5; 5; 4; 4; 4].
Proof. reflexivity. Qed.

Definition option_map {X Y : Type} (f : X -> Y) (xo : option X) : option Y :=
  match xo with
    | None => None
    | Some x => Some (f x)
  end.

Fixpoint fold {X Y : Type} (f: X -> Y -> Y) (l: list X) (b: Y) : Y :=
  match l with
    | nil => b
    | h::t => (f h (fold f t b))
  end.
Eval compute in (fold plus [1;2;3;4] 0).

Check (fold andb).
(* ===> fold andb : list bool -> bool -> bool *)

Example fold_example1 : fold mult [1;2;3;4] 1 = 24.
Proof. reflexivity. Qed.

Example fold_example2 : fold andb [true;true;false;true] true = false.
Proof. reflexivity. Qed.

Example fold_example3 : fold app [[1];[];[2;3];[4]] [] = [1;2;3;4].
Proof. reflexivity. Qed.

(* Exercise: 1 star, advanced (fold_types_different) 
Answer: Counter, which counts the number of each value within a list. *)

Definition constfun {X: Type} (x: X) : nat->X :=
  fun (k:nat) => x.

Definition ftrue := constfun true.

Example constfun_example1 : ftrue 0 = true.
Proof. reflexivity. Qed.

Example constfun_example2 : (constfun 5) 99 = 5.
Proof. reflexivity. Qed.

Definition override {X: Type} (f: nat->X) (k:nat) (x:X) : nat->X:=
  fun (k':nat) => if beq_nat k k' then x else f k'.
Definition fmostlytrue := override (override ftrue 1 false) 3 false.


Example override_example1 : fmostlytrue 0 = true.
Proof. reflexivity. Qed.

Example override_example2 : fmostlytrue 1 = false.
Proof. reflexivity. Qed.

Example override_example3 : fmostlytrue 2 = true.
Proof. reflexivity. Qed.

Example override_example4 : fmostlytrue 3 = false.
Proof. reflexivity. Qed.

Theorem override_example : forall b:bool,
                             (override (constfun b) 3 true ) 2 = b.
Proof. intros. destruct b as [true|false].
       reflexivity.
       reflexivity.
Qed.

Theorem unfold_example : forall m n,
                           3 + n = m ->
                           plus3 n + 1 = m + 1.
Proof.
  intros m n H.
  unfold plus3.
  rewrite H. reflexivity.
Qed.

Theorem override_eq :
  forall {X : Type} (x : X) (k : nat) (f : nat -> X),
    (override f k x) k = x.
Proof. intros.
       unfold override.
       rewrite <- beq_nat_refl. reflexivity.
Qed.

Theorem override_neq : forall (X:Type) x1 x2 k1 k2 (f : nat->X),
                         f k1 = x1 ->
                         beq_nat k2 k1 = false ->
                         (override f k2 x2) k1 = x1.
Proof. intros. unfold override.
       rewrite H, H0. reflexivity.
Qed.

Definition fold_length {X : Type} (l : list X) : nat :=
  fold (fun _ n => S n) l 0.
Example test_fold_length1 : fold_length [4;7;0] = 3.
Proof. reflexivity. Qed.

Theorem fold_length_correct : forall X (l : list X), 
                                fold_length l = length l.
Proof. intros. unfold fold_length.
       induction l as [| h t].
       reflexivity.
       simpl. rewrite IHt. reflexivity.
Qed.


(* Exercise: 2 stars, advanced (index_informal) *)
(*
Theorem: forall X n l, length l = n -> @index X n l = None.
Proof: By induction on l, we have @index X n [] = None from definition
Next: Suppose l = x::lx. then length x::lx = S (length lx) = n. From this we know that length lx = n - 1. By Induction Hypothesis we know that length lx = n - 1 -> @index X n-1 lx = None. Thus, @index X n l = None.
Qed. 
*)

