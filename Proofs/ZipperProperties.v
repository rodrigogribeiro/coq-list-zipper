Set Implicit Arguments.

Require Import
        Bool
        List
        Data.Zipper
        Tactics.Tactics.

Section PROPERTIES.

  Variable A : Type.
  Variable eqADec : forall (x y : A), {x = y} + {x <> y}.

  Lemma to_list__from_list : forall (xs : list A), to_list (from_list xs) = xs.
  Proof.
    induction xs ; crush.
  Qed.

  Lemma from_list__to_list : forall (z : zipper A),
      from_list (to_list (startz z)) = (startz z).
  Proof.
    destruct z ; simpl.
    unfold from_list.
    auto.
  Qed.

  Lemma startp__startz : forall (z : zipper A), Is_true (beginp (startz z)).
  Proof.
    intros z ; unfold Is_true, beginp, startz ; destruct z ; auto.
  Qed.

  Lemma endp__endz : forall (z : zipper A), Is_true (endp (endz z)).
  Proof.
    intros z ; unfold Is_true , endp, endz ; destruct z ; auto.
  Qed.

  Definition second (xs : list A) : option A :=
    match xs with
    | (_ :: x :: _) => Some x
    | _             => None
    end.

  Definition combine (x : option A)(xs : list A) : list A :=
    match x with
    | Some y => y :: xs
    | _      => xs
    end.

  Lemma right_correct : forall (z : zipper A),
      safe_cursor (right z) = (second (future z)) /\
      (past (right z) = (combine (safe_cursor z) (past z))).
  Proof.
    intros z ; destruct z ; destruct l0 ; crush.
  Qed.

  Lemma left_correct : forall (z : zipper A),
      (past (left z) = tl (past z)) /\
      (safe_cursor (left z) = (hd_error (combine (hd_error (past z)) (future z)))).
  Proof.
    intros z ; destruct z ; destruct l ; crush.
  Qed.

  Lemma insert_correct : forall (z : zipper A)(x : A), safe_cursor (insert x z) = Some x.
  Proof.
    intros z x ; destruct z ; crush.
  Qed.

  Lemma count_occ_app
    : forall (xs ys : list A)(x : A),
      count_occ eqADec (xs ++ ys) x = count_occ eqADec xs x + count_occ eqADec ys x.
  Proof. 
    induction xs ; intros ; crush.
    destruct (eqADec a x) eqn : Ha ; substs*.
  Qed.

  Lemma delete_removes : forall (z : zipper A),
      match safe_cursor z with
      | Some x =>
        count_occ eqADec (to_list z) x =
        1 + count_occ eqADec (to_list (delete z)) x
      | _      => True
      end.
  Proof.
    Hint Rewrite count_occ_app.
    intros z ; destruct (safe_cursor z) eqn : Ha ; crush.
    destruct z ; destruct l0 ; crush.
    destruct (eqADec a a) ; crush.
  Qed.

  Lemma push_pop_correct
    : forall (z : zipper A)(x : A),
      pop (push x z) = z.
  Proof.
    destruct z ; crush.
  Qed.

  Lemma replacez_correct
    : forall (z : zipper A)(x : A),
      Is_true (endp z) \/ (safe_cursor (replacez x z) = Some x).
  Proof.
    intros z x ; destruct z ; destruct l0 ; crush.
  Qed.

  Lemma reversez_idem : forall (z : zipper A), reversez (reversez z) = z.
  Proof.
    destruct z ; crush.
  Qed.
End PROPERTIES.
