Set Implicit Arguments.

Require Import
        List.

Import ListNotations.

Inductive zipper (A : Type) : Type :=
| Zip : list A -> list A -> zipper A.

Section INTERFACE.
  Variables A B : Type.

  Definition past (z : zipper A) : list A :=
    match z with
    | Zip ls _ => ls
    end.

  Definition future (z : zipper A) : list A :=
    match z with
    | Zip _ rs => rs
    end.

  Definition empty : zipper A := Zip [] [].
  
  Definition from_list (xs : list A) : zipper A :=
    Zip [] xs.
  
  Definition from_list_end (xs : list A) : zipper A :=
    Zip (rev xs) [].

  Definition to_list (z : zipper A) : list A :=
    match z with
    | Zip l r => l ++ r
    end.

  Definition beginp (z : zipper A) : bool :=
    match z with
    | Zip [] _ => true
    | _        => false
    end.

  Definition endp (z : zipper A) : bool :=
    match z with
    | Zip _ [] => true
    | _        => false
    end.

  Definition emptyp (z : zipper A) : bool :=
    match z with
    | Zip [] [] => true
    | _         => false
    end.

  Definition startz (z : zipper A) : zipper A :=
    match z with
    | Zip l r => Zip [] (rev l ++ r)
    end.
  
  Definition endz (z : zipper A) : zipper A :=
    match z with
    | Zip l r => Zip (rev r ++ l) []
    end.

  Definition cursor_type (z : zipper A) : Type :=
    if negb (endp z) then A else unit. 
  
  Definition cursor (z : zipper A) : cursor_type z.
    destruct (endp z) eqn : Ha ; unfold cursor_type ; rewrite Ha ; simpl.
    exact tt.
    destruct z.
    destruct l0 ; simpl in *.
    congruence.
    exact a.
  Defined.

  Definition safe_cursor (z : zipper A) : option A :=
    match z with
    | Zip _ (r :: _) => Some r
    | _              => None
    end.

  Definition left (z : zipper A) : zipper A :=
    match z with
    | Zip (a :: ls) rs => Zip ls (a :: rs)
    | _                => z
    end.
  
  Definition right (z : zipper A) : zipper A :=
    match z with
    | Zip ls (a :: rs) => Zip (a :: ls) rs
    | _                => z
    end.

  Definition insert (x : A)(z : zipper A) : zipper A :=
    match z with
    | Zip ls rs => Zip ls (x :: rs)
    end.

  Definition delete (z : zipper A) : zipper A :=
    match z with
    | Zip ls (_ :: rs) => Zip ls rs
    | _                => z
    end.

  Definition push (x : A)(z : zipper A) : zipper A :=
    match z with
    | Zip ls rs => Zip (x :: ls) rs
    end.

  Definition pop (z : zipper A) : zipper A :=
    match z with
    | Zip (_ :: ls) rs => Zip ls rs
    | _                => z
    end.

  Definition replacez (x : A)(z : zipper A) : zipper A :=
    match z with
    | Zip ls (_ :: rs) => Zip ls (x :: rs)
    | _                => z
    end.

  Definition reversez (z : zipper A) : zipper A :=
    match z with
    | Zip ls rs => Zip rs ls
    end.

  Fixpoint foldrz_fuel (fuel : nat)(f : zipper A -> B -> B)(v : B)(z : zipper A) : B :=
    match fuel with
    | O       => v
    | S fuel' => f z (foldrz_fuel fuel' f v (right z))
    end.

  Definition foldrz (f : zipper A -> B -> B)(v : B)(z : zipper A) : B :=
    match z with
    | Zip _ rs => foldrz_fuel (length rs) f v z
    end.

  Fixpoint foldlz_fuel (fuel : nat)(f : B -> zipper A -> B)(v : B)(z : zipper A) : B :=
    match fuel with
    | O       => v
    | S fuel' => foldlz_fuel fuel' f (f v z) (right z) 
    end.

  Definition foldlz (f : B -> zipper A -> B)(v : B)(z : zipper A) : B :=
    match z with
    | Zip ls _ => foldlz_fuel (length ls) f v z
    end.
End INTERFACE.
