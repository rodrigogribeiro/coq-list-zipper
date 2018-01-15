Set Warnings "-extraction-opaque-accessed,-extraction".
Set Warnings "-notation-overridden,-parsing".
Set Implicit Arguments.

From QuickChick Require Import QuickChick.

Import QcDefaultNotation. Open Scope qc_scope.
Import GenLow GenHigh.

Require Import
        Arith_base
        List
        String
        Data.Zipper.

Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import seq ssreflect ssrbool ssrnat eqtype.

Import ListNotations.

(** setting up generators *)

Derive Show for zipper.
Derive Arbitrary for zipper.

(** testing properties *)

Definition eq_zipper (z1 z2 : zipper nat) : bool :=
  match z1, z2 with
  | Zip l1 r1, Zip l2 r2 => (l1 == l2) && (r1 == r2)
  end.

(** 1. to_list and from_list are inverses *)

Definition to_list_from_list_inv (xs : list nat) :=
  to_list (from_list xs) == xs.

Definition from_list_to_list_inv (z : zipper nat) :=
  eq_zipper (from_list (to_list (startz z))) (startz z).

QuickChick to_list_from_list_inv.
QuickChick from_list_to_list_inv.

(** 2. startz puts a zipper in its beginning *)

Definition startz_beginp (z : zipper nat) :=
  beginp (startz z).

QuickChick startz_beginp.

(** 3. endz puts a zipper in the end *)

Definition endz_endp (z : zipper nat) :=
  endp (endz z).

QuickChick endz_endp.


(** 4. right puts the focus on the next element on the list *)

Definition second (xs : list nat) : option nat :=
  match xs with
  | (_ :: x :: _) => Some x
  | _             => None
  end.

Definition combine (x : option nat)(xs : list nat) : list nat :=
  match x with
  | Some y => y :: xs
  | _      => xs
  end.

Definition right_correct (z : zipper nat) :=
  (safe_cursor (right z) == (second (future z))) &&
  (past (right z) == (combine (safe_cursor z) (past z))).

QuickChick right_correct.


(** 5. left puts the focus on the previous element on the list *)

Definition left_correct (z : zipper nat) :=
  (past (left z) == tl (past z)) && 
  (safe_cursor (left z) == (hd_error (combine (hd_error (past z)) (future z)))).

QuickChick left_correct.


(** 6. insert puts a value at the cursor *)

Definition insert_correct (x : nat)(z : zipper nat) :=
  safe_cursor (insert x z) == Some x.

QuickChick insert_correct.

(** 7. properties for delete *)

Definition delete_removes (z : zipper nat) :=
  match safe_cursor z with
  | Some x =>
    count_occ eq_nat_dec (to_list z) x ==
    1 + (count_occ eq_nat_dec(to_list (delete z)) x)
  | _      => true
  end.

QuickChick delete_removes.

(** correctness of push and pop *)

Definition push_pop_ok (x : nat)(z : zipper nat) :=
  eq_zipper (pop (push x z)) z.

QuickChick push_pop_ok.

(** correctness of replacez *)

Definition replacez_correct (x : nat)(z : zipper nat) :=
  (negb (negb (endp z))) || (safe_cursor (replacez x z) == Some x).

QuickChick replacez_correct.


(** correctness of reversez *)

Definition reversez_idem (z : zipper nat) :=
  eq_zipper (reversez (reversez z)) z.

QuickChick reversez_idem.
