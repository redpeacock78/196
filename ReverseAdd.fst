module ReverseAdd

open FStar.List.Tot
open FStar.Math.Lemmas

// Digits are stored least-significant first.  The empty list is zero.
type base = b:nat { 2 <= b }
type digit (b:base) = d:nat { d < b }
type numeral (b:base) = list (digit b)
type carry = c:nat { c <= 1 }

let rec value (#b:base) (xs:numeral b) : Tot nat
  (decreases xs) =
  match xs with
  | [] -> 0
  | d::tl -> d + b * value tl

// Remove zeroes at the most-significant end.
let rec normalize (#b:base) (xs:numeral b) : Tot (numeral b)
  (decreases xs) =
  match xs with
  | [] -> []
  | d::tl ->
      let tl' = normalize tl in
      match tl' with
      | [] -> if d = 0 then [] else [d]
      | _ -> d::tl'

let rec canonical (#b:base) (xs:numeral b) : Tot prop
  (decreases xs) =
  match xs with
  | [] -> True
  | [d] -> d > 0
  | _::tl -> canonical tl

let rec canonical_value_positive (#b:base) (xs:numeral b)
  : Lemma (requires (canonical xs /\ xs <> []))
    (ensures (value xs > 0))
    (decreases xs) =
  match xs with
  | [] -> ()
  | [_] -> ()
  | _::tl -> canonical_value_positive tl

let rec digits_of_nat (#b:base) (n:nat) : Tot (numeral b)
  (decreases n) =
  if n = 0 then []
  else
    let q = n / b in
    let r = n % b in
    assert (r < b);
    r :: digits_of_nat q

let reverse_digits (#b:base) (xs:numeral b) : Tot (numeral b) =
  normalize (rev xs)

let reverse_base (#b:base) (n:nat) : Tot nat =
  value (reverse_digits #b (digits_of_nat #b n))

let rec digits_of_nat_value (#b:base) (n:nat)
  : Lemma (ensures (value (digits_of_nat #b n) == n))
    (decreases n) =
  if n = 0 then ()
  else
    let q = n / b in
    let r = n % b in
    digits_of_nat_value #b q;
    lemma_div_mod n b;
    swap_mul b q;
    ()

let rec digits_of_nat_of_canonical (#b:base) (xs:numeral b)
  : Lemma (requires (canonical xs))
    (ensures (digits_of_nat #b (value xs) == xs))
    (decreases xs) =
  match xs with
  | [] -> ()
  | [d] ->
      small_div d b;
      small_mod d b;
      ()
  | d::tl ->
      canonical_value_positive tl;
      digits_of_nat_of_canonical #b tl;
      lemma_div_mod_plus d (value tl) b;
      small_div d b;
      small_mod d b;
      swap_mul b (value tl);
      ()

let reverse_digits_value_as_reverse_base (#b:base) (xs:numeral b)
  : Lemma (requires (canonical xs))
    (ensures (value (reverse_digits xs) ==
      reverse_base #b (value xs))) =
  digits_of_nat_of_canonical #b xs;
  ()

type add_cell_result (b:base) = {
  digit: digit b;
  carry: carry
}

let split_add_cell (#b:base) (x:digit b) (y:digit b) (c:carry) : add_cell_result b =
  let s = x + y + c in
  assert (s < b + b);
  if s < b
  then { digit = s; carry = 0 }
  else { digit = s - b; carry = 1 }

let rec add_digits (#b:base)
  (xs:numeral b)
  (ys:numeral b)
  (c:carry)
  : Tot (numeral b)
    (decreases (length xs + length ys)) =
  match xs, ys with
  | [], [] -> if c = 0 then [] else [c]
  | x::xs', [] ->
      let cell = split_add_cell x 0 c in
      cell.digit :: add_digits xs' [] cell.carry
  | [], y::ys' ->
      let cell = split_add_cell 0 y c in
      cell.digit :: add_digits [] ys' cell.carry
  | x::xs', y::ys' ->
      let cell = split_add_cell x y c in
      cell.digit :: add_digits xs' ys' cell.carry

let reverse_add (#b:base) (xs:numeral b) : Tot (numeral b) =
  normalize (add_digits xs (reverse_digits xs) 0)

let rec normalize_value (#b:base) (xs:numeral b)
  : Lemma (ensures (value (normalize xs) == value xs))
    (decreases xs) =
  match xs with
  | [] -> ()
  | _::tl -> normalize_value tl

let rec normalize_canonical (#b:base) (xs:numeral b)
  : Lemma (ensures (canonical (normalize xs)))
    (decreases xs) =
  match xs with
  | [] -> ()
  | _::tl ->
      normalize_canonical tl;
      ()

let reverse_digits_canonical (#b:base) (xs:numeral b)
  : Lemma (canonical (reverse_digits xs)) =
  normalize_canonical (rev xs)

let split_add_cell_value (#b:base)
  (x:digit b) (y:digit b) (c:carry)
  : Lemma (
      (split_add_cell x y c).digit +
        b * (split_add_cell x y c).carry == x + y + c) =
  let s = x + y + c in
  if s < b then () else ()

let rec add_digits_value (#b:base)
  (xs:numeral b)
  (ys:numeral b)
  (c:carry)
  : Lemma (ensures (value (add_digits xs ys c) == value xs + value ys + c))
    (decreases (length xs + length ys)) =
  match xs, ys with
  | [], [] -> ()
  | x::xs', [] ->
      let cell = split_add_cell x 0 c in
      split_add_cell_value x 0 c;
      add_digits_value xs' [] cell.carry;
      distributivity_add_right b (value xs') (0 + cell.carry);
      ()
  | [], y::ys' ->
      let cell = split_add_cell 0 y c in
      split_add_cell_value 0 y c;
      add_digits_value [] ys' cell.carry;
      distributivity_add_right b (0 + value ys') cell.carry;
      ()
  | x::xs', y::ys' ->
      let cell = split_add_cell x y c in
      split_add_cell_value x y c;
      assert (length xs' + length ys' < length (x::xs') + length (y::ys'));
      add_digits_value xs' ys' cell.carry;
      distributivity_add_right b (value xs') (value ys' + cell.carry);
      distributivity_add_right b (value ys') cell.carry;
      ()

let reverse_add_value (#b:base) (xs:numeral b)
  : Lemma (value (reverse_add xs) ==
      value xs + value (reverse_digits xs)) =
  normalize_value (add_digits xs (reverse_digits xs) 0);
  add_digits_value xs (reverse_digits xs) 0

let reverse_add_value_as_reverse_base (#b:base) (xs:numeral b)
  : Lemma (requires (canonical xs))
    (ensures (value (reverse_add xs) ==
      value xs + reverse_base #b (value xs))) =
  reverse_add_value #b xs;
  reverse_digits_value_as_reverse_base #b xs;
  ()

let reverse_add_canonical (#b:base) (xs:numeral b)
  : Lemma (canonical (reverse_add xs)) =
  normalize_canonical (add_digits xs (reverse_digits xs) 0)

let palindrome (#b:base) (xs:numeral b) : Tot prop =
  xs == rev xs

let step (#b:base) (x:numeral b) (y:numeral b) : Tot prop =
  reverse_add x == y

let predecessor (#b:base) (y:numeral b) (x:numeral b) : Tot prop =
  step x y

let rec iterate (#b:base) (k:nat) (x:numeral b) : Tot (numeral b)
  (decreases k) =
  if k = 0 then x
  else iterate (k - 1) (reverse_add x)

let reaches (#b:base) (k:nat) (x y:numeral b) : Tot prop =
  iterate k x == y

let digits_56 : numeral 10 = [6; 5]
let digits_196 : numeral 10 = [6; 9; 1]
let digits_121 : numeral 10 = [1; 2; 1]
let digits_887 : numeral 10 = [7; 8; 8]
let digits_base2 : numeral 2 = [1; 1]

let example_56 () : Lemma (
    step digits_56 digits_121 /\
    reaches 1 digits_56 digits_121 /\
    value (reverse_add digits_56) == 121 /\
    palindrome digits_121) = ()

let example_196 () : Lemma (
    step digits_196 digits_887 /\
    value (reverse_add digits_196) == 887 /\
    ~ (palindrome digits_887)) = ()

let example_reverse_base () : Lemma (
    reverse_base #10 (value digits_196) == 691 /\
    value (reverse_add digits_196) ==
      value digits_196 + reverse_base #10 (value digits_196)) =
  reverse_digits_value_as_reverse_base #10 digits_196;
  reverse_add_value_as_reverse_base #10 digits_196;
  ()

let example_base2 () : Lemma (
    value (reverse_add digits_base2) == 6 /\
    canonical (reverse_add digits_base2)) = ()
