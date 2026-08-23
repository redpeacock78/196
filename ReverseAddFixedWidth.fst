module ReverseAddFixedWidth

open ReverseAdd
open AbstractReachability
open FStar.List.Tot
open FStar.ReflexiveTransitiveClosure

// Exact canonical values below 10^width; all other numerals use fallback.
let rec power10 (width:nat) : Tot nat
  (decreases width) =
  if width = 0 then 1 else 10 * power10 (width - 1)

let rec power10_positive (width:nat)
  : Lemma (ensures (power10 width > 0)) =
  if width = 0 then () else power10_positive (width - 1)

let fixed_count (width:nat) : state_count =
  let limit = power10 width in
  power10_positive width;
  assert (limit + 1 > 0);
  limit + 1

let fixed_fallback (width:nat) : state (fixed_count width) =
  let limit = power10 width in
  power10_positive width;
  assert (limit < limit + 1);
  limit

let rec canonical_flag (#b:base) (xs:numeral b) : Tot bool
  (decreases xs) =
  match xs with
  | [] -> true
  | [d] -> d > 0
  | _::tl -> canonical_flag tl

let rec canonical_flag_sound (#b:base) (xs:numeral b)
  : Lemma (requires (canonical_flag xs == true))
    (ensures (canonical xs))
    (decreases xs) =
  match xs with
  | [] -> ()
  | [d] -> ()
  | _::tl -> canonical_flag_sound tl

let canonical_digits_196 ()
  : Lemma (canonical_flag digits_196 == true) =
  ()

let value_digits_196 ()
  : Lemma (value digits_196 == 196) =
  ()

let fixed_196_bound (width:nat{power10 width > 887})
  : Lemma (value digits_196 < power10 width) =
  value_digits_196 ();
  ()

let fixed_alpha (width:nat) (xs:numeral 10)
  : state (fixed_count width) =
  let limit = power10 width in
  if canonical_flag xs && value xs < limit then begin
    assert (value xs < limit + 1);
    value xs
  end else
    fixed_fallback width

let fixed_edge (width:nat)
  (x y:state (fixed_count width)) : Tot bool =
  if x = fixed_fallback width then true
  else fixed_alpha width
    (reverse_add #10 (digits_of_nat #10 x)) = y

let fixed_bad (width:nat)
  (s:state (fixed_count width)) : Tot bool =
  if s = fixed_fallback width then true
  else
    let xs = digits_of_nat #10 s in
    xs = rev xs

let fixed_alpha_exact (width:nat) (xs:numeral 10)
  : Lemma (requires (canonical_flag xs == true /\
      value xs < power10 width))
    (ensures (fixed_alpha width xs == value xs)) =
  canonical_flag_sound #10 xs;
  ()

let fixed_simulates_step (width:nat) (x y:numeral 10)
  : Lemma (requires (step #10 x y))
    (ensures (fixed_edge width
      (fixed_alpha width x) (fixed_alpha width y))) =
  let ax = fixed_alpha width x in
  if ax = fixed_fallback width then ()
  else begin
    assert (canonical_flag x == true /\ value x < power10 width);
    fixed_alpha_exact width x;
    canonical_flag_sound #10 x;
    digits_of_nat_of_canonical #10 x;
    assert (digits_of_nat #10 (value x) == x);
    assert (reverse_add #10 (digits_of_nat #10 (value x)) ==
      reverse_add #10 x);
    assert (reverse_add #10 x == y);
    ()
  end

let fixed_palindrome_sound (width:nat) (xs:numeral 10)
  : Lemma (requires (palindrome #10 xs))
    (ensures (fixed_bad width (fixed_alpha width xs))) =
  let ax = fixed_alpha width xs in
  if ax = fixed_fallback width then ()
  else begin
    assert (canonical_flag xs == true /\ value xs < power10 width);
    fixed_alpha_exact width xs;
    canonical_flag_sound #10 xs;
    digits_of_nat_of_canonical #10 xs;
    ()
  end

let fixed_196_no_bad_one_step (width:nat{power10 width > 887})
  (s:state (fixed_count width))
  : Lemma (requires (fixed_edge width
      (fixed_alpha width digits_196) s))
    (ensures (~ (fixed_bad width s))) =
  canonical_digits_196 ();
  fixed_196_bound width;
  value_digits_196 ();
  fixed_alpha_exact width digits_196;
  assert (fixed_alpha width digits_196 == 196);
  assert (digits_of_nat #10 196 == digits_196);
  example_196 ();
  assert (reverse_add #10 (digits_of_nat #10 196) == digits_887);
  assert (fixed_alpha width digits_887 == 887);
  assert (s == 887);
  assert (~ (fixed_bad width s));
  ()

let fixed_unreachable_sound (width:nat)
  (x y:numeral 10)
  (states:list (state (fixed_count width)))
  : Lemma (requires (
      check_bad (fixed_edge width) (fixed_bad width)
          (fixed_alpha width x) == Unreachable states /\
      closure (step #10) x y /\
      palindrome #10 y))
    (ensures False) =
  introduce forall (u v:numeral 10).
    step #10 u v ==> fixed_edge width
      (fixed_alpha width u) (fixed_alpha width v)
  with (
    introduce _ ==> _
    with (fixed_simulates_step width u v)
  );
  introduce forall (u:numeral 10).
    palindrome #10 u ==> fixed_bad width (fixed_alpha width u)
  with (
    introduce _ ==> _
    with (fixed_palindrome_sound width u)
  );
  check_bad_sound
    (step #10)
    (fixed_alpha width)
    (fixed_edge width)
    (palindrome #10)
    (fixed_bad width)
    x y states;
  ()
