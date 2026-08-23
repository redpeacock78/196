module ReverseAddInvariant

open ReverseAdd
open ReverseAddCarry
open ReverseAddWitness
open ReverseAddBoundary
open ReverseAddHighSum
open ReverseAddOverflowProfile
open ReverseAddFixedWidth
open FStar.Classical
open FStar.List.Tot
open FStar.List.Tot.Properties
open FStar.Math.Lemmas

let rec iterate_succ (#b:base) (k:nat) (x:numeral b)
  : Lemma (ensures (iterate (k + 1) x == reverse_add (iterate k x)))
    (decreases k) =
  if k = 0 then
    ()
  else
    let k' : nat = k - 1 in
    iterate_succ k' (reverse_add x);
    ()

let iterate_next_obstruction_excludes_palindrome
  (k:nat) (xs:numeral 10)
  : Lemma (requires (
      xs <> [] /\
      trace_palindrome_obstruction (iterate k xs) /\
      trace_digits (iterate k xs) == reverse_add (iterate k xs) /\
      palindrome #10 (iterate (k + 1) xs)))
    (ensures False) =
  iterate_succ #10 k xs;
  reverse_add_palindrome_obstruction_excludes_palindrome
    (iterate k xs)

let rec reverse_head_positive (#b:base) (xs:numeral b)
  : Lemma (requires (canonical xs /\ xs <> []))
    (ensures (
      match rev xs with
      | d::_ -> d > 0
      | [] -> False))
    (decreases xs) =
  match xs with
  | [] -> ()
  | [_] -> ()
  | d::tl ->
      reverse_head_positive tl;
      rev_append [d] tl;
      ()

let reverse_digits_nonempty (#b:base) (xs:numeral b)
  : Lemma (requires (canonical xs /\ xs <> []))
    (ensures (reverse_digits xs <> [])) =
  reverse_head_positive #b xs;
  assert (reverse_digits xs <> []);
  ()

let reverse_digits_positive (#b:base) (xs:numeral b)
  : Lemma (requires (canonical xs /\ xs <> []))
    (ensures (value (reverse_digits xs) > 0)) =
  reverse_digits_canonical #b xs;
  reverse_digits_nonempty #b xs;
  canonical_value_positive #b (reverse_digits xs);
  ()

let reverse_add_strictly_increases (#b:base) (xs:numeral b)
  : Lemma (requires (canonical xs /\ xs <> []))
    (ensures (value xs < value (reverse_add xs))) =
  reverse_add_value #b xs;
  reverse_digits_positive #b xs;
  ()

let rec iterate_canonical (#b:base) (k:nat) (xs:numeral b)
  : Lemma (requires (canonical xs))
    (ensures (canonical (iterate k xs)))
    (decreases k) =
  if k = 0 then ()
  else
    let k' : nat = k - 1 in
    reverse_add_canonical #b xs;
    iterate_canonical #b k' (reverse_add xs)

let rec iterate_nonempty (#b:base) (k:nat) (xs:numeral b)
  : Lemma (requires (canonical xs /\ xs <> []))
    (ensures (iterate k xs <> []))
    (decreases k) =
  if k = 0 then ()
  else
    let k' : nat = k - 1 in
    reverse_add_strictly_increases #b xs;
    reverse_add_canonical #b xs;
    assert (reverse_add xs <> []);
    iterate_nonempty #b k' (reverse_add xs)

let rec iterate_value_strictly_increases (#b:base) (k:nat) (xs:numeral b)
  : Lemma (requires (canonical xs /\ xs <> [] /\ k > 0))
    (ensures (value xs < value (iterate k xs)))
    (decreases k) =
  if k = 1 then
    reverse_add_strictly_increases #b xs
  else
    let k' : nat = k - 1 in
    reverse_add_strictly_increases #b xs;
    reverse_add_canonical #b xs;
    assert (reverse_add xs <> []);
    iterate_value_strictly_increases #b k' (reverse_add xs);
    ()

let rec iterate_value_at_least (#b:base) (k:nat) (xs:numeral b)
  : Lemma (requires (canonical xs /\ xs <> []))
    (ensures (value xs + k <= value (iterate k xs)))
    (decreases k) =
  if k = 0 then
    ()
  else
    let k' : nat = k - 1 in
    reverse_add_strictly_increases #b xs;
    assert (value xs + 1 <= value (reverse_add xs));
    reverse_add_canonical #b xs;
    assert (reverse_add xs <> []);
    iterate_value_at_least #b k' (reverse_add xs);
    assert (iterate k xs == iterate k' (reverse_add xs));
    ()

let fixed_width_fallback_reached
  (width:nat) (xs:numeral 10)
  : Lemma (requires (canonical xs /\ xs <> []))
    (ensures (
      fixed_alpha width (iterate (power10 width) xs) ==
        fixed_fallback width)) =
  power10_positive width;
  iterate_value_at_least #10 (power10 width) xs;
  canonical_value_positive #10 xs;
  assert (value xs + power10 width > power10 width);
  assert (power10 width < value (iterate (power10 width) xs));
  assert (fixed_alpha width (iterate (power10 width) xs) ==
    fixed_fallback width);
  ()

let fixed_width_fallback_is_bad
  (width:nat) (xs:numeral 10)
  : Lemma (requires (canonical xs /\ xs <> []))
    (ensures (
      fixed_bad width (fixed_alpha width (iterate (power10 width) xs)))) =
  fixed_width_fallback_reached width xs;
  assert (fixed_bad width (fixed_fallback width));
  ()

let all_iterate_obstructions_exclude_palindrome (xs:numeral 10)
  : Lemma (requires (
      canonical xs /\
      xs <> [] /\
      (forall k. trace_palindrome_obstruction (iterate k xs))))
    (ensures (forall (k:nat).
      ~ (palindrome #10 (iterate (k + 1) xs)))) =
  introduce forall (k:nat).
    ~ (palindrome #10 (iterate (k + 1) xs))
  with (
    introduce (palindrome #10 (iterate (k + 1) xs)) ==> False
    with (
      iterate_canonical #10 k xs;
      iterate_nonempty #10 k xs;
      trace_digits_equals_reverse_add (iterate k xs);
      assert (trace_palindrome_obstruction (iterate k xs));
      iterate_next_obstruction_excludes_palindrome k xs))

let all_iterate_indexed_witnesses_exclude_palindrome
  (xs:numeral 10) (w:nat -> nat)
  : Lemma (requires (
      canonical xs /\
      xs <> [] /\
      (forall k.
        trace_palindrome_obstruction_at (iterate k xs) (w k))))
    (ensures (forall (k:nat).
      ~ (palindrome #10 (iterate (k + 1) xs)))) =
  introduce forall (k:nat).
    ~ (palindrome #10 (iterate (k + 1) xs))
  with (
    introduce (palindrome #10 (iterate (k + 1) xs)) ==> False
    with (
      iterate_canonical #10 k xs;
      iterate_nonempty #10 k xs;
      trace_digits_equals_reverse_add (iterate k xs);
      trace_palindrome_obstruction_at_sound
        (iterate k xs) (w k);
      iterate_next_obstruction_excludes_palindrome k xs))

let iterate_indexed_witness_excludes_palindrome
  (xs:numeral 10) (w:nat -> nat) (k:nat)
  : Lemma (requires (
      canonical xs /\
      xs <> [] /\
      trace_palindrome_obstruction_at (iterate k xs) (w k)))
    (ensures (~ (palindrome #10 (iterate (k + 1) xs)))) =
  introduce (palindrome #10 (iterate (k + 1) xs)) ==> False
  with (
    iterate_canonical #10 k xs;
    iterate_nonempty #10 k xs;
    trace_digits_equals_reverse_add (iterate k xs);
    trace_palindrome_obstruction_at_sound
      (iterate k xs) (w k);
    iterate_next_obstruction_excludes_palindrome k xs)

let all_iterate_obstructions_have_indexed_witnesses
  (xs:numeral 10)
  : Lemma (requires (
      canonical xs /\
      xs <> [] /\
      (forall k.
        trace_palindrome_obstruction (iterate k xs))))
    (ensures (forall (k:nat).
      exists (i:nat).
        trace_palindrome_obstruction_at (iterate k xs) i)) =
  introduce forall (k:nat).
    exists (i:nat).
      trace_palindrome_obstruction_at (iterate k xs) i
  with (
    assert (trace_palindrome_obstruction (iterate k xs));
    trace_palindrome_obstruction_at_exists (iterate k xs))

let all_iterate_existential_witnesses_exclude_palindrome
  (xs:numeral 10)
  : Lemma (requires (
      canonical xs /\
      xs <> [] /\
      (forall k.
        exists (i:nat).
          trace_palindrome_obstruction_at (iterate k xs) i)))
    (ensures (forall (k:nat).
      ~ (palindrome #10 (iterate (k + 1) xs)))) =
  introduce forall (k:nat).
    ~ (palindrome #10 (iterate (k + 1) xs))
  with (
    introduce (palindrome #10 (iterate (k + 1) xs)) ==> False
    with (
      iterate_canonical #10 k xs;
      iterate_nonempty #10 k xs;
      trace_digits_equals_reverse_add (iterate k xs);
      eliminate exists (i:nat).
        trace_palindrome_obstruction_at (iterate k xs) i
      with (
        trace_palindrome_obstruction_at_sound
          (iterate k xs) i;
        iterate_next_obstruction_excludes_palindrome k xs)))

let trace_palindrome_obstruction_exists (xs:numeral 10) : prop =
  exists (i:nat). trace_palindrome_obstruction_at xs i

// A coarse necessary profile for a palindromic next output.  The future
// 196-specific invariant can target this profile instead of duplicating the
// no-overflow and overflow cases.
let trace_palindrome_candidate (xs:numeral 10) : prop =
  (length (trace_digits xs) == length xs /\
   nth (trace_carries xs) (length xs) == Some 0 /\
   (forall i. i < length xs ==>
     trace_sum_at xs i < 10)) \/
  (length (trace_digits xs) == length xs + 1 /\
   nth (trace_carries xs) (length xs) == Some 1 /\
   trace_sum_at xs 0 == 11 /\
   (forall i. 0 < i /\ i <= length xs ==>
       ~(trace_sum_at xs i >= trace_sum_at xs (i - 1) + 12 \/
         trace_sum_at xs (i - 1) >= trace_sum_at xs i + 12)))

// An overflow trace cannot have outer sum 1: the mirrored final cell has
// the same sum, so it cannot produce the required final carry.
let trace_overflow_outer_sum_one_impossible (xs:numeral 10) : Lemma (
    requires (
      xs <> [] /\
      length (trace_digits xs) == length xs + 1 /\
      nth (trace_carries xs) (length xs) == Some 1 /\
      trace_sum_at xs 0 == 1))
    (ensures False) =
  let n : nat = length xs in
  assert (n > 0);
  assert (n - 1 < n);
  trace_sum_symmetric_at xs 0;
  trace_equation_at xs (n - 1);
  assert (trace_sum_at xs (n - 1) == 1);
  assert (trace_carry_at xs n == 1);
  assert (trace_digit_at xs (n - 1) + 10 ==
    trace_sum_at xs (n - 1) + trace_carry_at xs (n - 1));
  assert (trace_carry_at xs (n - 1) <= 1);
  assert (trace_digit_at xs (n - 1) + 10 >
    trace_sum_at xs (n - 1) + trace_carry_at xs (n - 1));
  assert False

// The complement of the candidate profile, retaining the branch-local witness
// needed by a future 196-specific one-step invariant.
let trace_candidate_complement_witness (xs:numeral 10) : prop =
  (length (trace_digits xs) == length xs /\
   nth (trace_carries xs) (length xs) == Some 0 /\
   exists (i:nat). i < length xs /\ trace_sum_at xs i >= 10) \/
  (length (trace_digits xs) == length xs + 1 /\
   nth (trace_carries xs) (length xs) == Some 1 /\
   (trace_sum_at xs 0 <> 11 \/
    exists (i:nat). 0 < i /\ i <= length xs /\
      (trace_sum_at xs i >= trace_sum_at xs (i - 1) + 12 \/
       trace_sum_at xs (i - 1) >= trace_sum_at xs i + 12)))

let trace_palindrome_implies_candidate (xs:numeral 10) : Lemma (requires (
      xs <> [] /\
      trace_digits xs == rev (trace_digits xs)))
    (ensures (trace_palindrome_candidate xs)) =
  reverse_trace_palindrome_cases xs;
  eliminate
    (length (trace_digits xs) == length xs /\
     nth (trace_carries xs) (length xs) == Some 0 /\
     (forall i. i < length xs ==>
       trace_carry_at xs i ==
           trace_carry_at xs (length xs - 1 - i))) \/
    (length (trace_digits xs) == length xs + 1 /\
     nth (trace_carries xs) (length xs) == Some 1 /\
     trace_digit_at xs 0 == 1)
  with (
    trace_no_overflow_palindrome_implies_sum_low xs;
    assert (trace_palindrome_candidate xs);
    ())
  and (
    trace_overflow_palindrome_outer_sum_is_1_or_11 xs;
    eliminate trace_sum_at xs 0 == 1 \/ trace_sum_at xs 0 == 11
    with (
      trace_overflow_outer_sum_one_impossible xs;
      assert False)
    and (
      assert (trace_sum_at xs 0 == 11);
      ());
    introduce forall (i:nat).
      0 < i /\ i <= length xs ==>
      ~(trace_sum_at xs i >= trace_sum_at xs (i - 1) + 12 \/
        trace_sum_at xs (i - 1) >= trace_sum_at xs i + 12)
    with (
      introduce (0 < i /\ i <= length xs) ==>
        ~(trace_sum_at xs i >= trace_sum_at xs (i - 1) + 12 \/
          trace_sum_at xs (i - 1) >= trace_sum_at xs i + 12)
      with (trace_overflow_palindrome_implies_no_sum_jump xs i));
    assert (trace_palindrome_candidate xs);
    ())

let trace_no_overflow_not_candidate_obstruction (xs:numeral 10)
  : Lemma (requires (
      xs <> [] /\
      length (trace_digits xs) == length xs /\
      nth (trace_carries xs) (length xs) == Some 0 /\
      ~(trace_palindrome_candidate xs)))
    (ensures (trace_palindrome_obstruction_exists xs)) =
  assert (~ (forall (i:nat). i < length xs ==>
    trace_sum_at xs i < 10));
  assert (~ (forall (i:nat). ~(
    i < length xs /\ trace_sum_at xs i >= 10)));
  not_forall_implies_exists #nat
    #(fun (i:nat) -> i < length xs /\ trace_sum_at xs i >= 10)
    ();
  eliminate exists (i:nat).
    i < length xs /\ trace_sum_at xs i >= 10
  with (
    trace_no_overflow_high_sum_exists xs i;
    ())

let trace_overflow_not_candidate_obstruction (xs:numeral 10)
  : Lemma (requires (
      xs <> [] /\
      length (trace_digits xs) == length xs + 1 /\
      nth (trace_carries xs) (length xs) == Some 1 /\
      ~(trace_palindrome_candidate xs)))
    (ensures (trace_palindrome_obstruction_exists xs)) =
  if trace_sum_at xs 0 = 1 then begin
    trace_overflow_outer_sum_one_impossible xs;
    assert False
  end else if trace_sum_at xs 0 = 11 then begin
    assert (~ (forall (i:nat). 0 < i /\ i <= length xs ==>
      ~(trace_sum_at xs i >= trace_sum_at xs (i - 1) + 12 \/
        trace_sum_at xs (i - 1) >= trace_sum_at xs i + 12)));
    assert (~ (forall (i:nat). ~(
      0 < i /\ i <= length xs /\
      (trace_sum_at xs i >= trace_sum_at xs (i - 1) + 12 \/
       trace_sum_at xs (i - 1) >= trace_sum_at xs i + 12))));
    not_forall_implies_exists #nat
      #(fun (i:nat) -> 0 < i /\ i <= length xs /\
        (trace_sum_at xs i >= trace_sum_at xs (i - 1) + 12 \/
         trace_sum_at xs (i - 1) >= trace_sum_at xs i + 12))
      ();
    eliminate exists (i:nat).
      0 < i /\ i <= length xs /\
      (trace_sum_at xs i >= trace_sum_at xs (i - 1) + 12 \/
       trace_sum_at xs (i - 1) >= trace_sum_at xs i + 12)
    with (
      trace_overflow_sum_jump_obstruction_at xs i;
      exists_intro
        (fun (i:nat) -> trace_palindrome_obstruction_at xs i) i;
      ())
  end else begin
    assert (trace_sum_at xs 0 <> 1);
    assert (trace_sum_at xs 0 <> 11);
    trace_overflow_outer_sum_not_1_or_11_obstruction_at xs;
    exists_intro
      (fun (i:nat) -> trace_palindrome_obstruction_at xs i) 0;
    ()
  end

// The complement of the candidate profile has an indexed obstruction.
let trace_not_candidate_implies_obstruction (xs:numeral 10)
  : Lemma (requires (
      xs <> [] /\
      ~(trace_palindrome_candidate xs)))
    (ensures (trace_palindrome_obstruction_exists xs)) =
  reverse_trace_output_length_case xs;
  rev_length xs;
  trace_output_length_carry_link xs (rev xs) 0;
  eliminate
    (length (trace_digits xs) == length xs /\
     nth (trace_carries xs) (length xs) == Some 0) \/
    (length (trace_digits xs) == length xs + 1 /\
     nth (trace_carries xs) (length xs) == Some 1)
  with (
    trace_no_overflow_not_candidate_obstruction xs;
    ())
  and (
    trace_overflow_not_candidate_obstruction xs;
    ())

let all_iterate_not_candidate_has_witnesses
  (xs:numeral 10)
  : Lemma (requires (
      canonical xs /\
      xs <> [] /\
      (forall k. ~(trace_palindrome_candidate (iterate k xs)))))
    (ensures (forall (k:nat).
    exists (i:nat).
      trace_palindrome_obstruction_at (iterate k xs) i)) =
  introduce forall (k:nat).
    exists (i:nat).
      trace_palindrome_obstruction_at (iterate k xs) i
  with (
    iterate_nonempty #10 k xs;
    assert (~ (trace_palindrome_candidate (iterate k xs)));
    trace_not_candidate_implies_obstruction (iterate k xs);
    ())

let all_iterate_not_candidate_excludes_palindrome
  (xs:numeral 10)
  : Lemma (requires (
      canonical xs /\
      xs <> [] /\
      (forall k. ~(trace_palindrome_candidate (iterate k xs)))))
    (ensures (forall (k:nat).
      ~ (palindrome #10 (iterate (k + 1) xs)))) =
  all_iterate_not_candidate_has_witnesses xs;
  all_iterate_existential_witnesses_exclude_palindrome xs

let rec iterate_not_candidate_from_step
  (xs:numeral 10)
  (preserved:(y:numeral 10 -> Lemma (
      requires (~(trace_palindrome_candidate y)))
      (ensures (~(trace_palindrome_candidate (reverse_add y))))))
  (k:nat)
  : Lemma (requires (~(trace_palindrome_candidate xs)))
    (ensures (~(trace_palindrome_candidate (iterate k xs))))
    (decreases k) =
  if k = 0 then
    ()
  else
    let k' : nat = k - 1 in
    iterate_not_candidate_from_step xs preserved k';
    iterate_succ #10 k' xs;
    preserved (iterate k' xs);
    ()

let all_iterate_not_candidate_from_step
  (xs:numeral 10)
  (preserved:(y:numeral 10 -> Lemma (
      requires (~(trace_palindrome_candidate y)))
      (ensures (~(trace_palindrome_candidate (reverse_add y))))))
  : Lemma (requires (
      canonical xs /\
      xs <> [] /\
      ~(trace_palindrome_candidate xs)))
    (ensures (forall (k:nat).
      ~(trace_palindrome_candidate (iterate k xs)))) =
  introduce forall (k:nat).
    ~(trace_palindrome_candidate (iterate k xs))
  with (
    iterate_not_candidate_from_step xs preserved k)

let all_iterate_not_candidate_step_excludes_palindrome
  (xs:numeral 10)
  (preserved:(y:numeral 10 -> Lemma (
      requires (~(trace_palindrome_candidate y)))
      (ensures (~(trace_palindrome_candidate (reverse_add y))))))
  : Lemma (requires (
      canonical xs /\
      xs <> [] /\
      ~(trace_palindrome_candidate xs)))
    (ensures (forall (k:nat).
      ~ (palindrome #10 (iterate (k + 1) xs)))) =
  all_iterate_not_candidate_from_step xs preserved;
  all_iterate_not_candidate_excludes_palindrome xs

let trace_palindrome_obstruction_exists_not_preserved_19 () : Lemma (
    trace_palindrome_obstruction_exists [9; 1] /\
    ~ (trace_palindrome_obstruction_exists [0; 1; 1])) =
  trace_palindrome_obstruction_not_inductive_19 ();
  trace_palindrome_obstruction_at_exists [9; 1];
  assert (~ (trace_palindrome_obstruction [0; 1; 1]));
  introduce (trace_palindrome_obstruction_exists [0; 1; 1]) ==> False
  with (
    eliminate exists (i:nat).
      trace_palindrome_obstruction_at [0; 1; 1] i
    with (
      trace_palindrome_obstruction_at_sound [0; 1; 1] i;
      assert False))

let candidate_110 () : Lemma (
    trace_palindrome_candidate [0; 1; 1]) = ()

let not_candidate_19 () : Lemma (
    ~(trace_palindrome_candidate [9; 1])) = ()

let trace_candidate_not_preserved_19 () : Lemma (
    ~(trace_palindrome_candidate [9; 1]) /\
    trace_palindrome_candidate [0; 1; 1]) =
  not_candidate_19 ();
  candidate_110 ();
  ()

let rec iterate_obstruction_from_step
  (xs:numeral 10)
  (preserved:(y:numeral 10 -> Lemma (
      requires (trace_palindrome_obstruction_exists y))
      (ensures (trace_palindrome_obstruction_exists (reverse_add y)))))
  (k:nat)
  : Lemma (requires (trace_palindrome_obstruction_exists xs))
    (ensures (trace_palindrome_obstruction_exists (iterate k xs)))
    (decreases k) =
  if k = 0 then
    ()
  else
    let k' : nat = k - 1 in
    iterate_obstruction_from_step xs preserved k';
    iterate_succ #10 k' xs;
    preserved (iterate k' xs);
    ()

let all_iterate_obstructions_from_step
  (xs:numeral 10)
  (preserved:(y:numeral 10 -> Lemma (
      requires (trace_palindrome_obstruction_exists y))
      (ensures (trace_palindrome_obstruction_exists (reverse_add y)))))
  : Lemma (requires (
      canonical xs /\
      xs <> [] /\
      trace_palindrome_obstruction_exists xs))
    (ensures (forall (k:nat).
      trace_palindrome_obstruction_exists (iterate k xs))) =
  introduce forall (k:nat).
    trace_palindrome_obstruction_exists (iterate k xs)
  with (
    iterate_obstruction_from_step xs preserved k)

let all_iterate_obstruction_step_excludes_palindrome
  (xs:numeral 10)
  (preserved:(y:numeral 10 -> Lemma (
      requires (trace_palindrome_obstruction_exists y))
      (ensures (trace_palindrome_obstruction_exists (reverse_add y)))))
  : Lemma (requires (
      canonical xs /\
      xs <> [] /\
      trace_palindrome_obstruction_exists xs))
    (ensures (forall (k:nat).
      ~ (palindrome #10 (iterate (k + 1) xs)))) =
  all_iterate_obstructions_from_step xs preserved;
  all_iterate_existential_witnesses_exclude_palindrome xs

let rec alternating_value (xs:numeral 10) : Tot int
  (decreases xs) =
  match xs with
  | [] -> 0
  | d::tl -> d - alternating_value tl

let rec alternating_value_mod11 (xs:numeral 10)
  : Lemma (ensures (
      value xs % 11 == alternating_value xs % 11))
    (decreases xs) =
  match xs with
  | [] -> ()
  | d::tl ->
      alternating_value_mod11 tl;
      lemma_mod_plus (alternating_value tl) (-(value tl)) 11;
      lemma_mod_mul_distr_l (value tl) 10 11;
      ()

let rec alternating_append_digit (xs:numeral 10) (d:digit 10)
  : Lemma (ensures (
      alternating_value (xs @ [d]) ==
        (if length xs % 2 = 0
         then alternating_value xs + d
         else alternating_value xs - d)))
    (decreases xs) =
  match xs with
  | [] -> ()
  | _::tl ->
      alternating_append_digit tl d;
      ()

let rec alternating_reverse (xs:numeral 10)
  : Lemma (ensures (
      alternating_value (rev xs) ==
        (if length xs % 2 = 0
         then -(alternating_value xs)
         else alternating_value xs)))
    (decreases xs) =
  match xs with
  | [] -> ()
  | d::tl ->
      alternating_reverse tl;
      rev_append [d] tl;
      rev_length tl;
      alternating_append_digit (rev tl) d;
      ()

let divisible_by_11 (n:nat) : prop =
  let z:int = n in z % 11 == 0

let value_1199 () : Lemma (value #10 [9; 9; 1; 1] == 1199) = ()

let divisible_1199 () : Lemma (
    divisible_by_11 (value #10 [9; 9; 1; 1])) =
  value_1199 ();
  ()

let no_obstruction_11110 () : Lemma (
    ~ (trace_palindrome_obstruction [0; 1; 1; 1; 1])) =
  assert (trace_digits [0; 1; 1; 1; 1] == [1; 2; 2; 2; 1]);
  assert (~ (trace_carry_obstruction [0; 1; 1; 1; 1]));
  assert (~ (trace_overflow_relation_obstruction [0; 1; 1; 1; 1]));
  ()

let trace_palindrome_obstruction_exists_not_preserved_11_1199 () : Lemma (
    divisible_by_11 (value #10 [9; 9; 1; 1]) /\
    trace_palindrome_obstruction_exists [9; 9; 1; 1] /\
    ~ (trace_palindrome_obstruction_exists [0; 1; 1; 1; 1])) =
  value_1199 ();
  divisible_1199 ();
  trace_palindrome_obstruction_at_1199 ();
  assert (trace_palindrome_obstruction_at [9; 9; 1; 1] 0);
  assert (trace_palindrome_obstruction [9; 9; 1; 1]);
  trace_palindrome_obstruction_at_exists [9; 9; 1; 1];
  no_obstruction_11110 ();
  introduce (trace_palindrome_obstruction_exists [0; 1; 1; 1; 1]) ==> False
  with (
    eliminate exists (i:nat).
      trace_palindrome_obstruction_at [0; 1; 1; 1; 1] i
    with (
      trace_palindrome_obstruction_at_sound [0; 1; 1; 1; 1] i;
      assert False))

let reverse_digits_divisible_by_11 (xs:numeral 10)
  : Lemma (requires (divisible_by_11 (value xs)))
    (ensures (divisible_by_11 (value (reverse_digits xs)))) =
  alternating_value_mod11 xs;
  alternating_reverse xs;
  assert (alternating_value xs % 11 == 0);
  lemma_mod_sub_distr 0 (alternating_value xs) 11;
  if length xs % 2 = 0 then
    assert ((-alternating_value xs) % 11 == 0)
  else
    ();
  alternating_value_mod11 (rev xs);
  assert (value (rev xs) % 11 == 0);
  normalize_value (rev xs);
  assert (value (normalize (rev xs)) % 11 == 0);
  ()

let reverse_add_divisible_by_11 (xs:numeral 10)
  : Lemma (requires (divisible_by_11 (value xs)))
    (ensures (divisible_by_11 (value (reverse_add xs)))) =
  reverse_add_value #10 xs;
  reverse_digits_divisible_by_11 xs;
  modulo_distributivity (value xs) (value (reverse_digits xs)) 11;
  ()

let digits_1675 : numeral 10 = [5; 7; 6; 1]
let digits_7436 : numeral 10 = [6; 3; 4; 7]
let digits_13783 : numeral 10 = [3; 8; 7; 3; 1]
let digits_52514 : numeral 10 = [4; 1; 5; 2; 5]
let digits_94039 : numeral 10 = [9; 3; 0; 4; 9]
let digits_187088 : numeral 10 = [8; 8; 0; 7; 8; 1]
let digits_1067869 : numeral 10 = [9; 6; 8; 7; 6; 0; 1]
let digits_10755470 : numeral 10 = [0; 7; 4; 5; 5; 7; 0; 1]
let digits_18211171 : numeral 10 = [1; 7; 1; 1; 1; 2; 8; 1]
let digits_35322452 : numeral 10 = [2; 5; 4; 2; 2; 3; 5; 3]
let digits_60744805 : numeral 10 = [5; 0; 8; 4; 4; 7; 0; 6]
let digits_111589511 : numeral 10 = [1; 1; 5; 9; 8; 5; 1; 1; 1]
let digits_227574622 : numeral 10 = [2; 2; 6; 4; 7; 5; 7; 2; 2]
let digits_454050344 : numeral 10 = [4; 4; 3; 0; 5; 0; 4; 5; 4]
let digits_897100798 : numeral 10 = [8; 9; 7; 0; 0; 1; 7; 9; 8]
let digits_1794102596 : numeral 10 = [6; 9; 5; 2; 0; 1; 4; 9; 7; 1]
let digits_8746117567 : numeral 10 = [7; 6; 5; 7; 1; 1; 6; 4; 7; 8]
let digits_16403234045 : numeral 10 = [5; 4; 0; 4; 3; 2; 3; 0; 4; 6; 1]
let digits_70446464506 : numeral 10 = [6; 0; 5; 4; 6; 4; 6; 4; 4; 0; 7]
let digits_130992928913 : numeral 10 = [3; 1; 9; 8; 2; 9; 2; 9; 9; 0; 3; 1]
let digits_450822227944 : numeral 10 = [4; 4; 9; 7; 2; 2; 2; 2; 8; 0; 5; 4]
let digits_900544455998 : numeral 10 = [8; 9; 9; 5; 5; 4; 4; 4; 5; 0; 0; 9]
let digits_1800098901007 : numeral 10 = [7; 0; 0; 1; 0; 9; 8; 9; 0; 0; 0; 8; 1]
let digits_8801197801088 : numeral 10 = [8; 8; 0; 1; 0; 8; 7; 9; 1; 1; 0; 8; 8]
let digits_17602285712176 : numeral 10 = [6; 7; 1; 2; 1; 7; 5; 8; 2; 2; 0; 6; 7; 1]
let digits_84724043932847 : numeral 10 = [7; 4; 8; 2; 3; 9; 3; 4; 0; 4; 2; 7; 4; 8]
let digits_159547977975595 : numeral 10 = [5; 9; 5; 5; 7; 9; 7; 7; 9; 7; 4; 5; 9; 5; 1]
let digits_755127757721546 : numeral 10 = [6; 4; 5; 1; 2; 7; 7; 5; 7; 7; 2; 1; 5; 5; 7]
let digits_1400255515443103 : numeral 10 = [3; 0; 1; 3; 4; 4; 5; 1; 5; 5; 5; 2; 0; 0; 4; 1]

let value_digits_7436 () : Lemma (value digits_7436 == 7436) = ()

let reaches_196_1675 () : Lemma (
    iterate 2 digits_196 == digits_1675) =
  example_196 ();
  assert (iterate 1 digits_196 == digits_887);
  assert (reverse_add #10 digits_887 == digits_1675);
  ()

let reaches_196_7436 () : Lemma (
    iterate 3 digits_196 == digits_7436) =
  example_196 ();
  assert (reverse_add #10 digits_887 == digits_1675);
  assert (reverse_add #10 digits_1675 == digits_7436);
  ()

let reaches_196_13783 () : Lemma (
    iterate 4 digits_196 == digits_13783) =
  reaches_196_7436 ();
  transition_7436_to_13783 ();
  assert (reverse_add #10 digits_7436 == digits_13783);
  ()

let reaches_196_52514 () : Lemma (
    iterate 5 digits_196 == digits_52514) =
  reaches_196_13783 ();
  transition_13783_to_52514 ();
  assert (reverse_add #10 digits_13783 == digits_52514);
  ()

let reaches_196_94039 () : Lemma (
    iterate 6 digits_196 == digits_94039) =
  reaches_196_52514 ();
  transition_52514_to_94039 ();
  assert (trace_digits [4; 1; 5; 2; 5] == [9; 3; 0; 4; 9]);
  assert (trace_digits [4; 1; 5; 2; 5] ==
    reverse_add [4; 1; 5; 2; 5]);
  assert (reverse_add #10 digits_52514 == digits_94039);
  ()

let reaches_196_187088 () : Lemma (
    iterate 7 digits_196 == [8; 8; 0; 7; 8; 1]) =
  reaches_196_94039 ();
  iterate_succ #10 6 digits_196;
  reverse_add_94039_to_187088 ();
  ()

let reaches_196_1067869 () : Lemma (
    iterate 8 digits_196 == [9; 6; 8; 7; 6; 0; 1]) =
  reaches_196_187088 ();
  iterate_succ #10 7 digits_196;
  reverse_add_187088_to_1067869 ();
  ()

let reaches_196_10755470 () : Lemma (
    iterate 9 digits_196 == [0; 7; 4; 5; 5; 7; 0; 1]) =
  reaches_196_1067869 ();
  iterate_succ #10 8 digits_196;
  reverse_add_1067869_to_10755470 ();
  ()

let reaches_196_18211171 () : Lemma (
    iterate 10 digits_196 == [1; 7; 1; 1; 1; 2; 8; 1]) =
  reaches_196_10755470 ();
  iterate_succ #10 9 digits_196;
  reverse_add_10755470_to_18211171 ();
  ()

let reaches_196_35322452 () : Lemma (
    iterate 11 digits_196 == [2; 5; 4; 2; 2; 3; 5; 3]) =
  reaches_196_18211171 ();
  iterate_succ #10 10 digits_196;
  reverse_add_18211171_to_35322452 ();
  ()

let reaches_196_60744805 () : Lemma (
    iterate 12 digits_196 == [5; 0; 8; 4; 4; 7; 0; 6]) =
  reaches_196_35322452 ();
  iterate_succ #10 11 digits_196;
  reverse_add_35322452_to_60744805 ();
  ()

let reaches_196_111589511 () : Lemma (
    iterate 13 digits_196 == [1; 1; 5; 9; 8; 5; 1; 1; 1]) =
  reaches_196_60744805 ();
  iterate_succ #10 12 digits_196;
  reverse_add_60744805_to_111589511 ();
  ()

let reaches_196_227574622 () : Lemma (
    iterate 14 digits_196 == digits_227574622) =
  reaches_196_111589511 ();
  iterate_succ #10 13 digits_196;
  reverse_add_111589511_to_227574622 ();
  ()

let reaches_196_454050344 () : Lemma (
    iterate 15 digits_196 == digits_454050344) =
  reaches_196_227574622 ();
  iterate_succ #10 14 digits_196;
  reverse_add_227574622_to_454050344 ();
  ()

let reaches_196_897100798 () : Lemma (
    iterate 16 digits_196 == digits_897100798) =
  reaches_196_454050344 ();
  iterate_succ #10 15 digits_196;
  reverse_add_454050344_to_897100798 ();
  ()

let reaches_196_1794102596 () : Lemma (
    iterate 17 digits_196 == digits_1794102596) =
  reaches_196_897100798 ();
  iterate_succ #10 16 digits_196;
  reverse_add_897100798_to_1794102596 ();
  ()

let reaches_196_8746117567 () : Lemma (
    iterate 18 digits_196 == digits_8746117567) =
  reaches_196_1794102596 ();
  iterate_succ #10 17 digits_196;
  reverse_add_1794102596_to_8746117567 ();
  ()

let reaches_196_16403234045 () : Lemma (
    iterate 19 digits_196 == digits_16403234045) =
  reaches_196_8746117567 ();
  iterate_succ #10 18 digits_196;
  reverse_add_8746117567_to_16403234045 ();
  ()

let reaches_196_70446464506 () : Lemma (
    iterate 20 digits_196 == digits_70446464506) =
  reaches_196_16403234045 ();
  iterate_succ #10 19 digits_196;
  reverse_add_16403234045_to_70446464506 ();
  ()

let reaches_196_130992928913 () : Lemma (
    iterate 21 digits_196 == digits_130992928913) =
  reaches_196_70446464506 ();
  iterate_succ #10 20 digits_196;
  reverse_add_70446464506_to_130992928913 ();
  ()

let reaches_196_450822227944 () : Lemma (
    iterate 22 digits_196 == digits_450822227944) =
  reaches_196_130992928913 ();
  iterate_succ #10 21 digits_196;
  reverse_add_130992928913_to_450822227944 ();
  ()

let reaches_196_900544455998 () : Lemma (
    iterate 23 digits_196 == digits_900544455998) =
  reaches_196_450822227944 ();
  iterate_succ #10 22 digits_196;
  reverse_add_450822227944_to_900544455998 ();
  ()

let reaches_196_1800098901007 () : Lemma (
    iterate 24 digits_196 == digits_1800098901007) =
  reaches_196_900544455998 ();
  iterate_succ #10 23 digits_196;
  reverse_add_900544455998_to_1800098901007 ();
  ()

let reaches_196_8801197801088 () : Lemma (
    iterate 25 digits_196 == digits_8801197801088) =
  reaches_196_1800098901007 ();
  iterate_succ #10 24 digits_196;
  reverse_add_1800098901007_to_8801197801088 ();
  ()

let reaches_196_17602285712176 () : Lemma (
    iterate 26 digits_196 == digits_17602285712176) =
  reaches_196_8801197801088 ();
  iterate_succ #10 25 digits_196;
  reverse_add_8801197801088_to_17602285712176 ();
  ()

let reaches_196_84724043932847 () : Lemma (
    iterate 27 digits_196 == digits_84724043932847) =
  reaches_196_17602285712176 ();
  iterate_succ #10 26 digits_196;
  reverse_add_17602285712176_to_84724043932847 ();
  ()

let reaches_196_159547977975595 () : Lemma (
    iterate 28 digits_196 == digits_159547977975595) =
  reaches_196_84724043932847 ();
  iterate_succ #10 27 digits_196;
  reverse_add_84724043932847_to_159547977975595 ();
  ()

let reaches_196_755127757721546 () : Lemma (
    iterate 29 digits_196 == digits_755127757721546) =
  reaches_196_159547977975595 ();
  iterate_succ #10 28 digits_196;
  reverse_add_159547977975595_to_755127757721546 ();
  ()

let reaches_196_1400255515443103 () : Lemma (
    iterate 30 digits_196 == digits_1400255515443103) =
  reaches_196_755127757721546 ();
  iterate_succ #10 29 digits_196;
  reverse_add_755127757721546_to_1400255515443103 ();
  ()

let finite_196_indexed_witnesses () : Lemma (
    trace_palindrome_obstruction_at (iterate 0 digits_196) 0 /\
    trace_palindrome_obstruction_at (iterate 1 digits_196) 0 /\
    trace_palindrome_obstruction_at (iterate 2 digits_196) 0 /\
    trace_palindrome_obstruction_at (iterate 3 digits_196) 0 /\
    trace_palindrome_obstruction_at (iterate 4 digits_196) 0 /\
    trace_palindrome_obstruction_at (iterate 5 digits_196) 1 /\
    trace_palindrome_obstruction_at (iterate 6 digits_196) 0) =
  assert (iterate 0 digits_196 == digits_196);
  trace_palindrome_obstruction_at_196 ();
  example_196 ();
  assert (iterate 1 digits_196 == digits_887);
  trace_palindrome_obstruction_at_887 ();
  reaches_196_1675 ();
  trace_palindrome_obstruction_at_1675 ();
  reaches_196_7436 ();
  trace_palindrome_obstruction_at_7436 ();
  reaches_196_13783 ();
  trace_palindrome_obstruction_at_13783 ();
  reaches_196_52514 ();
  trace_palindrome_obstruction_at_52514 ();
  reaches_196_94039 ();
  trace_palindrome_obstruction_at_94039 ();
  ()

let witness_index_196 (k:nat) : nat =
  if k = 5 then 1 else if k = 9 then 1 else if k = 12 then 2 else 0

let digits_196_canonical_nonempty () : Lemma (
    canonical digits_196 /\ digits_196 <> []) = ()

let finite_196_indexed_nonpalindrome () : Lemma (
    ~ (palindrome #10 (iterate 1 digits_196)) /\
    ~ (palindrome #10 (iterate 2 digits_196)) /\
    ~ (palindrome #10 (iterate 3 digits_196)) /\
    ~ (palindrome #10 (iterate 4 digits_196)) /\
    ~ (palindrome #10 (iterate 5 digits_196)) /\
    ~ (palindrome #10 (iterate 6 digits_196)) /\
    ~ (palindrome #10 (iterate 7 digits_196))) =
  digits_196_canonical_nonempty ();
  finite_196_indexed_witnesses ();
  assert (witness_index_196 0 == 0);
  assert (trace_palindrome_obstruction_at
    (iterate 0 digits_196) (witness_index_196 0));
  iterate_indexed_witness_excludes_palindrome
    digits_196 witness_index_196 0;
  assert (witness_index_196 1 == 0);
  assert (trace_palindrome_obstruction_at
    (iterate 1 digits_196) (witness_index_196 1));
  iterate_indexed_witness_excludes_palindrome
    digits_196 witness_index_196 1;
  assert (witness_index_196 2 == 0);
  assert (trace_palindrome_obstruction_at
    (iterate 2 digits_196) (witness_index_196 2));
  iterate_indexed_witness_excludes_palindrome
    digits_196 witness_index_196 2;
  assert (witness_index_196 3 == 0);
  assert (trace_palindrome_obstruction_at
    (iterate 3 digits_196) (witness_index_196 3));
  iterate_indexed_witness_excludes_palindrome
    digits_196 witness_index_196 3;
  assert (witness_index_196 4 == 0);
  assert (trace_palindrome_obstruction_at
    (iterate 4 digits_196) (witness_index_196 4));
  iterate_indexed_witness_excludes_palindrome
    digits_196 witness_index_196 4;
  assert (witness_index_196 5 == 1);
  assert (trace_palindrome_obstruction_at
    (iterate 5 digits_196) (witness_index_196 5));
  iterate_indexed_witness_excludes_palindrome
    digits_196 witness_index_196 5;
  assert (witness_index_196 6 == 0);
  assert (trace_palindrome_obstruction_at
    (iterate 6 digits_196) (witness_index_196 6));
  iterate_indexed_witness_excludes_palindrome
    digits_196 witness_index_196 6;
  ()

let finite_196_suffix_indexed_witnesses () : Lemma (
    trace_palindrome_obstruction_at (iterate 7 digits_196) 0 /\
    trace_palindrome_obstruction_at (iterate 8 digits_196) 0 /\
    trace_palindrome_obstruction_at (iterate 9 digits_196) 1 /\
    trace_palindrome_obstruction_at (iterate 10 digits_196) 0 /\
    trace_palindrome_obstruction_at (iterate 11 digits_196) 0 /\
    trace_palindrome_obstruction_at (iterate 12 digits_196) 2 /\
    trace_palindrome_obstruction_at (iterate 13 digits_196) 2 /\
    trace_palindrome_obstruction_at (iterate 14 digits_196) 1 /\
    trace_palindrome_obstruction_at (iterate 15 digits_196) 3 /\
    trace_palindrome_obstruction_at (iterate 16 digits_196) 0 /\
    trace_palindrome_obstruction_at (iterate 17 digits_196) 0 /\
    trace_palindrome_obstruction_at (iterate 18 digits_196) 0 /\
    trace_palindrome_obstruction_at (iterate 19 digits_196) 0 /\
    trace_palindrome_obstruction_at (iterate 20 digits_196) 0 /\
    trace_palindrome_obstruction_at (iterate 21 digits_196) 1 /\
    trace_palindrome_obstruction_at (iterate 22 digits_196) 0 /\
    trace_palindrome_obstruction_at (iterate 23 digits_196) 0 /\
    trace_palindrome_obstruction_at (iterate 24 digits_196) 4 /\
    trace_palindrome_obstruction_at (iterate 25 digits_196) 0 /\
    trace_palindrome_obstruction_at (iterate 26 digits_196) 0 /\
    trace_palindrome_obstruction_at (iterate 27 digits_196) 0 /\
    trace_palindrome_obstruction_at (iterate 28 digits_196) 0 /\
    trace_palindrome_obstruction_at (iterate 29 digits_196) 0) =
  reaches_196_187088 ();
  trace_palindrome_obstruction_at_187088 ();
  reaches_196_1067869 ();
  trace_palindrome_obstruction_at_1067869 ();
  reaches_196_10755470 ();
  trace_palindrome_obstruction_at_10755470 ();
  reaches_196_18211171 ();
  trace_palindrome_obstruction_at_18211171 ();
  reaches_196_35322452 ();
  trace_palindrome_obstruction_at_35322452 ();
  reaches_196_60744805 ();
  trace_palindrome_obstruction_at_60744805 ();
  reaches_196_111589511 ();
  trace_palindrome_obstruction_at_111589511 ();
  reaches_196_227574622 ();
  trace_palindrome_obstruction_at_227574622 ();
  reaches_196_454050344 ();
  trace_palindrome_obstruction_at_454050344 ();
  reaches_196_897100798 ();
  trace_palindrome_obstruction_at_897100798 ();
  reaches_196_1794102596 ();
  trace_palindrome_obstruction_at_1794102596 ();
  reaches_196_8746117567 ();
  trace_palindrome_obstruction_at_8746117567 ();
  reaches_196_16403234045 ();
  trace_palindrome_obstruction_at_16403234045 ();
  reaches_196_70446464506 ();
  trace_palindrome_obstruction_at_70446464506 ();
  reaches_196_130992928913 ();
  trace_palindrome_obstruction_at_130992928913 ();
  reaches_196_450822227944 ();
  trace_palindrome_obstruction_at_450822227944 ();
  reaches_196_900544455998 ();
  trace_palindrome_obstruction_at_900544455998 ();
  reaches_196_1800098901007 ();
  trace_palindrome_obstruction_at_1800098901007 ();
  reaches_196_8801197801088 ();
  trace_palindrome_obstruction_at_8801197801088 ();
  reaches_196_17602285712176 ();
  trace_palindrome_obstruction_at_17602285712176 ();
  reaches_196_84724043932847 ();
  trace_palindrome_obstruction_at_84724043932847 ();
  reaches_196_159547977975595 ();
  trace_palindrome_obstruction_at_159547977975595 ();
  reaches_196_755127757721546 ();
  trace_palindrome_obstruction_at_755127757721546 ();
  ()

let finite_196_suffix_indexed_nonpalindrome () : Lemma (
    ~ (palindrome #10 (iterate 8 digits_196)) /\
    ~ (palindrome #10 (iterate 9 digits_196)) /\
    ~ (palindrome #10 (iterate 10 digits_196)) /\
    ~ (palindrome #10 (iterate 11 digits_196)) /\
    ~ (palindrome #10 (iterate 12 digits_196)) /\
    ~ (palindrome #10 (iterate 13 digits_196)) /\
    ~ (palindrome #10 (iterate 14 digits_196)) /\
    ~ (palindrome #10 (iterate 15 digits_196)) /\
    ~ (palindrome #10 (iterate 16 digits_196)) /\
    ~ (palindrome #10 (iterate 17 digits_196)) /\
    ~ (palindrome #10 (iterate 18 digits_196)) /\
    ~ (palindrome #10 (iterate 19 digits_196)) /\
    ~ (palindrome #10 (iterate 20 digits_196)) /\
    ~ (palindrome #10 (iterate 21 digits_196)) /\
    ~ (palindrome #10 (iterate 22 digits_196)) /\
    ~ (palindrome #10 (iterate 23 digits_196)) /\
    ~ (palindrome #10 (iterate 24 digits_196)) /\
    ~ (palindrome #10 (iterate 25 digits_196)) /\
    ~ (palindrome #10 (iterate 26 digits_196)) /\
    ~ (palindrome #10 (iterate 27 digits_196)) /\
    ~ (palindrome #10 (iterate 28 digits_196)) /\
    ~ (palindrome #10 (iterate 29 digits_196)) /\
    ~ (palindrome #10 (iterate 30 digits_196))) =
  digits_196_canonical_nonempty ();
  finite_196_suffix_indexed_witnesses ();
  assert (trace_palindrome_obstruction_at
    (iterate 7 digits_196) 0);
  iterate_indexed_witness_excludes_palindrome
    digits_196 (fun _ -> 0) 7;
  assert (trace_palindrome_obstruction_at
    (iterate 8 digits_196) 0);
  iterate_indexed_witness_excludes_palindrome
    digits_196 (fun _ -> 0) 8;
  assert (trace_palindrome_obstruction_at
    (iterate 9 digits_196) 1);
  iterate_indexed_witness_excludes_palindrome
    digits_196 (fun _ -> 1) 9;
  assert (trace_palindrome_obstruction_at
    (iterate 10 digits_196) 0);
  iterate_indexed_witness_excludes_palindrome
    digits_196 (fun _ -> 0) 10;
  assert (trace_palindrome_obstruction_at
    (iterate 11 digits_196) 0);
  iterate_indexed_witness_excludes_palindrome
    digits_196 (fun _ -> 0) 11;
  assert (trace_palindrome_obstruction_at
    (iterate 12 digits_196) 2);
  iterate_indexed_witness_excludes_palindrome
    digits_196 (fun _ -> 2) 12;
  assert (trace_palindrome_obstruction_at
    (iterate 13 digits_196) 2);
  iterate_indexed_witness_excludes_palindrome
    digits_196 (fun _ -> 2) 13;
  assert (trace_palindrome_obstruction_at
    (iterate 14 digits_196) 1);
  iterate_indexed_witness_excludes_palindrome
    digits_196 (fun _ -> 1) 14;
  assert (trace_palindrome_obstruction_at
    (iterate 15 digits_196) 3);
  iterate_indexed_witness_excludes_palindrome
    digits_196 (fun _ -> 3) 15;
  assert (trace_palindrome_obstruction_at
    (iterate 16 digits_196) 0);
  iterate_indexed_witness_excludes_palindrome
    digits_196 (fun _ -> 0) 16;
  assert (trace_palindrome_obstruction_at
    (iterate 17 digits_196) 0);
  iterate_indexed_witness_excludes_palindrome
    digits_196 (fun _ -> 0) 17;
  assert (trace_palindrome_obstruction_at
    (iterate 18 digits_196) 0);
  iterate_indexed_witness_excludes_palindrome
    digits_196 (fun _ -> 0) 18;
  assert (trace_palindrome_obstruction_at
    (iterate 19 digits_196) 0);
  iterate_indexed_witness_excludes_palindrome
    digits_196 (fun _ -> 0) 19;
  assert (trace_palindrome_obstruction_at
    (iterate 20 digits_196) 0);
  iterate_indexed_witness_excludes_palindrome
    digits_196 (fun _ -> 0) 20;
  assert (trace_palindrome_obstruction_at
    (iterate 21 digits_196) 1);
  iterate_indexed_witness_excludes_palindrome
    digits_196 (fun _ -> 1) 21;
  assert (trace_palindrome_obstruction_at
    (iterate 22 digits_196) 0);
  iterate_indexed_witness_excludes_palindrome
    digits_196 (fun _ -> 0) 22;
  assert (trace_palindrome_obstruction_at
    (iterate 23 digits_196) 0);
  iterate_indexed_witness_excludes_palindrome
    digits_196 (fun _ -> 0) 23;
  assert (trace_palindrome_obstruction_at
    (iterate 24 digits_196) 4);
  iterate_indexed_witness_excludes_palindrome
    digits_196 (fun _ -> 4) 24;
  assert (trace_palindrome_obstruction_at
    (iterate 25 digits_196) 0);
  iterate_indexed_witness_excludes_palindrome
    digits_196 (fun _ -> 0) 25;
  assert (trace_palindrome_obstruction_at
    (iterate 26 digits_196) 0);
  iterate_indexed_witness_excludes_palindrome
    digits_196 (fun _ -> 0) 26;
  assert (trace_palindrome_obstruction_at
    (iterate 27 digits_196) 0);
  iterate_indexed_witness_excludes_palindrome
    digits_196 (fun _ -> 0) 27;
  assert (trace_palindrome_obstruction_at
    (iterate 28 digits_196) 0);
  iterate_indexed_witness_excludes_palindrome
    digits_196 (fun _ -> 0) 28;
  assert (trace_palindrome_obstruction_at
    (iterate 29 digits_196) 0);
  iterate_indexed_witness_excludes_palindrome
    digits_196 (fun _ -> 0) 29;
  ()

let finite_196_prefix_nonpalindrome () : Lemma (
    ~ (palindrome #10 (iterate 1 digits_196)) /\
    ~ (palindrome #10 (iterate 2 digits_196)) /\
    ~ (palindrome #10 (iterate 3 digits_196)) /\
    ~ (palindrome #10 (iterate 4 digits_196)) /\
    ~ (palindrome #10 (iterate 5 digits_196)) /\
    ~ (palindrome #10 (iterate 6 digits_196)) /\
    ~ (palindrome #10 (iterate 7 digits_196)) /\
    ~ (palindrome #10 (iterate 8 digits_196)) /\
    ~ (palindrome #10 (iterate 9 digits_196)) /\
    ~ (palindrome #10 (iterate 10 digits_196)) /\
    ~ (palindrome #10 (iterate 11 digits_196)) /\
    ~ (palindrome #10 (iterate 12 digits_196)) /\
    ~ (palindrome #10 (iterate 13 digits_196)) /\
    ~ (palindrome #10 (iterate 14 digits_196)) /\
    ~ (palindrome #10 (iterate 15 digits_196)) /\
    ~ (palindrome #10 (iterate 16 digits_196)) /\
    ~ (palindrome #10 (iterate 17 digits_196)) /\
    ~ (palindrome #10 (iterate 18 digits_196)) /\
    ~ (palindrome #10 (iterate 19 digits_196)) /\
    ~ (palindrome #10 (iterate 20 digits_196)) /\
    ~ (palindrome #10 (iterate 21 digits_196)) /\
    ~ (palindrome #10 (iterate 22 digits_196)) /\
    ~ (palindrome #10 (iterate 23 digits_196)) /\
    ~ (palindrome #10 (iterate 24 digits_196)) /\
    ~ (palindrome #10 (iterate 25 digits_196)) /\
    ~ (palindrome #10 (iterate 26 digits_196)) /\
    ~ (palindrome #10 (iterate 27 digits_196)) /\
    ~ (palindrome #10 (iterate 28 digits_196)) /\
    ~ (palindrome #10 (iterate 29 digits_196)) /\
    ~ (palindrome #10 (iterate 30 digits_196))) =
  finite_196_indexed_nonpalindrome ();
  finite_196_suffix_indexed_nonpalindrome ()

let finite_196_prefix_obstruction () : Lemma (
    trace_palindrome_obstruction (iterate 0 digits_196) /\
    trace_palindrome_obstruction (iterate 1 digits_196) /\
    trace_palindrome_obstruction (iterate 2 digits_196) /\
    trace_palindrome_obstruction (iterate 3 digits_196) /\
    trace_palindrome_obstruction (iterate 4 digits_196) /\
    trace_palindrome_obstruction (iterate 5 digits_196)) =
  assert (iterate 0 digits_196 == digits_196);
  trace_carry_obstruction_196 ();
  assert (trace_palindrome_obstruction digits_196);
  example_196 ();
  assert (iterate 1 digits_196 == digits_887);
  trace_carry_obstruction_887 ();
  assert (trace_palindrome_obstruction digits_887);
  assert (digits_1675 == [5; 7; 6; 1]);
  reaches_196_1675 ();
  trace_carry_obstruction_1675 ();
  assert (trace_palindrome_obstruction digits_1675);
  assert (digits_7436 == [6; 3; 4; 7]);
  reaches_196_7436 ();
  trace_carry_obstruction_7436 ();
  assert (trace_palindrome_obstruction digits_7436);
  reaches_196_13783 ();
  trace_carry_obstruction_13783 ();
  assert (trace_palindrome_obstruction digits_13783);
  reaches_196_52514 ();
  trace_carry_obstruction_52514 ();
  assert (trace_palindrome_obstruction digits_52514);
  reaches_196_94039 ();
  trace_carry_obstruction_94039 ();
  assert (trace_palindrome_obstruction digits_94039);
  ()

let divisible_196_by_11_at_7436 () : Lemma (
    divisible_by_11 (value (iterate 3 digits_196))) =
  reaches_196_7436 ();
  value_digits_7436 ();
  ()

let rec iterate_divisible_by_11 (k:nat) (xs:numeral 10)
  : Lemma (requires (divisible_by_11 (value xs)))
    (ensures (divisible_by_11 (value (iterate k xs))))
    (decreases k) =
  if k = 0 then
    ()
  else
    let k' : nat = k - 1 in
    reverse_add_divisible_by_11 xs;
    iterate_divisible_by_11 k' (reverse_add xs)

let divisible_196_by_11_after_7436 (k:nat)
  : Lemma (ensures (
      divisible_by_11 (value (iterate k digits_7436)))) =
  value_digits_7436 ();
  iterate_divisible_by_11 k digits_7436;
  ()

let rec divisible_196_by_11_after_iterate_3 (k:nat) : Lemma (
    ensures (divisible_by_11 (value (iterate (k + 3) digits_196))))
    (decreases k) =
  if k = 0 then
    divisible_196_by_11_at_7436 ()
  else
    let k' : nat = k - 1 in
    divisible_196_by_11_after_iterate_3 k';
    iterate_succ #10 (k' + 3) digits_196;
    reverse_add_divisible_by_11 (iterate (k' + 3) digits_196);
    assert (k == k' + 1);
    assert ((k' + 3) + 1 == k + 3);
    ()

let divisible_by_11_does_not_exclude_palindrome () : Lemma (
    divisible_by_11 (value digits_121) /\ palindrome #10 digits_121) =
  assert (value digits_121 == 121);
  example_56 ();
  ()

let trace_no_overflow_high_sum_not_candidate
  (xs:numeral 10) (i:nat) : Lemma (requires (
      xs <> [] /\
      length (trace_digits xs) == length xs /\
      nth (trace_carries xs) (length xs) == Some 0 /\
      i < length xs /\
      trace_sum_at xs i >= 10))
    (ensures (~ (trace_palindrome_candidate xs))) =
  introduce (trace_palindrome_candidate xs) ==> False
  with (
    eliminate
      (length (trace_digits xs) == length xs /\
       nth (trace_carries xs) (length xs) == Some 0 /\
       (forall j. j < length xs ==> trace_sum_at xs j < 10)) \/
      (length (trace_digits xs) == length xs + 1 /\
       nth (trace_carries xs) (length xs) == Some 1 /\
       trace_sum_at xs 0 == 11 /\
       (forall j. 0 < j /\ j <= length xs ==>
         ~(trace_sum_at xs j >= trace_sum_at xs (j - 1) + 12 \/
           trace_sum_at xs (j - 1) >= trace_sum_at xs j + 12)))
    with (
      assert (trace_sum_at xs i < 10);
      assert False)
    and (
      assert False))

let trace_no_overflow_carry_obstruction_not_candidate
  (xs:numeral 10) (i:nat) : Lemma (requires (
      xs <> [] /\
      length (trace_digits xs) == length xs /\
      nth (trace_carries xs) (length xs) == Some 0 /\
      i < length xs /\
      ~(trace_carry_at xs i ==
        trace_carry_at xs (length xs - 1 - i))))
    (ensures (~ (trace_palindrome_candidate xs))) =
  introduce (trace_palindrome_candidate xs) ==> False
  with (
    eliminate
      (length (trace_digits xs) == length xs /\
       nth (trace_carries xs) (length xs) == Some 0 /\
       (forall j. j < length xs ==> trace_sum_at xs j < 10)) \/
      (length (trace_digits xs) == length xs + 1 /\
       nth (trace_carries xs) (length xs) == Some 1 /\
       trace_sum_at xs 0 == 11 /\
       (forall j. 0 < j /\ j <= length xs ==>
         ~(trace_sum_at xs j >= trace_sum_at xs (j - 1) + 12 \/
           trace_sum_at xs (j - 1) >= trace_sum_at xs j + 12)))
    with (
      let mirror : nat = length xs - 1 - i in
      assert (mirror < length xs);
      trace_carry_prefix_zero xs i;
      trace_carry_prefix_zero xs mirror;
      assert (trace_carry_at xs i == 0);
      assert (trace_carry_at xs mirror == 0);
      assert False)
    and (
      assert False))

let trace_overflow_outer_sum_not_candidate
  (xs:numeral 10) : Lemma (requires (
      xs <> [] /\
      length (trace_digits xs) == length xs + 1 /\
      nth (trace_carries xs) (length xs) == Some 1 /\
      trace_sum_at xs 0 <> 1 /\
      trace_sum_at xs 0 <> 11))
    (ensures (~ (trace_palindrome_candidate xs))) =
  introduce (trace_palindrome_candidate xs) ==> False
  with (
    eliminate
      (length (trace_digits xs) == length xs /\
       nth (trace_carries xs) (length xs) == Some 0 /\
       (forall j. j < length xs ==> trace_sum_at xs j < 10)) \/
      (length (trace_digits xs) == length xs + 1 /\
       nth (trace_carries xs) (length xs) == Some 1 /\
       trace_sum_at xs 0 == 11 /\
       (forall j. 0 < j /\ j <= length xs ==>
         ~(trace_sum_at xs j >= trace_sum_at xs (j - 1) + 12 \/
           trace_sum_at xs (j - 1) >= trace_sum_at xs j + 12)))
    with (
      assert False)
    and (
      assert False))

let trace_overflow_sum_jump_not_candidate
  (xs:numeral 10) (i:nat) : Lemma (requires (
      xs <> [] /\
      length (trace_digits xs) == length xs + 1 /\
      nth (trace_carries xs) (length xs) == Some 1 /\
      0 < i /\
      i <= length xs /\
      (trace_sum_at xs i >= trace_sum_at xs (i - 1) + 12 \/
       trace_sum_at xs (i - 1) >= trace_sum_at xs i + 12)))
    (ensures (~ (trace_palindrome_candidate xs))) =
  introduce (trace_palindrome_candidate xs) ==> False
  with (
    eliminate
      (length (trace_digits xs) == length xs /\
       nth (trace_carries xs) (length xs) == Some 0 /\
       (forall j. j < length xs ==> trace_sum_at xs j < 10)) \/
      (length (trace_digits xs) == length xs + 1 /\
       nth (trace_carries xs) (length xs) == Some 1 /\
       trace_sum_at xs 0 == 11 /\
       (forall j. 0 < j /\ j <= length xs ==>
         ~(trace_sum_at xs j >= trace_sum_at xs (j - 1) + 12 \/
           trace_sum_at xs (j - 1) >= trace_sum_at xs j + 12)))
    with (
      assert False)
    and (
      assert (~ (trace_sum_at xs i >= trace_sum_at xs (i - 1) + 12 \/
        trace_sum_at xs (i - 1) >= trace_sum_at xs i + 12));
      assert False))

let trace_overflow_low_one_not_candidate
  (xs:numeral 10) : Lemma (requires (
      xs <> [] /\
      length (trace_digits xs) == length xs + 1 /\
      nth (trace_carries xs) (length xs) == Some 1 /\
      ~(trace_digit_at xs 0 == 1)))
    (ensures (~ (trace_palindrome_candidate xs))) =
  introduce (trace_palindrome_candidate xs) ==> False
  with (
    eliminate
      (length (trace_digits xs) == length xs /\
       nth (trace_carries xs) (length xs) == Some 0 /\
       (forall j. j < length xs ==> trace_sum_at xs j < 10)) \/
      (length (trace_digits xs) == length xs + 1 /\
       nth (trace_carries xs) (length xs) == Some 1 /\
       trace_sum_at xs 0 == 11 /\
       (forall j. 0 < j /\ j <= length xs ==>
         ~(trace_sum_at xs j >= trace_sum_at xs (j - 1) + 12 \/
           trace_sum_at xs (j - 1) >= trace_sum_at xs j + 12)))
    with (
      assert False)
    and (
      trace_equation_at xs 0;
      assert (trace_carry_at xs 0 == 0);
      assert (trace_carry_at xs 1 == 0 \/ trace_carry_at xs 1 == 1);
      assert (trace_sum_at xs 0 == 11);
      eliminate trace_carry_at xs 1 == 0 \/ trace_carry_at xs 1 == 1
      with (
        assert (trace_digit_at xs 0 == 11);
        assert False)
      and (
        assert (trace_digit_at xs 0 == 1);
        assert False)))

let not_candidate_196 () : Lemma (
    ~ (trace_palindrome_candidate digits_196)) =
  assert (length (trace_digits digits_196) == length digits_196);
  assert (nth (trace_carries digits_196) (length digits_196) == Some 0);
  assert (trace_sum_at digits_196 1 >= 10);
  trace_no_overflow_high_sum_not_candidate digits_196 1;
  ()

let not_candidate_887 () : Lemma (
    ~ (trace_palindrome_candidate digits_887)) =
  assert (length (trace_digits digits_887) == length digits_887 + 1);
  assert (nth (trace_carries digits_887) (length digits_887) == Some 1);
  assert (~ (trace_digit_at digits_887 0 == 1));
  trace_overflow_low_one_not_candidate digits_887;
  ()

let not_candidate_1675 () : Lemma (
    ~ (trace_palindrome_candidate digits_1675)) =
  assert (digits_1675 == [5; 7; 6; 1]);
  assert (length (trace_digits digits_1675) == length digits_1675);
  assert (nth (trace_carries digits_1675) (length digits_1675) == Some 0);
  assert (~ (trace_carry_at digits_1675 0 ==
    trace_carry_at digits_1675 3));
  trace_no_overflow_carry_obstruction_not_candidate digits_1675 0;
  ()

let not_candidate_7436 () : Lemma (
    ~ (trace_palindrome_candidate digits_7436)) =
  assert (digits_7436 == [6; 3; 4; 7]);
  assert (trace_sum_at digits_7436 0 <> 1);
  assert (trace_sum_at digits_7436 0 <> 11);
  assert (length (trace_digits digits_7436) == length digits_7436 + 1);
  assert (nth (trace_carries digits_7436) (length digits_7436) == Some 1);
  trace_overflow_outer_sum_not_candidate digits_7436;
  ()

let not_candidate_13783 () : Lemma (
    ~ (trace_palindrome_candidate digits_13783)) =
  assert (digits_13783 == [3; 8; 7; 3; 1]);
  assert (length (trace_digits digits_13783) == length digits_13783);
  assert (nth (trace_carries digits_13783) (length digits_13783) == Some 0);
  assert (~ (trace_carry_at digits_13783 0 ==
    trace_carry_at digits_13783 4));
  trace_no_overflow_carry_obstruction_not_candidate digits_13783 0;
  ()

let not_candidate_52514 () : Lemma (
    ~ (trace_palindrome_candidate digits_52514)) =
  assert (digits_52514 == [4; 1; 5; 2; 5]);
  assert (length (trace_digits digits_52514) == length digits_52514);
  assert (nth (trace_carries digits_52514) (length digits_52514) == Some 0);
  assert (~ (trace_carry_at digits_52514 1 ==
    trace_carry_at digits_52514 3));
  trace_no_overflow_carry_obstruction_not_candidate digits_52514 1;
  ()

let not_candidate_94039 () : Lemma (
    ~ (trace_palindrome_candidate digits_94039)) =
  assert (digits_94039 == [9; 3; 0; 4; 9]);
  assert (trace_sum_at digits_94039 0 <> 1);
  assert (trace_sum_at digits_94039 0 <> 11);
  assert (length (trace_digits digits_94039) == length digits_94039 + 1);
  assert (nth (trace_carries digits_94039) (length digits_94039) == Some 1);
  trace_overflow_outer_sum_not_candidate digits_94039;
  ()

// The generalized low-outer-sum rule applies to the concrete 196 boundary
// 13783 -> 52514 at its central cell.
let local_profile_witness_52514 () : Lemma (
    trace_local_profile_complement_witness digits_52514) =
  assert (digits_13783 == [3; 8; 7; 3; 1]);
  assert (digits_52514 == [4; 1; 5; 2; 5]);
  assert (canonical digits_13783);
  assert (digits_13783 <> []);
  assert (length (trace_digits digits_13783) == length digits_13783);
  assert (nth (trace_carries digits_13783) (length digits_13783) == Some 0);
  assert (trace_sum_at digits_13783 0 == 4);
  assert (trace_sum_at digits_13783 2 == 14);
  assert (trace_carry_at digits_13783 2 == 1);
  assert (trace_carry_at digits_13783 3 == 1);
  exists_intro
    (fun (i:nat) -> i < length digits_13783 /\
      2 * trace_sum_at digits_13783 i +
          trace_carry_at digits_13783 i +
          trace_carry_at digits_13783 (length digits_13783 - 1 - i) >=
        10 + 10 * (trace_carry_at digits_13783 (i + 1) +
          trace_carry_at digits_13783 (length digits_13783 - i)))
    2;
  transition_13783_to_52514 ();
  no_overflow_outer_sum_1_to_4_cell_implies_next_witness digits_13783;
  ()

// The overflow rule also discharges the concrete 887 -> 1675 boundary.
let local_profile_witness_1675 () : Lemma (
    trace_local_profile_complement_witness digits_1675) =
  assert (digits_887 == [7; 8; 8]);
  assert (digits_1675 == [5; 7; 6; 1]);
  assert (canonical digits_887);
  assert (digits_887 <> []);
  assert (length (trace_digits digits_887) == length digits_887 + 1);
  assert (nth (trace_carries digits_887) (length digits_887) == Some 1);
  assert (trace_sum_at digits_887 0 == 15);
  assert (trace_sum_at digits_887 1 == 16);
  assert (trace_sum_at digits_887 2 == 15);
  assert (trace_carry_at digits_887 1 == 1);
  assert (trace_carry_at digits_887 2 == 1);
  assert (trace_carry_at digits_887 3 == 1);
  exists_intro
    (fun (i:nat) -> 0 < i /\ i < length digits_887 /\
      trace_sum_at digits_887 i +
          trace_sum_at digits_887 (length digits_887 - i) +
          trace_carry_at digits_887 i +
          trace_carry_at digits_887 (length digits_887 - i) >=
        10 + 10 * (trace_carry_at digits_887 (i + 1) +
          trace_carry_at digits_887 (length digits_887 - i + 1)))
    1;
  assert (reverse_add #10 digits_887 == digits_1675);
  overflow_internal_cell_implies_next_witness digits_887;
  ()

// The outer-sum-10 exception is covered by the known no-overflow branch at
// the concrete 1067869 -> 10755470 boundary.
let local_profile_witness_10755470 () : Lemma (
    trace_local_profile_complement_witness
      [0; 7; 4; 5; 5; 7; 0; 1]) =
  assert (canonical #10 [9; 6; 8; 7; 6; 0; 1]);
  trace_palindrome_obstruction_at_1067869 ();
  assert (length (trace_digits [9; 6; 8; 7; 6; 0; 1]) ==
    length [9; 6; 8; 7; 6; 0; 1] + 1);
  assert (nth (trace_carries [9; 6; 8; 7; 6; 0; 1])
    (length [9; 6; 8; 7; 6; 0; 1]) == Some 1);
  assert (trace_sum_at [9; 6; 8; 7; 6; 0; 1] 0 == 10);
  assert (trace_sum_at [9; 6; 8; 7; 6; 0; 1] 2 == 14);
  assert (trace_sum_at [9; 6; 8; 7; 6; 0; 1] 5 == 6);
  assert (trace_carry_at [9; 6; 8; 7; 6; 0; 1] 2 == 0);
  assert (trace_carry_at [9; 6; 8; 7; 6; 0; 1] 3 == 1);
  assert (trace_carry_at [9; 6; 8; 7; 6; 0; 1] 5 == 1);
  assert (trace_carry_at [9; 6; 8; 7; 6; 0; 1] 6 == 0);
  reverse_add_1067869_to_10755470 ();
  trace_no_overflow_10755470 ();
  assert (length (trace_digits [0; 7; 4; 5; 5; 7; 0; 1]) ==
    length [0; 7; 4; 5; 5; 7; 0; 1]);
  assert (nth (trace_carries [0; 7; 4; 5; 5; 7; 0; 1])
    (length [0; 7; 4; 5; 5; 7; 0; 1]) == Some 0);
  exists_intro
    (fun (i:nat) -> 0 < i /\ i < length [9; 6; 8; 7; 6; 0; 1] /\
      trace_sum_at [9; 6; 8; 7; 6; 0; 1] i +
          trace_sum_at [9; 6; 8; 7; 6; 0; 1]
            (length [9; 6; 8; 7; 6; 0; 1] - i) +
          trace_carry_at [9; 6; 8; 7; 6; 0; 1] i +
          trace_carry_at [9; 6; 8; 7; 6; 0; 1]
            (length [9; 6; 8; 7; 6; 0; 1] - i) >=
        10 + 10 *
          (trace_carry_at [9; 6; 8; 7; 6; 0; 1] (i + 1) +
           trace_carry_at [9; 6; 8; 7; 6; 0; 1]
             (length [9; 6; 8; 7; 6; 0; 1] - i + 1)))
    2;
  overflow_to_no_overflow_internal_cell_implies_next_witness
    [9; 6; 8; 7; 6; 0; 1]
    [0; 7; 4; 5; 5; 7; 0; 1];
  ()

// The no-overflow low-sum rule discharges the next concrete boundary at
// 10755470 -> 18211171 using the internal cell i=1.
let local_profile_witness_18211171 () : Lemma (
    trace_local_profile_complement_witness
      [1; 7; 1; 1; 1; 2; 8; 1]) =
  trace_profile_shape_10755470 ();
  trace_profile_facts_10755470 ();
  trace_no_overflow_10755470 ();
  reverse_add_10755470_to_18211171 ();
  exists_intro
    (fun (i:nat) -> i < length [0; 7; 4; 5; 5; 7; 0; 1] /\
      2 * trace_sum_at [0; 7; 4; 5; 5; 7; 0; 1] i +
          trace_carry_at [0; 7; 4; 5; 5; 7; 0; 1] i +
          trace_carry_at [0; 7; 4; 5; 5; 7; 0; 1]
            (length [0; 7; 4; 5; 5; 7; 0; 1] - 1 - i) >=
        10 + 10 *
          (trace_carry_at [0; 7; 4; 5; 5; 7; 0; 1] (i + 1) +
           trace_carry_at [0; 7; 4; 5; 5; 7; 0; 1]
             (length [0; 7; 4; 5; 5; 7; 0; 1] - i)))
    1;
  no_overflow_outer_sum_1_to_4_cell_implies_next_witness
    [0; 7; 4; 5; 5; 7; 0; 1];
  ()

// The same no-overflow low-sum rule discharges the following boundary at
// 18211171 -> 35322452 using the internal cell i=1.
let local_profile_witness_35322452 () : Lemma (
    trace_local_profile_complement_witness
      [2; 5; 4; 2; 2; 3; 5; 3]) =
  trace_profile_shape_18211171 ();
  trace_profile_facts_18211171 ();
  trace_no_overflow_18211171 ();
  reverse_add_18211171_to_35322452 ();
  exists_intro
    (fun (i:nat) -> i < length [1; 7; 1; 1; 1; 2; 8; 1] /\
      2 * trace_sum_at [1; 7; 1; 1; 1; 2; 8; 1] i +
          trace_carry_at [1; 7; 1; 1; 1; 2; 8; 1] i +
          trace_carry_at [1; 7; 1; 1; 1; 2; 8; 1]
            (length [1; 7; 1; 1; 1; 2; 8; 1] - 1 - i) >=
        10 + 10 *
          (trace_carry_at [1; 7; 1; 1; 1; 2; 8; 1] (i + 1) +
           trace_carry_at [1; 7; 1; 1; 1; 2; 8; 1]
             (length [1; 7; 1; 1; 1; 2; 8; 1] - i)))
    1;
  no_overflow_outer_sum_1_to_4_cell_implies_next_witness
    [1; 7; 1; 1; 1; 2; 8; 1];
  ()

// The outer-sum-5 carry-1 jump rule discharges the next boundary at
// 35322452 -> 60744805 using the i=2 jump in the next trace.
let local_profile_witness_60744805 () : Lemma (
    trace_local_profile_complement_witness
      [5; 0; 8; 4; 4; 7; 0; 6]) =
  ReverseAddBoundary.local_profile_witness_60744805 ();
  ()

// The overflow internal-cell rule discharges 60744805 -> 111589511.
let local_profile_witness_111589511 () : Lemma (
    trace_local_profile_complement_witness
      [1; 1; 5; 9; 8; 5; 1; 1; 1]) =
  ReverseAddBoundary.local_profile_witness_111589511 ();
  ()

// The no-overflow low-sum rule discharges 111589511 -> 227574622.
let local_profile_witness_227574622 () : Lemma (
    trace_local_profile_complement_witness
      [2; 2; 6; 4; 7; 5; 7; 2; 2]) =
  ReverseAddBoundary.local_profile_witness_227574622 ();
  ()

// The no-overflow low-sum rule discharges 227574622 -> 454050344.
let local_profile_witness_454050344 () : Lemma (
    trace_local_profile_complement_witness
      [4; 4; 3; 0; 5; 0; 4; 5; 4]) =
  ReverseAddBoundary.local_profile_witness_454050344 ();
  ()

// The no-overflow outer-sum rule discharges 454050344 -> 897100798.
let local_profile_witness_897100798 () : Lemma (
    trace_local_profile_complement_witness
      [8; 9; 7; 0; 0; 1; 7; 9; 8]) =
  ReverseAddBoundary.local_profile_witness_897100798 ();
  ()

// The overflow internal-cell rule discharges 897100798 -> 1794102596.
let local_profile_witness_1794102596 () : Lemma (
    trace_local_profile_complement_witness
      [6; 9; 5; 2; 0; 1; 4; 9; 7; 1]) =
  ReverseAddBoundary.local_profile_witness_1794102596 ();
  ()

// The no-overflow outer-sum rule discharges 1794102596 -> 8746117567.
let local_profile_witness_8746117567 () : Lemma (
    trace_local_profile_complement_witness
      [7; 6; 5; 7; 1; 1; 6; 4; 7; 8]) =
  ReverseAddBoundary.local_profile_witness_8746117567 ();
  ()

// The overflow internal-cell rule discharges 8746117567 -> 16403234045.
let local_profile_witness_16403234045 () : Lemma (
    trace_local_profile_complement_witness
      [5; 4; 0; 4; 3; 2; 3; 0; 4; 6; 1]) =
  ReverseAddBoundary.local_profile_witness_16403234045 ();
  ()

// The no-overflow outer-sum rule discharges 16403234045 -> 70446464506.
let local_profile_witness_70446464506 () : Lemma (
    trace_local_profile_complement_witness
      [6; 0; 5; 4; 6; 4; 6; 4; 4; 0; 7]) =
  ReverseAddBoundary.local_profile_witness_70446464506 ();
  ()

// The overflow internal-cell rule discharges 70446464506 -> 130992928913.
let local_profile_witness_130992928913 () : Lemma (
    trace_local_profile_complement_witness
      [3; 1; 9; 8; 2; 9; 2; 9; 9; 0; 3; 1]) =
  ReverseAddBoundary.local_profile_witness_130992928913 ();
  ()

// The no-overflow low-sum rule discharges 130992928913 -> 450822227944.
let local_profile_witness_450822227944 () : Lemma (
    trace_local_profile_complement_witness
      [4; 4; 9; 7; 2; 2; 2; 2; 8; 0; 5; 4]) =
  ReverseAddBoundary.local_profile_witness_450822227944 ();
  ()

// The no-overflow outer-sum rule discharges 450822227944 -> 900544455998.
let local_profile_witness_900544455998 () : Lemma (
    trace_local_profile_complement_witness
      [8; 9; 9; 5; 5; 4; 4; 4; 5; 0; 0; 9]) =
  ReverseAddBoundary.local_profile_witness_900544455998 ();
  ()

// The overflow internal-cell rule discharges 900544455998 -> 1800098901007.
let local_profile_witness_1800098901007 () : Lemma (
    trace_local_profile_complement_witness
      [7; 0; 0; 1; 0; 9; 8; 9; 0; 0; 0; 8; 1]) =
  ReverseAddBoundary.local_profile_witness_1800098901007 ();
  ()

// The no-overflow outer-sum rule discharges 1800098901007 -> 8801197801088.
let local_profile_witness_8801197801088 () : Lemma (
    trace_local_profile_complement_witness
      [8; 8; 0; 1; 0; 8; 7; 9; 1; 1; 0; 8; 8]) =
  ReverseAddBoundary.local_profile_witness_8801197801088 ();
  ()

// The overflow internal-cell rule discharges 8801197801088 -> 17602285712176.
let local_profile_witness_17602285712176 () : Lemma (
    trace_local_profile_complement_witness
      [6; 7; 1; 2; 1; 7; 5; 8; 2; 2; 0; 6; 7; 1]) =
  ReverseAddBoundary.local_profile_witness_17602285712176 ();
  ()

// The no-overflow outer-sum rule discharges 17602285712176 -> 84724043932847.
let local_profile_witness_84724043932847 () : Lemma (
    trace_local_profile_complement_witness
      [7; 4; 8; 2; 3; 9; 3; 4; 0; 4; 2; 7; 4; 8]) =
  ReverseAddBoundary.local_profile_witness_84724043932847 ();
  ()

// The overflow internal-cell rule discharges 84724043932847 -> 159547977975595.
let local_profile_witness_159547977975595 () : Lemma (
    trace_local_profile_complement_witness
      [5; 9; 5; 5; 7; 9; 7; 7; 9; 7; 4; 5; 9; 5; 1]) =
  ReverseAddBoundary.local_profile_witness_159547977975595 ();
  ()

// The no-overflow outer-sum rule discharges 159547977975595 -> 755127757721546.
let local_profile_witness_755127757721546 () : Lemma (
    trace_local_profile_complement_witness
      [6; 4; 5; 1; 2; 7; 7; 5; 7; 7; 2; 1; 5; 5; 7]) =
  ReverseAddBoundary.local_profile_witness_755127757721546 ();
  ()

// The overflow internal-cell rule discharges 755127757721546 -> 1400255515443103.
let local_profile_witness_1400255515443103 () : Lemma (
    trace_local_profile_complement_witness
      [3; 0; 1; 3; 4; 4; 5; 1; 5; 5; 5; 2; 0; 0; 4; 1]) =
  ReverseAddBoundary.local_profile_witness_1400255515443103 ();
  ()

let finite_196_candidate_prefix () : Lemma (
    ~ (trace_palindrome_candidate (iterate 0 digits_196)) /\
    ~ (trace_palindrome_candidate (iterate 1 digits_196)) /\
    ~ (trace_palindrome_candidate (iterate 2 digits_196)) /\
    ~ (trace_palindrome_candidate (iterate 3 digits_196)) /\
    ~ (trace_palindrome_candidate (iterate 4 digits_196)) /\
    ~ (trace_palindrome_candidate (iterate 5 digits_196)) /\
    ~ (trace_palindrome_candidate (iterate 6 digits_196))) =
  assert (iterate 0 digits_196 == digits_196);
  not_candidate_196 ();
  example_196 ();
  assert (iterate 1 digits_196 == digits_887);
  not_candidate_887 ();
  reaches_196_1675 ();
  not_candidate_1675 ();
  reaches_196_7436 ();
  not_candidate_7436 ();
  reaches_196_13783 ();
  not_candidate_13783 ();
  reaches_196_52514 ();
  not_candidate_52514 ();
  reaches_196_94039 ();
  not_candidate_94039 ();
  ()

let trace_not_candidate_implies_witness (xs:numeral 10)
  : Lemma (requires (
      xs <> [] /\
      ~(trace_palindrome_candidate xs)))
    (ensures (trace_candidate_complement_witness xs)) =
  reverse_trace_output_length_case xs;
  rev_length xs;
  trace_output_length_carry_link xs (rev xs) 0;
  eliminate
    (length (trace_digits xs) == length xs /\
     nth (trace_carries xs) (length xs) == Some 0) \/
    (length (trace_digits xs) == length xs + 1 /\
     nth (trace_carries xs) (length xs) == Some 1)
  with (
    assert (~ (forall (i:nat). i < length xs ==>
      trace_sum_at xs i < 10));
    assert (~ (forall (i:nat). ~(
      i < length xs /\ trace_sum_at xs i >= 10)));
    not_forall_implies_exists #nat
      #(fun (i:nat) -> i < length xs /\ trace_sum_at xs i >= 10)
      ();
    eliminate exists (i:nat).
      i < length xs /\ trace_sum_at xs i >= 10
    with (
      assert (trace_candidate_complement_witness xs);
      ()))
  and (
    if trace_sum_at xs 0 = 1 then begin
      trace_overflow_outer_sum_one_impossible xs;
      assert False
    end else if trace_sum_at xs 0 = 11 then begin
      assert (~ (forall (i:nat). 0 < i /\ i <= length xs ==>
        ~(trace_sum_at xs i >= trace_sum_at xs (i - 1) + 12 \/
          trace_sum_at xs (i - 1) >= trace_sum_at xs i + 12)));
      assert (~ (forall (i:nat). ~(
        0 < i /\ i <= length xs /\
        (trace_sum_at xs i >= trace_sum_at xs (i - 1) + 12 \/
         trace_sum_at xs (i - 1) >= trace_sum_at xs i + 12))));
      not_forall_implies_exists #nat
        #(fun (i:nat) -> 0 < i /\ i <= length xs /\
          (trace_sum_at xs i >= trace_sum_at xs (i - 1) + 12 \/
           trace_sum_at xs (i - 1) >= trace_sum_at xs i + 12))
        ();
      eliminate exists (i:nat).
        0 < i /\ i <= length xs /\
        (trace_sum_at xs i >= trace_sum_at xs (i - 1) + 12 \/
         trace_sum_at xs (i - 1) >= trace_sum_at xs i + 12)
      with (
        assert (trace_candidate_complement_witness xs);
        ())
    end else begin
      assert (trace_sum_at xs 0 <> 1);
      assert (trace_sum_at xs 0 <> 11);
      assert (trace_candidate_complement_witness xs);
      ()
    end)

let trace_candidate_witness_implies_obstruction (xs:numeral 10)
  : Lemma (requires (
      xs <> [] /\
      trace_candidate_complement_witness xs))
    (ensures (trace_palindrome_obstruction_exists xs)) =
  eliminate
    (length (trace_digits xs) == length xs /\
     nth (trace_carries xs) (length xs) == Some 0 /\
     exists (i:nat). i < length xs /\ trace_sum_at xs i >= 10) \/
    (length (trace_digits xs) == length xs + 1 /\
     nth (trace_carries xs) (length xs) == Some 1 /\
     (trace_sum_at xs 0 <> 11 \/
      exists (i:nat). 0 < i /\ i <= length xs /\
        (trace_sum_at xs i >= trace_sum_at xs (i - 1) + 12 \/
         trace_sum_at xs (i - 1) >= trace_sum_at xs i + 12)))
  with (
    eliminate exists (i:nat).
      i < length xs /\ trace_sum_at xs i >= 10
    with (
      trace_no_overflow_high_sum_exists xs i;
      ()))
  and (
    if trace_sum_at xs 0 = 1 then begin
      trace_overflow_outer_sum_one_impossible xs;
      assert False
    end else if trace_sum_at xs 0 = 11 then begin
      assert (~ (forall (i:nat). 0 < i /\ i <= length xs ==>
        ~(trace_sum_at xs i >= trace_sum_at xs (i - 1) + 12 \/
          trace_sum_at xs (i - 1) >= trace_sum_at xs i + 12)));
      assert (~ (forall (i:nat). ~(
        0 < i /\ i <= length xs /\
        (trace_sum_at xs i >= trace_sum_at xs (i - 1) + 12 \/
         trace_sum_at xs (i - 1) >= trace_sum_at xs i + 12))));
      not_forall_implies_exists #nat
        #(fun (i:nat) -> 0 < i /\ i <= length xs /\
          (trace_sum_at xs i >= trace_sum_at xs (i - 1) + 12 \/
           trace_sum_at xs (i - 1) >= trace_sum_at xs i + 12))
        ();
      eliminate exists (i:nat).
        0 < i /\ i <= length xs /\
        (trace_sum_at xs i >= trace_sum_at xs (i - 1) + 12 \/
         trace_sum_at xs (i - 1) >= trace_sum_at xs i + 12)
      with (
        trace_overflow_sum_jump_obstruction_at xs i;
        exists_intro
          (fun (i:nat) -> trace_palindrome_obstruction_at xs i) i;
        ())
    end else begin
      assert (trace_sum_at xs 0 <> 1);
      assert (trace_sum_at xs 0 <> 11);
      trace_overflow_outer_sum_not_1_or_11_obstruction_at xs;
      exists_intro
        (fun (i:nat) -> trace_palindrome_obstruction_at xs i) 0;
      ()
    end)

let rec iterate_candidate_witness_from_step
  (xs:numeral 10)
  (preserved:(y:numeral 10 -> Lemma (
      requires (trace_candidate_complement_witness y))
      (ensures (trace_candidate_complement_witness (reverse_add y)))))
  (k:nat)
  : Lemma (requires (trace_candidate_complement_witness xs))
    (ensures (trace_candidate_complement_witness (iterate k xs)))
    (decreases k) =
  if k = 0 then
    ()
  else if k > 0 then
    let k' : nat = k - 1 in
    iterate_candidate_witness_from_step xs preserved k';
    iterate_succ #10 k' xs;
    preserved (iterate k' xs);
    ()
  else
    assert False

let all_iterate_candidate_witness_from_step
  (xs:numeral 10)
  (preserved:(y:numeral 10 -> Lemma (
      requires (trace_candidate_complement_witness y))
      (ensures (trace_candidate_complement_witness (reverse_add y)))))
  : Lemma (requires (
      canonical xs /\
      xs <> [] /\
      trace_candidate_complement_witness xs))
    (ensures (forall (k:nat).
      trace_candidate_complement_witness (iterate k xs))) =
  introduce forall (k:nat).
    trace_candidate_complement_witness (iterate k xs)
  with (
    iterate_candidate_witness_from_step xs preserved k)

let all_iterate_candidate_witnesses_exclude_palindrome
  (xs:numeral 10)
  : Lemma (requires (
      canonical xs /\
      xs <> [] /\
      (forall k. trace_candidate_complement_witness (iterate k xs))))
    (ensures (forall (k:nat).
      ~ (palindrome #10 (iterate (k + 1) xs)))) =
  introduce forall (k:nat).
    ~ (palindrome #10 (iterate (k + 1) xs))
  with (
    introduce (palindrome #10 (iterate (k + 1) xs)) ==> False
    with (
      iterate_canonical #10 k xs;
      iterate_nonempty #10 k xs;
      trace_digits_equals_reverse_add (iterate k xs);
      assert (trace_candidate_complement_witness (iterate k xs));
      trace_candidate_witness_implies_obstruction (iterate k xs);
      eliminate exists (i:nat).
        trace_palindrome_obstruction_at (iterate k xs) i
      with (
        trace_palindrome_obstruction_at_sound (iterate k xs) i;
        iterate_next_obstruction_excludes_palindrome k xs)))

let all_iterate_candidate_witness_step_excludes_palindrome
  (xs:numeral 10)
  (preserved:(y:numeral 10 -> Lemma (
      requires (trace_candidate_complement_witness y))
      (ensures (trace_candidate_complement_witness (reverse_add y)))))
  : Lemma (requires (
      canonical xs /\
      xs <> [] /\
      trace_candidate_complement_witness xs))
    (ensures (forall (k:nat).
      ~ (palindrome #10 (iterate (k + 1) xs)))) =
  all_iterate_candidate_witness_from_step xs preserved;
  all_iterate_candidate_witnesses_exclude_palindrome xs

let trace_candidate_witness_implies_not_candidate (xs:numeral 10)
  : Lemma (requires (
      xs <> [] /\
      trace_candidate_complement_witness xs))
    (ensures (~ (trace_palindrome_candidate xs))) =
  eliminate
    (length (trace_digits xs) == length xs /\
     nth (trace_carries xs) (length xs) == Some 0 /\
     exists (i:nat). i < length xs /\ trace_sum_at xs i >= 10) \/
    (length (trace_digits xs) == length xs + 1 /\
     nth (trace_carries xs) (length xs) == Some 1 /\
     (trace_sum_at xs 0 <> 11 \/
      exists (i:nat). 0 < i /\ i <= length xs /\
        (trace_sum_at xs i >= trace_sum_at xs (i - 1) + 12 \/
         trace_sum_at xs (i - 1) >= trace_sum_at xs i + 12)))
  with (
    eliminate exists (i:nat).
      i < length xs /\ trace_sum_at xs i >= 10
    with (
      trace_no_overflow_high_sum_not_candidate xs i;
      ()))
  and (
    if trace_sum_at xs 0 = 1 then begin
      trace_overflow_outer_sum_one_impossible xs;
      assert False
    end else if trace_sum_at xs 0 = 11 then begin
      eliminate exists (i:nat).
        0 < i /\ i <= length xs /\
        (trace_sum_at xs i >= trace_sum_at xs (i - 1) + 12 \/
         trace_sum_at xs (i - 1) >= trace_sum_at xs i + 12)
      with (
        trace_overflow_sum_jump_not_candidate xs i;
        ())
    end else begin
      assert (trace_sum_at xs 0 <> 1);
      assert (trace_sum_at xs 0 <> 11);
      trace_overflow_outer_sum_not_candidate xs
    end)

let finite_196_candidate_witness_prefix () : Lemma (
    trace_candidate_complement_witness (iterate 0 digits_196) /\
    trace_candidate_complement_witness (iterate 1 digits_196) /\
    trace_candidate_complement_witness (iterate 2 digits_196) /\
    trace_candidate_complement_witness (iterate 3 digits_196) /\
    trace_candidate_complement_witness (iterate 4 digits_196) /\
    trace_candidate_complement_witness (iterate 5 digits_196) /\
    trace_candidate_complement_witness (iterate 6 digits_196)) =
  digits_196_canonical_nonempty ();
  finite_196_candidate_prefix ();
  iterate_nonempty #10 0 digits_196;
  trace_not_candidate_implies_witness (iterate 0 digits_196);
  trace_candidate_witness_implies_not_candidate (iterate 0 digits_196);
  iterate_nonempty #10 1 digits_196;
  trace_not_candidate_implies_witness (iterate 1 digits_196);
  trace_candidate_witness_implies_not_candidate (iterate 1 digits_196);
  iterate_nonempty #10 2 digits_196;
  trace_not_candidate_implies_witness (iterate 2 digits_196);
  trace_candidate_witness_implies_not_candidate (iterate 2 digits_196);
  iterate_nonempty #10 3 digits_196;
  trace_not_candidate_implies_witness (iterate 3 digits_196);
  trace_candidate_witness_implies_not_candidate (iterate 3 digits_196);
  iterate_nonempty #10 4 digits_196;
  trace_not_candidate_implies_witness (iterate 4 digits_196);
  trace_candidate_witness_implies_not_candidate (iterate 4 digits_196);
  iterate_nonempty #10 5 digits_196;
  trace_not_candidate_implies_witness (iterate 5 digits_196);
  trace_candidate_witness_implies_not_candidate (iterate 5 digits_196);
  iterate_nonempty #10 6 digits_196;
  trace_not_candidate_implies_witness (iterate 6 digits_196);
  trace_candidate_witness_implies_not_candidate (iterate 6 digits_196)

// The 196-specific endgame starts from one concrete witness.  The only
// remaining obligation is the genuinely infinite one-step preservation
// proof supplied by the caller below.
let candidate_witness_196 () : Lemma (
    trace_candidate_complement_witness digits_196) =
  digits_196_canonical_nonempty ();
  not_candidate_196 ();
  trace_not_candidate_implies_witness digits_196;
  ()

let conditional_196_no_palindrome
  (preserved:(y:numeral 10 -> Lemma (
      requires (trace_candidate_complement_witness y))
      (ensures (trace_candidate_complement_witness (reverse_add y)))))
  : Lemma (ensures (forall (k:nat).
      ~ (palindrome #10 (iterate (k + 1) digits_196)))) =
  digits_196_canonical_nonempty ();
  candidate_witness_196 ();
  all_iterate_candidate_witness_step_excludes_palindrome
    digits_196 preserved

let rec iterate_local_profile_from_step
  (xs:numeral 10)
  (preserved:(y:numeral 10 -> Lemma (
      requires (~(trace_local_palindrome_profile y)))
      (ensures (~(trace_local_palindrome_profile (reverse_add y))))))
  (k:nat)
  : Lemma (requires (~(trace_local_palindrome_profile xs)))
    (ensures (~(trace_local_palindrome_profile (iterate k xs))))
    (decreases k) =
  if k = 0 then
    ()
  else
    let k' : nat = k - 1 in
    iterate_local_profile_from_step xs preserved k';
    iterate_succ #10 k' xs;
    preserved (iterate k' xs);
    ()

let rec iterate_local_profile_witness_from_step
  (xs:numeral 10)
  (preserved:(y:numeral 10 -> Lemma (
      requires (trace_local_profile_complement_witness y))
      (ensures (trace_local_profile_complement_witness (reverse_add y)))))
  (k:nat)
  : Lemma (requires (trace_local_profile_complement_witness xs))
    (ensures (trace_local_profile_complement_witness (iterate k xs)))
    (decreases k) =
  if k = 0 then
    ()
  else
    let k' : nat = k - 1 in
    iterate_local_profile_witness_from_step xs preserved k';
    iterate_succ #10 k' xs;
    preserved (iterate k' xs);
    ()

let conditional_196_local_profile_no_palindrome
  (preserved:(y:numeral 10 -> Lemma (
      requires (~(trace_local_palindrome_profile y)))
      (ensures (~(trace_local_palindrome_profile (reverse_add y))))))
  : Lemma (ensures (forall (k:nat).
      ~ (palindrome #10 (iterate (k + 1) digits_196)))) =
  digits_196_canonical_nonempty ();
  local_profile_196_is_false ();
  introduce forall (k:nat).
    ~ (palindrome #10 (iterate (k + 1) digits_196))
  with (
    introduce (palindrome #10 (iterate (k + 1) digits_196)) ==> False
    with (
      iterate_local_profile_from_step digits_196 preserved k;
      iterate_canonical #10 k digits_196;
      iterate_nonempty #10 k digits_196;
      iterate_succ #10 k digits_196;
      reverse_add_local_profile_excludes_palindrome
        (iterate k digits_196)))

let conditional_196_local_profile_witness_no_palindrome
  (preserved:(y:numeral 10 -> Lemma (
      requires (trace_local_profile_complement_witness y))
      (ensures (trace_local_profile_complement_witness (reverse_add y)))))
  : Lemma (ensures (forall (k:nat).
      ~ (palindrome #10 (iterate (k + 1) digits_196)))) =
  digits_196_canonical_nonempty ();
  local_profile_196_is_false ();
  trace_not_local_profile_implies_witness digits_196;
  introduce forall (k:nat).
    ~ (palindrome #10 (iterate (k + 1) digits_196))
  with (
    introduce (palindrome #10 (iterate (k + 1) digits_196)) ==> False
    with (
      iterate_local_profile_witness_from_step digits_196 preserved k;
      iterate_canonical #10 k digits_196;
      iterate_nonempty #10 k digits_196;
      local_profile_witness_implies_not_local_profile
        (iterate k digits_196);
      iterate_succ #10 k digits_196;
      reverse_add_local_profile_excludes_palindrome
        (iterate k digits_196)))
