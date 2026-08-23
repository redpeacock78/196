module ReverseAddOverflowProfile

open ReverseAdd
open ReverseAddCarry
open ReverseAddWitness
open ReverseAddHighSum
open FStar.Classical
open FStar.List.Tot

// Conversely, the overflow sum/carry relation reconstructs mirrored output
// digits from the two local cell equations.
let mirrored_overflow_cells_force_digit_symmetry
  (n:nat)
  (s:nat -> nat)
  (d:nat -> digit 10)
  (c:nat -> carry)
  : Lemma (requires (
      (forall i. i <= n ==> (
        d i + 10 * c (i + 1) == s i + c i)) /\
      (forall i. i <= n ==> (
        s i + c i + 10 * c (n - i + 1) ==
          s (n - i) + c (n - i) + 10 * c (i + 1)))))
    (ensures (forall i. i <= n ==>
      d i == d (n - i))) =
  introduce forall (i:nat). i <= n ==> d i == d (n - i)
  with (
    introduce _ ==> _
    with (
      let j : nat = n - i in
      assert (j <= n);
      assert (d i + 10 * c (i + 1) == s i + c i);
      assert (d j + 10 * c (j + 1) == s j + c j);
      assert (j + 1 == n - i + 1);
      assert (s i + c i + 10 * c (j + 1) ==
        s j + c j + 10 * c (i + 1));
      assert (d i == d j);
      ()));
  ()

let reverse_trace_overflow_relation_implies_digit_symmetry
  (xs:numeral 10) : Lemma (requires (
      xs <> [] /\
      length (trace_digits xs) == length xs + 1 /\
      nth (trace_carries xs) (length xs) == Some 1 /\
      (forall i. i <= length xs ==>
        trace_sum_at xs i + overflow_trace_carry_at xs i +
            10 * overflow_trace_carry_at xs (length xs - i + 1) ==
          trace_sum_at xs (length xs - i) +
            overflow_trace_carry_at xs (length xs - i) +
            10 * overflow_trace_carry_at xs (i + 1))))
    (ensures (forall i. i <= length xs ==>
      trace_digit_at xs i == trace_digit_at xs (length xs - i))) =
  let n : nat = length xs in
  introduce forall (i:nat). i <= n ==>
    trace_digit_at xs i == trace_digit_at xs (n - i)
  with (
    introduce (i <= n) ==> _
    with (
      let j : nat = n - i in
      assert (j <= n);
      overflow_trace_equation_at xs i;
      overflow_trace_equation_at xs j;
      assert (j + 1 == n - i + 1);
      assert (trace_sum_at xs i + overflow_trace_carry_at xs i +
        10 * overflow_trace_carry_at xs (j + 1) ==
        trace_sum_at xs j + overflow_trace_carry_at xs j +
        10 * overflow_trace_carry_at xs (i + 1));
      assert (trace_digit_at xs i == trace_digit_at xs j);
      ()))

let trace_local_palindrome_profile (xs:numeral 10) : prop =
  (length (trace_digits xs) == length xs /\
   nth (trace_carries xs) (length xs) == Some 0 /\
   (forall i. i < length xs ==>
     trace_sum_at xs i < 10)) \/
  (length (trace_digits xs) == length xs + 1 /\
   nth (trace_carries xs) (length xs) == Some 1 /\
   (forall i. i <= length xs ==>
     trace_sum_at xs i + overflow_trace_carry_at xs i +
         10 * overflow_trace_carry_at xs (length xs - i + 1) ==
       trace_sum_at xs (length xs - i) +
         overflow_trace_carry_at xs (length xs - i) +
         10 * overflow_trace_carry_at xs (i + 1)))

let trace_local_profile_relation (xs:numeral 10) (i:nat) : prop =
  if i <= length xs then
    trace_sum_at xs i + overflow_trace_carry_at xs i +
        10 * overflow_trace_carry_at xs (length xs - i + 1) ==
      trace_sum_at xs (length xs - i) +
        overflow_trace_carry_at xs (length xs - i) +
        10 * overflow_trace_carry_at xs (i + 1)
  else
    False

// The complement has a concrete witness in either output-length branch.
let trace_local_profile_complement_witness (xs:numeral 10) : prop =
  (length (trace_digits xs) == length xs /\
   nth (trace_carries xs) (length xs) == Some 0 /\
   exists (i:nat). i < length xs /\ trace_sum_at xs i >= 10) \/
  (length (trace_digits xs) == length xs + 1 /\
   nth (trace_carries xs) (length xs) == Some 1 /\
   exists (i:nat). i <= length xs /\
     ~(trace_local_profile_relation xs i))

let trace_not_local_profile_implies_witness (xs:numeral 10)
  : Lemma (requires (xs <> [] /\
      ~(trace_local_palindrome_profile xs)))
    (ensures (trace_local_profile_complement_witness xs)) =
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
      exists_intro
        (fun (i:nat) -> i < length xs /\ trace_sum_at xs i >= 10) i;
      ()))
  and (
    assert (~ (forall (i:nat). i <= length xs ==>
      trace_local_profile_relation xs i));
    assert (~ (forall (i:nat). ~(
      i <= length xs /\ ~(trace_local_profile_relation xs i))));
    not_forall_implies_exists #nat
      #(fun (i:nat) -> i <= length xs /\
        ~(trace_local_profile_relation xs i))
      ();
    eliminate exists (i:nat).
      i <= length xs /\ ~(trace_local_profile_relation xs i)
    with (
      exists_intro
        (fun (i:nat) -> i <= length xs /\
          ~(trace_local_profile_relation xs i)) i;
      ()))

let no_overflow_profile_witness_implies_not
  (xs:numeral 10) (i:nat)
  : Lemma (requires (
      length (trace_digits xs) == length xs /\
      nth (trace_carries xs) (length xs) == Some 0 /\
      i < length xs /\ trace_sum_at xs i >= 10))
    (ensures (~(trace_local_palindrome_profile xs))) =
  introduce (trace_local_palindrome_profile xs) ==> False
  with (
    eliminate
      (length (trace_digits xs) == length xs /\
       nth (trace_carries xs) (length xs) == Some 0 /\
       (forall j. j < length xs ==> trace_sum_at xs j < 10)) \/
      (length (trace_digits xs) == length xs + 1 /\
       nth (trace_carries xs) (length xs) == Some 1 /\
       (forall j. j <= length xs ==>
         trace_local_profile_relation xs j))
    with (
      assert (trace_sum_at xs i < 10);
      assert False)
    and (
      assert False))

let overflow_profile_witness_implies_not
  (xs:numeral 10) (i:nat)
  : Lemma (requires (
      length (trace_digits xs) == length xs + 1 /\
      nth (trace_carries xs) (length xs) == Some 1 /\
      i <= length xs /\ ~(trace_local_profile_relation xs i)))
    (ensures (~(trace_local_palindrome_profile xs))) =
  introduce (trace_local_palindrome_profile xs) ==> False
  with (
    eliminate
      (length (trace_digits xs) == length xs /\
       nth (trace_carries xs) (length xs) == Some 0 /\
       (forall j. j < length xs ==> trace_sum_at xs j < 10)) \/
      (length (trace_digits xs) == length xs + 1 /\
       nth (trace_carries xs) (length xs) == Some 1 /\
       (forall j. j <= length xs ==>
         trace_local_profile_relation xs j))
    with (
      assert False)
    and (
      assert (trace_local_profile_relation xs i);
      assert False))

let local_profile_witness_implies_not_local_profile
  (xs:numeral 10)
  : Lemma (requires (xs <> [] /\
      trace_local_profile_complement_witness xs))
    (ensures (~(trace_local_palindrome_profile xs))) =
  eliminate
    (length (trace_digits xs) == length xs /\
     nth (trace_carries xs) (length xs) == Some 0 /\
     exists (i:nat). i < length xs /\ trace_sum_at xs i >= 10) \/
    (length (trace_digits xs) == length xs + 1 /\
     nth (trace_carries xs) (length xs) == Some 1 /\
     exists (i:nat). i <= length xs /\
       ~(trace_local_profile_relation xs i))
  with (
    eliminate exists (i:nat).
      i < length xs /\ trace_sum_at xs i >= 10
    with (
      no_overflow_profile_witness_implies_not xs i))
  and (
    eliminate exists (i:nat).
      i <= length xs /\ ~(trace_local_profile_relation xs i)
    with (
      overflow_profile_witness_implies_not xs i))

// In a no-overflow step, the next trace's outer sum is determined by the
// current outer sum and the two carry cells touching the boundary.
let no_overflow_trace_outer_sum_equation (xs:numeral 10)
  : Lemma (requires (
      xs <> [] /\
      length (trace_digits xs) == length xs /\
      nth (trace_carries xs) (length xs) == Some 0))
    (ensures (
      trace_sum_at (trace_digits xs) 0 +
          10 * trace_carry_at xs 1 ==
        2 * trace_sum_at xs 0 +
          trace_carry_at xs (length xs - 1))) =
  let n : nat = length xs in
  assert (n > 0);
  assert (n - 1 < n);
  trace_equation_at xs 0;
  trace_equation_at xs (n - 1);
  trace_sum_symmetric_at xs 0;
  rev_length (trace_digits xs);
  nth_rev (trace_digits xs) 0;
  assert (trace_digit_at xs 0 == digit_at (trace_digits xs) 0);
  assert (trace_digit_at xs (n - 1) ==
    digit_at (trace_digits xs) (n - 1));
  assert (trace_sum_at (trace_digits xs) 0 ==
    trace_digit_at xs 0 + trace_digit_at xs (n - 1));
  assert (trace_digit_at xs 0 +
    10 * trace_carry_at xs 1 == trace_sum_at xs 0);
  assert (trace_digit_at xs (n - 1) ==
    trace_sum_at xs (n - 1) + trace_carry_at xs (n - 1));
  assert (trace_sum_at xs (n - 1) == trace_sum_at xs 0);
  assert (trace_sum_at (trace_digits xs) 0 +
    10 * trace_carry_at xs 1 ==
    2 * trace_sum_at xs 0 + trace_carry_at xs (n - 1));
  ()

let overflow_profile_relation_at_zero_implies_sum_le_11
  (xs:numeral 10)
  : Lemma (requires (
      xs <> [] /\
      length (trace_digits xs) == length xs + 1 /\
      nth (trace_carries xs) (length xs) == Some 1 /\
      trace_local_profile_relation xs 0))
    (ensures (
      trace_sum_at xs 0 <= 11 /\
      trace_sum_at xs 0 ==
        1 + 10 * overflow_trace_carry_at xs 1)) =
  let n : nat = length xs in
  assert (n > 0);
  rev_length xs;
  nth_length_none xs;
  nth_length_none (rev xs);
  assert (trace_sum_at xs n == 0);
  assert (overflow_trace_carry_at xs n == 1);
  assert (overflow_trace_carry_at xs (n + 1) == 0);
  assert (trace_local_profile_relation xs 0);
  assert (trace_sum_at xs 0 ==
    1 + 10 * overflow_trace_carry_at xs 1);
  assert (overflow_trace_carry_at xs 1 <= 1);
  assert (trace_sum_at xs 0 <= 11);
  ()

let overflow_profile_relation_at_zero_is_1_or_11
  (xs:numeral 10)
  : Lemma (requires (
      xs <> [] /\
      length (trace_digits xs) == length xs + 1 /\
      nth (trace_carries xs) (length xs) == Some 1 /\
      trace_local_profile_relation xs 0))
    (ensures (trace_sum_at xs 0 == 1 \/ trace_sum_at xs 0 == 11)) =
  overflow_profile_relation_at_zero_implies_sum_le_11 xs;
  assert (trace_sum_at xs 0 ==
    1 + 10 * overflow_trace_carry_at xs 1);
  if overflow_trace_carry_at xs 1 == 0 then begin
    assert (trace_sum_at xs 0 == 1);
    ()
  end else begin
    assert (overflow_trace_carry_at xs 1 == 1);
    assert (trace_sum_at xs 0 == 11);
    ()
  end

let overflow_profile_relation_at_zero_impossible_above_11
  (xs:numeral 10)
  : Lemma (requires (
      xs <> [] /\
      length (trace_digits xs) == length xs + 1 /\
      nth (trace_carries xs) (length xs) == Some 1 /\
      trace_sum_at xs 0 >= 12))
    (ensures (~(trace_local_profile_relation xs 0))) =
  introduce (trace_local_profile_relation xs 0) ==> False
  with (
    overflow_profile_relation_at_zero_implies_sum_le_11 xs;
    assert False)

let overflow_profile_relation_at_zero_impossible_at_10
  (xs:numeral 10)
  : Lemma (requires (
      xs <> [] /\
      length (trace_digits xs) == length xs + 1 /\
      nth (trace_carries xs) (length xs) == Some 1 /\
      trace_sum_at xs 0 == 10))
    (ensures (~(trace_local_profile_relation xs 0))) =
  introduce (trace_local_profile_relation xs 0) ==> False
  with (
    overflow_profile_relation_at_zero_is_1_or_11 xs;
    assert False)

let overflow_profile_relation_at_zero_impossible_between_2_and_9
  (xs:numeral 10)
  : Lemma (requires (
      xs <> [] /\
      length (trace_digits xs) == length xs + 1 /\
      nth (trace_carries xs) (length xs) == Some 1 /\
      2 <= trace_sum_at xs 0 /\ trace_sum_at xs 0 <= 9))
    (ensures (~(trace_local_profile_relation xs 0))) =
  introduce (trace_local_profile_relation xs 0) ==> False
  with (
    overflow_profile_relation_at_zero_is_1_or_11 xs;
    assert False)

// A no-overflow input whose outer sum is 6..9 produces a next-step
// complement witness at the outer cell, regardless of the next final carry.
let no_overflow_outer_sum_6_to_9_implies_next_witness
  (xs:numeral 10)
  : Lemma (requires (
      canonical xs /\ xs <> [] /\
      length (trace_digits xs) == length xs /\
      nth (trace_carries xs) (length xs) == Some 0 /\
      6 <= trace_sum_at xs 0 /\ trace_sum_at xs 0 < 10))
    (ensures (trace_local_profile_complement_witness (reverse_add xs))) =
  trace_digits_equals_reverse_add xs;
  let n : nat = length xs in
  trace_carry_prefix_zero xs 0;
  trace_equation_at xs 0;
  assert (trace_carry_at xs 1 == 0);
  no_overflow_trace_outer_sum_equation xs;
  assert (trace_sum_at (reverse_add xs) 0 ==
    trace_sum_at (trace_digits xs) 0);
  assert (trace_sum_at (reverse_add xs) 0 >= 12);
  rev_length (reverse_add xs);
  reverse_trace_output_length_case (reverse_add xs);
  trace_output_length_carry_link
    (reverse_add xs) (rev (reverse_add xs)) 0;
  eliminate
    (length (trace_digits (reverse_add xs)) == length (reverse_add xs) /\
     nth (trace_carries (reverse_add xs))
       (length (reverse_add xs)) == Some 0) \/
    (length (trace_digits (reverse_add xs)) == length (reverse_add xs) + 1 /\
     nth (trace_carries (reverse_add xs))
       (length (reverse_add xs)) == Some 1)
  with (
    exists_intro
      (fun (i:nat) -> i < length (reverse_add xs) /\
        trace_sum_at (reverse_add xs) i >= 10)
      0;
    assert (trace_sum_at (reverse_add xs) 0 >= 10);
    ())

  and (
    overflow_profile_relation_at_zero_impossible_above_11
      (reverse_add xs);
    exists_intro
      (fun (i:nat) -> i <= length (reverse_add xs) /\
        ~(trace_local_profile_relation (reverse_add xs) i))
      0;
    ())

// With a low outer sum, a sufficiently high interior cell survives into the
// next no-overflow trace; an overflow next step already fails at cell 0.
let no_overflow_outer_sum_1_to_4_high_sum_15_implies_next_witness
  (xs:numeral 10)
  : Lemma (requires (
      canonical xs /\ xs <> [] /\
      length (trace_digits xs) == length xs /\
      nth (trace_carries xs) (length xs) == Some 0 /\
      1 <= trace_sum_at xs 0 /\ trace_sum_at xs 0 <= 4 /\
      exists (i:nat). i < length xs /\ trace_sum_at xs i >= 15))
    (ensures (trace_local_profile_complement_witness (reverse_add xs))) =
  trace_digits_equals_reverse_add xs;
  let n : nat = length xs in
  trace_carry_prefix_zero xs 0;
  trace_equation_at xs 0;
  assert (trace_carry_at xs 1 == 0);
  no_overflow_trace_outer_sum_equation xs;
  eliminate exists (i:nat).
    i < length xs /\ trace_sum_at xs i >= 15
  with (
    let j : nat = n - 1 - i in
    assert (j < n);
    trace_equation_at xs i;
    trace_equation_at xs j;
    trace_sum_symmetric_at xs i;
    assert (trace_carry_at xs (i + 1) == 1);
    assert (trace_carry_at xs (j + 1) == 1);
    rev_length (reverse_add xs);
    assert (i < length (reverse_add xs));
    nth_rev (reverse_add xs) i;
    assert (trace_digit_at xs i == digit_at (reverse_add xs) i);
    assert (trace_digit_at xs j == digit_at (reverse_add xs) j);
    assert (trace_sum_at (reverse_add xs) i ==
      trace_digit_at xs i + trace_digit_at xs j);
    assert (trace_sum_at (reverse_add xs) i >= 10);
    reverse_trace_output_length_case (reverse_add xs);
    trace_output_length_carry_link
      (reverse_add xs) (rev (reverse_add xs)) 0;
    eliminate
      (length (trace_digits (reverse_add xs)) == length (reverse_add xs) /\
       nth (trace_carries (reverse_add xs))
         (length (reverse_add xs)) == Some 0) \/
      (length (trace_digits (reverse_add xs)) == length (reverse_add xs) + 1 /\
       nth (trace_carries (reverse_add xs))
         (length (reverse_add xs)) == Some 1)
    with (
      exists_intro
        (fun (k:nat) -> k < length (reverse_add xs) /\
          trace_sum_at (reverse_add xs) k >= 10)
        i;
      ())
    and (
      assert (trace_sum_at (reverse_add xs) 0 >= 2);
      assert (trace_sum_at (reverse_add xs) 0 <= 9);
      overflow_profile_relation_at_zero_impossible_between_2_and_9
        (reverse_add xs);
      exists_intro
        (fun (k:nat) -> k <= length (reverse_add xs) /\
          ~(trace_local_profile_relation (reverse_add xs) k))
        0;
      ()))

let no_overflow_outer_sum_5_carry0_implies_next_witness
  (xs:numeral 10)
  : Lemma (requires (
      canonical xs /\ xs <> [] /\
      length (trace_digits xs) == length xs /\
      nth (trace_carries xs) (length xs) == Some 0 /\
      trace_sum_at xs 0 == 5 /\
      trace_carry_at xs (length xs - 1) == 0))
    (ensures (trace_local_profile_complement_witness (reverse_add xs))) =
  trace_digits_equals_reverse_add xs;
  let n : nat = length xs in
  trace_carry_prefix_zero xs 0;
  trace_equation_at xs 0;
  assert (trace_carry_at xs 1 == 0);
  no_overflow_trace_outer_sum_equation xs;
  assert (trace_sum_at (reverse_add xs) 0 ==
    trace_sum_at (trace_digits xs) 0);
  assert (trace_sum_at (reverse_add xs) 0 == 10);
  rev_length (reverse_add xs);
  reverse_trace_output_length_case (reverse_add xs);
  trace_output_length_carry_link
    (reverse_add xs) (rev (reverse_add xs)) 0;
  eliminate
    (length (trace_digits (reverse_add xs)) == length (reverse_add xs) /\
     nth (trace_carries (reverse_add xs))
       (length (reverse_add xs)) == Some 0) \/
    (length (trace_digits (reverse_add xs)) == length (reverse_add xs) + 1 /\
     nth (trace_carries (reverse_add xs))
       (length (reverse_add xs)) == Some 1)
  with (
    exists_intro
      (fun (i:nat) -> i < length (reverse_add xs) /\
        trace_sum_at (reverse_add xs) i >= 10)
      0;
    assert (trace_sum_at (reverse_add xs) 0 >= 10);
    ())
  and (
    overflow_profile_relation_at_zero_impossible_at_10
      (reverse_add xs);
    exists_intro
      (fun (i:nat) -> i <= length (reverse_add xs) /\
        ~(trace_local_profile_relation (reverse_add xs) i))
      0;
    ())

// The remaining outer-sum-5 boundary is discharged when the next trace has
// an indexed jump; its no-overflow branch already has outer sum 11.
let no_overflow_outer_sum_5_carry1_jump_implies_next_witness
  (xs:numeral 10)
  : Lemma (requires (
      canonical xs /\ xs <> [] /\
      length (trace_digits xs) == length xs /\
      nth (trace_carries xs) (length xs) == Some 0 /\
      trace_sum_at xs 0 == 5 /\
      trace_carry_at xs (length xs - 1) == 1 /\
      exists (i:nat). 0 < i /\ i <= length (reverse_add xs) /\
        (trace_sum_at (reverse_add xs) i >=
           trace_sum_at (reverse_add xs) (i - 1) + 12 \/
         trace_sum_at (reverse_add xs) (i - 1) >=
           trace_sum_at (reverse_add xs) i + 12)))
    (ensures (trace_local_profile_complement_witness (reverse_add xs))) =
  trace_digits_equals_reverse_add xs;
  add_trace_nonempty #10 xs (rev xs) 0;
  assert (trace_digits xs <> []);
  assert (reverse_add xs <> []);
  let n : nat = length xs in
  trace_carry_prefix_zero xs 0;
  trace_equation_at xs 0;
  assert (trace_carry_at xs 1 == 0);
  no_overflow_trace_outer_sum_equation xs;
  assert (trace_sum_at (reverse_add xs) 0 ==
    trace_sum_at (trace_digits xs) 0);
  assert (trace_sum_at (reverse_add xs) 0 == 11);
  rev_length (reverse_add xs);
  reverse_trace_output_length_case (reverse_add xs);
  trace_output_length_carry_link
    (reverse_add xs) (rev (reverse_add xs)) 0;
  eliminate
    (length (trace_digits (reverse_add xs)) == length (reverse_add xs) /\
     nth (trace_carries (reverse_add xs))
       (length (reverse_add xs)) == Some 0) \/
    (length (trace_digits (reverse_add xs)) == length (reverse_add xs) + 1 /\
     nth (trace_carries (reverse_add xs))
       (length (reverse_add xs)) == Some 1)
  with (
    exists_intro
      (fun (i:nat) -> i < length (reverse_add xs) /\
        trace_sum_at (reverse_add xs) i >= 10)
      0;
    ())
  and (
    eliminate exists (i:nat).
      0 < i /\ i <= length (reverse_add xs) /\
      (trace_sum_at (reverse_add xs) i >=
         trace_sum_at (reverse_add xs) (i - 1) + 12 \/
       trace_sum_at (reverse_add xs) (i - 1) >=
         trace_sum_at (reverse_add xs) i + 12)
    with (
      trace_overflow_sum_jump_obstruction_at (reverse_add xs) i;
      exists_intro
        (fun (k:nat) -> k <= length (reverse_add xs) /\
          ~(trace_local_profile_relation (reverse_add xs) k))
        i;
      ()))
let local_profile_196_is_false () : Lemma (
    ~(trace_local_palindrome_profile digits_196)) =
  assert (length (trace_digits digits_196) == length digits_196);
  assert (nth (trace_carries digits_196) (length digits_196) == Some 0);
  assert (trace_sum_at digits_196 1 == 18);
  introduce (trace_local_palindrome_profile digits_196) ==> False
  with (
    eliminate
      (length (trace_digits digits_196) == length digits_196 /\
       nth (trace_carries digits_196) (length digits_196) == Some 0 /\
       (forall i. i < length digits_196 ==>
         trace_sum_at digits_196 i < 10)) \/
      (length (trace_digits digits_196) == length digits_196 + 1 /\
       nth (trace_carries digits_196) (length digits_196) == Some 1 /\
       (forall i. i <= length digits_196 ==>
         trace_sum_at digits_196 i + overflow_trace_carry_at digits_196 i +
             10 * overflow_trace_carry_at digits_196
               (length digits_196 - i + 1) ==
           trace_sum_at digits_196 (length digits_196 - i) +
             overflow_trace_carry_at digits_196 (length digits_196 - i) +
             10 * overflow_trace_carry_at digits_196 (i + 1)))
    with (
      assert (trace_sum_at digits_196 1 < 10);
      assert False)
    and (
      assert False))

let trace_palindrome_implies_local_profile (xs:numeral 10)
  : Lemma (requires (
      xs <> [] /\ trace_digits xs == rev (trace_digits xs)))
    (ensures (trace_local_palindrome_profile xs)) =
  reverse_trace_palindrome_cases xs;
  eliminate
    (length (trace_digits xs) == length xs /\
     nth (trace_carries xs) (length xs) == Some 0 /\
     (forall i. i < length xs ==>
       trace_carry_at xs i == trace_carry_at xs (length xs - 1 - i))) \/
    (length (trace_digits xs) == length xs + 1 /\
     nth (trace_carries xs) (length xs) == Some 1 /\
     trace_digit_at xs 0 == 1)
  with (
    trace_no_overflow_palindrome_implies_sum_low xs;
    assert (trace_local_palindrome_profile xs);
    ())
  and (
    reverse_trace_overflow_sum_carry_relation xs;
    assert (trace_local_palindrome_profile xs);
    ())

let trace_local_profile_implies_digit_symmetry (xs:numeral 10)
  : Lemma (requires (
      xs <> [] /\ trace_local_palindrome_profile xs))
    (ensures (
      (length (trace_digits xs) == length xs /\
       (forall i. i < length xs ==>
         trace_digit_at xs i ==
           trace_digit_at xs (length xs - 1 - i))) \/
      (length (trace_digits xs) == length xs + 1 /\
       (forall i. i <= length xs ==>
         trace_digit_at xs i ==
           trace_digit_at xs (length xs - i))))) =
  eliminate
    (length (trace_digits xs) == length xs /\
     nth (trace_carries xs) (length xs) == Some 0 /\
     (forall i. i < length xs ==> trace_sum_at xs i < 10)) \/
    (length (trace_digits xs) == length xs + 1 /\
     nth (trace_carries xs) (length xs) == Some 1 /\
     (forall i. i <= length xs ==>
       trace_sum_at xs i + overflow_trace_carry_at xs i +
           10 * overflow_trace_carry_at xs (length xs - i + 1) ==
         trace_sum_at xs (length xs - i) +
           overflow_trace_carry_at xs (length xs - i) +
           10 * overflow_trace_carry_at xs (i + 1)))
  with (
    trace_no_overflow_low_sums_imply_digit_symmetry xs;
    assert (length (trace_digits xs) == length xs /\
      (forall i. i < length xs ==>
        trace_digit_at xs i ==
          trace_digit_at xs (length xs - 1 - i)));
    ())
  and (
    reverse_trace_overflow_relation_implies_digit_symmetry xs;
    assert (length (trace_digits xs) == length xs + 1 /\
      (forall i. i <= length xs ==>
        trace_digit_at xs i ==
          trace_digit_at xs (length xs - i)));
    ())

let trace_local_profile_excludes_trace_palindrome
  (xs:numeral 10) : Lemma (requires (
      xs <> [] /\ ~(trace_local_palindrome_profile xs)))
    (ensures (~ (palindrome #10 (trace_digits xs)))) =
  introduce (palindrome #10 (trace_digits xs)) ==> False
  with (
    assert (trace_digits xs == rev (trace_digits xs));
    trace_palindrome_implies_local_profile xs;
    assert False)

let reverse_add_local_profile_excludes_palindrome
  (xs:numeral 10) : Lemma (requires (
      canonical xs /\ xs <> [] /\
      ~(trace_local_palindrome_profile xs)))
    (ensures (~ (palindrome #10 (reverse_add xs)))) =
  trace_digits_equals_reverse_add xs;
  introduce (palindrome #10 (reverse_add xs)) ==> False
  with (
    assert (palindrome #10 (trace_digits xs));
    trace_local_profile_excludes_trace_palindrome xs)
