module ReverseAddOverflowProfile

open ReverseAdd
open ReverseAddCarry
open ReverseAddHighSum
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
