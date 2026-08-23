module ReverseAddWitness

#set-options "--fuel 20 --ifuel 20 --retry 10"

open ReverseAdd
open ReverseAddCarry
open FStar.Classical
open FStar.List.Tot

let not_forall_implies_exists (#a:Type) (#p:a -> prop)
  (h:~ (forall (x:a). ~(p x)))
  : Lemma (exists (x:a). p x) =
  let contradiction
    (all_not:(x:a -> Lemma (~(p x)))) : Lemma False =
      forall_intro #a #(fun (x:a) -> ~(p x)) all_not;
      assert (forall (x:a). ~(p x));
      assert False
  in
  exists_intro_not_all_not #a #p contradiction

let trace_carry_obstruction_at (xs:numeral 10) (i:nat) : prop =
  length (trace_digits xs) == length xs /\
  nth (trace_carries xs) (length xs) == Some 0 /\
  i < length xs /\
  ~(trace_carry_at xs i ==
    trace_carry_at xs (length xs - 1 - i))

let trace_overflow_low_one_obstruction (xs:numeral 10) : prop =
  length (trace_digits xs) == length xs + 1 /\
  nth (trace_carries xs) (length xs) == Some 1 /\
  ~(trace_digit_at xs 0 == 1)

let trace_overflow_relation_obstruction_at
  (xs:numeral 10) (i:nat) : prop =
  length (trace_digits xs) == length xs + 1 /\
  nth (trace_carries xs) (length xs) == Some 1 /\
  i <= length xs /\
  ~(trace_sum_at xs i + overflow_trace_carry_at xs i +
      10 * overflow_trace_carry_at xs (length xs - i + 1) ==
    trace_sum_at xs (length xs - i) +
      overflow_trace_carry_at xs (length xs - i) +
      10 * overflow_trace_carry_at xs (i + 1))

// The carry terms can change a mirrored relation by at most 11.  A larger
// adjacent sum jump therefore gives an indexed overflow obstruction.
let trace_overflow_sum_jump_obstruction_at
  (xs:numeral 10) (i:nat) : Lemma (requires (
      xs <> [] /\
      length (trace_digits xs) == length xs + 1 /\
      nth (trace_carries xs) (length xs) == Some 1 /\
      0 < i /\
      i <= length xs /\
      (trace_sum_at xs i >= trace_sum_at xs (i - 1) + 12 \/
       trace_sum_at xs (i - 1) >= trace_sum_at xs i + 12)))
    (ensures (trace_overflow_relation_obstruction_at xs i)) =
  let n : nat = length xs in
  assert (i - 1 < n);
  trace_sum_symmetric_at xs (i - 1);
  assert (n - 1 - (i - 1) == n - i);
  assert (trace_sum_at xs (n - i) ==
    trace_sum_at xs (i - 1));
  assert (overflow_trace_carry_at xs i <= 1);
  assert (overflow_trace_carry_at xs (i + 1) <= 1);
  assert (overflow_trace_carry_at xs (n - i) <= 1);
  assert (overflow_trace_carry_at xs (n - i + 1) <= 1);
  eliminate
    (trace_sum_at xs i >= trace_sum_at xs (i - 1) + 12) \/
    (trace_sum_at xs (i - 1) >= trace_sum_at xs i + 12)
  with (
    assert (trace_sum_at xs i +
      overflow_trace_carry_at xs i +
      10 * overflow_trace_carry_at xs (n - i + 1) >=
      trace_sum_at xs i);
    assert (trace_sum_at xs (n - i) +
      overflow_trace_carry_at xs (n - i) +
      10 * overflow_trace_carry_at xs (i + 1) <=
      trace_sum_at xs (i - 1) + 11);
    assert (~ (
      trace_sum_at xs i + overflow_trace_carry_at xs i +
        10 * overflow_trace_carry_at xs (n - i + 1) ==
      trace_sum_at xs (n - i) + overflow_trace_carry_at xs (n - i) +
        10 * overflow_trace_carry_at xs (i + 1)));
    ())
  and (
    assert (trace_sum_at xs i +
      overflow_trace_carry_at xs i +
      10 * overflow_trace_carry_at xs (n - i + 1) <=
      trace_sum_at xs i + 11);
    assert (trace_sum_at xs (n - i) +
      overflow_trace_carry_at xs (n - i) +
      10 * overflow_trace_carry_at xs (i + 1) >=
      trace_sum_at xs (i - 1));
    assert (~ (
      trace_sum_at xs i + overflow_trace_carry_at xs i +
        10 * overflow_trace_carry_at xs (n - i + 1) ==
      trace_sum_at xs (n - i) + overflow_trace_carry_at xs (n - i) +
        10 * overflow_trace_carry_at xs (i + 1)));
    ());
  assert (trace_overflow_relation_obstruction_at xs i);
  ()

// The endpoint equation reduces to the two concrete possible outer sums.
let trace_overflow_palindrome_outer_sum_is_1_or_11
  (xs:numeral 10) : Lemma (requires (
      xs <> [] /\
      length (trace_digits xs) == length xs + 1 /\
      nth (trace_carries xs) (length xs) == Some 1 /\
      trace_digits xs == rev (trace_digits xs)))
    (ensures (trace_sum_at xs 0 == 1 \/
      trace_sum_at xs 0 == 11)) =
  reverse_trace_overflow_outer_sum_condition xs;
  assert (trace_carry_at xs 1 == 0 \/
    trace_carry_at xs 1 == 1);
  eliminate trace_carry_at xs 1 == 0 \/
    trace_carry_at xs 1 == 1
  with (
    assert (trace_sum_at xs 0 == 1);
    ())
  and (
    assert (trace_sum_at xs 0 == 11);
    ())

let trace_palindrome_obstruction_at
  (xs:numeral 10) (i:nat) : prop =
  trace_carry_obstruction_at xs i \/
  (i == 0 /\ trace_overflow_low_one_obstruction xs) \/
  trace_overflow_relation_obstruction_at xs i

let trace_carry_obstruction_at_sound
  (xs:numeral 10) (i:nat)
  : Lemma (requires (trace_carry_obstruction_at xs i))
    (ensures (trace_carry_obstruction xs)) =
  assert (~ (carry_prefix_symmetric xs));
  assert (trace_carry_obstruction xs);
  ()

let trace_overflow_low_one_obstruction_sound
  (xs:numeral 10)
  : Lemma (requires (trace_overflow_low_one_obstruction xs))
    (ensures (trace_carry_obstruction xs)) =
  assert (trace_carry_obstruction xs);
  ()

let trace_overflow_outer_obstruction_at_sound
  (xs:numeral 10)
  : Lemma (requires (trace_overflow_outer_obstruction xs))
    (ensures (trace_palindrome_obstruction_at xs 0)) =
  assert (xs <> []);
  trace_equation_at xs 0;
  assert (trace_carry_at xs 0 == 0);
  assert (~ (trace_digit_at xs 0 == 1));
  assert (trace_overflow_low_one_obstruction xs);
  ()

// Any overflow endpoint sum other than 1 or 11 makes the low output digit
// differ from one, hence supplies the index-zero obstruction.
let trace_overflow_outer_sum_not_1_or_11_obstruction_at
  (xs:numeral 10) : Lemma (requires (
      xs <> [] /\
      length (trace_digits xs) == length xs + 1 /\
      nth (trace_carries xs) (length xs) == Some 1 /\
      trace_sum_at xs 0 <> 1 /\
      trace_sum_at xs 0 <> 11))
    (ensures (trace_palindrome_obstruction_at xs 0)) =
  trace_equation_at xs 0;
  assert (trace_carry_at xs 0 == 0);
  assert (trace_carry_at xs 1 == 0 \/
    trace_carry_at xs 1 == 1);
  assert (~ (trace_digit_at xs 0 == 1));
  assert (trace_overflow_low_one_obstruction xs);
  assert (trace_palindrome_obstruction_at xs 0);
  ()

let trace_overflow_relation_obstruction_at_sound
  (xs:numeral 10) (i:nat)
  : Lemma (requires (trace_overflow_relation_obstruction_at xs i))
    (ensures (trace_overflow_relation_obstruction xs)) =
  assert (~ (overflow_sum_carry_relation_holds xs));
  assert (trace_overflow_relation_obstruction xs);
  ()

// A palindromic overflow output cannot contain either orientation of a
// neighboring sum jump larger than the carry correction range.
let trace_overflow_palindrome_implies_no_sum_jump
  (xs:numeral 10) (i:nat) : Lemma (requires (
      xs <> [] /\
      length (trace_digits xs) == length xs + 1 /\
      nth (trace_carries xs) (length xs) == Some 1 /\
      0 < i /\
      i <= length xs /\
      trace_digits xs == rev (trace_digits xs)))
    (ensures (~ (
      trace_sum_at xs i >= trace_sum_at xs (i - 1) + 12 \/
      trace_sum_at xs (i - 1) >= trace_sum_at xs i + 12))) =
  introduce (
    trace_sum_at xs i >= trace_sum_at xs (i - 1) + 12 \/
    trace_sum_at xs (i - 1) >= trace_sum_at xs i + 12) ==> False
  with (
    trace_overflow_sum_jump_obstruction_at xs i;
    trace_overflow_relation_obstruction_at_sound xs i;
    trace_overflow_relation_obstruction_excludes_palindrome xs)

let trace_palindrome_obstruction_at_sound
  (xs:numeral 10) (i:nat)
  : Lemma (requires (trace_palindrome_obstruction_at xs i))
    (ensures (trace_palindrome_obstruction xs)) =
  assert (trace_palindrome_obstruction xs);
  ()

let trace_palindrome_obstruction_at_exists (xs:numeral 10)
  : Lemma (requires (trace_palindrome_obstruction xs))
    (ensures (exists (i:nat). trace_palindrome_obstruction_at xs i)) =
  eliminate
    trace_carry_obstruction xs \/
    trace_overflow_relation_obstruction xs
  with (
    eliminate
      (length (trace_digits xs) == length xs /\
       nth (trace_carries xs) (length xs) == Some 0 /\
       ~(carry_prefix_symmetric xs)) \/
      (length (trace_digits xs) == length xs + 1 /\
       nth (trace_carries xs) (length xs) == Some 1 /\
       ~(trace_digit_at xs 0 == 1))
    with (
      assert (length (trace_digits xs) == length xs);
      assert (nth (trace_carries xs) (length xs) == Some 0);
      assert (~ (forall i. i < length xs ==>
        trace_carry_at xs i ==
          trace_carry_at xs (length xs - 1 - i)));
      assert (~ (forall (i:nat). ~(
        i < length xs /\
        ~(trace_carry_at xs i ==
          trace_carry_at xs (length xs - 1 - i)))));
      not_forall_implies_exists #nat
        #(fun (i:nat) -> i < length xs /\
          ~(trace_carry_at xs i ==
            trace_carry_at xs (length xs - 1 - i)))
        ();
      eliminate exists (i:nat). i < length xs /\
        ~(trace_carry_at xs i ==
          trace_carry_at xs (length xs - 1 - i))
      with (
        exists_intro
          (fun (i:nat) -> trace_palindrome_obstruction_at xs i) i;
        assert (trace_carry_obstruction_at xs i);
        ())
    )
    and (
      exists_intro
        (fun (i:nat) -> trace_palindrome_obstruction_at xs i) 0;
      assert (trace_palindrome_obstruction_at xs 0);
      ())
  )
  and (
    assert (length (trace_digits xs) == length xs + 1);
    assert (nth (trace_carries xs) (length xs) == Some 1);
    assert (~ (forall (i:nat). ~(
      i <= length xs /\
      ~(trace_sum_at xs i + overflow_trace_carry_at xs i +
        10 * overflow_trace_carry_at xs (length xs - i + 1) ==
        trace_sum_at xs (length xs - i) +
        overflow_trace_carry_at xs (length xs - i) +
        10 * overflow_trace_carry_at xs (i + 1)))));
    not_forall_implies_exists #nat
      #(fun (i:nat) -> i <= length xs /\
        ~(trace_sum_at xs i + overflow_trace_carry_at xs i +
          10 * overflow_trace_carry_at xs (length xs - i + 1) ==
          trace_sum_at xs (length xs - i) +
          overflow_trace_carry_at xs (length xs - i) +
          10 * overflow_trace_carry_at xs (i + 1)))
      ();
    eliminate exists (i:nat). i <= length xs /\
      ~(trace_sum_at xs i + overflow_trace_carry_at xs i +
        10 * overflow_trace_carry_at xs (length xs - i + 1) ==
        trace_sum_at xs (length xs - i) +
        overflow_trace_carry_at xs (length xs - i) +
        10 * overflow_trace_carry_at xs (i + 1))
    with (
      exists_intro
        (fun (i:nat) -> trace_palindrome_obstruction_at xs i) i;
      assert (trace_overflow_relation_obstruction_at xs i);
      ())
  )

let trace_palindrome_obstruction_at_excludes_palindrome
  (xs:numeral 10) (i:nat)
  : Lemma (requires (
      xs <> [] /\
      trace_palindrome_obstruction_at xs i /\
      trace_digits xs == rev (trace_digits xs)))
    (ensures False) =
  trace_palindrome_obstruction_at_sound xs i;
  trace_palindrome_obstruction_excludes_palindrome xs

let trace_palindrome_obstruction_at_196 () : Lemma (
    trace_palindrome_obstruction_at digits_196 0) =
  trace_carry_obstruction_196 ();
  ()

let trace_palindrome_obstruction_at_887 () : Lemma (
    trace_palindrome_obstruction_at [7; 8; 8] 0) =
  assert (length (trace_digits [7; 8; 8]) == length [7; 8; 8] + 1);
  assert (nth (trace_carries [7; 8; 8])
    (length [7; 8; 8]) == Some 1);
  assert (~ (trace_digit_at [7; 8; 8] 0 == 1));
  ()

let trace_palindrome_obstruction_at_1675 () : Lemma (
    trace_palindrome_obstruction_at [5; 7; 6; 1] 0) =
  assert (length (trace_digits [5; 7; 6; 1]) == length [5; 7; 6; 1]);
  assert (nth (trace_carries [5; 7; 6; 1])
    (length [5; 7; 6; 1]) == Some 0);
  assert (~ (trace_carry_at [5; 7; 6; 1] 0 ==
    trace_carry_at [5; 7; 6; 1] 3));
  ()

let trace_palindrome_obstruction_at_7436 () : Lemma (
    trace_palindrome_obstruction_at [6; 3; 4; 7] 0) =
  assert (length (trace_digits [6; 3; 4; 7]) == length [6; 3; 4; 7] + 1);
  assert (nth (trace_carries [6; 3; 4; 7])
    (length [6; 3; 4; 7]) == Some 1);
  assert (~ (trace_digit_at [6; 3; 4; 7] 0 == 1));
  ()

let trace_palindrome_obstruction_at_1199 () : Lemma (
    trace_palindrome_obstruction_at [9; 9; 1; 1] 0) =
  assert (length (trace_digits [9; 9; 1; 1]) ==
    length [9; 9; 1; 1] + 1);
  assert (nth (trace_carries [9; 9; 1; 1])
    (length [9; 9; 1; 1]) == Some 1);
  assert (~ (trace_digit_at [9; 9; 1; 1] 0 == 1));
  ()

let trace_palindrome_obstruction_at_13783 () : Lemma (
    trace_palindrome_obstruction_at [3; 8; 7; 3; 1] 0) =
  assert (length (trace_digits [3; 8; 7; 3; 1]) ==
    length [3; 8; 7; 3; 1]);
  assert (nth (trace_carries [3; 8; 7; 3; 1])
    (length [3; 8; 7; 3; 1]) == Some 0);
  assert (~ (trace_carry_at [3; 8; 7; 3; 1] 0 ==
    trace_carry_at [3; 8; 7; 3; 1] 4));
  ()

let trace_palindrome_obstruction_at_52514 () : Lemma (
    trace_palindrome_obstruction_at [4; 1; 5; 2; 5] 1) =
  assert (length (trace_digits [4; 1; 5; 2; 5]) ==
    length [4; 1; 5; 2; 5]);
  assert (nth (trace_carries [4; 1; 5; 2; 5])
    (length [4; 1; 5; 2; 5]) == Some 0);
  assert (~ (trace_carry_at [4; 1; 5; 2; 5] 1 ==
    trace_carry_at [4; 1; 5; 2; 5] 3));
  ()

let trace_palindrome_obstruction_at_94039 () : Lemma (
    trace_palindrome_obstruction_at [9; 3; 0; 4; 9] 0) =
  assert (length (trace_digits [9; 3; 0; 4; 9]) ==
    length [9; 3; 0; 4; 9] + 1);
  assert (nth (trace_carries [9; 3; 0; 4; 9])
    (length [9; 3; 0; 4; 9]) == Some 1);
  assert (~ (trace_digit_at [9; 3; 0; 4; 9] 0 == 1));
  ()

let trace_palindrome_obstruction_at_187088 () : Lemma (
    trace_palindrome_obstruction_at [8; 8; 0; 7; 8; 1] 0) =
  assert (length (trace_digits [8; 8; 0; 7; 8; 1]) ==
    length [8; 8; 0; 7; 8; 1] + 1);
  assert (nth (trace_carries [8; 8; 0; 7; 8; 1])
    (length [8; 8; 0; 7; 8; 1]) == Some 1);
  assert (~ (trace_digit_at [8; 8; 0; 7; 8; 1] 0 == 1));
  ()

let trace_palindrome_obstruction_at_1067869 () : Lemma (
    trace_palindrome_obstruction_at [9; 6; 8; 7; 6; 0; 1] 0) =
  assert (length (trace_digits [9; 6; 8; 7; 6; 0; 1]) ==
    length [9; 6; 8; 7; 6; 0; 1] + 1);
  assert (nth (trace_carries [9; 6; 8; 7; 6; 0; 1])
    (length [9; 6; 8; 7; 6; 0; 1]) == Some 1);
  assert (~ (trace_digit_at [9; 6; 8; 7; 6; 0; 1] 0 == 1));
  ()

let trace_palindrome_obstruction_at_10755470 () : Lemma (
    trace_palindrome_obstruction_at [0; 7; 4; 5; 5; 7; 0; 1] 1) =
  assert (length (trace_digits [0; 7; 4; 5; 5; 7; 0; 1]) ==
    length [0; 7; 4; 5; 5; 7; 0; 1]);
  assert (nth (trace_carries [0; 7; 4; 5; 5; 7; 0; 1])
    (length [0; 7; 4; 5; 5; 7; 0; 1]) == Some 0);
  assert (~ (trace_carry_at [0; 7; 4; 5; 5; 7; 0; 1] 1 ==
    trace_carry_at [0; 7; 4; 5; 5; 7; 0; 1] 6));
  ()

let trace_no_overflow_10755470 () : Lemma (
    length (trace_digits [0; 7; 4; 5; 5; 7; 0; 1]) ==
      length [0; 7; 4; 5; 5; 7; 0; 1] /\
    nth (trace_carries [0; 7; 4; 5; 5; 7; 0; 1])
      (length [0; 7; 4; 5; 5; 7; 0; 1]) == Some 0) =
  assert (length (trace_digits [0; 7; 4; 5; 5; 7; 0; 1]) ==
    length [0; 7; 4; 5; 5; 7; 0; 1]);
  assert (nth (trace_carries [0; 7; 4; 5; 5; 7; 0; 1])
    (length [0; 7; 4; 5; 5; 7; 0; 1]) == Some 0);
  ()

let trace_palindrome_obstruction_at_18211171 () : Lemma (
    trace_palindrome_obstruction_at [1; 7; 1; 1; 1; 2; 8; 1] 0) =
  assert (length (trace_digits [1; 7; 1; 1; 1; 2; 8; 1]) ==
    length [1; 7; 1; 1; 1; 2; 8; 1]);
  assert (nth (trace_carries [1; 7; 1; 1; 1; 2; 8; 1])
    (length [1; 7; 1; 1; 1; 2; 8; 1]) == Some 0);
  assert (~ (trace_carry_at [1; 7; 1; 1; 1; 2; 8; 1] 0 ==
    trace_carry_at [1; 7; 1; 1; 1; 2; 8; 1] 7));
  ()

let trace_palindrome_obstruction_at_35322452 () : Lemma (
    trace_palindrome_obstruction_at [2; 5; 4; 2; 2; 3; 5; 3] 0) =
  assert (length (trace_digits [2; 5; 4; 2; 2; 3; 5; 3]) ==
    length [2; 5; 4; 2; 2; 3; 5; 3]);
  assert (nth (trace_carries [2; 5; 4; 2; 2; 3; 5; 3])
    (length [2; 5; 4; 2; 2; 3; 5; 3]) == Some 0);
  assert (~ (trace_carry_at [2; 5; 4; 2; 2; 3; 5; 3] 0 ==
    trace_carry_at [2; 5; 4; 2; 2; 3; 5; 3] 7));
  ()

let trace_palindrome_obstruction_at_60744805 () : Lemma (
    trace_palindrome_obstruction_at [5; 0; 8; 4; 4; 7; 0; 6] 2) =
  assert (trace_digits [5; 0; 8; 4; 4; 7; 0; 6] ==
    [1; 1; 5; 9; 8; 5; 1; 1; 1]);
  assert (trace_carries [5; 0; 8; 4; 4; 7; 0; 6] ==
    [0; 1; 0; 1; 0; 0; 1; 0; 1]);
  assert (trace_sum_at [5; 0; 8; 4; 4; 7; 0; 6] 2 == 15);
  assert (trace_sum_at [5; 0; 8; 4; 4; 7; 0; 6] 6 == 0);
  assert (~ (
    trace_sum_at [5; 0; 8; 4; 4; 7; 0; 6] 2 +
      overflow_trace_carry_at [5; 0; 8; 4; 4; 7; 0; 6] 2 +
      10 * overflow_trace_carry_at [5; 0; 8; 4; 4; 7; 0; 6]
        (length [5; 0; 8; 4; 4; 7; 0; 6] - 2 + 1) ==
    trace_sum_at [5; 0; 8; 4; 4; 7; 0; 6]
        (length [5; 0; 8; 4; 4; 7; 0; 6] - 2) +
      overflow_trace_carry_at [5; 0; 8; 4; 4; 7; 0; 6]
        (length [5; 0; 8; 4; 4; 7; 0; 6] - 2) +
      10 * overflow_trace_carry_at [5; 0; 8; 4; 4; 7; 0; 6] (2 + 1)));
  ()

let trace_palindrome_obstruction_at_111589511 () : Lemma (
    trace_palindrome_obstruction_at [1; 1; 5; 9; 8; 5; 1; 1; 1] 2) =
  assert (length (trace_digits [1; 1; 5; 9; 8; 5; 1; 1; 1]) ==
    length [1; 1; 5; 9; 8; 5; 1; 1; 1]);
  assert (nth (trace_carries [1; 1; 5; 9; 8; 5; 1; 1; 1])
    (length [1; 1; 5; 9; 8; 5; 1; 1; 1]) == Some 0);
  assert (~ (trace_carry_at [1; 1; 5; 9; 8; 5; 1; 1; 1] 2 ==
    trace_carry_at [1; 1; 5; 9; 8; 5; 1; 1; 1] 6));
  ()

let trace_palindrome_obstruction_at_227574622 () : Lemma (
    trace_palindrome_obstruction_at [2; 2; 6; 4; 7; 5; 7; 2; 2] 1) =
  assert (length (trace_digits [2; 2; 6; 4; 7; 5; 7; 2; 2]) ==
    length [2; 2; 6; 4; 7; 5; 7; 2; 2]);
  assert (nth (trace_carries [2; 2; 6; 4; 7; 5; 7; 2; 2])
    (length [2; 2; 6; 4; 7; 5; 7; 2; 2]) == Some 0);
  assert (~ (trace_carry_at [2; 2; 6; 4; 7; 5; 7; 2; 2] 1 ==
    trace_carry_at [2; 2; 6; 4; 7; 5; 7; 2; 2] 7));
  ()

let trace_palindrome_obstruction_at_454050344 () : Lemma (
    trace_palindrome_obstruction_at [4; 4; 3; 0; 5; 0; 4; 5; 4] 3) =
  assert (length (trace_digits [4; 4; 3; 0; 5; 0; 4; 5; 4]) ==
    length [4; 4; 3; 0; 5; 0; 4; 5; 4]);
  assert (nth (trace_carries [4; 4; 3; 0; 5; 0; 4; 5; 4])
    (length [4; 4; 3; 0; 5; 0; 4; 5; 4]) == Some 0);
  assert (~ (trace_carry_at [4; 4; 3; 0; 5; 0; 4; 5; 4] 3 ==
    trace_carry_at [4; 4; 3; 0; 5; 0; 4; 5; 4] 5));
  ()

let trace_palindrome_obstruction_at_897100798 () : Lemma (
    trace_palindrome_obstruction_at [8; 9; 7; 0; 0; 1; 7; 9; 8] 0) =
  assert (trace_digits [8; 9; 7; 0; 0; 1; 7; 9; 8] ==
    [6; 9; 5; 2; 0; 1; 4; 9; 7; 1]);
  assert (length (trace_digits [8; 9; 7; 0; 0; 1; 7; 9; 8]) ==
    length [8; 9; 7; 0; 0; 1; 7; 9; 8] + 1);
  assert (nth (trace_carries [8; 9; 7; 0; 0; 1; 7; 9; 8])
    (length [8; 9; 7; 0; 0; 1; 7; 9; 8]) == Some 1);
  assert (~ (trace_digit_at [8; 9; 7; 0; 0; 1; 7; 9; 8] 0 == 1));
  ()

let trace_palindrome_obstruction_at_1794102596 () : Lemma (
    trace_palindrome_obstruction_at [6; 9; 5; 2; 0; 1; 4; 9; 7; 1] 0) =
  assert (length (trace_digits [6; 9; 5; 2; 0; 1; 4; 9; 7; 1]) ==
    length [6; 9; 5; 2; 0; 1; 4; 9; 7; 1]);
  assert (nth (trace_carries [6; 9; 5; 2; 0; 1; 4; 9; 7; 1])
    (length [6; 9; 5; 2; 0; 1; 4; 9; 7; 1]) == Some 0);
  assert (~ (trace_carry_at [6; 9; 5; 2; 0; 1; 4; 9; 7; 1] 0 ==
    trace_carry_at [6; 9; 5; 2; 0; 1; 4; 9; 7; 1] 9));
  ()

let trace_palindrome_obstruction_at_8746117567 () : Lemma (
    trace_palindrome_obstruction_at [7; 6; 5; 7; 1; 1; 6; 4; 7; 8] 0) =
  assert (trace_digits [7; 6; 5; 7; 1; 1; 6; 4; 7; 8] ==
    [5; 4; 0; 4; 3; 2; 3; 0; 4; 6; 1]);
  assert (trace_carries [7; 6; 5; 7; 1; 1; 6; 4; 7; 8] ==
    [0; 1; 1; 1; 1; 0; 0; 1; 1; 1; 1]);
  assert (length (trace_digits [7; 6; 5; 7; 1; 1; 6; 4; 7; 8]) ==
    length [7; 6; 5; 7; 1; 1; 6; 4; 7; 8] + 1);
  assert (nth (trace_carries [7; 6; 5; 7; 1; 1; 6; 4; 7; 8])
    (length [7; 6; 5; 7; 1; 1; 6; 4; 7; 8]) == Some 1);
  assert (~ (trace_digit_at [7; 6; 5; 7; 1; 1; 6; 4; 7; 8] 0 == 1));
  ()

let trace_palindrome_obstruction_at_16403234045 () : Lemma (
    trace_palindrome_obstruction_at [5; 4; 0; 4; 3; 2; 3; 0; 4; 6; 1] 0) =
  assert (length (trace_digits [5; 4; 0; 4; 3; 2; 3; 0; 4; 6; 1]) ==
    length [5; 4; 0; 4; 3; 2; 3; 0; 4; 6; 1]);
  assert (nth (trace_carries [5; 4; 0; 4; 3; 2; 3; 0; 4; 6; 1])
    (length [5; 4; 0; 4; 3; 2; 3; 0; 4; 6; 1]) == Some 0);
  assert (~ (trace_carry_at [5; 4; 0; 4; 3; 2; 3; 0; 4; 6; 1] 0 ==
    trace_carry_at [5; 4; 0; 4; 3; 2; 3; 0; 4; 6; 1] 10));
  ()

let trace_palindrome_obstruction_at_70446464506 () : Lemma (
    trace_palindrome_obstruction_at [6; 0; 5; 4; 6; 4; 6; 4; 4; 0; 7] 0) =
  assert (length (trace_digits [6; 0; 5; 4; 6; 4; 6; 4; 4; 0; 7]) ==
    length [6; 0; 5; 4; 6; 4; 6; 4; 4; 0; 7] + 1);
  assert (nth (trace_carries [6; 0; 5; 4; 6; 4; 6; 4; 4; 0; 7])
    (length [6; 0; 5; 4; 6; 4; 6; 4; 4; 0; 7]) == Some 1);
  assert (~ (trace_digit_at [6; 0; 5; 4; 6; 4; 6; 4; 4; 0; 7] 0 == 1));
  ()

let trace_palindrome_obstruction_at_130992928913 () : Lemma (
    trace_palindrome_obstruction_at
      [3; 1; 9; 8; 2; 9; 2; 9; 9; 0; 3; 1] 1) =
  assert (length (trace_digits
    [3; 1; 9; 8; 2; 9; 2; 9; 9; 0; 3; 1]) ==
    length [3; 1; 9; 8; 2; 9; 2; 9; 9; 0; 3; 1]);
  assert (nth (trace_carries
    [3; 1; 9; 8; 2; 9; 2; 9; 9; 0; 3; 1])
    (length [3; 1; 9; 8; 2; 9; 2; 9; 9; 0; 3; 1]) == Some 0);
  assert (~ (trace_carry_at
    [3; 1; 9; 8; 2; 9; 2; 9; 9; 0; 3; 1] 1 ==
    trace_carry_at
      [3; 1; 9; 8; 2; 9; 2; 9; 9; 0; 3; 1] 10));
  ()

let trace_palindrome_obstruction_at_450822227944 () : Lemma (
    trace_palindrome_obstruction_at
      [4; 4; 9; 7; 2; 2; 2; 2; 8; 0; 5; 4] 0) =
  assert (length (trace_digits
    [4; 4; 9; 7; 2; 2; 2; 2; 8; 0; 5; 4]) ==
    length [4; 4; 9; 7; 2; 2; 2; 2; 8; 0; 5; 4]);
  assert (nth (trace_carries
    [4; 4; 9; 7; 2; 2; 2; 2; 8; 0; 5; 4])
    (length [4; 4; 9; 7; 2; 2; 2; 2; 8; 0; 5; 4]) == Some 0);
  assert (~ (trace_carry_at
    [4; 4; 9; 7; 2; 2; 2; 2; 8; 0; 5; 4] 0 ==
    trace_carry_at
      [4; 4; 9; 7; 2; 2; 2; 2; 8; 0; 5; 4] 11));
  ()

let trace_palindrome_obstruction_at_900544455998 () : Lemma (
    trace_palindrome_obstruction_at
      [8; 9; 9; 5; 5; 4; 4; 4; 5; 0; 0; 9] 0) =
  assert (length (trace_digits
    [8; 9; 9; 5; 5; 4; 4; 4; 5; 0; 0; 9]) ==
    length [8; 9; 9; 5; 5; 4; 4; 4; 5; 0; 0; 9] + 1);
  assert (nth (trace_carries
    [8; 9; 9; 5; 5; 4; 4; 4; 5; 0; 0; 9])
    (length [8; 9; 9; 5; 5; 4; 4; 4; 5; 0; 0; 9]) == Some 1);
  assert (~ (trace_digit_at
    [8; 9; 9; 5; 5; 4; 4; 4; 5; 0; 0; 9] 0 == 1));
  ()

let trace_palindrome_obstruction_at_1800098901007 () : Lemma (
    trace_palindrome_obstruction_at
      [7; 0; 0; 1; 0; 9; 8; 9; 0; 0; 0; 8; 1] 4) =
  assert (length (trace_digits
    [7; 0; 0; 1; 0; 9; 8; 9; 0; 0; 0; 8; 1]) ==
    length [7; 0; 0; 1; 0; 9; 8; 9; 0; 0; 0; 8; 1]);
  assert (nth (trace_carries
    [7; 0; 0; 1; 0; 9; 8; 9; 0; 0; 0; 8; 1])
    (length [7; 0; 0; 1; 0; 9; 8; 9; 0; 0; 0; 8; 1]) == Some 0);
  assert (~ (trace_carry_at
    [7; 0; 0; 1; 0; 9; 8; 9; 0; 0; 0; 8; 1] 4 ==
    trace_carry_at
      [7; 0; 0; 1; 0; 9; 8; 9; 0; 0; 0; 8; 1] 8));
  ()

let trace_palindrome_obstruction_at_8801197801088 () : Lemma (
    trace_palindrome_obstruction_at
      [8; 8; 0; 1; 0; 8; 7; 9; 1; 1; 0; 8; 8] 0) =
  assert (length (trace_digits
    [8; 8; 0; 1; 0; 8; 7; 9; 1; 1; 0; 8; 8]) ==
    length [8; 8; 0; 1; 0; 8; 7; 9; 1; 1; 0; 8; 8] + 1);
  assert (nth (trace_carries
    [8; 8; 0; 1; 0; 8; 7; 9; 1; 1; 0; 8; 8])
    (length [8; 8; 0; 1; 0; 8; 7; 9; 1; 1; 0; 8; 8]) == Some 1);
  assert (~ (trace_digit_at
    [8; 8; 0; 1; 0; 8; 7; 9; 1; 1; 0; 8; 8] 0 == 1));
  ()

let trace_palindrome_obstruction_at_17602285712176 () : Lemma (
    trace_palindrome_obstruction_at
      [6; 7; 1; 2; 1; 7; 5; 8; 2; 2; 0; 6; 7; 1] 0) =
  assert (length (trace_digits
    [6; 7; 1; 2; 1; 7; 5; 8; 2; 2; 0; 6; 7; 1]) ==
    length [6; 7; 1; 2; 1; 7; 5; 8; 2; 2; 0; 6; 7; 1]);
  assert (nth (trace_carries
    [6; 7; 1; 2; 1; 7; 5; 8; 2; 2; 0; 6; 7; 1])
    (length [6; 7; 1; 2; 1; 7; 5; 8; 2; 2; 0; 6; 7; 1]) == Some 0);
  assert (~ (trace_carry_at
    [6; 7; 1; 2; 1; 7; 5; 8; 2; 2; 0; 6; 7; 1] 0 ==
    trace_carry_at
      [6; 7; 1; 2; 1; 7; 5; 8; 2; 2; 0; 6; 7; 1] 13));
  ()

let trace_palindrome_obstruction_at_84724043932847 () : Lemma (
    trace_palindrome_obstruction_at
      [7; 4; 8; 2; 3; 9; 3; 4; 0; 4; 2; 7; 4; 8] 0) =
  assert (length (trace_digits
    [7; 4; 8; 2; 3; 9; 3; 4; 0; 4; 2; 7; 4; 8]) ==
    length [7; 4; 8; 2; 3; 9; 3; 4; 0; 4; 2; 7; 4; 8] + 1);
  assert (nth (trace_carries
    [7; 4; 8; 2; 3; 9; 3; 4; 0; 4; 2; 7; 4; 8])
    (length [7; 4; 8; 2; 3; 9; 3; 4; 0; 4; 2; 7; 4; 8]) == Some 1);
  assert (~ (trace_digit_at
    [7; 4; 8; 2; 3; 9; 3; 4; 0; 4; 2; 7; 4; 8] 0 == 1));
  ()

let trace_palindrome_obstruction_at_159547977975595 () : Lemma (
    trace_palindrome_obstruction_at
      [5; 9; 5; 5; 7; 9; 7; 7; 9; 7; 4; 5; 9; 5; 1] 0) =
  assert (length (trace_digits
    [5; 9; 5; 5; 7; 9; 7; 7; 9; 7; 4; 5; 9; 5; 1]) ==
    length [5; 9; 5; 5; 7; 9; 7; 7; 9; 7; 4; 5; 9; 5; 1]);
  assert (nth (trace_carries
    [5; 9; 5; 5; 7; 9; 7; 7; 9; 7; 4; 5; 9; 5; 1])
    (length [5; 9; 5; 5; 7; 9; 7; 7; 9; 7; 4; 5; 9; 5; 1]) == Some 0);
  assert (~ (trace_carry_at
    [5; 9; 5; 5; 7; 9; 7; 7; 9; 7; 4; 5; 9; 5; 1] 0 ==
    trace_carry_at
      [5; 9; 5; 5; 7; 9; 7; 7; 9; 7; 4; 5; 9; 5; 1] 14));
  ()

let trace_palindrome_obstruction_at_755127757721546 () : Lemma (
    trace_palindrome_obstruction_at
      [6; 4; 5; 1; 2; 7; 7; 5; 7; 7; 2; 1; 5; 5; 7] 0) =
  assert (length (trace_digits
    [6; 4; 5; 1; 2; 7; 7; 5; 7; 7; 2; 1; 5; 5; 7]) ==
    length [6; 4; 5; 1; 2; 7; 7; 5; 7; 7; 2; 1; 5; 5; 7] + 1);
  assert (nth (trace_carries
    [6; 4; 5; 1; 2; 7; 7; 5; 7; 7; 2; 1; 5; 5; 7])
    (length [6; 4; 5; 1; 2; 7; 7; 5; 7; 7; 2; 1; 5; 5; 7]) == Some 1);
  assert (~ (trace_digit_at
    [6; 4; 5; 1; 2; 7; 7; 5; 7; 7; 2; 1; 5; 5; 7] 0 == 1));
  ()

let reverse_add_94039_to_187088 () : Lemma (
    reverse_add #10 [9; 3; 0; 4; 9] == [8; 8; 0; 7; 8; 1]) =
  assert (trace_digits [9; 3; 0; 4; 9] == [8; 8; 0; 7; 8; 1]);
  trace_digits_equals_reverse_add [9; 3; 0; 4; 9];
  ()

let reverse_add_187088_to_1067869 () : Lemma (
    reverse_add #10 [8; 8; 0; 7; 8; 1] == [9; 6; 8; 7; 6; 0; 1]) =
  assert (trace_digits [8; 8; 0; 7; 8; 1] ==
    [9; 6; 8; 7; 6; 0; 1]);
  trace_digits_equals_reverse_add [8; 8; 0; 7; 8; 1];
  ()

let reverse_add_1067869_to_10755470 () : Lemma (
    reverse_add #10 [9; 6; 8; 7; 6; 0; 1] ==
      [0; 7; 4; 5; 5; 7; 0; 1]) =
  assert (trace_digits [9; 6; 8; 7; 6; 0; 1] ==
    [0; 7; 4; 5; 5; 7; 0; 1]);
  trace_digits_equals_reverse_add [9; 6; 8; 7; 6; 0; 1];
  ()

let reverse_add_10755470_to_18211171 () : Lemma (
    reverse_add #10 [0; 7; 4; 5; 5; 7; 0; 1] ==
      [1; 7; 1; 1; 1; 2; 8; 1]) =
  assert (trace_digits [0; 7; 4; 5; 5; 7; 0; 1] ==
    [1; 7; 1; 1; 1; 2; 8; 1]);
  trace_digits_equals_reverse_add [0; 7; 4; 5; 5; 7; 0; 1];
  ()

let reverse_add_18211171_to_35322452 () : Lemma (
    reverse_add #10 [1; 7; 1; 1; 1; 2; 8; 1] ==
      [2; 5; 4; 2; 2; 3; 5; 3]) =
  assert (trace_digits [1; 7; 1; 1; 1; 2; 8; 1] ==
    [2; 5; 4; 2; 2; 3; 5; 3]);
  trace_digits_equals_reverse_add [1; 7; 1; 1; 1; 2; 8; 1];
  ()

let reverse_add_35322452_to_60744805 () : Lemma (
    reverse_add #10 [2; 5; 4; 2; 2; 3; 5; 3] ==
      [5; 0; 8; 4; 4; 7; 0; 6]) =
  assert (trace_digits [2; 5; 4; 2; 2; 3; 5; 3] ==
    [5; 0; 8; 4; 4; 7; 0; 6]);
  trace_digits_equals_reverse_add [2; 5; 4; 2; 2; 3; 5; 3];
  ()

let reverse_add_60744805_to_111589511 () : Lemma (
    reverse_add #10 [5; 0; 8; 4; 4; 7; 0; 6] ==
      [1; 1; 5; 9; 8; 5; 1; 1; 1]) =
  assert (trace_digits [5; 0; 8; 4; 4; 7; 0; 6] ==
    [1; 1; 5; 9; 8; 5; 1; 1; 1]);
  trace_digits_equals_reverse_add [5; 0; 8; 4; 4; 7; 0; 6];
  ()

let reverse_add_111589511_to_227574622 () : Lemma (
    reverse_add #10 [1; 1; 5; 9; 8; 5; 1; 1; 1] ==
      [2; 2; 6; 4; 7; 5; 7; 2; 2]) =
  assert (trace_digits [1; 1; 5; 9; 8; 5; 1; 1; 1] ==
    [2; 2; 6; 4; 7; 5; 7; 2; 2]);
  trace_digits_equals_reverse_add [1; 1; 5; 9; 8; 5; 1; 1; 1];
  ()

let reverse_add_227574622_to_454050344 () : Lemma (
    reverse_add #10 [2; 2; 6; 4; 7; 5; 7; 2; 2] ==
      [4; 4; 3; 0; 5; 0; 4; 5; 4]) =
  assert (trace_digits [2; 2; 6; 4; 7; 5; 7; 2; 2] ==
    [4; 4; 3; 0; 5; 0; 4; 5; 4]);
  trace_digits_equals_reverse_add [2; 2; 6; 4; 7; 5; 7; 2; 2];
  ()

let reverse_add_454050344_to_897100798 () : Lemma (
    reverse_add #10 [4; 4; 3; 0; 5; 0; 4; 5; 4] ==
      [8; 9; 7; 0; 0; 1; 7; 9; 8]) =
  assert (trace_digits [4; 4; 3; 0; 5; 0; 4; 5; 4] ==
    [8; 9; 7; 0; 0; 1; 7; 9; 8]);
  trace_digits_equals_reverse_add [4; 4; 3; 0; 5; 0; 4; 5; 4];
  ()

let reverse_add_897100798_to_1794102596 () : Lemma (
    reverse_add #10 [8; 9; 7; 0; 0; 1; 7; 9; 8] ==
      [6; 9; 5; 2; 0; 1; 4; 9; 7; 1]) =
  assert (trace_digits [8; 9; 7; 0; 0; 1; 7; 9; 8] ==
    [6; 9; 5; 2; 0; 1; 4; 9; 7; 1]);
  trace_digits_equals_reverse_add [8; 9; 7; 0; 0; 1; 7; 9; 8];
  ()

let reverse_add_1794102596_to_8746117567 () : Lemma (
    reverse_add #10 [6; 9; 5; 2; 0; 1; 4; 9; 7; 1] ==
      [7; 6; 5; 7; 1; 1; 6; 4; 7; 8]) =
  assert (trace_digits [6; 9; 5; 2; 0; 1; 4; 9; 7; 1] ==
    [7; 6; 5; 7; 1; 1; 6; 4; 7; 8]);
  trace_digits_equals_reverse_add [6; 9; 5; 2; 0; 1; 4; 9; 7; 1];
  ()

let reverse_add_8746117567_to_16403234045 () : Lemma (
    reverse_add #10 [7; 6; 5; 7; 1; 1; 6; 4; 7; 8] ==
      [5; 4; 0; 4; 3; 2; 3; 0; 4; 6; 1]) =
  assert (trace_digits [7; 6; 5; 7; 1; 1; 6; 4; 7; 8] ==
    [5; 4; 0; 4; 3; 2; 3; 0; 4; 6; 1]);
  trace_digits_equals_reverse_add [7; 6; 5; 7; 1; 1; 6; 4; 7; 8];
  ()

let reverse_add_16403234045_to_70446464506 () : Lemma (
    reverse_add #10 [5; 4; 0; 4; 3; 2; 3; 0; 4; 6; 1] ==
      [6; 0; 5; 4; 6; 4; 6; 4; 4; 0; 7]) =
  assert (trace_digits [5; 4; 0; 4; 3; 2; 3; 0; 4; 6; 1] ==
    [6; 0; 5; 4; 6; 4; 6; 4; 4; 0; 7]);
  trace_digits_equals_reverse_add [5; 4; 0; 4; 3; 2; 3; 0; 4; 6; 1];
  ()

let reverse_add_70446464506_to_130992928913 () : Lemma (
    reverse_add #10 [6; 0; 5; 4; 6; 4; 6; 4; 4; 0; 7] ==
      [3; 1; 9; 8; 2; 9; 2; 9; 9; 0; 3; 1]) =
  assert (trace_digits [6; 0; 5; 4; 6; 4; 6; 4; 4; 0; 7] ==
    [3; 1; 9; 8; 2; 9; 2; 9; 9; 0; 3; 1]);
  trace_digits_equals_reverse_add [6; 0; 5; 4; 6; 4; 6; 4; 4; 0; 7];
  ()

let reverse_add_130992928913_to_450822227944 () : Lemma (
    reverse_add #10 [3; 1; 9; 8; 2; 9; 2; 9; 9; 0; 3; 1] ==
      [4; 4; 9; 7; 2; 2; 2; 2; 8; 0; 5; 4]) =
  assert (trace_digits [3; 1; 9; 8; 2; 9; 2; 9; 9; 0; 3; 1] ==
    [4; 4; 9; 7; 2; 2; 2; 2; 8; 0; 5; 4]);
  trace_digits_equals_reverse_add [3; 1; 9; 8; 2; 9; 2; 9; 9; 0; 3; 1];
  ()

let reverse_add_450822227944_to_900544455998 () : Lemma (
    reverse_add #10 [4; 4; 9; 7; 2; 2; 2; 2; 8; 0; 5; 4] ==
      [8; 9; 9; 5; 5; 4; 4; 4; 5; 0; 0; 9]) =
  assert (trace_digits [4; 4; 9; 7; 2; 2; 2; 2; 8; 0; 5; 4] ==
    [8; 9; 9; 5; 5; 4; 4; 4; 5; 0; 0; 9]);
  trace_digits_equals_reverse_add [4; 4; 9; 7; 2; 2; 2; 2; 8; 0; 5; 4];
  ()

let reverse_add_900544455998_to_1800098901007 () : Lemma (
    reverse_add #10 [8; 9; 9; 5; 5; 4; 4; 4; 5; 0; 0; 9] ==
      [7; 0; 0; 1; 0; 9; 8; 9; 0; 0; 0; 8; 1]) =
  assert (trace_digits [8; 9; 9; 5; 5; 4; 4; 4; 5; 0; 0; 9] ==
    [7; 0; 0; 1; 0; 9; 8; 9; 0; 0; 0; 8; 1]);
  trace_digits_equals_reverse_add [8; 9; 9; 5; 5; 4; 4; 4; 5; 0; 0; 9];
  ()

let reverse_add_1800098901007_to_8801197801088 () : Lemma (
    reverse_add #10 [7; 0; 0; 1; 0; 9; 8; 9; 0; 0; 0; 8; 1] ==
      [8; 8; 0; 1; 0; 8; 7; 9; 1; 1; 0; 8; 8]) =
  assert (trace_digits [7; 0; 0; 1; 0; 9; 8; 9; 0; 0; 0; 8; 1] ==
    [8; 8; 0; 1; 0; 8; 7; 9; 1; 1; 0; 8; 8]);
  trace_digits_equals_reverse_add [7; 0; 0; 1; 0; 9; 8; 9; 0; 0; 0; 8; 1];
  ()

let reverse_add_8801197801088_to_17602285712176 () : Lemma (
    reverse_add #10 [8; 8; 0; 1; 0; 8; 7; 9; 1; 1; 0; 8; 8] ==
      [6; 7; 1; 2; 1; 7; 5; 8; 2; 2; 0; 6; 7; 1]) =
  assert (trace_digits [8; 8; 0; 1; 0; 8; 7; 9; 1; 1; 0; 8; 8] ==
    [6; 7; 1; 2; 1; 7; 5; 8; 2; 2; 0; 6; 7; 1]);
  trace_digits_equals_reverse_add [8; 8; 0; 1; 0; 8; 7; 9; 1; 1; 0; 8; 8];
  ()

let reverse_add_17602285712176_to_84724043932847 () : Lemma (
    reverse_add #10 [6; 7; 1; 2; 1; 7; 5; 8; 2; 2; 0; 6; 7; 1] ==
      [7; 4; 8; 2; 3; 9; 3; 4; 0; 4; 2; 7; 4; 8]) =
  assert (trace_digits [6; 7; 1; 2; 1; 7; 5; 8; 2; 2; 0; 6; 7; 1] ==
    [7; 4; 8; 2; 3; 9; 3; 4; 0; 4; 2; 7; 4; 8]);
  trace_digits_equals_reverse_add [6; 7; 1; 2; 1; 7; 5; 8; 2; 2; 0; 6; 7; 1];
  ()

let reverse_add_84724043932847_to_159547977975595 () : Lemma (
    reverse_add #10 [7; 4; 8; 2; 3; 9; 3; 4; 0; 4; 2; 7; 4; 8] ==
      [5; 9; 5; 5; 7; 9; 7; 7; 9; 7; 4; 5; 9; 5; 1]) =
  assert (trace_digits [7; 4; 8; 2; 3; 9; 3; 4; 0; 4; 2; 7; 4; 8] ==
    [5; 9; 5; 5; 7; 9; 7; 7; 9; 7; 4; 5; 9; 5; 1]);
  trace_digits_equals_reverse_add [7; 4; 8; 2; 3; 9; 3; 4; 0; 4; 2; 7; 4; 8];
  ()

let reverse_add_159547977975595_to_755127757721546 () : Lemma (
    reverse_add #10 [5; 9; 5; 5; 7; 9; 7; 7; 9; 7; 4; 5; 9; 5; 1] ==
      [6; 4; 5; 1; 2; 7; 7; 5; 7; 7; 2; 1; 5; 5; 7]) =
  assert (trace_digits [5; 9; 5; 5; 7; 9; 7; 7; 9; 7; 4; 5; 9; 5; 1] ==
    [6; 4; 5; 1; 2; 7; 7; 5; 7; 7; 2; 1; 5; 5; 7]);
  trace_digits_equals_reverse_add [5; 9; 5; 5; 7; 9; 7; 7; 9; 7; 4; 5; 9; 5; 1];
  ()

let reverse_add_755127757721546_to_1400255515443103 () : Lemma (
    reverse_add #10 [6; 4; 5; 1; 2; 7; 7; 5; 7; 7; 2; 1; 5; 5; 7] ==
      [3; 0; 1; 3; 4; 4; 5; 1; 5; 5; 5; 2; 0; 0; 4; 1]) =
  assert (trace_digits [6; 4; 5; 1; 2; 7; 7; 5; 7; 7; 2; 1; 5; 5; 7] ==
    [3; 0; 1; 3; 4; 4; 5; 1; 5; 5; 5; 2; 0; 0; 4; 1]);
  trace_digits_equals_reverse_add [6; 4; 5; 1; 2; 7; 7; 5; 7; 7; 2; 1; 5; 5; 7];
  ()

let reverse_add_1400255515443103_to_4413700670963144 () : Lemma (
    reverse_add #10 [3; 0; 1; 3; 4; 4; 5; 1; 5; 5; 5; 2; 0; 0; 4; 1] ==
      [4; 4; 1; 3; 6; 9; 0; 7; 6; 0; 0; 7; 3; 1; 4; 4]) =
  assert (trace_digits [3; 0; 1; 3; 4; 4; 5; 1; 5; 5; 5; 2; 0; 0; 4; 1] ==
    [4; 4; 1; 3; 6; 9; 0; 7; 6; 0; 0; 7; 3; 1; 4; 4]);
  trace_digits_equals_reverse_add [3; 0; 1; 3; 4; 4; 5; 1; 5; 5; 5; 2; 0; 0; 4; 1];
  ()

let trace_profile_facts_10755470 () : Lemma (
    trace_digits [0; 7; 4; 5; 5; 7; 0; 1] ==
      [1; 7; 1; 1; 1; 2; 8; 1] /\
    trace_carries [0; 7; 4; 5; 5; 7; 0; 1] ==
      [0; 0; 0; 1; 1; 1; 1; 0; 0] /\
    trace_sum_at [0; 7; 4; 5; 5; 7; 0; 1] 0 == 1 /\
    trace_sum_at [0; 7; 4; 5; 5; 7; 0; 1] 1 == 7 /\
    trace_sum_at [0; 7; 4; 5; 5; 7; 0; 1] 2 == 11 /\
    trace_sum_at [0; 7; 4; 5; 5; 7; 0; 1] 5 == 11) =
  assert (trace_digits [0; 7; 4; 5; 5; 7; 0; 1] ==
    [1; 7; 1; 1; 1; 2; 8; 1]);
  assert (trace_carries [0; 7; 4; 5; 5; 7; 0; 1] ==
    [0; 0; 0; 1; 1; 1; 1; 0; 0]);
  assert (trace_sum_at [0; 7; 4; 5; 5; 7; 0; 1] 0 == 1);
  assert (trace_sum_at [0; 7; 4; 5; 5; 7; 0; 1] 1 == 7);
  assert (trace_sum_at [0; 7; 4; 5; 5; 7; 0; 1] 2 == 11);
  assert (trace_sum_at [0; 7; 4; 5; 5; 7; 0; 1] 5 == 11);
  ()

let trace_profile_shape_10755470 () : Lemma (
    canonical #10 [0; 7; 4; 5; 5; 7; 0; 1] /\
    [0; 7; 4; 5; 5; 7; 0; 1] <> [] /\
    length [0; 7; 4; 5; 5; 7; 0; 1] == 8) =
  assert (canonical #10 [0; 7; 4; 5; 5; 7; 0; 1]);
  assert ([0; 7; 4; 5; 5; 7; 0; 1] <> []);
  assert (length [0; 7; 4; 5; 5; 7; 0; 1] == 8);
  ()

let trace_profile_facts_18211171 () : Lemma (
    trace_digits [1; 7; 1; 1; 1; 2; 8; 1] ==
      [2; 5; 4; 2; 2; 3; 5; 3] /\
    trace_carries [1; 7; 1; 1; 1; 2; 8; 1] ==
      [0; 0; 1; 0; 0; 0; 0; 1; 0] /\
    trace_sum_at [1; 7; 1; 1; 1; 2; 8; 1] 0 == 2 /\
    trace_sum_at [1; 7; 1; 1; 1; 2; 8; 1] 1 == 15) =
  assert (trace_digits [1; 7; 1; 1; 1; 2; 8; 1] ==
    [2; 5; 4; 2; 2; 3; 5; 3]);
  assert (trace_carries [1; 7; 1; 1; 1; 2; 8; 1] ==
    [0; 0; 1; 0; 0; 0; 0; 1; 0]);
  assert (trace_sum_at [1; 7; 1; 1; 1; 2; 8; 1] 0 == 2);
  assert (trace_sum_at [1; 7; 1; 1; 1; 2; 8; 1] 1 == 15);
  ()

let trace_profile_shape_18211171 () : Lemma (
    canonical #10 [1; 7; 1; 1; 1; 2; 8; 1] /\
    [1; 7; 1; 1; 1; 2; 8; 1] <> [] /\
    length [1; 7; 1; 1; 1; 2; 8; 1] == 8) =
  assert (canonical #10 [1; 7; 1; 1; 1; 2; 8; 1]);
  assert ([1; 7; 1; 1; 1; 2; 8; 1] <> []);
  assert (length [1; 7; 1; 1; 1; 2; 8; 1] == 8);
  ()

let trace_no_overflow_18211171 () : Lemma (
    length (trace_digits [1; 7; 1; 1; 1; 2; 8; 1]) ==
      length [1; 7; 1; 1; 1; 2; 8; 1] /\
    nth (trace_carries [1; 7; 1; 1; 1; 2; 8; 1])
      (length [1; 7; 1; 1; 1; 2; 8; 1]) == Some 0) =
  assert (length (trace_digits [1; 7; 1; 1; 1; 2; 8; 1]) ==
    length [1; 7; 1; 1; 1; 2; 8; 1]);
  assert (nth (trace_carries [1; 7; 1; 1; 1; 2; 8; 1])
    (length [1; 7; 1; 1; 1; 2; 8; 1]) == Some 0);
  ()
