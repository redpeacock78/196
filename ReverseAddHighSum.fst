module ReverseAddHighSum

open ReverseAdd
open ReverseAddCarry
open ReverseAddWitness
open FStar.Classical
open FStar.List.Tot

// If every preceding sum cell is below the base, no carry can enter cell i.
let rec trace_carry_prefix_zero
  (xs:numeral 10) (i:nat) : Lemma (requires (
      i <= length xs /\
      (forall j. j < i ==> trace_sum_at xs j < 10)))
    (ensures (trace_carry_at xs i == 0))
    (decreases i) =
  if i = 0 then
    ()
  else
    let j : nat = i - 1 in
    trace_carry_prefix_zero xs j;
    trace_equation_at xs j;
    assert (trace_sum_at xs j < 10);
    assert (trace_carry_at xs j == 0);
    assert (trace_carry_at xs (j + 1) == 0);
    assert (i == j + 1);
    ()

// A high sum at i+1 forces a carry at the mirrored cell, while the
// low-side prefix remains carry-free; this is an indexed obstruction.
let trace_no_overflow_high_sum_obstruction
  (xs:numeral 10) (i:nat) : Lemma (requires (
      xs <> [] /\
      length (trace_digits xs) == length xs /\
      nth (trace_carries xs) (length xs) == Some 0 /\
      i + 1 < length xs /\
      trace_sum_at xs (i + 1) >= 10 /\
      (forall j. j < i + 1 ==>
        trace_sum_at xs j < 10)))
    (ensures (trace_carry_obstruction_at xs i)) =
  trace_carry_prefix_zero xs i;
  trace_sum_symmetric_at xs (i + 1);
  let n : nat = length xs in
  let mirror : nat = n - 1 - (i + 1) in
  assert (mirror < n);
  trace_equation_at xs mirror;
  assert (trace_sum_at xs mirror >= 10);
  assert (trace_carry_at xs (mirror + 1) == 1);
  assert (mirror + 1 == n - 1 - i);
  assert (~ (trace_carry_at xs i ==
    trace_carry_at xs (n - 1 - i)));
  assert (trace_carry_obstruction_at xs i);
  ()

// A high sum cannot be the first cell of a no-overflow trace: its mirror
// would force the final carry to one.  Otherwise recurse to the first high
// cell and apply the indexed obstruction above.
let rec trace_no_overflow_high_sum_exists
  (xs:numeral 10) (h:nat) : Lemma (requires (
      xs <> [] /\
      length (trace_digits xs) == length xs /\
      nth (trace_carries xs) (length xs) == Some 0 /\
      h < length xs /\
      trace_sum_at xs h >= 10))
    (ensures (exists (i:nat).
      trace_palindrome_obstruction_at xs i))
    (decreases h) =
  if h = 0 then begin
    let n : nat = length xs in
    trace_sum_symmetric_at xs 0;
    assert (n > 0);
    trace_equation_at xs (n - 1);
    assert (n - 1 < n);
    assert (n - 1 + 1 == n);
    assert (trace_carry_at xs n == 0);
    assert (trace_sum_at xs (n - 1) >= 10);
    assert (trace_digit_at xs (n - 1) <= 9);
    assert (trace_carry_at xs (n - 1) >= 0);
    assert (trace_digit_at xs (n - 1) +
      10 * trace_carry_at xs n >= 10);
    assert (trace_carry_at xs n == 1);
    assert False
  end else begin
    assert (h > 0);
    assert ((forall j. j < h ==> trace_sum_at xs j < 10) \/
      ~(forall j. j < h ==> trace_sum_at xs j < 10));
    eliminate
      (forall j. j < h ==> trace_sum_at xs j < 10) \/
      ~(forall j. j < h ==> trace_sum_at xs j < 10)
    with (
      let i : nat = h - 1 in
      assert (i + 1 == h);
      assert (i + 1 < length xs);
      trace_no_overflow_high_sum_obstruction xs i;
      exists_intro
        (fun (i:nat) -> trace_palindrome_obstruction_at xs i) i;
      ())
    and (
      assert (~ (forall (j:nat). ~(
        j < h /\ trace_sum_at xs j >= 10)));
      not_forall_implies_exists #nat
        #(fun (j:nat) -> j < h /\ trace_sum_at xs j >= 10)
        ();
      eliminate exists (j:nat). j < h /\ trace_sum_at xs j >= 10
      with (
        trace_no_overflow_high_sum_exists xs j;
        ()))
  end

// In the no-overflow branch, a palindromic output therefore forces every
// mirrored input-digit sum below the base.
let trace_no_overflow_palindrome_implies_sum_low
  (xs:numeral 10) : Lemma (requires (
      xs <> [] /\
      length (trace_digits xs) == length xs /\
      nth (trace_carries xs) (length xs) == Some 0 /\
      trace_digits xs == rev (trace_digits xs)))
    (ensures (forall i. i < length xs ==>
      trace_sum_at xs i < 10)) =
  introduce forall (i:nat). i < length xs ==>
    trace_sum_at xs i < 10
  with (
    introduce (i < length xs) ==> (trace_sum_at xs i < 10)
    with (
      introduce (trace_sum_at xs i >= 10) ==> False
      with (
        trace_no_overflow_high_sum_exists xs i;
        eliminate exists (j:nat).
          trace_palindrome_obstruction_at xs j
        with (
          trace_palindrome_obstruction_at_excludes_palindrome xs j))))

// Conversely, if every mirrored input-digit sum stays below the base, no
// carry enters any cell and the output digits are mirrored.
let trace_no_overflow_low_sums_imply_digit_symmetry
  (xs:numeral 10) : Lemma (requires (
      xs <> [] /\
      length (trace_digits xs) == length xs /\
      nth (trace_carries xs) (length xs) == Some 0 /\
      (forall j. j < length xs ==> trace_sum_at xs j < 10)))
    (ensures (forall i. i < length xs ==>
      trace_digit_at xs i ==
        trace_digit_at xs (length xs - 1 - i))) =
  introduce forall (i:nat). i < length xs ==>
    trace_digit_at xs i == trace_digit_at xs (length xs - 1 - i)
  with (
    introduce (i < length xs) ==> _
    with (
      let mirror : nat = length xs - 1 - i in
      assert (mirror < length xs);
      trace_carry_prefix_zero xs i;
      trace_carry_prefix_zero xs (i + 1);
      trace_carry_prefix_zero xs mirror;
      trace_carry_prefix_zero xs (mirror + 1);
      trace_equation_at xs i;
      trace_equation_at xs mirror;
      trace_sum_symmetric_at xs i;
      assert (trace_carry_at xs i == 0);
      assert (trace_carry_at xs (i + 1) == 0);
      assert (trace_carry_at xs mirror == 0);
      assert (trace_carry_at xs (mirror + 1) == 0);
      assert (trace_digit_at xs i == trace_sum_at xs i);
      assert (trace_digit_at xs mirror == trace_sum_at xs mirror);
      assert (trace_digit_at xs i == trace_digit_at xs mirror);
      ()));
  ()

let high_sum_witness_1675 () : Lemma (
    trace_palindrome_obstruction_at [5; 7; 6; 1] 0) =
  assert (length (trace_digits [5; 7; 6; 1]) ==
    length [5; 7; 6; 1]);
  assert (nth (trace_carries [5; 7; 6; 1])
    (length [5; 7; 6; 1]) == Some 0);
  assert (trace_sum_at [5; 7; 6; 1] 1 >= 10);
  assert (trace_sum_at [5; 7; 6; 1] 0 < 10);
  assert (forall j. j < 1 ==> trace_sum_at [5; 7; 6; 1] j < 10);
  trace_no_overflow_high_sum_obstruction [5; 7; 6; 1] 0;
  ()
