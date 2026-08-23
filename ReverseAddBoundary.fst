module ReverseAddBoundary

#set-options "--fuel 10 --ifuel 10 --retry 10"

open ReverseAdd
open ReverseAddCarry
open ReverseAddWitness
open ReverseAddOverflowProfile
open FStar.Classical
open FStar.List.Tot

let trace_profile_60744805 () : Lemma (
    trace_digits [5; 0; 8; 4; 4; 7; 0; 6] ==
      [1; 1; 5; 9; 8; 5; 1; 1; 1] /\
    trace_carries [5; 0; 8; 4; 4; 7; 0; 6] ==
      [0; 1; 0; 1; 0; 0; 1; 0; 1] /\
    length (trace_digits [5; 0; 8; 4; 4; 7; 0; 6]) ==
      length [5; 0; 8; 4; 4; 7; 0; 6] + 1 /\
    nth (trace_carries [5; 0; 8; 4; 4; 7; 0; 6])
      (length [5; 0; 8; 4; 4; 7; 0; 6]) == Some 1 /\
    trace_sum_at [5; 0; 8; 4; 4; 7; 0; 6] 2 == 15 /\
    trace_sum_at [5; 0; 8; 4; 4; 7; 0; 6] 1 == 0) =
  assert (trace_digits [5; 0; 8; 4; 4; 7; 0; 6] ==
    [1; 1; 5; 9; 8; 5; 1; 1; 1]);
  assert (trace_carries [5; 0; 8; 4; 4; 7; 0; 6] ==
    [0; 1; 0; 1; 0; 0; 1; 0; 1]);
  ()

let trace_no_overflow_35322452 () : Lemma (
    length (trace_digits [2; 5; 4; 2; 2; 3; 5; 3]) ==
      length [2; 5; 4; 2; 2; 3; 5; 3] /\
    nth (trace_carries [2; 5; 4; 2; 2; 3; 5; 3])
      (length [2; 5; 4; 2; 2; 3; 5; 3]) == Some 0 /\
    trace_carry_at [2; 5; 4; 2; 2; 3; 5; 3] 7 == 1 /\
    trace_carry_at [2; 5; 4; 2; 2; 3; 5; 3]
      (length [2; 5; 4; 2; 2; 3; 5; 3] - 1) == 1) =
  assert (length (trace_digits [2; 5; 4; 2; 2; 3; 5; 3]) ==
    length [2; 5; 4; 2; 2; 3; 5; 3]);
  assert (nth (trace_carries [2; 5; 4; 2; 2; 3; 5; 3])
    (length [2; 5; 4; 2; 2; 3; 5; 3]) == Some 0);
  assert (trace_carry_at [2; 5; 4; 2; 2; 3; 5; 3] 0 == 0);
  assert (~ (trace_carry_at [2; 5; 4; 2; 2; 3; 5; 3] 0 ==
    trace_carry_at [2; 5; 4; 2; 2; 3; 5; 3] 7));
  assert (trace_carry_at [2; 5; 4; 2; 2; 3; 5; 3] 7 == 0 \/
    trace_carry_at [2; 5; 4; 2; 2; 3; 5; 3] 7 == 1);
  eliminate
    trace_carry_at [2; 5; 4; 2; 2; 3; 5; 3] 7 == 0 \/
      trace_carry_at [2; 5; 4; 2; 2; 3; 5; 3] 7 == 1
  with (
    assert False)
  and (
    assert (trace_carry_at [2; 5; 4; 2; 2; 3; 5; 3] 7 == 1));
  assert (length [2; 5; 4; 2; 2; 3; 5; 3] == 8);
  assert (length [2; 5; 4; 2; 2; 3; 5; 3] - 1 == 7);
  assert (trace_carry_at [2; 5; 4; 2; 2; 3; 5; 3]
    (length [2; 5; 4; 2; 2; 3; 5; 3] - 1) == 1);
  ()

let trace_outer_sum_35322452 () : Lemma (
    canonical #10 [2; 5; 4; 2; 2; 3; 5; 3] /\
    [2; 5; 4; 2; 2; 3; 5; 3] <> [] /\
    length (trace_digits [2; 5; 4; 2; 2; 3; 5; 3]) ==
      length [2; 5; 4; 2; 2; 3; 5; 3] /\
    nth (trace_carries [2; 5; 4; 2; 2; 3; 5; 3])
      (length [2; 5; 4; 2; 2; 3; 5; 3]) == Some 0 /\
    trace_sum_at [2; 5; 4; 2; 2; 3; 5; 3] 0 == 5 /\
    trace_carry_at [2; 5; 4; 2; 2; 3; 5; 3]
      (length [2; 5; 4; 2; 2; 3; 5; 3] - 1) == 1) =
  assert (canonical #10 [2; 5; 4; 2; 2; 3; 5; 3]);
  assert ([2; 5; 4; 2; 2; 3; 5; 3] <> []);
  let source : numeral 10 = [2; 5; 4; 2; 2; 3; 5; 3] in
  assert (source == [2; 5; 4; 2; 2; 3; 5; 3]);
  assert (source <> []);
  reverse_first_is_last #(digit 10) source;
  assert (nth (rev source) 0 == Some (last source));
  assert (last source == 3);
  assert (digit_at #10 source 0 == 2);
  assert (digit_at #10 (rev source) 0 == 3);
  assert (trace_sum_at source 0 ==
    digit_at #10 source 0 + digit_at #10 (rev source) 0);
  assert (trace_sum_at source 0 == 5);
  assert (trace_sum_at [2; 5; 4; 2; 2; 3; 5; 3] 0 == 5);
  trace_no_overflow_35322452 ();
  ()

let local_profile_witness_60744805 () : Lemma (
    trace_local_profile_complement_witness
      [5; 0; 8; 4; 4; 7; 0; 6]) =
  trace_outer_sum_35322452 ();
  reverse_add_35322452_to_60744805 ();
  trace_profile_60744805 ();
  assert (2 <= length (reverse_add #10 [2; 5; 4; 2; 2; 3; 5; 3]));
  assert (trace_sum_at (reverse_add #10 [2; 5; 4; 2; 2; 3; 5; 3]) 2 == 15);
  assert (trace_sum_at (reverse_add #10 [2; 5; 4; 2; 2; 3; 5; 3]) 1 == 0);
  assert (15 >= 0 + 12);
  assert (trace_sum_at (reverse_add #10 [2; 5; 4; 2; 2; 3; 5; 3]) 2 >=
    trace_sum_at (reverse_add #10 [2; 5; 4; 2; 2; 3; 5; 3]) 1 + 12);
  exists_intro
    (fun (i:nat) -> 0 < i /\
      i <= length (reverse_add #10 [2; 5; 4; 2; 2; 3; 5; 3]) /\
      (trace_sum_at (reverse_add #10 [2; 5; 4; 2; 2; 3; 5; 3]) i >=
         trace_sum_at (reverse_add #10 [2; 5; 4; 2; 2; 3; 5; 3]) (i - 1) + 12 \/
       trace_sum_at (reverse_add #10 [2; 5; 4; 2; 2; 3; 5; 3]) (i - 1) >=
         trace_sum_at (reverse_add #10 [2; 5; 4; 2; 2; 3; 5; 3]) i + 12))
    2;
  no_overflow_outer_sum_5_carry1_jump_implies_next_witness
    [2; 5; 4; 2; 2; 3; 5; 3];
  ()

// The following overflow step uses the internal-cell rule at i=3.
let trace_outer_sum_60744805 () : Lemma (
    canonical #10 [5; 0; 8; 4; 4; 7; 0; 6] /\
    [5; 0; 8; 4; 4; 7; 0; 6] <> [] /\
    length (trace_digits [5; 0; 8; 4; 4; 7; 0; 6]) ==
      length [5; 0; 8; 4; 4; 7; 0; 6] + 1 /\
    nth (trace_carries [5; 0; 8; 4; 4; 7; 0; 6])
      (length [5; 0; 8; 4; 4; 7; 0; 6]) == Some 1 /\
    1 <= trace_sum_at [5; 0; 8; 4; 4; 7; 0; 6] 0 /\
    trace_sum_at [5; 0; 8; 4; 4; 7; 0; 6] 0 <= 18 /\
    trace_sum_at [5; 0; 8; 4; 4; 7; 0; 6] 0 <> 10) =
  assert (canonical #10 [5; 0; 8; 4; 4; 7; 0; 6]);
  assert ([5; 0; 8; 4; 4; 7; 0; 6] <> []);
  let source : numeral 10 = [5; 0; 8; 4; 4; 7; 0; 6] in
  assert (source == [5; 0; 8; 4; 4; 7; 0; 6]);
  reverse_first_is_last #(digit 10) source;
  assert (nth (rev source) 0 == Some (last source));
  assert (last source == 6);
  assert (digit_at #10 source 0 == 5);
  assert (digit_at #10 (rev source) 0 == 6);
  assert (trace_sum_at source 0 ==
    digit_at #10 source 0 + digit_at #10 (rev source) 0);
  assert (trace_sum_at source 0 == 11);
  assert (trace_sum_at [5; 0; 8; 4; 4; 7; 0; 6] 0 == 11);
  trace_profile_60744805 ();
  ()

let local_profile_witness_111589511 () : Lemma (
    trace_local_profile_complement_witness
      [1; 1; 5; 9; 8; 5; 1; 1; 1]) =
  trace_outer_sum_60744805 ();
  trace_profile_60744805 ();
  assert (trace_sum_at [5; 0; 8; 4; 4; 7; 0; 6] 3 == 8);
  assert (trace_sum_at [5; 0; 8; 4; 4; 7; 0; 6] 5 == 15);
  reverse_add_60744805_to_111589511 ();
  exists_intro
    (fun (i:nat) -> 0 < i /\ i < length [5; 0; 8; 4; 4; 7; 0; 6] /\
      trace_sum_at [5; 0; 8; 4; 4; 7; 0; 6] i +
          trace_sum_at [5; 0; 8; 4; 4; 7; 0; 6]
            (length [5; 0; 8; 4; 4; 7; 0; 6] - i) +
          trace_carry_at [5; 0; 8; 4; 4; 7; 0; 6] i +
          trace_carry_at [5; 0; 8; 4; 4; 7; 0; 6]
            (length [5; 0; 8; 4; 4; 7; 0; 6] - i) >=
        10 + 10 *
          (trace_carry_at [5; 0; 8; 4; 4; 7; 0; 6] (i + 1) +
           trace_carry_at [5; 0; 8; 4; 4; 7; 0; 6]
             (length [5; 0; 8; 4; 4; 7; 0; 6] - i + 1)))
    3;
  overflow_internal_cell_implies_next_witness
    [5; 0; 8; 4; 4; 7; 0; 6];
  ()

let trace_profile_111589511 () : Lemma (
    trace_digits [1; 1; 5; 9; 8; 5; 1; 1; 1] ==
      [2; 2; 6; 4; 7; 5; 7; 2; 2] /\
    trace_carries [1; 1; 5; 9; 8; 5; 1; 1; 1] ==
      [0; 0; 0; 0; 1; 1; 1; 0; 0; 0] /\
    length (trace_digits [1; 1; 5; 9; 8; 5; 1; 1; 1]) ==
      length [1; 1; 5; 9; 8; 5; 1; 1; 1] /\
    nth (trace_carries [1; 1; 5; 9; 8; 5; 1; 1; 1])
      (length [1; 1; 5; 9; 8; 5; 1; 1; 1]) == Some 0 /\
    trace_sum_at [1; 1; 5; 9; 8; 5; 1; 1; 1] 0 == 2 /\
    trace_sum_at [1; 1; 5; 9; 8; 5; 1; 1; 1] 2 == 6) =
  assert (trace_digits [1; 1; 5; 9; 8; 5; 1; 1; 1] ==
    [2; 2; 6; 4; 7; 5; 7; 2; 2]);
  assert (trace_carries [1; 1; 5; 9; 8; 5; 1; 1; 1] ==
    [0; 0; 0; 0; 1; 1; 1; 0; 0; 0]);
  assert (trace_sum_at [1; 1; 5; 9; 8; 5; 1; 1; 1] 0 == 2);
  assert (trace_sum_at [1; 1; 5; 9; 8; 5; 1; 1; 1] 2 == 6);
  ()

let local_profile_witness_227574622 () : Lemma (
    trace_local_profile_complement_witness
      [2; 2; 6; 4; 7; 5; 7; 2; 2]) =
  assert (canonical #10 [1; 1; 5; 9; 8; 5; 1; 1; 1]);
  assert ([1; 1; 5; 9; 8; 5; 1; 1; 1] <> []);
  trace_profile_111589511 ();
  reverse_add_111589511_to_227574622 ();
  exists_intro
    (fun (i:nat) -> i < length [1; 1; 5; 9; 8; 5; 1; 1; 1] /\
      2 * trace_sum_at [1; 1; 5; 9; 8; 5; 1; 1; 1] i +
          trace_carry_at [1; 1; 5; 9; 8; 5; 1; 1; 1] i +
          trace_carry_at [1; 1; 5; 9; 8; 5; 1; 1; 1]
            (length [1; 1; 5; 9; 8; 5; 1; 1; 1] - 1 - i) >=
        10 + 10 *
          (trace_carry_at [1; 1; 5; 9; 8; 5; 1; 1; 1] (i + 1) +
           trace_carry_at [1; 1; 5; 9; 8; 5; 1; 1; 1]
             (length [1; 1; 5; 9; 8; 5; 1; 1; 1] - i)))
    2;
  no_overflow_outer_sum_1_to_4_cell_implies_next_witness
    [1; 1; 5; 9; 8; 5; 1; 1; 1];
  ()

let trace_profile_227574622 () : Lemma (
    trace_digits [2; 2; 6; 4; 7; 5; 7; 2; 2] ==
      [4; 4; 3; 0; 5; 0; 4; 5; 4] /\
    trace_carries [2; 2; 6; 4; 7; 5; 7; 2; 2] ==
      [0; 0; 0; 1; 1; 1; 1; 1; 0; 0] /\
    length (trace_digits [2; 2; 6; 4; 7; 5; 7; 2; 2]) ==
      length [2; 2; 6; 4; 7; 5; 7; 2; 2] /\
    nth (trace_carries [2; 2; 6; 4; 7; 5; 7; 2; 2])
      (length [2; 2; 6; 4; 7; 5; 7; 2; 2]) == Some 0 /\
    trace_sum_at [2; 2; 6; 4; 7; 5; 7; 2; 2] 0 == 4 /\
    trace_sum_at [2; 2; 6; 4; 7; 5; 7; 2; 2] 4 == 14) =
  assert (trace_digits [2; 2; 6; 4; 7; 5; 7; 2; 2] ==
    [4; 4; 3; 0; 5; 0; 4; 5; 4]);
  assert (trace_carries [2; 2; 6; 4; 7; 5; 7; 2; 2] ==
    [0; 0; 0; 1; 1; 1; 1; 1; 0; 0]);
  assert (trace_sum_at [2; 2; 6; 4; 7; 5; 7; 2; 2] 0 == 4);
  assert (trace_sum_at [2; 2; 6; 4; 7; 5; 7; 2; 2] 4 == 14);
  ()

let local_profile_witness_454050344 () : Lemma (
    trace_local_profile_complement_witness
      [4; 4; 3; 0; 5; 0; 4; 5; 4]) =
  assert (canonical #10 [2; 2; 6; 4; 7; 5; 7; 2; 2]);
  assert ([2; 2; 6; 4; 7; 5; 7; 2; 2] <> []);
  trace_profile_227574622 ();
  reverse_add_227574622_to_454050344 ();
  exists_intro
    (fun (i:nat) -> i < length [2; 2; 6; 4; 7; 5; 7; 2; 2] /\
      2 * trace_sum_at [2; 2; 6; 4; 7; 5; 7; 2; 2] i +
          trace_carry_at [2; 2; 6; 4; 7; 5; 7; 2; 2] i +
          trace_carry_at [2; 2; 6; 4; 7; 5; 7; 2; 2]
            (length [2; 2; 6; 4; 7; 5; 7; 2; 2] - 1 - i) >=
        10 + 10 *
          (trace_carry_at [2; 2; 6; 4; 7; 5; 7; 2; 2] (i + 1) +
           trace_carry_at [2; 2; 6; 4; 7; 5; 7; 2; 2]
             (length [2; 2; 6; 4; 7; 5; 7; 2; 2] - i)))
    4;
  no_overflow_outer_sum_1_to_4_cell_implies_next_witness
    [2; 2; 6; 4; 7; 5; 7; 2; 2];
  ()

let trace_profile_454050344 () : Lemma (
    trace_digits [4; 4; 3; 0; 5; 0; 4; 5; 4] ==
      [8; 9; 7; 0; 0; 1; 7; 9; 8] /\
    trace_carries [4; 4; 3; 0; 5; 0; 4; 5; 4] ==
      [0; 0; 0; 0; 0; 1; 0; 0; 0; 0] /\
    length (trace_digits [4; 4; 3; 0; 5; 0; 4; 5; 4]) ==
      length [4; 4; 3; 0; 5; 0; 4; 5; 4] /\
    nth (trace_carries [4; 4; 3; 0; 5; 0; 4; 5; 4])
      (length [4; 4; 3; 0; 5; 0; 4; 5; 4]) == Some 0 /\
    trace_sum_at [4; 4; 3; 0; 5; 0; 4; 5; 4] 0 == 8) =
  assert (trace_digits [4; 4; 3; 0; 5; 0; 4; 5; 4] ==
    [8; 9; 7; 0; 0; 1; 7; 9; 8]);
  assert (trace_carries [4; 4; 3; 0; 5; 0; 4; 5; 4] ==
    [0; 0; 0; 0; 0; 1; 0; 0; 0; 0]);
  assert (trace_sum_at [4; 4; 3; 0; 5; 0; 4; 5; 4] 0 == 8);
  ()

let local_profile_witness_897100798 () : Lemma (
    trace_local_profile_complement_witness
      [8; 9; 7; 0; 0; 1; 7; 9; 8]) =
  assert (canonical #10 [4; 4; 3; 0; 5; 0; 4; 5; 4]);
  assert ([4; 4; 3; 0; 5; 0; 4; 5; 4] <> []);
  trace_profile_454050344 ();
  reverse_add_454050344_to_897100798 ();
  no_overflow_outer_sum_6_to_9_implies_next_witness
    [4; 4; 3; 0; 5; 0; 4; 5; 4];
  ()

let trace_palindrome_obstruction_60744805 () : Lemma (
    trace_palindrome_obstruction [5; 0; 8; 4; 4; 7; 0; 6]) =
  trace_palindrome_obstruction_at_60744805 ();
  trace_palindrome_obstruction_at_sound
    [5; 0; 8; 4; 4; 7; 0; 6] 2;
  ()

let simple_trace_obstruction_fails_60744805 () : Lemma (
    ~ (trace_carry_obstruction [5; 0; 8; 4; 4; 7; 0; 6])) =
  assert (trace_digits [5; 0; 8; 4; 4; 7; 0; 6] ==
    [1; 1; 5; 9; 8; 5; 1; 1; 1]);
  assert (trace_carries [5; 0; 8; 4; 4; 7; 0; 6] ==
    [0; 1; 0; 1; 0; 0; 1; 0; 1]);
  assert (trace_digit_at [5; 0; 8; 4; 4; 7; 0; 6] 0 == 1);
  ()

let reverse_add_60744805_output_not_palindrome ()
  : Lemma (ensures (~ (palindrome #10
      (reverse_add [5; 0; 8; 4; 4; 7; 0; 6])))) =
  introduce (palindrome #10
      (reverse_add [5; 0; 8; 4; 4; 7; 0; 6])) ==> False
  with (
    assert (trace_digits [5; 0; 8; 4; 4; 7; 0; 6] ==
      reverse_add [5; 0; 8; 4; 4; 7; 0; 6]);
    trace_palindrome_obstruction_60744805 ();
    reverse_add_palindrome_obstruction_excludes_palindrome
      [5; 0; 8; 4; 4; 7; 0; 6])
