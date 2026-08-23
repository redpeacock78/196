module ReverseAddBoundary

#set-options "--fuel 20 --ifuel 20 --retry 10"

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

let trace_profile_897100798 () : Lemma (
    trace_digits [8; 9; 7; 0; 0; 1; 7; 9; 8] ==
      [6; 9; 5; 2; 0; 1; 4; 9; 7; 1] /\
    trace_carries [8; 9; 7; 0; 0; 1; 7; 9; 8] ==
      [0; 1; 1; 1; 0; 0; 0; 1; 1; 1] /\
    length (trace_digits [8; 9; 7; 0; 0; 1; 7; 9; 8]) ==
      length [8; 9; 7; 0; 0; 1; 7; 9; 8] + 1 /\
    nth (trace_carries [8; 9; 7; 0; 0; 1; 7; 9; 8])
      (length [8; 9; 7; 0; 0; 1; 7; 9; 8]) == Some 1 /\
    trace_sum_at [8; 9; 7; 0; 0; 1; 7; 9; 8] 0 == 16 /\
    trace_sum_at [8; 9; 7; 0; 0; 1; 7; 9; 8] 1 == 18) =
  assert (trace_digits [8; 9; 7; 0; 0; 1; 7; 9; 8] ==
    [6; 9; 5; 2; 0; 1; 4; 9; 7; 1]);
  assert (trace_carries [8; 9; 7; 0; 0; 1; 7; 9; 8] ==
    [0; 1; 1; 1; 0; 0; 0; 1; 1; 1]);
  assert (trace_sum_at [8; 9; 7; 0; 0; 1; 7; 9; 8] 0 == 16);
  assert (trace_sum_at [8; 9; 7; 0; 0; 1; 7; 9; 8] 1 == 18);
  ()

let local_profile_witness_1794102596 () : Lemma (
    trace_local_profile_complement_witness
      [6; 9; 5; 2; 0; 1; 4; 9; 7; 1]) =
  assert (canonical #10 [8; 9; 7; 0; 0; 1; 7; 9; 8]);
  assert ([8; 9; 7; 0; 0; 1; 7; 9; 8] <> []);
  trace_profile_897100798 ();
  reverse_add_897100798_to_1794102596 ();
  exists_intro
    (fun (i:nat) -> 0 < i /\ i < length [8; 9; 7; 0; 0; 1; 7; 9; 8] /\
      trace_sum_at [8; 9; 7; 0; 0; 1; 7; 9; 8] i +
          trace_sum_at [8; 9; 7; 0; 0; 1; 7; 9; 8]
            (length [8; 9; 7; 0; 0; 1; 7; 9; 8] - i) +
          trace_carry_at [8; 9; 7; 0; 0; 1; 7; 9; 8] i +
          trace_carry_at [8; 9; 7; 0; 0; 1; 7; 9; 8]
            (length [8; 9; 7; 0; 0; 1; 7; 9; 8] - i) >=
        10 + 10 *
          (trace_carry_at [8; 9; 7; 0; 0; 1; 7; 9; 8] (i + 1) +
           trace_carry_at [8; 9; 7; 0; 0; 1; 7; 9; 8]
             (length [8; 9; 7; 0; 0; 1; 7; 9; 8] - i + 1)))
    1;
  overflow_internal_cell_implies_next_witness
    [8; 9; 7; 0; 0; 1; 7; 9; 8];
  ()

let trace_profile_1794102596 () : Lemma (
    trace_digits [6; 9; 5; 2; 0; 1; 4; 9; 7; 1] ==
      [7; 6; 5; 7; 1; 1; 6; 4; 7; 8] /\
    trace_carries [6; 9; 5; 2; 0; 1; 4; 9; 7; 1] ==
      [0; 0; 1; 1; 0; 0; 0; 0; 1; 1; 0] /\
    length (trace_digits [6; 9; 5; 2; 0; 1; 4; 9; 7; 1]) ==
      length [6; 9; 5; 2; 0; 1; 4; 9; 7; 1] /\
    nth (trace_carries [6; 9; 5; 2; 0; 1; 4; 9; 7; 1])
      (length [6; 9; 5; 2; 0; 1; 4; 9; 7; 1]) == Some 0 /\
    trace_sum_at [6; 9; 5; 2; 0; 1; 4; 9; 7; 1] 0 == 7) =
  assert (trace_digits [6; 9; 5; 2; 0; 1; 4; 9; 7; 1] ==
    [7; 6; 5; 7; 1; 1; 6; 4; 7; 8]);
  assert (trace_carries [6; 9; 5; 2; 0; 1; 4; 9; 7; 1] ==
    [0; 0; 1; 1; 0; 0; 0; 0; 1; 1; 0]);
  assert (trace_sum_at [6; 9; 5; 2; 0; 1; 4; 9; 7; 1] 0 == 7);
  ()

let local_profile_witness_8746117567 () : Lemma (
    trace_local_profile_complement_witness
      [7; 6; 5; 7; 1; 1; 6; 4; 7; 8]) =
  assert (canonical #10 [6; 9; 5; 2; 0; 1; 4; 9; 7; 1]);
  assert ([6; 9; 5; 2; 0; 1; 4; 9; 7; 1] <> []);
  trace_profile_1794102596 ();
  reverse_add_1794102596_to_8746117567 ();
  no_overflow_outer_sum_6_to_9_implies_next_witness
    [6; 9; 5; 2; 0; 1; 4; 9; 7; 1];
  ()

let trace_profile_8746117567 () : Lemma (
    trace_digits [7; 6; 5; 7; 1; 1; 6; 4; 7; 8] ==
      [5; 4; 0; 4; 3; 2; 3; 0; 4; 6; 1] /\
    trace_carries [7; 6; 5; 7; 1; 1; 6; 4; 7; 8] ==
      [0; 1; 1; 1; 1; 0; 0; 1; 1; 1; 1] /\
    length (trace_digits [7; 6; 5; 7; 1; 1; 6; 4; 7; 8]) ==
      length [7; 6; 5; 7; 1; 1; 6; 4; 7; 8] + 1 /\
    nth (trace_carries [7; 6; 5; 7; 1; 1; 6; 4; 7; 8])
      (length [7; 6; 5; 7; 1; 1; 6; 4; 7; 8]) == Some 1 /\
    trace_sum_at [7; 6; 5; 7; 1; 1; 6; 4; 7; 8] 0 == 15 /\
    trace_sum_at [7; 6; 5; 7; 1; 1; 6; 4; 7; 8] 1 == 13) =
  assert (trace_digits [7; 6; 5; 7; 1; 1; 6; 4; 7; 8] ==
    [5; 4; 0; 4; 3; 2; 3; 0; 4; 6; 1]);
  assert (trace_carries [7; 6; 5; 7; 1; 1; 6; 4; 7; 8] ==
    [0; 1; 1; 1; 1; 0; 0; 1; 1; 1; 1]);
  assert (trace_sum_at [7; 6; 5; 7; 1; 1; 6; 4; 7; 8] 0 == 15);
  assert (trace_sum_at [7; 6; 5; 7; 1; 1; 6; 4; 7; 8] 1 == 13);
  ()

let local_profile_witness_16403234045 () : Lemma (
    trace_local_profile_complement_witness
      [5; 4; 0; 4; 3; 2; 3; 0; 4; 6; 1]) =
  let source : numeral 10 = [7; 6; 5; 7; 1; 1; 6; 4; 7; 8] in
  assert (source == [7; 6; 5; 7; 1; 1; 6; 4; 7; 8]);
  assert (canonical #10 source);
  assert (source <> []);
  trace_profile_8746117567 ();
  reverse_add_8746117567_to_16403234045 ();
  let n : nat = length source in
  exists_intro
    (fun (i:nat) -> 0 < i /\ i < n /\
      trace_sum_at source i + trace_sum_at source (n - i) +
          trace_carry_at source i + trace_carry_at source (n - i) >=
        10 + 10 *
          (trace_carry_at source (i + 1) +
           trace_carry_at source (n - i + 1)))
    1;
  overflow_internal_cell_implies_next_witness source;
  ()

let trace_profile_16403234045 () : Lemma (
    trace_digits [5; 4; 0; 4; 3; 2; 3; 0; 4; 6; 1] ==
      [6; 0; 5; 4; 6; 4; 6; 4; 4; 0; 7] /\
    trace_carries [5; 4; 0; 4; 3; 2; 3; 0; 4; 6; 1] ==
      [0; 0; 1; 0; 0; 0; 0; 0; 0; 0; 1; 0] /\
    length (trace_digits [5; 4; 0; 4; 3; 2; 3; 0; 4; 6; 1]) ==
      length [5; 4; 0; 4; 3; 2; 3; 0; 4; 6; 1] /\
    nth (trace_carries [5; 4; 0; 4; 3; 2; 3; 0; 4; 6; 1])
      (length [5; 4; 0; 4; 3; 2; 3; 0; 4; 6; 1]) == Some 0 /\
    trace_sum_at [5; 4; 0; 4; 3; 2; 3; 0; 4; 6; 1] 0 == 6) =
  assert (trace_digits [5; 4; 0; 4; 3; 2; 3; 0; 4; 6; 1] ==
    [6; 0; 5; 4; 6; 4; 6; 4; 4; 0; 7]);
  assert (trace_carries [5; 4; 0; 4; 3; 2; 3; 0; 4; 6; 1] ==
    [0; 0; 1; 0; 0; 0; 0; 0; 0; 0; 1; 0]);
  assert (trace_sum_at [5; 4; 0; 4; 3; 2; 3; 0; 4; 6; 1] 0 == 6);
  ()

let local_profile_witness_70446464506 () : Lemma (
    trace_local_profile_complement_witness
      [6; 0; 5; 4; 6; 4; 6; 4; 4; 0; 7]) =
  assert (canonical #10 [5; 4; 0; 4; 3; 2; 3; 0; 4; 6; 1]);
  assert ([5; 4; 0; 4; 3; 2; 3; 0; 4; 6; 1] <> []);
  trace_profile_16403234045 ();
  reverse_add_16403234045_to_70446464506 ();
  no_overflow_outer_sum_6_to_9_implies_next_witness
    [5; 4; 0; 4; 3; 2; 3; 0; 4; 6; 1];
  ()

let trace_profile_70446464506 () : Lemma (
    trace_digits [6; 0; 5; 4; 6; 4; 6; 4; 4; 0; 7] ==
      [3; 1; 9; 8; 2; 9; 2; 9; 9; 0; 3; 1] /\
    trace_carries [6; 0; 5; 4; 6; 4; 6; 4; 4; 0; 7] ==
      [0; 1; 0; 0; 0; 1; 0; 1; 0; 0; 0; 1] /\
    length (trace_digits [6; 0; 5; 4; 6; 4; 6; 4; 4; 0; 7]) ==
      length [6; 0; 5; 4; 6; 4; 6; 4; 4; 0; 7] + 1 /\
    nth (trace_carries [6; 0; 5; 4; 6; 4; 6; 4; 4; 0; 7])
      (length [6; 0; 5; 4; 6; 4; 6; 4; 4; 0; 7]) == Some 1 /\
    trace_sum_at [6; 0; 5; 4; 6; 4; 6; 4; 4; 0; 7] 0 == 13 /\
    trace_sum_at [6; 0; 5; 4; 6; 4; 6; 4; 4; 0; 7] 3 == 8 /\
    trace_sum_at [6; 0; 5; 4; 6; 4; 6; 4; 4; 0; 7] 8 == 9) =
  assert (trace_digits [6; 0; 5; 4; 6; 4; 6; 4; 4; 0; 7] ==
    [3; 1; 9; 8; 2; 9; 2; 9; 9; 0; 3; 1]);
  assert (trace_carries [6; 0; 5; 4; 6; 4; 6; 4; 4; 0; 7] ==
    [0; 1; 0; 0; 0; 1; 0; 1; 0; 0; 0; 1]);
  assert (trace_sum_at [6; 0; 5; 4; 6; 4; 6; 4; 4; 0; 7] 0 == 13);
  assert (trace_sum_at [6; 0; 5; 4; 6; 4; 6; 4; 4; 0; 7] 3 == 8);
  assert (trace_sum_at [6; 0; 5; 4; 6; 4; 6; 4; 4; 0; 7] 8 == 9);
  ()

let overflow_precondition_70446464506 () : Lemma (
    canonical #10 [6; 0; 5; 4; 6; 4; 6; 4; 4; 0; 7] /\
    [6; 0; 5; 4; 6; 4; 6; 4; 4; 0; 7] <> [] /\
    length (trace_digits [6; 0; 5; 4; 6; 4; 6; 4; 4; 0; 7]) ==
      length [6; 0; 5; 4; 6; 4; 6; 4; 4; 0; 7] + 1 /\
    nth (trace_carries [6; 0; 5; 4; 6; 4; 6; 4; 4; 0; 7])
      (length [6; 0; 5; 4; 6; 4; 6; 4; 4; 0; 7]) == Some 1 /\
    1 <= trace_sum_at [6; 0; 5; 4; 6; 4; 6; 4; 4; 0; 7] 0 /\
    trace_sum_at [6; 0; 5; 4; 6; 4; 6; 4; 4; 0; 7] 0 <= 18 /\
    trace_sum_at [6; 0; 5; 4; 6; 4; 6; 4; 4; 0; 7] 0 <> 10 /\
    exists (i:nat). 0 < i /\
      i < length [6; 0; 5; 4; 6; 4; 6; 4; 4; 0; 7] /\
      trace_sum_at [6; 0; 5; 4; 6; 4; 6; 4; 4; 0; 7] i +
          trace_sum_at [6; 0; 5; 4; 6; 4; 6; 4; 4; 0; 7]
            (length [6; 0; 5; 4; 6; 4; 6; 4; 4; 0; 7] - i) +
          trace_carry_at [6; 0; 5; 4; 6; 4; 6; 4; 4; 0; 7] i +
          trace_carry_at [6; 0; 5; 4; 6; 4; 6; 4; 4; 0; 7]
            (length [6; 0; 5; 4; 6; 4; 6; 4; 4; 0; 7] - i) >=
        10 + 10 *
          (trace_carry_at [6; 0; 5; 4; 6; 4; 6; 4; 4; 0; 7] (i + 1) +
           trace_carry_at [6; 0; 5; 4; 6; 4; 6; 4; 4; 0; 7]
             (length [6; 0; 5; 4; 6; 4; 6; 4; 4; 0; 7] - i + 1))) =
  trace_profile_70446464506 ();
  assert (canonical #10 [6; 0; 5; 4; 6; 4; 6; 4; 4; 0; 7]);
  assert ([6; 0; 5; 4; 6; 4; 6; 4; 4; 0; 7] <> []);
  let source : numeral 10 = [6; 0; 5; 4; 6; 4; 6; 4; 4; 0; 7] in
  let n : nat = length source in
  exists_intro
    (fun (i:nat) -> 0 < i /\ i < n /\
      trace_sum_at source i + trace_sum_at source (n - i) +
          trace_carry_at source i + trace_carry_at source (n - i) >=
        10 + 10 *
          (trace_carry_at source (i + 1) +
           trace_carry_at source (n - i + 1)))
    3;
  ()

let local_profile_witness_130992928913 () : Lemma (
    trace_local_profile_complement_witness
      [3; 1; 9; 8; 2; 9; 2; 9; 9; 0; 3; 1]) =
  let source : numeral 10 = [6; 0; 5; 4; 6; 4; 6; 4; 4; 0; 7] in
  assert (source == [6; 0; 5; 4; 6; 4; 6; 4; 4; 0; 7]);
  assert (canonical #10 source);
  assert (source <> []);
  overflow_precondition_70446464506 ();
  reverse_add_70446464506_to_130992928913 ();
  overflow_internal_cell_implies_next_witness
    [6; 0; 5; 4; 6; 4; 6; 4; 4; 0; 7];
  ()

let trace_profile_130992928913 () : Lemma (
    trace_digits [3; 1; 9; 8; 2; 9; 2; 9; 9; 0; 3; 1] ==
      [4; 4; 9; 7; 2; 2; 2; 2; 8; 0; 5; 4] /\
    trace_carries [3; 1; 9; 8; 2; 9; 2; 9; 9; 0; 3; 1] ==
      [0; 0; 0; 0; 1; 1; 1; 1; 1; 1; 1; 0; 0] /\
    length (trace_digits [3; 1; 9; 8; 2; 9; 2; 9; 9; 0; 3; 1]) ==
      length [3; 1; 9; 8; 2; 9; 2; 9; 9; 0; 3; 1] /\
    nth (trace_carries [3; 1; 9; 8; 2; 9; 2; 9; 9; 0; 3; 1])
      (length [3; 1; 9; 8; 2; 9; 2; 9; 9; 0; 3; 1]) == Some 0 /\
    trace_sum_at [3; 1; 9; 8; 2; 9; 2; 9; 9; 0; 3; 1] 0 == 4 /\
    trace_sum_at [3; 1; 9; 8; 2; 9; 2; 9; 9; 0; 3; 1] 3 == 17) =
  assert (trace_digits [3; 1; 9; 8; 2; 9; 2; 9; 9; 0; 3; 1] ==
    [4; 4; 9; 7; 2; 2; 2; 2; 8; 0; 5; 4]);
  assert (trace_carries [3; 1; 9; 8; 2; 9; 2; 9; 9; 0; 3; 1] ==
    [0; 0; 0; 0; 1; 1; 1; 1; 1; 1; 1; 0; 0]);
  assert (trace_sum_at [3; 1; 9; 8; 2; 9; 2; 9; 9; 0; 3; 1] 0 == 4);
  assert (trace_sum_at [3; 1; 9; 8; 2; 9; 2; 9; 9; 0; 3; 1] 3 == 17);
  ()

let local_profile_witness_450822227944 () : Lemma (
    trace_local_profile_complement_witness
      [4; 4; 9; 7; 2; 2; 2; 2; 8; 0; 5; 4]) =
  let source : numeral 10 = [3; 1; 9; 8; 2; 9; 2; 9; 9; 0; 3; 1] in
  assert (source == [3; 1; 9; 8; 2; 9; 2; 9; 9; 0; 3; 1]);
  assert (canonical #10 source);
  assert (source <> []);
  trace_profile_130992928913 ();
  reverse_add_130992928913_to_450822227944 ();
  let n : nat = length source in
  exists_intro
    (fun (i:nat) -> i < n /\
      2 * trace_sum_at source i +
          trace_carry_at source i +
          trace_carry_at source (n - 1 - i) >=
        10 + 10 *
          (trace_carry_at source (i + 1) +
           trace_carry_at source (n - i)))
    3;
  no_overflow_outer_sum_1_to_4_cell_implies_next_witness source;
  ()

let trace_profile_450822227944 () : Lemma (
    trace_digits [4; 4; 9; 7; 2; 2; 2; 2; 8; 0; 5; 4] ==
      [8; 9; 9; 5; 5; 4; 4; 4; 5; 0; 0; 9] /\
    trace_carries [4; 4; 9; 7; 2; 2; 2; 2; 8; 0; 5; 4] ==
      [0; 0; 0; 0; 1; 0; 0; 0; 0; 1; 1; 1; 0] /\
    length (trace_digits [4; 4; 9; 7; 2; 2; 2; 2; 8; 0; 5; 4]) ==
      length [4; 4; 9; 7; 2; 2; 2; 2; 8; 0; 5; 4] /\
    nth (trace_carries [4; 4; 9; 7; 2; 2; 2; 2; 8; 0; 5; 4])
      (length [4; 4; 9; 7; 2; 2; 2; 2; 8; 0; 5; 4]) == Some 0 /\
    trace_sum_at [4; 4; 9; 7; 2; 2; 2; 2; 8; 0; 5; 4] 0 == 8) =
  assert (trace_digits [4; 4; 9; 7; 2; 2; 2; 2; 8; 0; 5; 4] ==
    [8; 9; 9; 5; 5; 4; 4; 4; 5; 0; 0; 9]);
  assert (trace_carries [4; 4; 9; 7; 2; 2; 2; 2; 8; 0; 5; 4] ==
    [0; 0; 0; 0; 1; 0; 0; 0; 0; 1; 1; 1; 0]);
  assert (trace_sum_at [4; 4; 9; 7; 2; 2; 2; 2; 8; 0; 5; 4] 0 == 8);
  ()

let local_profile_witness_900544455998 () : Lemma (
    trace_local_profile_complement_witness
      [8; 9; 9; 5; 5; 4; 4; 4; 5; 0; 0; 9]) =
  assert (canonical #10 [4; 4; 9; 7; 2; 2; 2; 2; 8; 0; 5; 4]);
  assert ([4; 4; 9; 7; 2; 2; 2; 2; 8; 0; 5; 4] <> []);
  trace_profile_450822227944 ();
  reverse_add_450822227944_to_900544455998 ();
  no_overflow_outer_sum_6_to_9_implies_next_witness
    [4; 4; 9; 7; 2; 2; 2; 2; 8; 0; 5; 4];
  ()

let trace_profile_900544455998 () : Lemma (
    trace_digits [8; 9; 9; 5; 5; 4; 4; 4; 5; 0; 0; 9] ==
      [7; 0; 0; 1; 0; 9; 8; 9; 0; 0; 0; 8; 1] /\
    trace_carries [8; 9; 9; 5; 5; 4; 4; 4; 5; 0; 0; 9] ==
      [0; 1; 1; 1; 1; 1; 0; 0; 0; 1; 1; 1; 1] /\
    length (trace_digits [8; 9; 9; 5; 5; 4; 4; 4; 5; 0; 0; 9]) ==
      length [8; 9; 9; 5; 5; 4; 4; 4; 5; 0; 0; 9] + 1 /\
    nth (trace_carries [8; 9; 9; 5; 5; 4; 4; 4; 5; 0; 0; 9])
      (length [8; 9; 9; 5; 5; 4; 4; 4; 5; 0; 0; 9]) == Some 1 /\
    trace_sum_at [8; 9; 9; 5; 5; 4; 4; 4; 5; 0; 0; 9] 0 == 17 /\
    trace_sum_at [8; 9; 9; 5; 5; 4; 4; 4; 5; 0; 0; 9] 5 == 8 /\
    trace_sum_at [8; 9; 9; 5; 5; 4; 4; 4; 5; 0; 0; 9] 7 == 9) =
  assert (trace_digits [8; 9; 9; 5; 5; 4; 4; 4; 5; 0; 0; 9] ==
    [7; 0; 0; 1; 0; 9; 8; 9; 0; 0; 0; 8; 1]);
  assert (trace_carries [8; 9; 9; 5; 5; 4; 4; 4; 5; 0; 0; 9] ==
    [0; 1; 1; 1; 1; 1; 0; 0; 0; 1; 1; 1; 1]);
  assert (trace_sum_at [8; 9; 9; 5; 5; 4; 4; 4; 5; 0; 0; 9] 0 == 17);
  assert (trace_sum_at [8; 9; 9; 5; 5; 4; 4; 4; 5; 0; 0; 9] 5 == 8);
  assert (trace_sum_at [8; 9; 9; 5; 5; 4; 4; 4; 5; 0; 0; 9] 7 == 9);
  ()

let overflow_precondition_900544455998 () : Lemma (
    canonical #10 [8; 9; 9; 5; 5; 4; 4; 4; 5; 0; 0; 9] /\
    [8; 9; 9; 5; 5; 4; 4; 4; 5; 0; 0; 9] <> [] /\
    length (trace_digits [8; 9; 9; 5; 5; 4; 4; 4; 5; 0; 0; 9]) ==
      length [8; 9; 9; 5; 5; 4; 4; 4; 5; 0; 0; 9] + 1 /\
    nth (trace_carries [8; 9; 9; 5; 5; 4; 4; 4; 5; 0; 0; 9])
      (length [8; 9; 9; 5; 5; 4; 4; 4; 5; 0; 0; 9]) == Some 1 /\
    1 <= trace_sum_at [8; 9; 9; 5; 5; 4; 4; 4; 5; 0; 0; 9] 0 /\
    trace_sum_at [8; 9; 9; 5; 5; 4; 4; 4; 5; 0; 0; 9] 0 <= 18 /\
    trace_sum_at [8; 9; 9; 5; 5; 4; 4; 4; 5; 0; 0; 9] 0 <> 10 /\
    exists (i:nat). 0 < i /\
      i < length [8; 9; 9; 5; 5; 4; 4; 4; 5; 0; 0; 9] /\
      trace_sum_at [8; 9; 9; 5; 5; 4; 4; 4; 5; 0; 0; 9] i +
          trace_sum_at [8; 9; 9; 5; 5; 4; 4; 4; 5; 0; 0; 9]
            (length [8; 9; 9; 5; 5; 4; 4; 4; 5; 0; 0; 9] - i) +
          trace_carry_at [8; 9; 9; 5; 5; 4; 4; 4; 5; 0; 0; 9] i +
          trace_carry_at [8; 9; 9; 5; 5; 4; 4; 4; 5; 0; 0; 9]
            (length [8; 9; 9; 5; 5; 4; 4; 4; 5; 0; 0; 9] - i) >=
        10 + 10 *
          (trace_carry_at [8; 9; 9; 5; 5; 4; 4; 4; 5; 0; 0; 9] (i + 1) +
           trace_carry_at [8; 9; 9; 5; 5; 4; 4; 4; 5; 0; 0; 9]
             (length [8; 9; 9; 5; 5; 4; 4; 4; 5; 0; 0; 9] - i + 1))) =
  trace_profile_900544455998 ();
  assert (canonical #10 [8; 9; 9; 5; 5; 4; 4; 4; 5; 0; 0; 9]);
  assert ([8; 9; 9; 5; 5; 4; 4; 4; 5; 0; 0; 9] <> []);
  let source : numeral 10 = [8; 9; 9; 5; 5; 4; 4; 4; 5; 0; 0; 9] in
  let n : nat = length source in
  exists_intro
    (fun (i:nat) -> 0 < i /\ i < n /\
      trace_sum_at source i + trace_sum_at source (n - i) +
          trace_carry_at source i + trace_carry_at source (n - i) >=
        10 + 10 *
          (trace_carry_at source (i + 1) +
           trace_carry_at source (n - i + 1)))
    5;
  ()

let local_profile_witness_1800098901007 () : Lemma (
    trace_local_profile_complement_witness
      [7; 0; 0; 1; 0; 9; 8; 9; 0; 0; 0; 8; 1]) =
  overflow_precondition_900544455998 ();
  reverse_add_900544455998_to_1800098901007 ();
  overflow_internal_cell_implies_next_witness
    [8; 9; 9; 5; 5; 4; 4; 4; 5; 0; 0; 9];
  ()

let trace_profile_1800098901007 () : Lemma (
    trace_digits [7; 0; 0; 1; 0; 9; 8; 9; 0; 0; 0; 8; 1] ==
      [8; 8; 0; 1; 0; 8; 7; 9; 1; 1; 0; 8; 8] /\
    trace_carries [7; 0; 0; 1; 0; 9; 8; 9; 0; 0; 0; 8; 1] ==
      [0; 0; 0; 0; 0; 0; 1; 1; 1; 0; 0; 0; 0; 0] /\
    length (trace_digits [7; 0; 0; 1; 0; 9; 8; 9; 0; 0; 0; 8; 1]) ==
      length [7; 0; 0; 1; 0; 9; 8; 9; 0; 0; 0; 8; 1] /\
    nth (trace_carries [7; 0; 0; 1; 0; 9; 8; 9; 0; 0; 0; 8; 1])
      (length [7; 0; 0; 1; 0; 9; 8; 9; 0; 0; 0; 8; 1]) == Some 0 /\
    trace_sum_at [7; 0; 0; 1; 0; 9; 8; 9; 0; 0; 0; 8; 1] 0 == 8) =
  assert (trace_digits [7; 0; 0; 1; 0; 9; 8; 9; 0; 0; 0; 8; 1] ==
    [8; 8; 0; 1; 0; 8; 7; 9; 1; 1; 0; 8; 8]);
  assert (trace_carries [7; 0; 0; 1; 0; 9; 8; 9; 0; 0; 0; 8; 1] ==
    [0; 0; 0; 0; 0; 0; 1; 1; 1; 0; 0; 0; 0; 0]);
  assert (trace_sum_at [7; 0; 0; 1; 0; 9; 8; 9; 0; 0; 0; 8; 1] 0 == 8);
  ()

let local_profile_witness_8801197801088 () : Lemma (
    trace_local_profile_complement_witness
      [8; 8; 0; 1; 0; 8; 7; 9; 1; 1; 0; 8; 8]) =
  assert (canonical #10 [7; 0; 0; 1; 0; 9; 8; 9; 0; 0; 0; 8; 1]);
  assert ([7; 0; 0; 1; 0; 9; 8; 9; 0; 0; 0; 8; 1] <> []);
  trace_profile_1800098901007 ();
  reverse_add_1800098901007_to_8801197801088 ();
  no_overflow_outer_sum_6_to_9_implies_next_witness
    [7; 0; 0; 1; 0; 9; 8; 9; 0; 0; 0; 8; 1];
  ()

let trace_profile_8801197801088 () : Lemma (
    trace_digits [8; 8; 0; 1; 0; 8; 7; 9; 1; 1; 0; 8; 8] ==
      [6; 7; 1; 2; 1; 7; 5; 8; 2; 2; 0; 6; 7; 1] /\
    trace_carries [8; 8; 0; 1; 0; 8; 7; 9; 1; 1; 0; 8; 8] ==
      [0; 1; 1; 0; 0; 0; 1; 1; 1; 0; 0; 0; 1; 1] /\
    length (trace_digits [8; 8; 0; 1; 0; 8; 7; 9; 1; 1; 0; 8; 8]) ==
      length [8; 8; 0; 1; 0; 8; 7; 9; 1; 1; 0; 8; 8] + 1 /\
    nth (trace_carries [8; 8; 0; 1; 0; 8; 7; 9; 1; 1; 0; 8; 8])
      (length [8; 8; 0; 1; 0; 8; 7; 9; 1; 1; 0; 8; 8]) == Some 1 /\
    trace_sum_at [8; 8; 0; 1; 0; 8; 7; 9; 1; 1; 0; 8; 8] 0 == 16 /\
    trace_sum_at [8; 8; 0; 1; 0; 8; 7; 9; 1; 1; 0; 8; 8] 1 == 16) =
  assert (trace_digits [8; 8; 0; 1; 0; 8; 7; 9; 1; 1; 0; 8; 8] ==
    [6; 7; 1; 2; 1; 7; 5; 8; 2; 2; 0; 6; 7; 1]);
  assert (trace_carries [8; 8; 0; 1; 0; 8; 7; 9; 1; 1; 0; 8; 8] ==
    [0; 1; 1; 0; 0; 0; 1; 1; 1; 0; 0; 0; 1; 1]);
  assert (trace_sum_at [8; 8; 0; 1; 0; 8; 7; 9; 1; 1; 0; 8; 8] 0 == 16);
  assert (trace_sum_at [8; 8; 0; 1; 0; 8; 7; 9; 1; 1; 0; 8; 8] 1 == 16);
  ()

let overflow_precondition_8801197801088 () : Lemma (
    canonical #10 [8; 8; 0; 1; 0; 8; 7; 9; 1; 1; 0; 8; 8] /\
    [8; 8; 0; 1; 0; 8; 7; 9; 1; 1; 0; 8; 8] <> [] /\
    length (trace_digits [8; 8; 0; 1; 0; 8; 7; 9; 1; 1; 0; 8; 8]) ==
      length [8; 8; 0; 1; 0; 8; 7; 9; 1; 1; 0; 8; 8] + 1 /\
    nth (trace_carries [8; 8; 0; 1; 0; 8; 7; 9; 1; 1; 0; 8; 8])
      (length [8; 8; 0; 1; 0; 8; 7; 9; 1; 1; 0; 8; 8]) == Some 1 /\
    1 <= trace_sum_at [8; 8; 0; 1; 0; 8; 7; 9; 1; 1; 0; 8; 8] 0 /\
    trace_sum_at [8; 8; 0; 1; 0; 8; 7; 9; 1; 1; 0; 8; 8] 0 <= 18 /\
    trace_sum_at [8; 8; 0; 1; 0; 8; 7; 9; 1; 1; 0; 8; 8] 0 <> 10 /\
    exists (i:nat). 0 < i /\
      i < length [8; 8; 0; 1; 0; 8; 7; 9; 1; 1; 0; 8; 8] /\
      trace_sum_at [8; 8; 0; 1; 0; 8; 7; 9; 1; 1; 0; 8; 8] i +
          trace_sum_at [8; 8; 0; 1; 0; 8; 7; 9; 1; 1; 0; 8; 8]
            (length [8; 8; 0; 1; 0; 8; 7; 9; 1; 1; 0; 8; 8] - i) +
          trace_carry_at [8; 8; 0; 1; 0; 8; 7; 9; 1; 1; 0; 8; 8] i +
          trace_carry_at [8; 8; 0; 1; 0; 8; 7; 9; 1; 1; 0; 8; 8]
            (length [8; 8; 0; 1; 0; 8; 7; 9; 1; 1; 0; 8; 8] - i) >=
        10 + 10 *
          (trace_carry_at [8; 8; 0; 1; 0; 8; 7; 9; 1; 1; 0; 8; 8] (i + 1) +
           trace_carry_at [8; 8; 0; 1; 0; 8; 7; 9; 1; 1; 0; 8; 8]
             (length [8; 8; 0; 1; 0; 8; 7; 9; 1; 1; 0; 8; 8] - i + 1))) =
  trace_profile_8801197801088 ();
  assert (canonical #10 [8; 8; 0; 1; 0; 8; 7; 9; 1; 1; 0; 8; 8]);
  assert ([8; 8; 0; 1; 0; 8; 7; 9; 1; 1; 0; 8; 8] <> []);
  let source : numeral 10 = [8; 8; 0; 1; 0; 8; 7; 9; 1; 1; 0; 8; 8] in
  let n : nat = length source in
  exists_intro
    (fun (i:nat) -> 0 < i /\ i < n /\
      trace_sum_at source i + trace_sum_at source (n - i) +
          trace_carry_at source i + trace_carry_at source (n - i) >=
        10 + 10 *
          (trace_carry_at source (i + 1) +
           trace_carry_at source (n - i + 1)))
    1;
  ()

let local_profile_witness_17602285712176 () : Lemma (
    trace_local_profile_complement_witness
      [6; 7; 1; 2; 1; 7; 5; 8; 2; 2; 0; 6; 7; 1]) =
  overflow_precondition_8801197801088 ();
  reverse_add_8801197801088_to_17602285712176 ();
  overflow_internal_cell_implies_next_witness
    [8; 8; 0; 1; 0; 8; 7; 9; 1; 1; 0; 8; 8];
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
