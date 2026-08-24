module ReverseAddContinuation

#set-options "--fuel 100 --ifuel 100 --retry 10"

open ReverseAdd
open ReverseAddCarry
open ReverseAddWitness
open FStar.List.Tot

let source_3603815405135183953 : numeral 10 =
  [3; 5; 9; 3; 8; 1; 5; 3; 1; 5; 0; 4; 5; 1; 8; 3; 0; 6; 3]

let source_7197630720180367016 : numeral 10 =
  [6; 1; 0; 7; 6; 3; 0; 8; 1; 0; 2; 7; 0; 3; 6; 7; 9; 1; 7]

let source_13305261530450734933 : numeral 10 =
  [3; 3; 9; 4; 3; 7; 0; 5; 4; 0; 3; 5; 1; 6; 2; 5; 0; 3; 3; 1]

let source_47248966933966985264 : numeral 10 =
  [4; 6; 2; 5; 8; 9; 6; 6; 9; 3; 3; 9; 6; 6; 9; 8; 4; 2; 7; 4]

let reverse_list_3603815405135183953 () : Lemma (
    rev source_3603815405135183953 ==
      [3; 6; 0; 3; 8; 1; 5; 4; 0; 5; 1; 3; 5; 1; 8; 3; 9; 5; 3]) =
  assert (rev source_3603815405135183953 ==
    [3; 6; 0; 3; 8; 1; 5; 4; 0; 5; 1; 3; 5; 1; 8; 3; 9; 5; 3]);
  ()

let reverse_list_7197630720180367016 () : Lemma (
    rev source_7197630720180367016 ==
      [7; 1; 9; 7; 6; 3; 0; 7; 2; 0; 1; 8; 0; 3; 6; 7; 0; 1; 6]) =
  assert (rev source_7197630720180367016 ==
    [7; 1; 9; 7; 6; 3; 0; 7; 2; 0; 1; 8; 0; 3; 6; 7; 0; 1; 6]);
  ()

let reverse_list_13305261530450734933 () : Lemma (
    rev source_13305261530450734933 ==
      [1; 3; 3; 0; 5; 2; 6; 1; 5; 3; 0; 4; 5; 0; 7; 3; 4; 9; 3; 3]) =
  assert (rev source_13305261530450734933 ==
    [1; 3; 3; 0; 5; 2; 6; 1; 5; 3; 0; 4; 5; 0; 7; 3; 4; 9; 3; 3]);
  ()

let reverse_list_47248966933966985264 () : Lemma (
    rev source_47248966933966985264 ==
      [4; 7; 2; 4; 8; 9; 6; 6; 9; 3; 3; 9; 6; 6; 9; 8; 5; 2; 6; 4]) =
  assert (rev source_47248966933966985264 ==
    [4; 7; 2; 4; 8; 9; 6; 6; 9; 3; 3; 9; 6; 6; 9; 8; 5; 2; 6; 4]);
  ()

let canonical_13305261530450734933 () : Lemma (
    canonical #10 source_13305261530450734933 /\
    source_13305261530450734933 <> []) =
  assert (canonical #10 [1]);
  canonical_cons #10 3 [1];
  canonical_cons #10 3 [3; 1];
  canonical_cons #10 0 [3; 3; 1];
  canonical_cons #10 5 [0; 3; 3; 1];
  canonical_cons #10 2 [5; 0; 3; 3; 1];
  canonical_cons #10 6 [2; 5; 0; 3; 3; 1];
  canonical_cons #10 1 [6; 2; 5; 0; 3; 3; 1];
  canonical_cons #10 5 [1; 6; 2; 5; 0; 3; 3; 1];
  canonical_cons #10 3 [5; 1; 6; 2; 5; 0; 3; 3; 1];
  canonical_cons #10 0 [3; 5; 1; 6; 2; 5; 0; 3; 3; 1];
  canonical_cons #10 4 [0; 3; 5; 1; 6; 2; 5; 0; 3; 3; 1];
  canonical_cons #10 5 [4; 0; 3; 5; 1; 6; 2; 5; 0; 3; 3; 1];
  canonical_cons #10 0 [5; 4; 0; 3; 5; 1; 6; 2; 5; 0; 3; 3; 1];
  canonical_cons #10 7 [0; 5; 4; 0; 3; 5; 1; 6; 2; 5; 0; 3; 3; 1];
  canonical_cons #10 3 [7; 0; 5; 4; 0; 3; 5; 1; 6; 2; 5; 0; 3; 3; 1];
  canonical_cons #10 4 [3; 7; 0; 5; 4; 0; 3; 5; 1; 6; 2; 5; 0; 3; 3; 1];
  canonical_cons #10 9 [4; 3; 7; 0; 5; 4; 0; 3; 5; 1; 6; 2; 5; 0; 3; 3; 1];
  canonical_cons #10 3 [9; 4; 3; 7; 0; 5; 4; 0; 3; 5; 1; 6; 2; 5; 0; 3; 3; 1];
  canonical_cons #10 3 [3; 9; 4; 3; 7; 0; 5; 4; 0; 3; 5; 1; 6; 2; 5; 0; 3; 3; 1];
  assert (source_13305261530450734933 <> []);
  ()

let canonical_47248966933966985264 () : Lemma (
    canonical #10 source_47248966933966985264 /\
    source_47248966933966985264 <> []) =
  assert (canonical #10 [4]);
  canonical_cons #10 7 [4];
  canonical_cons #10 2 [7; 4];
  canonical_cons #10 4 [2; 7; 4];
  canonical_cons #10 8 [4; 2; 7; 4];
  canonical_cons #10 9 [8; 4; 2; 7; 4];
  canonical_cons #10 6 [9; 8; 4; 2; 7; 4];
  canonical_cons #10 6 [6; 9; 8; 4; 2; 7; 4];
  canonical_cons #10 9 [6; 6; 9; 8; 4; 2; 7; 4];
  canonical_cons #10 3 [9; 6; 6; 9; 8; 4; 2; 7; 4];
  canonical_cons #10 3 [3; 9; 6; 6; 9; 8; 4; 2; 7; 4];
  canonical_cons #10 9 [3; 3; 9; 6; 6; 9; 8; 4; 2; 7; 4];
  canonical_cons #10 6 [9; 3; 3; 9; 6; 6; 9; 8; 4; 2; 7; 4];
  canonical_cons #10 6 [6; 9; 3; 3; 9; 6; 6; 9; 8; 4; 2; 7; 4];
  canonical_cons #10 9 [6; 6; 9; 3; 3; 9; 6; 6; 9; 8; 4; 2; 7; 4];
  canonical_cons #10 8 [9; 6; 6; 9; 3; 3; 9; 6; 6; 9; 8; 4; 2; 7; 4];
  canonical_cons #10 5 [8; 9; 6; 6; 9; 3; 3; 9; 6; 6; 9; 8; 4; 2; 7; 4];
  canonical_cons #10 2 [5; 8; 9; 6; 6; 9; 3; 3; 9; 6; 6; 9; 8; 4; 2; 7; 4];
  canonical_cons #10 6 [2; 5; 8; 9; 6; 6; 9; 3; 3; 9; 6; 6; 9; 8; 4; 2; 7; 4];
  canonical_cons #10 4 [6; 2; 5; 8; 9; 6; 6; 9; 3; 3; 9; 6; 6; 9; 8; 4; 2; 7; 4];
  assert (source_47248966933966985264 <> []);
  ()

let reverse_add_3603815405135183953_to_7197630720180367016 () : Lemma (
    reverse_add #10 source_3603815405135183953 ==
      [6; 1; 0; 7; 6; 3; 0; 8; 1; 0; 2; 7; 0; 3; 6; 7; 9; 1; 7]) =
  assert (canonical #10 source_3603815405135183953);
  assert (source_3603815405135183953 <> []);
  trace_digits_equals_reverse_add source_3603815405135183953;
  assert (trace_digits source_3603815405135183953 ==
    [6; 1; 0; 7; 6; 3; 0; 8; 1; 0; 2; 7; 0; 3; 6; 7; 9; 1; 7]);
  assert (trace_digits source_3603815405135183953 ==
    reverse_add #10 source_3603815405135183953);
  ()

let reverse_add_7197630720180367016_to_13305261530450734933 () : Lemma (
    reverse_add #10 source_7197630720180367016 ==
      [3; 3; 9; 4; 3; 7; 0; 5; 4; 0; 3; 5; 1; 6; 2; 5; 0; 3; 3; 1]) =
  assert (canonical #10 source_7197630720180367016);
  assert (source_7197630720180367016 <> []);
  trace_digits_equals_reverse_add source_7197630720180367016;
  assert (trace_digits source_7197630720180367016 ==
    [3; 3; 9; 4; 3; 7; 0; 5; 4; 0; 3; 5; 1; 6; 2; 5; 0; 3; 3; 1]);
  assert (trace_digits source_7197630720180367016 ==
    reverse_add #10 source_7197630720180367016);
  ()

let reverse_add_13305261530450734933_to_47248966933966985264 () : Lemma (
    reverse_add #10 source_13305261530450734933 ==
      [4; 6; 2; 5; 8; 9; 6; 6; 9; 3; 3; 9; 6; 6; 9; 8; 4; 2; 7; 4]) =
  canonical_13305261530450734933 ();
  trace_digits_equals_reverse_add source_13305261530450734933;
  assert (trace_digits source_13305261530450734933 ==
    [4; 6; 2; 5; 8; 9; 6; 6; 9; 3; 3; 9; 6; 6; 9; 8; 4; 2; 7; 4]);
  assert (trace_digits source_13305261530450734933 ==
    reverse_add #10 source_13305261530450734933);
  ()

let reverse_add_47248966933966985264_to_93507933867933969538 () : Lemma (
    reverse_add #10 source_47248966933966985264 ==
      [8; 3; 5; 9; 6; 9; 3; 3; 9; 7; 6; 8; 3; 3; 9; 7; 0; 5; 3; 9]) =
  canonical_47248966933966985264 ();
  trace_digits_equals_reverse_add source_47248966933966985264;
  assert (trace_digits source_47248966933966985264 ==
    [8; 3; 5; 9; 6; 9; 3; 3; 9; 7; 6; 8; 3; 3; 9; 7; 0; 5; 3; 9]);
  assert (trace_digits source_47248966933966985264 ==
    reverse_add #10 source_47248966933966985264);
  ()

let trace_digits_profile_3603815405135183953 () : Lemma (
    requires (canonical #10 source_3603815405135183953 /\
      source_3603815405135183953 <> []))
    (ensures (trace_digits source_3603815405135183953 ==
      [6; 1; 0; 7; 6; 3; 0; 8; 1; 0; 2; 7; 0; 3; 6; 7; 9; 1; 7])) =
  reverse_add_3603815405135183953_to_7197630720180367016 ();
  ()

let trace_digits_profile_7197630720180367016 () : Lemma (
    requires (canonical #10 source_7197630720180367016 /\
      source_7197630720180367016 <> []))
    (ensures (trace_digits source_7197630720180367016 ==
      [3; 3; 9; 4; 3; 7; 0; 5; 4; 0; 3; 5; 1; 6; 2; 5; 0; 3; 3; 1])) =
  reverse_add_7197630720180367016_to_13305261530450734933 ();
  ()

let trace_digits_profile_13305261530450734933 () : Lemma (
    requires (canonical #10 source_13305261530450734933 /\
      source_13305261530450734933 <> []))
    (ensures (trace_digits source_13305261530450734933 ==
      [4; 6; 2; 5; 8; 9; 6; 6; 9; 3; 3; 9; 6; 6; 9; 8; 4; 2; 7; 4])) =
  reverse_add_13305261530450734933_to_47248966933966985264 ();
  ()

let trace_digits_profile_47248966933966985264 () : Lemma (
    requires (canonical #10 source_47248966933966985264 /\
      source_47248966933966985264 <> []))
    (ensures (trace_digits source_47248966933966985264 ==
      [8; 3; 5; 9; 6; 9; 3; 3; 9; 7; 6; 8; 3; 3; 9; 7; 0; 5; 3; 9])) =
  reverse_add_47248966933966985264_to_93507933867933969538 ();
  ()

let trace_profile_shape_3603815405135183953 () : Lemma (
    requires (canonical #10 source_3603815405135183953 /\
      source_3603815405135183953 <> []))
    (ensures (length (trace_digits source_3603815405135183953) ==
      length source_3603815405135183953)) =
  trace_digits_profile_3603815405135183953 ();
  length_of_eq #(digit 10) (trace_digits source_3603815405135183953)
    [6; 1; 0; 7; 6; 3; 0; 8; 1; 0; 2; 7; 0; 3; 6; 7; 9; 1; 7];
  ()

let trace_profile_shape_7197630720180367016 () : Lemma (
    requires (canonical #10 source_7197630720180367016 /\
      source_7197630720180367016 <> []))
    (ensures (length (trace_digits source_7197630720180367016) ==
      length source_7197630720180367016 + 1)) =
  trace_digits_profile_7197630720180367016 ();
  length_of_eq #(digit 10) (trace_digits source_7197630720180367016)
    [3; 3; 9; 4; 3; 7; 0; 5; 4; 0; 3; 5; 1; 6; 2; 5; 0; 3; 3; 1];
  ()

let trace_profile_shape_13305261530450734933 () : Lemma (
    requires (canonical #10 source_13305261530450734933 /\
      source_13305261530450734933 <> []))
    (ensures (length (trace_digits source_13305261530450734933) ==
      length source_13305261530450734933)) =
  trace_digits_profile_13305261530450734933 ();
  length_of_eq #(digit 10) (trace_digits source_13305261530450734933)
    [4; 6; 2; 5; 8; 9; 6; 6; 9; 3; 3; 9; 6; 6; 9; 8; 4; 2; 7; 4];
  ()

let trace_profile_shape_47248966933966985264 () : Lemma (
    requires (canonical #10 source_47248966933966985264 /\
      source_47248966933966985264 <> []))
    (ensures (length (trace_digits source_47248966933966985264) ==
      length source_47248966933966985264)) =
  trace_digits_profile_47248966933966985264 ();
  length_of_eq #(digit 10) (trace_digits source_47248966933966985264)
    [8; 3; 5; 9; 6; 9; 3; 3; 9; 7; 6; 8; 3; 3; 9; 7; 0; 5; 3; 9];
  ()

let final_carry_from_overflow_length (xs:numeral 10) : Lemma (
    requires (length (trace_digits xs) == length xs + 1))
    (ensures (nth (trace_carries xs) (length xs) == Some 1)) =
  rev_length xs;
  trace_output_length_carry_link #10 xs (rev xs) 0;
  eliminate
    (length (add_trace #10 xs (rev xs) 0).digits == length xs /\
     nth (add_trace #10 xs (rev xs) 0).carries (length xs) == Some 0) \/
    (length (add_trace #10 xs (rev xs) 0).digits == length xs + 1 /\
     nth (add_trace #10 xs (rev xs) 0).carries (length xs) == Some 1)
  with (
    assert (length (add_trace #10 xs (rev xs) 0).digits ==
      length (trace_digits xs));
    assert (length xs == length xs + 1);
    assert False)
  and (
    assert (nth (trace_carries xs) (length xs) == Some 1);
    ())

let trace_profile_final_carry_3603815405135183953 () : Lemma (
    nth (trace_carries source_3603815405135183953)
      (length source_3603815405135183953) == Some 0) =
  final_carry_from_length source_3603815405135183953;
  ()

let trace_profile_final_carry_7197630720180367016 () : Lemma (
    nth (trace_carries source_7197630720180367016)
      (length source_7197630720180367016) == Some 1) =
  final_carry_from_overflow_length source_7197630720180367016;
  ()

let trace_profile_final_carry_13305261530450734933 () : Lemma (
    nth (trace_carries source_13305261530450734933)
      (length source_13305261530450734933) == Some 0) =
  final_carry_from_length source_13305261530450734933;
  ()

let trace_profile_final_carry_47248966933966985264 () : Lemma (
    nth (trace_carries source_47248966933966985264)
      (length source_47248966933966985264) == Some 0) =
  final_carry_from_length source_47248966933966985264;
  ()

let trace_profile_sums_3603815405135183953 () : Lemma (
    trace_sum_at source_3603815405135183953 0 == 6) =
  reverse_list_3603815405135183953 ();
  assert (trace_sum_at source_3603815405135183953 0 == 6);
  ()

let trace_profile_sums_7197630720180367016 () : Lemma (
    trace_sum_at source_7197630720180367016 0 == 13 /\
    trace_sum_at source_7197630720180367016 2 == 9 /\
    trace_sum_at source_7197630720180367016 17 == 2) =
  reverse_list_7197630720180367016 ();
  assert (trace_sum_at source_7197630720180367016 0 == 13);
  assert (trace_sum_at source_7197630720180367016 2 == 9);
  assert (trace_sum_at source_7197630720180367016 17 == 2);
  ()

let trace_profile_sums_13305261530450734933 () : Lemma (
    trace_sum_at source_13305261530450734933 0 == 4 /\
    trace_sum_at source_13305261530450734933 1 == 6) =
  reverse_list_13305261530450734933 ();
  assert (trace_sum_at source_13305261530450734933 0 == 4);
  assert (trace_sum_at source_13305261530450734933 1 == 6);
  ()

let trace_profile_sums_47248966933966985264 () : Lemma (
    trace_sum_at source_47248966933966985264 0 == 8) =
  reverse_list_47248966933966985264 ();
  assert (trace_sum_at source_47248966933966985264 0 == 8);
  ()

let trace_profile_carries_7197630720180367016 () : Lemma (
    trace_carry_at source_7197630720180367016 2 == 0 /\
    trace_carry_at source_7197630720180367016 17 == 1 /\
    trace_carry_at source_7197630720180367016 3 == 0 /\
    trace_carry_at source_7197630720180367016 18 == 0) =
  reverse_list_7197630720180367016 ();
  assert (trace_carries source_7197630720180367016 ==
    (add_trace #10 source_7197630720180367016
      [7; 1; 9; 7; 6; 3; 0; 7; 2; 0; 1; 8; 0; 3; 6; 7; 0; 1; 6] 0).carries);
  add_trace_carries_step #10 6 7
    [1; 0; 7; 6; 3; 0; 8; 1; 0; 2; 7; 0; 3; 6; 7; 9; 1; 7]
    [1; 9; 7; 6; 3; 0; 7; 2; 0; 1; 8; 0; 3; 6; 7; 0; 1; 6] 0;
  add_trace_carries_step #10 1 1
    [0; 7; 6; 3; 0; 8; 1; 0; 2; 7; 0; 3; 6; 7; 9; 1; 7]
    [9; 7; 6; 3; 0; 7; 2; 0; 1; 8; 0; 3; 6; 7; 0; 1; 6] 1;
  add_trace_carries_step #10 0 9
    [7; 6; 3; 0; 8; 1; 0; 2; 7; 0; 3; 6; 7; 9; 1; 7]
    [7; 6; 3; 0; 7; 2; 0; 1; 8; 0; 3; 6; 7; 0; 1; 6] 0;
  add_trace_carries_step #10 7 7
    [6; 3; 0; 8; 1; 0; 2; 7; 0; 3; 6; 7; 9; 1; 7]
    [6; 3; 0; 7; 2; 0; 1; 8; 0; 3; 6; 7; 0; 1; 6] 0;
  add_trace_carries_step #10 6 6
    [3; 0; 8; 1; 0; 2; 7; 0; 3; 6; 7; 9; 1; 7]
    [3; 0; 7; 2; 0; 1; 8; 0; 3; 6; 7; 0; 1; 6] 1;
  add_trace_carries_step #10 3 3
    [0; 8; 1; 0; 2; 7; 0; 3; 6; 7; 9; 1; 7]
    [0; 7; 2; 0; 1; 8; 0; 3; 6; 7; 0; 1; 6] 1;
  add_trace_carries_step #10 0 0
    [8; 1; 0; 2; 7; 0; 3; 6; 7; 9; 1; 7]
    [7; 2; 0; 1; 8; 0; 3; 6; 7; 0; 1; 6] 0;
  add_trace_carries_step #10 8 7
    [1; 0; 2; 7; 0; 3; 6; 7; 9; 1; 7]
    [2; 0; 1; 8; 0; 3; 6; 7; 0; 1; 6] 0;
  add_trace_carries_step #10 1 2
    [0; 2; 7; 0; 3; 6; 7; 9; 1; 7]
    [0; 1; 8; 0; 3; 6; 7; 0; 1; 6] 1;
  add_trace_carries_step #10 0 0
    [2; 7; 0; 3; 6; 7; 9; 1; 7]
    [1; 8; 0; 3; 6; 7; 0; 1; 6] 0;
  add_trace_carries_step #10 2 1
    [7; 0; 3; 6; 7; 9; 1; 7]
    [8; 0; 3; 6; 7; 0; 1; 6] 0;
  add_trace_carries_step #10 7 8
    [0; 3; 6; 7; 9; 1; 7]
    [0; 3; 6; 7; 0; 1; 6] 0;
  add_trace_carries_step #10 0 0
    [3; 6; 7; 9; 1; 7]
    [3; 6; 7; 0; 1; 6] 1;
  add_trace_carries_step #10 3 3
    [6; 7; 9; 1; 7]
    [6; 7; 0; 1; 6] 0;
  add_trace_carries_step #10 6 6
    [7; 9; 1; 7]
    [7; 0; 1; 6] 0;
  add_trace_carries_step #10 7 7
    [9; 1; 7]
    [0; 1; 6] 1;
  add_trace_carries_step #10 9 0
    [1; 7]
    [1; 6] 1;
  add_trace_carries_step #10 1 1
    [7] [6] 1;
  add_trace_carries_step #10 7 6 [] [] 0;
  assert ((add_trace #10 [] [] 1).carries == [1]);
  assert ((add_trace #10 source_7197630720180367016
      [7; 1; 9; 7; 6; 3; 0; 7; 2; 0; 1; 8; 0; 3; 6; 7; 0; 1; 6] 0).carries ==
    [0; 1; 0; 0; 1; 1; 0; 0; 1; 0; 0; 0; 1; 0; 0; 1; 1; 1; 0; 1]);
  assert (trace_carry_at source_7197630720180367016 2 == 0);
  assert (trace_carry_at source_7197630720180367016 17 == 1);
  assert (trace_carry_at source_7197630720180367016 3 == 0);
  assert (trace_carry_at source_7197630720180367016 18 == 0);
  ()

let trace_profile_carries_13305261530450734933 () : Lemma (
    trace_carry_at source_13305261530450734933 1 == 0 /\
    trace_carry_at source_13305261530450734933 18 == 1 /\
    trace_carry_at source_13305261530450734933 2 == 0 /\
    trace_carry_at source_13305261530450734933 19 == 0) =
  reverse_list_13305261530450734933 ();
  assert (trace_carries source_13305261530450734933 ==
    (add_trace #10 source_13305261530450734933
      [1; 3; 3; 0; 5; 2; 6; 1; 5; 3; 0; 4; 5; 0; 7; 3; 4; 9; 3; 3] 0).carries);
  assert ((add_trace #10 source_13305261530450734933
      [1; 3; 3; 0; 5; 2; 6; 1; 5; 3; 0; 4; 5; 0; 7; 3; 4; 9; 3; 3] 0).carries ==
    [0; 0; 0; 1; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 1; 0; 0]);
  assert (trace_carry_at source_13305261530450734933 1 == 0);
  assert (trace_carry_at source_13305261530450734933 18 == 1);
  assert (trace_carry_at source_13305261530450734933 2 == 0);
  assert (trace_carry_at source_13305261530450734933 19 == 0);
  ()

let overflow_precondition_7197630720180367016 () : Lemma (
    canonical #10 source_7197630720180367016 /\
    source_7197630720180367016 <> [] /\
    length (trace_digits source_7197630720180367016) ==
      length source_7197630720180367016 + 1 /\
    nth (trace_carries source_7197630720180367016)
      (length source_7197630720180367016) == Some 1 /\
    1 <= trace_sum_at source_7197630720180367016 0 /\
    trace_sum_at source_7197630720180367016 0 <= 18 /\
    trace_sum_at source_7197630720180367016 0 <> 10 /\
    exists (i:nat). 0 < i /\
      i < length source_7197630720180367016 /\
      trace_sum_at source_7197630720180367016 i +
          trace_sum_at source_7197630720180367016
            (length source_7197630720180367016 - i) +
          trace_carry_at source_7197630720180367016 i +
          trace_carry_at source_7197630720180367016
            (length source_7197630720180367016 - i) >=
        10 + 10 *
          (trace_carry_at source_7197630720180367016 (i + 1) +
           trace_carry_at source_7197630720180367016
             (length source_7197630720180367016 - i + 1))) =
  assert (canonical #10 source_7197630720180367016);
  assert (source_7197630720180367016 <> []);
  trace_profile_shape_7197630720180367016 ();
  trace_profile_final_carry_7197630720180367016 ();
  trace_profile_sums_7197630720180367016 ();
  trace_profile_carries_7197630720180367016 ();
  assert (trace_sum_at source_7197630720180367016 0 <> 10);
  FStar.Classical.exists_intro #nat
    (fun (i:nat) -> 0 < i /\
      i < length source_7197630720180367016 /\
      trace_sum_at source_7197630720180367016 i +
          trace_sum_at source_7197630720180367016
            (length source_7197630720180367016 - i) +
          trace_carry_at source_7197630720180367016 i +
          trace_carry_at source_7197630720180367016
            (length source_7197630720180367016 - i) >=
        10 + 10 *
          (trace_carry_at source_7197630720180367016 (i + 1) +
           trace_carry_at source_7197630720180367016
             (length source_7197630720180367016 - i + 1)))
    2;
  ()

let no_overflow_precondition_13305261530450734933 () : Lemma (
    canonical #10 source_13305261530450734933 /\
    source_13305261530450734933 <> [] /\
    length (trace_digits source_13305261530450734933) ==
      length source_13305261530450734933 /\
    nth (trace_carries source_13305261530450734933)
      (length source_13305261530450734933) == Some 0 /\
    1 <= trace_sum_at source_13305261530450734933 0 /\
    trace_sum_at source_13305261530450734933 0 <= 4 /\
    exists (i:nat). i < length source_13305261530450734933 /\
      2 * trace_sum_at source_13305261530450734933 i +
          trace_carry_at source_13305261530450734933 i +
          trace_carry_at source_13305261530450734933
            (length source_13305261530450734933 - 1 - i) >=
        10 + 10 *
          (trace_carry_at source_13305261530450734933 (i + 1) +
           trace_carry_at source_13305261530450734933
             (length source_13305261530450734933 - i))) =
  canonical_13305261530450734933 ();
  trace_profile_shape_13305261530450734933 ();
  trace_profile_final_carry_13305261530450734933 ();
  trace_profile_sums_13305261530450734933 ();
  trace_profile_carries_13305261530450734933 ();
  assert (1 <= trace_sum_at source_13305261530450734933 0);
  assert (trace_sum_at source_13305261530450734933 0 <= 4);
  FStar.Classical.exists_intro #nat
    (fun (i:nat) -> i < length source_13305261530450734933 /\
      2 * trace_sum_at source_13305261530450734933 i +
          trace_carry_at source_13305261530450734933 i +
          trace_carry_at source_13305261530450734933
            (length source_13305261530450734933 - 1 - i) >=
        10 + 10 *
          (trace_carry_at source_13305261530450734933 (i + 1) +
           trace_carry_at source_13305261530450734933
             (length source_13305261530450734933 - i)))
    1;
  ()
