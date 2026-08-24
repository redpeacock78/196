module ReverseAddNext

#set-options "--fuel 100 --ifuel 100 --retry 10 --split_queries always"

open ReverseAdd
open ReverseAddCarry
open ReverseAddWitness
open ReverseAddOverflowProfile
open FStar.Classical
open FStar.List.Tot

let next_source : numeral 10 =
  [7; 7; 0; 0; 4; 9; 7; 6; 7; 4; 4; 8; 7; 6; 8; 4; 0; 1; 7; 7; 1]

let next_target : numeral 10 =
  [8; 4; 8; 1; 4; 3; 6; 3; 5; 3; 9; 2; 5; 3; 6; 4; 5; 1; 7; 4; 9]

let next_reversed : numeral 10 =
  [1; 7; 7; 1; 0; 4; 8; 6; 7; 8; 4; 4; 7; 6; 7; 9; 4; 0; 0; 7; 7]

let reverse_list_next_source () : Lemma (rev next_source == next_reversed) =
  assert (rev [1] == [1]);
  rev_cons 7 [1];
  rev_cons 7 [7; 1];
  rev_cons 1 [7; 7; 1];
  rev_cons 0 [1; 7; 7; 1];
  rev_cons 4 [0; 1; 7; 7; 1];
  rev_cons 8 [4; 0; 1; 7; 7; 1];
  rev_cons 6 [8; 4; 0; 1; 7; 7; 1];
  rev_cons 7 [6; 8; 4; 0; 1; 7; 7; 1];
  rev_cons 8 [7; 6; 8; 4; 0; 1; 7; 7; 1];
  rev_cons 4 [8; 7; 6; 8; 4; 0; 1; 7; 7; 1];
  rev_cons 4 [4; 8; 7; 6; 8; 4; 0; 1; 7; 7; 1];
  rev_cons 7 [4; 4; 8; 7; 6; 8; 4; 0; 1; 7; 7; 1];
  rev_cons 6 [7; 4; 4; 8; 7; 6; 8; 4; 0; 1; 7; 7; 1];
  rev_cons 7 [6; 7; 4; 4; 8; 7; 6; 8; 4; 0; 1; 7; 7; 1];
  rev_cons 9 [7; 6; 7; 4; 4; 8; 7; 6; 8; 4; 0; 1; 7; 7; 1];
  rev_cons 4 [9; 7; 6; 7; 4; 4; 8; 7; 6; 8; 4; 0; 1; 7; 7; 1];
  rev_cons 0 [4; 9; 7; 6; 7; 4; 4; 8; 7; 6; 8; 4; 0; 1; 7; 7; 1];
  rev_cons 0 [0; 4; 9; 7; 6; 7; 4; 4; 8; 7; 6; 8; 4; 0; 1; 7; 7; 1];
  rev_cons 7 [0; 0; 4; 9; 7; 6; 7; 4; 4; 8; 7; 6; 8; 4; 0; 1; 7; 7; 1];
  rev_cons 7 [7; 0; 0; 4; 9; 7; 6; 7; 4; 4; 8; 7; 6; 8; 4; 0; 1; 7; 7; 1];
  ()

let value_next_source () : Lemma (value next_source == 177104867844767940077) =
  value_cons #10 7 [7; 0; 0; 4; 9; 7; 6; 7; 4; 4; 8; 7; 6; 8; 4; 0; 1; 7; 7; 1];
  value_cons #10 7 [0; 0; 4; 9; 7; 6; 7; 4; 4; 8; 7; 6; 8; 4; 0; 1; 7; 7; 1];
  value_cons #10 0 [0; 4; 9; 7; 6; 7; 4; 4; 8; 7; 6; 8; 4; 0; 1; 7; 7; 1];
  value_cons #10 0 [4; 9; 7; 6; 7; 4; 4; 8; 7; 6; 8; 4; 0; 1; 7; 7; 1];
  value_cons #10 4 [9; 7; 6; 7; 4; 4; 8; 7; 6; 8; 4; 0; 1; 7; 7; 1];
  value_cons #10 9 [7; 6; 7; 4; 4; 8; 7; 6; 8; 4; 0; 1; 7; 7; 1];
  value_cons #10 7 [6; 7; 4; 4; 8; 7; 6; 8; 4; 0; 1; 7; 7; 1];
  value_cons #10 6 [7; 4; 4; 8; 7; 6; 8; 4; 0; 1; 7; 7; 1];
  value_cons #10 7 [4; 4; 8; 7; 6; 8; 4; 0; 1; 7; 7; 1];
  value_cons #10 4 [4; 8; 7; 6; 8; 4; 0; 1; 7; 7; 1];
  value_cons #10 4 [8; 7; 6; 8; 4; 0; 1; 7; 7; 1];
  value_cons #10 8 [7; 6; 8; 4; 0; 1; 7; 7; 1];
  value_cons #10 7 [6; 8; 4; 0; 1; 7; 7; 1];
  value_cons #10 6 [8; 4; 0; 1; 7; 7; 1];
  value_cons #10 8 [4; 0; 1; 7; 7; 1];
  value_cons #10 4 [0; 1; 7; 7; 1];
  value_cons #10 0 [1; 7; 7; 1];
  value_cons #10 1 [7; 7; 1];
  value_cons #10 7 [7; 1];
  value_cons #10 7 [1];
  value_cons #10 1 [];
  ()

let value_next_reversed () : Lemma (value next_reversed == 770049767448768401771) =
  value_cons #10 1 [7; 7; 1; 0; 4; 8; 6; 7; 8; 4; 4; 7; 6; 7; 9; 4; 0; 0; 7; 7];
  value_cons #10 7 [7; 1; 0; 4; 8; 6; 7; 8; 4; 4; 7; 6; 7; 9; 4; 0; 0; 7; 7];
  value_cons #10 7 [1; 0; 4; 8; 6; 7; 8; 4; 4; 7; 6; 7; 9; 4; 0; 0; 7; 7];
  value_cons #10 1 [0; 4; 8; 6; 7; 8; 4; 4; 7; 6; 7; 9; 4; 0; 0; 7; 7];
  value_cons #10 0 [4; 8; 6; 7; 8; 4; 4; 7; 6; 7; 9; 4; 0; 0; 7; 7];
  value_cons #10 4 [8; 6; 7; 8; 4; 4; 7; 6; 7; 9; 4; 0; 0; 7; 7];
  value_cons #10 8 [6; 7; 8; 4; 4; 7; 6; 7; 9; 4; 0; 0; 7; 7];
  value_cons #10 6 [7; 8; 4; 4; 7; 6; 7; 9; 4; 0; 0; 7; 7];
  value_cons #10 7 [8; 4; 4; 7; 6; 7; 9; 4; 0; 0; 7; 7];
  value_cons #10 8 [4; 4; 7; 6; 7; 9; 4; 0; 0; 7; 7];
  value_cons #10 4 [4; 7; 6; 7; 9; 4; 0; 0; 7; 7];
  value_cons #10 4 [7; 6; 7; 9; 4; 0; 0; 7; 7];
  value_cons #10 7 [6; 7; 9; 4; 0; 0; 7; 7];
  value_cons #10 6 [7; 9; 4; 0; 0; 7; 7];
  value_cons #10 7 [9; 4; 0; 0; 7; 7];
  value_cons #10 9 [4; 0; 0; 7; 7];
  value_cons #10 4 [0; 0; 7; 7];
  value_cons #10 0 [0; 7; 7];
  value_cons #10 0 [7; 7];
  value_cons #10 7 [7];
  value_cons #10 7 [];
  ()

let value_next_target () : Lemma (value next_target == 947154635293536341848) =
  value_cons #10 8 [4; 8; 1; 4; 3; 6; 3; 5; 3; 9; 2; 5; 3; 6; 4; 5; 1; 7; 4; 9];
  value_cons #10 4 [8; 1; 4; 3; 6; 3; 5; 3; 9; 2; 5; 3; 6; 4; 5; 1; 7; 4; 9];
  value_cons #10 8 [1; 4; 3; 6; 3; 5; 3; 9; 2; 5; 3; 6; 4; 5; 1; 7; 4; 9];
  value_cons #10 1 [4; 3; 6; 3; 5; 3; 9; 2; 5; 3; 6; 4; 5; 1; 7; 4; 9];
  value_cons #10 4 [3; 6; 3; 5; 3; 9; 2; 5; 3; 6; 4; 5; 1; 7; 4; 9];
  value_cons #10 3 [6; 3; 5; 3; 9; 2; 5; 3; 6; 4; 5; 1; 7; 4; 9];
  value_cons #10 6 [3; 5; 3; 9; 2; 5; 3; 6; 4; 5; 1; 7; 4; 9];
  value_cons #10 3 [5; 3; 9; 2; 5; 3; 6; 4; 5; 1; 7; 4; 9];
  value_cons #10 5 [3; 9; 2; 5; 3; 6; 4; 5; 1; 7; 4; 9];
  value_cons #10 3 [9; 2; 5; 3; 6; 4; 5; 1; 7; 4; 9];
  value_cons #10 9 [2; 5; 3; 6; 4; 5; 1; 7; 4; 9];
  value_cons #10 2 [5; 3; 6; 4; 5; 1; 7; 4; 9];
  value_cons #10 5 [3; 6; 4; 5; 1; 7; 4; 9];
  value_cons #10 3 [6; 4; 5; 1; 7; 4; 9];
  value_cons #10 6 [4; 5; 1; 7; 4; 9];
  value_cons #10 4 [5; 1; 7; 4; 9];
  value_cons #10 5 [1; 7; 4; 9];
  value_cons #10 1 [7; 4; 9];
  value_cons #10 7 [4; 9];
  value_cons #10 4 [9];
  value_cons #10 9 [];
  ()

let canonical_next_source () : Lemma (canonical #10 next_source /\ next_source <> []) =
  assert (canonical #10 [1]);
  canonical_cons #10 7 [1];
  canonical_cons #10 7 [7; 1];
  canonical_cons #10 1 [7; 7; 1];
  canonical_cons #10 0 [1; 7; 7; 1];
  canonical_cons #10 4 [0; 1; 7; 7; 1];
  canonical_cons #10 8 [4; 0; 1; 7; 7; 1];
  canonical_cons #10 6 [8; 4; 0; 1; 7; 7; 1];
  canonical_cons #10 7 [6; 8; 4; 0; 1; 7; 7; 1];
  canonical_cons #10 8 [7; 6; 8; 4; 0; 1; 7; 7; 1];
  canonical_cons #10 4 [8; 7; 6; 8; 4; 0; 1; 7; 7; 1];
  canonical_cons #10 4 [4; 8; 7; 6; 8; 4; 0; 1; 7; 7; 1];
  canonical_cons #10 7 [4; 4; 8; 7; 6; 8; 4; 0; 1; 7; 7; 1];
  canonical_cons #10 6 [7; 4; 4; 8; 7; 6; 8; 4; 0; 1; 7; 7; 1];
  canonical_cons #10 7 [6; 7; 4; 4; 8; 7; 6; 8; 4; 0; 1; 7; 7; 1];
  canonical_cons #10 9 [7; 6; 7; 4; 4; 8; 7; 6; 8; 4; 0; 1; 7; 7; 1];
  canonical_cons #10 4 [9; 7; 6; 7; 4; 4; 8; 7; 6; 8; 4; 0; 1; 7; 7; 1];
  canonical_cons #10 0 [4; 9; 7; 6; 7; 4; 4; 8; 7; 6; 8; 4; 0; 1; 7; 7; 1];
  canonical_cons #10 0 [0; 4; 9; 7; 6; 7; 4; 4; 8; 7; 6; 8; 4; 0; 1; 7; 7; 1];
  canonical_cons #10 7 [0; 0; 4; 9; 7; 6; 7; 4; 4; 8; 7; 6; 8; 4; 0; 1; 7; 7; 1];
  canonical_cons #10 7 [7; 0; 0; 4; 9; 7; 6; 7; 4; 4; 8; 7; 6; 8; 4; 0; 1; 7; 7; 1];
  ()

let canonical_next_reversed () : Lemma (canonical #10 next_reversed) =
  assert (canonical #10 [7]);
  canonical_cons #10 7 [7];
  canonical_cons #10 0 [7; 7];
  canonical_cons #10 0 [0; 7; 7];
  canonical_cons #10 4 [0; 0; 7; 7];
  canonical_cons #10 9 [4; 0; 0; 7; 7];
  canonical_cons #10 7 [9; 4; 0; 0; 7; 7];
  canonical_cons #10 6 [7; 9; 4; 0; 0; 7; 7];
  canonical_cons #10 7 [6; 7; 9; 4; 0; 0; 7; 7];
  canonical_cons #10 8 [7; 6; 7; 9; 4; 0; 0; 7; 7];
  canonical_cons #10 4 [8; 7; 6; 7; 9; 4; 0; 0; 7; 7];
  canonical_cons #10 4 [4; 8; 7; 6; 7; 9; 4; 0; 0; 7; 7];
  canonical_cons #10 7 [4; 4; 8; 7; 6; 7; 9; 4; 0; 0; 7; 7];
  canonical_cons #10 6 [7; 4; 4; 8; 7; 6; 7; 9; 4; 0; 0; 7; 7];
  canonical_cons #10 7 [6; 7; 4; 4; 8; 7; 6; 7; 9; 4; 0; 0; 7; 7];
  canonical_cons #10 9 [7; 6; 7; 4; 4; 8; 7; 6; 7; 9; 4; 0; 0; 7; 7];
  canonical_cons #10 4 [9; 7; 6; 7; 4; 4; 8; 7; 6; 7; 9; 4; 0; 0; 7; 7];
  canonical_cons #10 0 [4; 9; 7; 6; 7; 4; 4; 8; 7; 6; 7; 9; 4; 0; 0; 7; 7];
  canonical_cons #10 0 [0; 4; 9; 7; 6; 7; 4; 4; 8; 7; 6; 7; 9; 4; 0; 0; 7; 7];
  canonical_cons #10 7 [0; 0; 4; 9; 7; 6; 7; 4; 4; 8; 7; 6; 7; 9; 4; 0; 0; 7; 7];
  canonical_cons #10 7 [7; 0; 0; 4; 9; 7; 6; 7; 4; 4; 8; 7; 6; 7; 9; 4; 0; 0; 7; 7];
  canonical_cons #10 1 [7; 7; 0; 0; 4; 9; 7; 6; 7; 4; 4; 8; 7; 6; 7; 9; 4; 0; 0; 7; 7];
  ()

let canonical_next_target () : Lemma (canonical #10 next_target) =
  assert (canonical #10 [9]);
  canonical_cons #10 4 [9];
  canonical_cons #10 7 [4; 9];
  canonical_cons #10 1 [7; 4; 9];
  canonical_cons #10 5 [1; 7; 4; 9];
  canonical_cons #10 4 [5; 1; 7; 4; 9];
  canonical_cons #10 6 [4; 5; 1; 7; 4; 9];
  canonical_cons #10 3 [6; 4; 5; 1; 7; 4; 9];
  canonical_cons #10 5 [3; 6; 4; 5; 1; 7; 4; 9];
  canonical_cons #10 3 [5; 3; 6; 4; 5; 1; 7; 4; 9];
  canonical_cons #10 9 [3; 5; 3; 6; 4; 5; 1; 7; 4; 9];
  canonical_cons #10 2 [9; 3; 5; 3; 6; 4; 5; 1; 7; 4; 9];
  canonical_cons #10 5 [2; 9; 3; 5; 3; 6; 4; 5; 1; 7; 4; 9];
  canonical_cons #10 3 [5; 2; 9; 3; 5; 3; 6; 4; 5; 1; 7; 4; 9];
  canonical_cons #10 6 [3; 5; 2; 9; 3; 5; 3; 6; 4; 5; 1; 7; 4; 9];
  canonical_cons #10 3 [6; 3; 5; 2; 9; 3; 5; 3; 6; 4; 5; 1; 7; 4; 9];
  canonical_cons #10 4 [3; 6; 3; 5; 2; 9; 3; 5; 3; 6; 4; 5; 1; 7; 4; 9];
  canonical_cons #10 8 [4; 3; 6; 3; 5; 2; 9; 3; 5; 3; 6; 4; 5; 1; 7; 4; 9];
  canonical_cons #10 4 [8; 4; 3; 6; 3; 5; 2; 9; 3; 5; 3; 6; 4; 5; 1; 7; 4; 9];
  canonical_cons #10 8 [4; 8; 4; 3; 6; 3; 5; 2; 9; 3; 5; 3; 6; 4; 5; 1; 7; 4; 9];
  ()

let reverse_digits_next_source () : Lemma (
    reverse_digits #10 next_source == next_reversed) =
  canonical_next_source ();
  reverse_list_next_source ();
  value_next_reversed ();
  canonical_next_reversed ();
  reverse_digits_canonical #10 next_source;
  normalize_value #10 (rev next_source);
  assert (value (reverse_digits #10 next_source) ==
    770049767448768401771);
  digits_of_nat_of_canonical #10 (reverse_digits #10 next_source);
  digits_of_nat_of_canonical #10 next_reversed;
  assert (reverse_digits #10 next_source == next_reversed);
  ()

let reverse_add_177104867844767940077_to_947154635293536341848 () : Lemma (
    reverse_add #10 next_source == next_target) =
  canonical_next_source ();
  reverse_add_value #10 next_source;
  value_next_source ();
  reverse_digits_next_source ();
  value_next_reversed ();
  value_next_target ();
  assert (value (reverse_add #10 next_source) ==
    947154635293536341848);
  reverse_add_canonical #10 next_source;
  digits_of_nat_of_canonical #10 (reverse_add #10 next_source);
  canonical_next_target ();
  digits_of_nat_of_canonical #10 next_target;
  assert (reverse_add #10 next_source == next_target);
  ()

let trace_profile_shape_177104867844767940077 () : Lemma (
    length (trace_digits next_source) == length next_source) =
  reverse_add_177104867844767940077_to_947154635293536341848 ();
  length_of_eq #(digit 10) (trace_digits next_source) next_target;
  assert (length next_target == length next_source);
  ()

let trace_profile_final_carry_177104867844767940077 () : Lemma (
    nth (trace_carries next_source) (length next_source) == Some 0) =
  trace_profile_shape_177104867844767940077 ();
  final_carry_from_length next_source;
  ()

let local_profile_witness_947154635293536341848 () : Lemma (
    trace_local_profile_complement_witness next_target) =
  assert (canonical #10 next_source);
  assert (next_source <> []);
  trace_profile_shape_177104867844767940077 ();
  trace_profile_final_carry_177104867844767940077 ();
  assert (trace_sum_at next_source 0 == 8);
  reverse_add_177104867844767940077_to_947154635293536341848 ();
  no_overflow_outer_sum_6_to_9_implies_next_witness next_source;
  ()

let next2_source : numeral 10 = next_target

let next2_reversed : numeral 10 =
  [9; 4; 7; 1; 5; 4; 6; 3; 5; 2; 9; 3; 5; 3; 6; 3; 4; 1; 8; 4; 8]

let next2_target : numeral 10 =
  [7; 9; 5; 3; 9; 7; 2; 7; 0; 6; 8; 6; 0; 7; 2; 8; 9; 2; 5; 9; 7; 1]

let reverse_list_next2_source () : Lemma (rev next2_source == next2_reversed) =
  assert (rev [9] == [9]);
  rev_cons 4 [9];
  rev_cons 7 [4; 9];
  rev_cons 1 [7; 4; 9];
  rev_cons 8 [1; 7; 4; 9];
  rev_cons 4 [8; 1; 7; 4; 9];
  rev_cons 3 [4; 8; 1; 7; 4; 9];
  rev_cons 6 [3; 4; 8; 1; 7; 4; 9];
  rev_cons 3 [6; 3; 4; 8; 1; 7; 4; 9];
  rev_cons 5 [3; 6; 3; 4; 8; 1; 7; 4; 9];
  rev_cons 3 [5; 3; 6; 3; 4; 8; 1; 7; 4; 9];
  rev_cons 9 [3; 5; 3; 6; 3; 4; 8; 1; 7; 4; 9];
  rev_cons 2 [9; 3; 5; 3; 6; 3; 4; 8; 1; 7; 4; 9];
  rev_cons 5 [2; 9; 3; 5; 3; 6; 3; 4; 8; 1; 7; 4; 9];
  rev_cons 3 [5; 2; 9; 3; 5; 3; 6; 3; 4; 8; 1; 7; 4; 9];
  rev_cons 6 [3; 5; 2; 9; 3; 5; 3; 6; 3; 4; 8; 1; 7; 4; 9];
  rev_cons 4 [6; 3; 5; 2; 9; 3; 5; 3; 6; 3; 4; 8; 1; 7; 4; 9];
  rev_cons 5 [4; 6; 3; 5; 2; 9; 3; 5; 3; 6; 3; 4; 8; 1; 7; 4; 9];
  rev_cons 1 [5; 4; 6; 3; 5; 2; 9; 3; 5; 3; 6; 3; 4; 8; 1; 7; 4; 9];
  rev_cons 4 [1; 5; 4; 6; 3; 5; 2; 9; 3; 5; 3; 6; 3; 4; 8; 1; 7; 4; 9];
  rev_cons 8 [4; 1; 5; 4; 6; 3; 5; 2; 9; 3; 5; 3; 6; 3; 4; 8; 1; 7; 4; 9];
  ()

let value_next2_reversed () : Lemma (
    value next2_reversed == 848143635392536451749) =
  value_cons #10 9 [4; 7; 1; 5; 4; 6; 3; 5; 2; 9; 3; 5; 3; 6; 3; 4; 1; 8; 4; 8];
  value_cons #10 4 [7; 1; 5; 4; 6; 3; 5; 2; 9; 3; 5; 3; 6; 3; 4; 1; 8; 4; 8];
  value_cons #10 7 [1; 5; 4; 6; 3; 5; 2; 9; 3; 5; 3; 6; 3; 4; 1; 8; 4; 8];
  value_cons #10 1 [5; 4; 6; 3; 5; 2; 9; 3; 5; 3; 6; 3; 4; 1; 8; 4; 8];
  value_cons #10 5 [4; 6; 3; 5; 2; 9; 3; 5; 3; 6; 3; 4; 1; 8; 4; 8];
  value_cons #10 4 [6; 3; 5; 2; 9; 3; 5; 3; 6; 3; 4; 1; 8; 4; 8];
  value_cons #10 6 [3; 5; 2; 9; 3; 5; 3; 6; 3; 4; 1; 8; 4; 8];
  value_cons #10 3 [5; 2; 9; 3; 5; 3; 6; 3; 4; 1; 8; 4; 8];
  value_cons #10 5 [2; 9; 3; 5; 3; 6; 3; 4; 1; 8; 4; 8];
  value_cons #10 2 [9; 3; 5; 3; 6; 3; 4; 1; 8; 4; 8];
  value_cons #10 9 [3; 5; 3; 6; 3; 4; 1; 8; 4; 8];
  value_cons #10 3 [5; 3; 6; 3; 4; 1; 8; 4; 8];
  value_cons #10 5 [3; 6; 3; 4; 1; 8; 4; 8];
  value_cons #10 3 [6; 3; 4; 1; 8; 4; 8];
  value_cons #10 6 [3; 4; 1; 8; 4; 8];
  value_cons #10 3 [4; 1; 8; 4; 8];
  value_cons #10 4 [1; 8; 4; 8];
  value_cons #10 1 [8; 4; 8];
  value_cons #10 8 [4; 8];
  value_cons #10 4 [8];
  value_cons #10 8 [];
  ()

let value_next2_target () : Lemma (
    value next2_target == 1795298270686072793597) =
  value_cons #10 7 [9; 5; 3; 9; 7; 2; 7; 0; 6; 8; 6; 0; 7; 2; 8; 9; 2; 5; 9; 7; 1];
  value_cons #10 9 [5; 3; 9; 7; 2; 7; 0; 6; 8; 6; 0; 7; 2; 8; 9; 2; 5; 9; 7; 1];
  value_cons #10 5 [3; 9; 7; 2; 7; 0; 6; 8; 6; 0; 7; 2; 8; 9; 2; 5; 9; 7; 1];
  value_cons #10 3 [9; 7; 2; 7; 0; 6; 8; 6; 0; 7; 2; 8; 9; 2; 5; 9; 7; 1];
  value_cons #10 9 [7; 2; 7; 0; 6; 8; 6; 0; 7; 2; 8; 9; 2; 5; 9; 7; 1];
  value_cons #10 7 [2; 7; 0; 6; 8; 6; 0; 7; 2; 8; 9; 2; 5; 9; 7; 1];
  value_cons #10 2 [7; 0; 6; 8; 6; 0; 7; 2; 8; 9; 2; 5; 9; 7; 1];
  value_cons #10 7 [0; 6; 8; 6; 0; 7; 2; 8; 9; 2; 5; 9; 7; 1];
  value_cons #10 0 [6; 8; 6; 0; 7; 2; 8; 9; 2; 5; 9; 7; 1];
  value_cons #10 6 [8; 6; 0; 7; 2; 8; 9; 2; 5; 9; 7; 1];
  value_cons #10 8 [6; 0; 7; 2; 8; 9; 2; 5; 9; 7; 1];
  value_cons #10 6 [0; 7; 2; 8; 9; 2; 5; 9; 7; 1];
  value_cons #10 0 [7; 2; 8; 9; 2; 5; 9; 7; 1];
  value_cons #10 7 [2; 8; 9; 2; 5; 9; 7; 1];
  value_cons #10 2 [8; 9; 2; 5; 9; 7; 1];
  value_cons #10 8 [9; 2; 5; 9; 7; 1];
  value_cons #10 9 [2; 5; 9; 7; 1];
  value_cons #10 2 [5; 9; 7; 1];
  value_cons #10 5 [9; 7; 1];
  value_cons #10 9 [7; 1];
  value_cons #10 7 [1];
  value_cons #10 1 [];
  ()

let canonical_next2_reversed () : Lemma (canonical #10 next2_reversed) =
  assert (canonical #10 [8]);
  canonical_cons #10 4 [8];
  canonical_cons #10 1 [4; 8];
  canonical_cons #10 3 [1; 4; 8];
  canonical_cons #10 6 [3; 1; 4; 8];
  canonical_cons #10 3 [6; 3; 1; 4; 8];
  canonical_cons #10 5 [3; 6; 3; 1; 4; 8];
  canonical_cons #10 3 [5; 3; 6; 3; 1; 4; 8];
  canonical_cons #10 9 [3; 5; 3; 6; 3; 1; 4; 8];
  canonical_cons #10 2 [9; 3; 5; 3; 6; 3; 1; 4; 8];
  canonical_cons #10 5 [2; 9; 3; 5; 3; 6; 3; 1; 4; 8];
  canonical_cons #10 3 [5; 2; 9; 3; 5; 3; 6; 3; 1; 4; 8];
  canonical_cons #10 5 [3; 5; 2; 9; 3; 5; 3; 6; 3; 1; 4; 8];
  canonical_cons #10 3 [5; 3; 5; 2; 9; 3; 5; 3; 6; 3; 1; 4; 8];
  canonical_cons #10 6 [3; 5; 3; 5; 2; 9; 3; 5; 3; 6; 3; 1; 4; 8];
  canonical_cons #10 4 [6; 3; 5; 3; 5; 2; 9; 3; 5; 3; 6; 3; 1; 4; 8];
  canonical_cons #10 5 [4; 6; 3; 5; 3; 5; 2; 9; 3; 5; 3; 6; 3; 1; 4; 8];
  canonical_cons #10 1 [5; 4; 6; 3; 5; 3; 5; 2; 9; 3; 5; 3; 6; 3; 1; 4; 8];
  canonical_cons #10 7 [1; 5; 4; 6; 3; 5; 3; 5; 2; 9; 3; 5; 3; 6; 3; 1; 4; 8];
  canonical_cons #10 4 [7; 1; 5; 4; 6; 3; 5; 3; 5; 2; 9; 3; 5; 3; 6; 3; 1; 4; 8];
  canonical_cons #10 9 [4; 7; 1; 5; 4; 6; 3; 5; 3; 5; 2; 9; 3; 5; 3; 6; 3; 1; 4; 8];
  ()

let canonical_next2_target () : Lemma (canonical #10 next2_target) =
  assert (canonical #10 [1]);
  canonical_cons #10 7 [1];
  canonical_cons #10 9 [7; 1];
  canonical_cons #10 5 [9; 7; 1];
  canonical_cons #10 2 [5; 9; 7; 1];
  canonical_cons #10 9 [2; 5; 9; 7; 1];
  canonical_cons #10 8 [9; 2; 5; 9; 7; 1];
  canonical_cons #10 2 [8; 9; 2; 5; 9; 7; 1];
  canonical_cons #10 7 [2; 8; 9; 2; 5; 9; 7; 1];
  canonical_cons #10 0 [7; 2; 8; 9; 2; 5; 9; 7; 1];
  canonical_cons #10 6 [0; 7; 2; 8; 9; 2; 5; 9; 7; 1];
  canonical_cons #10 8 [6; 0; 7; 2; 8; 9; 2; 5; 9; 7; 1];
  canonical_cons #10 6 [8; 6; 0; 7; 2; 8; 9; 2; 5; 9; 7; 1];
  canonical_cons #10 0 [6; 8; 6; 0; 7; 2; 8; 9; 2; 5; 9; 7; 1];
  canonical_cons #10 7 [0; 6; 8; 6; 0; 7; 2; 8; 9; 2; 5; 9; 7; 1];
  canonical_cons #10 2 [7; 0; 6; 8; 6; 0; 7; 2; 8; 9; 2; 5; 9; 7; 1];
  canonical_cons #10 7 [2; 7; 0; 6; 8; 6; 0; 7; 2; 8; 9; 2; 5; 9; 7; 1];
  canonical_cons #10 3 [7; 2; 7; 0; 6; 8; 6; 0; 7; 2; 8; 9; 2; 5; 9; 7; 1];
  canonical_cons #10 5 [3; 7; 2; 7; 0; 6; 8; 6; 0; 7; 2; 8; 9; 2; 5; 9; 7; 1];
  canonical_cons #10 9 [5; 3; 7; 2; 7; 0; 6; 8; 6; 0; 7; 2; 8; 9; 2; 5; 9; 7; 1];
  canonical_cons #10 7 [9; 5; 3; 7; 2; 7; 0; 6; 8; 6; 0; 7; 2; 8; 9; 2; 5; 9; 7; 1];
  canonical_cons #10 9 [7; 9; 5; 3; 7; 2; 7; 0; 6; 8; 6; 0; 7; 2; 8; 9; 2; 5; 9; 7; 1];
  canonical_cons #10 7 [9; 7; 9; 5; 3; 7; 2; 7; 0; 6; 8; 6; 0; 7; 2; 8; 9; 2; 5; 9; 7; 1];
  ()

let reverse_digits_next2_source () : Lemma (
    reverse_digits #10 next2_source == next2_reversed) =
  ReverseAddNext.canonical_next_target ();
  reverse_list_next2_source ();
  value_next2_reversed ();
  canonical_next2_reversed ();
  reverse_digits_canonical #10 next2_source;
  normalize_value #10 (rev next2_source);
  assert (value (reverse_digits #10 next2_source) ==
    848143635392536451749);
  digits_of_nat_of_canonical #10 (reverse_digits #10 next2_source);
  digits_of_nat_of_canonical #10 next2_reversed;
  assert (reverse_digits #10 next2_source == next2_reversed);
  ()

let reverse_add_947154635293536341848_to_1795298270686072793597 () : Lemma (
    reverse_add #10 next2_source == next2_target) =
  ReverseAddNext.canonical_next_target ();
  reverse_add_value #10 next2_source;
  ReverseAddNext.value_next_target ();
  reverse_digits_next2_source ();
  value_next2_reversed ();
  value_next2_target ();
  assert (value (reverse_add #10 next2_source) ==
    1795298270686072793597);
  reverse_add_canonical #10 next2_source;
  digits_of_nat_of_canonical #10 (reverse_add #10 next2_source);
  canonical_next2_target ();
  digits_of_nat_of_canonical #10 next2_target;
  assert (reverse_add #10 next2_source == next2_target);
  ()

let trace_digits_profile_947154635293536341848 () : Lemma (
    trace_digits next2_source == next2_target) =
  reverse_add_947154635293536341848_to_1795298270686072793597 ();
  trace_digits_equals_reverse_add next2_source;
  assert (trace_digits next2_source == next2_target);
  ()

let trace_carries_next2_source () : Lemma (trace_carries next2_source ==
    [0; 1; 0; 1; 0; 0; 0; 1; 0; 1; 0; 1; 0; 1; 0; 1; 0; 0; 0; 1; 0; 1]) =
  reverse_list_next2_source ();
  assert (trace_carries next2_source ==
    (add_trace #10 next2_source next2_reversed 0).carries);
  add_trace_carries_step #10 8 9
    [4; 8; 1; 4; 3; 6; 3; 5; 3; 9; 2; 5; 3; 6; 4; 5; 1; 7; 4; 9]
    [4; 7; 1; 5; 4; 6; 3; 5; 2; 9; 3; 5; 3; 6; 3; 4; 1; 8; 4; 8] 0;
  add_trace_carries_step #10 4 4
    [8; 1; 4; 3; 6; 3; 5; 3; 9; 2; 5; 3; 6; 4; 5; 1; 7; 4; 9]
    [7; 1; 5; 4; 6; 3; 5; 2; 9; 3; 5; 3; 6; 3; 4; 1; 8; 4; 8] 1;
  add_trace_carries_step #10 8 7
    [1; 4; 3; 6; 3; 5; 3; 9; 2; 5; 3; 6; 4; 5; 1; 7; 4; 9]
    [1; 5; 4; 6; 3; 5; 2; 9; 3; 5; 3; 6; 3; 4; 1; 8; 4; 8] 0;
  add_trace_carries_step #10 1 1
    [4; 3; 6; 3; 5; 3; 9; 2; 5; 3; 6; 4; 5; 1; 7; 4; 9]
    [5; 4; 6; 3; 5; 2; 9; 3; 5; 3; 6; 3; 4; 1; 8; 4; 8] 1;
  add_trace_carries_step #10 4 5
    [3; 6; 3; 5; 3; 9; 2; 5; 3; 6; 4; 5; 1; 7; 4; 9]
    [4; 6; 3; 5; 2; 9; 3; 5; 3; 6; 3; 4; 1; 8; 4; 8] 0;
  add_trace_carries_step #10 3 4
    [6; 3; 5; 3; 9; 2; 5; 3; 6; 4; 5; 1; 7; 4; 9]
    [6; 3; 5; 2; 9; 3; 5; 3; 6; 3; 4; 1; 8; 4; 8] 0;
  add_trace_carries_step #10 6 6
    [3; 5; 3; 9; 2; 5; 3; 6; 4; 5; 1; 7; 4; 9]
    [3; 5; 2; 9; 3; 5; 3; 6; 3; 4; 1; 8; 4; 8] 0;
  add_trace_carries_step #10 3 3
    [5; 3; 9; 2; 5; 3; 6; 4; 5; 1; 7; 4; 9]
    [5; 2; 9; 3; 5; 3; 6; 3; 4; 1; 8; 4; 8] 1;
  add_trace_carries_step #10 5 5
    [3; 9; 2; 5; 3; 6; 4; 5; 1; 7; 4; 9]
    [2; 9; 3; 5; 3; 6; 3; 4; 1; 8; 4; 8] 0;
  add_trace_carries_step #10 3 2
    [9; 2; 5; 3; 6; 4; 5; 1; 7; 4; 9]
    [9; 3; 5; 3; 6; 3; 4; 1; 8; 4; 8] 1;
  add_trace_carries_step #10 9 9
    [2; 5; 3; 6; 4; 5; 1; 7; 4; 9]
    [3; 5; 3; 6; 3; 4; 1; 8; 4; 8] 0;
  add_trace_carries_step #10 2 3
    [5; 3; 6; 4; 5; 1; 7; 4; 9]
    [5; 3; 6; 3; 4; 1; 8; 4; 8] 1;
  add_trace_carries_step #10 5 5
    [3; 6; 4; 5; 1; 7; 4; 9]
    [3; 6; 3; 4; 1; 8; 4; 8] 0;
  add_trace_carries_step #10 3 3
    [6; 4; 5; 1; 7; 4; 9]
    [6; 3; 4; 1; 8; 4; 8] 1;
  add_trace_carries_step #10 6 6
    [4; 5; 1; 7; 4; 9]
    [3; 4; 1; 8; 4; 8] 0;
  add_trace_carries_step #10 4 3
    [5; 1; 7; 4; 9]
    [4; 1; 8; 4; 8] 1;
  add_trace_carries_step #10 5 4
    [1; 7; 4; 9]
    [1; 8; 4; 8] 0;
  add_trace_carries_step #10 1 1
    [7; 4; 9]
    [8; 4; 8] 0;
  add_trace_carries_step #10 7 8
    [4; 9]
    [4; 8] 0;
  add_trace_carries_step #10 4 4
    [9]
    [8] 1;
  add_trace_carries_step #10 9 8 [] [] 0;
  assert ((add_trace #10 [] [] 1).carries == [1]);
  assert ((add_trace #10 next2_source next2_reversed 0).carries ==
    [0; 1; 0; 1; 0; 0; 0; 1; 0; 1; 0; 1; 0; 1; 0; 1; 0; 0; 0; 1; 0; 1]);
  ()

let trace_profile_shape_947154635293536341848 () : Lemma (
    length (trace_digits next2_source) == length next2_source + 1) =
  trace_digits_profile_947154635293536341848 ();
  length_of_eq #(digit 10) (trace_digits next2_source) next2_target;
  assert (length next2_target == length next2_source + 1);
  ()

let trace_profile_final_carry_947154635293536341848 () : Lemma (
    nth (trace_carries next2_source) (length next2_source) == Some 1) =
  trace_profile_shape_947154635293536341848 ();
  ReverseAddContinuation.final_carry_from_overflow_length next2_source;
  ()

let trace_profile_sums_947154635293536341848 () : Lemma (
    trace_sum_at next2_source 0 == 17 /\
    trace_sum_at next2_source 1 == 8 /\
    trace_sum_at next2_source 20 == 17) =
  reverse_list_next2_source ();
  ()

let trace_profile_carry_facts_947154635293536341848 () : Lemma (
    trace_carry_at next2_source 1 == 1 /\
    trace_carry_at next2_source 20 == 0 /\
    trace_carry_at next2_source 2 == 0 /\
    trace_carry_at next2_source 21 == 1) =
  trace_carries_next2_source ();
  ()

let overflow_precondition_1795298270686072793597 () : Lemma (
    canonical #10 next2_source /\
    next2_source <> [] /\
    length (trace_digits next2_source) == length next2_source + 1 /\
    nth (trace_carries next2_source) (length next2_source) == Some 1 /\
    1 <= trace_sum_at next2_source 0 /\
    trace_sum_at next2_source 0 <= 18 /\
    trace_sum_at next2_source 0 <> 10 /\
    exists (i:nat). 0 < i /\ i < length next2_source /\
      trace_sum_at next2_source i +
          trace_sum_at next2_source (length next2_source - i) +
          trace_carry_at next2_source i +
          trace_carry_at next2_source (length next2_source - i) >=
        10 + 10 *
          (trace_carry_at next2_source (i + 1) +
           trace_carry_at next2_source (length next2_source - i + 1))) =
  ReverseAddNext.canonical_next_target ();
  assert (next2_source <> []);
  trace_profile_shape_947154635293536341848 ();
  trace_profile_final_carry_947154635293536341848 ();
  trace_profile_sums_947154635293536341848 ();
  trace_profile_carry_facts_947154635293536341848 ();
  assert (1 <= trace_sum_at next2_source 0 /\
    trace_sum_at next2_source 0 <= 18);
  assert (trace_sum_at next2_source 0 <> 10);
  let n : nat = length next2_source in
  exists_intro
    (fun (i:nat) -> 0 < i /\ i < n /\
      trace_sum_at next2_source i +
          trace_sum_at next2_source (n - i) +
          trace_carry_at next2_source i +
          trace_carry_at next2_source (n - i) >=
        10 + 10 *
          (trace_carry_at next2_source (i + 1) +
           trace_carry_at next2_source (n - i + 1)))
    1;
  ()

let local_profile_witness_1795298270686072793597 () : Lemma (
    trace_local_profile_complement_witness next2_target) =
  overflow_precondition_1795298270686072793597 ();
  reverse_add_947154635293536341848_to_1795298270686072793597 ();
  overflow_internal_cell_implies_next_witness next2_source;
  ()

let next3_source : numeral 10 = next2_target

let next3_reversed : numeral 10 =
  [1; 7; 9; 5; 2; 9; 8; 2; 7; 0; 6; 8; 6; 0; 7; 2; 7; 9; 3; 5; 9; 7]

let next3_target : numeral 10 =
  [8; 6; 5; 9; 1; 7; 1; 0; 8; 6; 4; 5; 7; 7; 9; 0; 7; 2; 9; 4; 7; 9]

let reverse_list_next3_source () : Lemma (rev next3_source == next3_reversed) =
  assert (rev [1] == [1]);
  rev_cons 7 [1];
  rev_cons 9 [7; 1];
  rev_cons 5 [9; 7; 1];
  rev_cons 3 [5; 9; 7; 1];
  rev_cons 9 [3; 5; 9; 7; 1];
  rev_cons 7 [9; 3; 5; 9; 7; 1];
  rev_cons 2 [7; 9; 3; 5; 9; 7; 1];
  rev_cons 7 [2; 7; 9; 3; 5; 9; 7; 1];
  rev_cons 0 [7; 2; 7; 9; 3; 5; 9; 7; 1];
  rev_cons 6 [0; 7; 2; 7; 9; 3; 5; 9; 7; 1];
  rev_cons 8 [6; 0; 7; 2; 7; 9; 3; 5; 9; 7; 1];
  rev_cons 6 [8; 6; 0; 7; 2; 7; 9; 3; 5; 9; 7; 1];
  rev_cons 0 [6; 8; 6; 0; 7; 2; 7; 9; 3; 5; 9; 7; 1];
  rev_cons 7 [0; 6; 8; 6; 0; 7; 2; 7; 9; 3; 5; 9; 7; 1];
  rev_cons 2 [7; 0; 6; 8; 6; 0; 7; 2; 7; 9; 3; 5; 9; 7; 1];
  rev_cons 9 [2; 7; 0; 6; 8; 6; 0; 7; 2; 7; 9; 3; 5; 9; 7; 1];
  rev_cons 1 [9; 2; 7; 0; 6; 8; 6; 0; 7; 2; 7; 9; 3; 5; 9; 7; 1];
  rev_cons 5 [1; 9; 2; 7; 0; 6; 8; 6; 0; 7; 2; 7; 9; 3; 5; 9; 7; 1];
  rev_cons 9 [5; 1; 9; 2; 7; 0; 6; 8; 6; 0; 7; 2; 7; 9; 3; 5; 9; 7; 1];
  rev_cons 7 [9; 5; 1; 9; 2; 7; 0; 6; 8; 6; 0; 7; 2; 7; 9; 3; 5; 9; 7; 1];
  ()

let value_next3_reversed () : Lemma (
    value next3_reversed == 7953972706860728925971) =
  value_cons #10 1 [7; 9; 5; 2; 9; 8; 2; 7; 0; 6; 8; 6; 0; 7; 2; 7; 9; 3; 5; 9; 7];
  value_cons #10 7 [9; 5; 2; 9; 8; 2; 7; 0; 6; 8; 6; 0; 7; 2; 7; 9; 3; 5; 9; 7];
  value_cons #10 9 [5; 2; 9; 8; 2; 7; 0; 6; 8; 6; 0; 7; 2; 7; 9; 3; 5; 9; 7];
  value_cons #10 5 [2; 9; 8; 2; 7; 0; 6; 8; 6; 0; 7; 2; 7; 9; 3; 5; 9; 7];
  value_cons #10 2 [9; 8; 2; 7; 0; 6; 8; 6; 0; 7; 2; 7; 9; 3; 5; 9; 7];
  value_cons #10 9 [8; 2; 7; 0; 6; 8; 6; 0; 7; 2; 7; 9; 3; 5; 9; 7];
  value_cons #10 8 [2; 7; 0; 6; 8; 6; 0; 7; 2; 7; 9; 3; 5; 9; 7];
  value_cons #10 2 [7; 0; 6; 8; 6; 0; 7; 2; 7; 9; 3; 5; 9; 7];
  value_cons #10 7 [0; 6; 8; 6; 0; 7; 2; 7; 9; 3; 5; 9; 7];
  value_cons #10 0 [6; 8; 6; 0; 7; 2; 7; 9; 3; 5; 9; 7];
  value_cons #10 6 [8; 6; 0; 7; 2; 7; 9; 3; 5; 9; 7];
  value_cons #10 8 [6; 0; 7; 2; 7; 9; 3; 5; 9; 7];
  value_cons #10 6 [0; 7; 2; 7; 9; 3; 5; 9; 7];
  value_cons #10 0 [7; 2; 7; 9; 3; 5; 9; 7];
  value_cons #10 7 [2; 7; 9; 3; 5; 9; 7];
  value_cons #10 2 [7; 9; 3; 5; 9; 7];
  value_cons #10 7 [9; 3; 5; 9; 7];
  value_cons #10 9 [3; 5; 9; 7];
  value_cons #10 3 [5; 9; 7];
  value_cons #10 5 [9; 7];
  value_cons #10 9 [7];
  value_cons #10 7 [];
  ()

let value_next3_target () : Lemma (
    value next3_target == 9749270977546801719568) =
  value_cons #10 8 [6; 5; 9; 1; 7; 1; 0; 8; 6; 4; 5; 7; 7; 9; 0; 7; 2; 9; 4; 7; 9];
  value_cons #10 6 [5; 9; 1; 7; 1; 0; 8; 6; 4; 5; 7; 7; 9; 0; 7; 2; 9; 4; 7; 9];
  value_cons #10 5 [9; 1; 7; 1; 0; 8; 6; 4; 5; 7; 7; 9; 0; 7; 2; 9; 4; 7; 9];
  value_cons #10 9 [1; 7; 1; 0; 8; 6; 4; 5; 7; 7; 9; 0; 7; 2; 9; 4; 7; 9];
  value_cons #10 1 [7; 1; 0; 8; 6; 4; 5; 7; 7; 9; 0; 7; 2; 9; 4; 7; 9];
  value_cons #10 7 [1; 0; 8; 6; 4; 5; 7; 7; 9; 0; 7; 2; 9; 4; 7; 9];
  value_cons #10 1 [0; 8; 6; 4; 5; 7; 7; 9; 0; 7; 2; 9; 4; 7; 9];
  value_cons #10 0 [8; 6; 4; 5; 7; 7; 9; 0; 7; 2; 9; 4; 7; 9];
  value_cons #10 8 [6; 4; 5; 7; 7; 9; 0; 7; 2; 9; 4; 7; 9];
  value_cons #10 6 [4; 5; 7; 7; 9; 0; 7; 2; 9; 4; 7; 9];
  value_cons #10 4 [5; 7; 7; 9; 0; 7; 2; 9; 4; 7; 9];
  value_cons #10 5 [7; 7; 9; 0; 7; 2; 9; 4; 7; 9];
  value_cons #10 7 [7; 9; 0; 7; 2; 9; 4; 7; 9];
  value_cons #10 7 [9; 0; 7; 2; 9; 4; 7; 9];
  value_cons #10 9 [0; 7; 2; 9; 4; 7; 9];
  value_cons #10 0 [7; 2; 9; 4; 7; 9];
  value_cons #10 7 [2; 9; 4; 7; 9];
  value_cons #10 2 [9; 4; 7; 9];
  value_cons #10 9 [4; 7; 9];
  value_cons #10 4 [7; 9];
  value_cons #10 7 [9];
  value_cons #10 9 [];
  ()

let canonical_next3_reversed () : Lemma (canonical #10 next3_reversed) =
  assert (canonical #10 [7]);
  canonical_cons #10 9 [7];
  canonical_cons #10 5 [9; 7];
  canonical_cons #10 3 [5; 9; 7];
  canonical_cons #10 9 [3; 5; 9; 7];
  canonical_cons #10 7 [9; 3; 5; 9; 7];
  canonical_cons #10 2 [7; 9; 3; 5; 9; 7];
  canonical_cons #10 7 [2; 7; 9; 3; 5; 9; 7];
  canonical_cons #10 0 [7; 2; 7; 9; 3; 5; 9; 7];
  canonical_cons #10 6 [0; 7; 2; 7; 9; 3; 5; 9; 7];
  canonical_cons #10 8 [6; 0; 7; 2; 7; 9; 3; 5; 9; 7];
  canonical_cons #10 6 [8; 6; 0; 7; 2; 7; 9; 3; 5; 9; 7];
  canonical_cons #10 0 [6; 8; 6; 0; 7; 2; 7; 9; 3; 5; 9; 7];
  canonical_cons #10 7 [0; 6; 8; 6; 0; 7; 2; 7; 9; 3; 5; 9; 7];
  canonical_cons #10 2 [7; 0; 6; 8; 6; 0; 7; 2; 7; 9; 3; 5; 9; 7];
  canonical_cons #10 9 [2; 7; 0; 6; 8; 6; 0; 7; 2; 7; 9; 3; 5; 9; 7];
  canonical_cons #10 1 [9; 2; 7; 0; 6; 8; 6; 0; 7; 2; 7; 9; 3; 5; 9; 7];
  canonical_cons #10 5 [1; 9; 2; 7; 0; 6; 8; 6; 0; 7; 2; 7; 9; 3; 5; 9; 7];
  canonical_cons #10 9 [5; 1; 9; 2; 7; 0; 6; 8; 6; 0; 7; 2; 7; 9; 3; 5; 9; 7];
  canonical_cons #10 7 [9; 5; 1; 9; 2; 7; 0; 6; 8; 6; 0; 7; 2; 7; 9; 3; 5; 9; 7];
  ()

let canonical_next3_target () : Lemma (canonical #10 next3_target) =
  assert (canonical #10 [9]);
  canonical_cons #10 7 [9];
  canonical_cons #10 4 [7; 9];
  canonical_cons #10 2 [4; 7; 9];
  canonical_cons #10 7 [2; 4; 7; 9];
  canonical_cons #10 0 [7; 2; 4; 7; 9];
  canonical_cons #10 9 [0; 7; 2; 4; 7; 9];
  canonical_cons #10 7 [9; 0; 7; 2; 4; 7; 9];
  canonical_cons #10 7 [7; 9; 0; 7; 2; 4; 7; 9];
  canonical_cons #10 5 [7; 7; 9; 0; 7; 2; 4; 7; 9];
  canonical_cons #10 4 [5; 7; 7; 9; 0; 7; 2; 4; 7; 9];
  canonical_cons #10 6 [4; 5; 7; 7; 9; 0; 7; 2; 4; 7; 9];
  canonical_cons #10 8 [6; 4; 5; 7; 7; 9; 0; 7; 2; 4; 7; 9];
  canonical_cons #10 0 [8; 6; 4; 5; 7; 7; 9; 0; 7; 2; 4; 7; 9];
  canonical_cons #10 1 [0; 8; 6; 4; 5; 7; 7; 9; 0; 7; 2; 4; 7; 9];
  canonical_cons #10 7 [1; 0; 8; 6; 4; 5; 7; 7; 9; 0; 7; 2; 4; 7; 9];
  canonical_cons #10 1 [7; 1; 0; 8; 6; 4; 5; 7; 7; 9; 0; 7; 2; 4; 7; 9];
  canonical_cons #10 9 [1; 7; 1; 0; 8; 6; 4; 5; 7; 7; 9; 0; 7; 2; 4; 7; 9];
  canonical_cons #10 5 [9; 1; 7; 1; 0; 8; 6; 4; 5; 7; 7; 9; 0; 7; 2; 4; 7; 9];
  canonical_cons #10 9 [5; 9; 1; 7; 1; 0; 8; 6; 4; 5; 7; 7; 9; 0; 7; 2; 4; 7; 9];
  ()

let reverse_digits_next3_source () : Lemma (
    reverse_digits #10 next3_source == next3_reversed) =
  ReverseAddNext.canonical_next2_target ();
  reverse_list_next3_source ();
  value_next3_reversed ();
  canonical_next3_reversed ();
  reverse_digits_canonical #10 next3_source;
  normalize_value #10 (rev next3_source);
  assert (value (reverse_digits #10 next3_source) ==
    7953972706860728925971);
  digits_of_nat_of_canonical #10 (reverse_digits #10 next3_source);
  digits_of_nat_of_canonical #10 next3_reversed;
  assert (reverse_digits #10 next3_source == next3_reversed);
  ()

let reverse_add_1795298270686072793597_to_9749270977546801719568 () : Lemma (
    reverse_add #10 next3_source == next3_target) =
  ReverseAddNext.canonical_next2_target ();
  reverse_add_value #10 next3_source;
  ReverseAddNext.value_next2_target ();
  reverse_digits_next3_source ();
  value_next3_reversed ();
  value_next3_target ();
  assert (value (reverse_add #10 next3_source) ==
    9749270977546801719568);
  reverse_add_canonical #10 next3_source;
  digits_of_nat_of_canonical #10 (reverse_add #10 next3_source);
  canonical_next3_target ();
  digits_of_nat_of_canonical #10 next3_target;
  assert (reverse_add #10 next3_source == next3_target);
  ()

let trace_digits_profile_1795298270686072793597 () : Lemma (
    trace_digits next3_source == next3_target) =
  reverse_add_1795298270686072793597_to_9749270977546801719568 ();
  trace_digits_equals_reverse_add next3_source;
  assert (trace_digits next3_source == next3_target);
  ()

let trace_profile_shape_1795298270686072793597 () : Lemma (
    length (trace_digits next3_source) == length next3_source) =
  trace_digits_profile_1795298270686072793597 ();
  length_of_eq #(digit 10) (trace_digits next3_source) next3_target;
  assert (length next3_target == length next3_source);
  ()

let trace_profile_final_carry_1795298270686072793597 () : Lemma (
    nth (trace_carries next3_source) (length next3_source) == Some 0) =
  trace_profile_shape_1795298270686072793597 ();
  final_carry_from_length next3_source;
  ()

let local_profile_witness_9749270977546801719568 () : Lemma (
    trace_local_profile_complement_witness next3_target) =
  ReverseAddNext.canonical_next2_target ();
  trace_profile_shape_1795298270686072793597 ();
  trace_profile_final_carry_1795298270686072793597 ();
  assert (trace_sum_at next3_source 0 == 8);
  reverse_add_1795298270686072793597_to_9749270977546801719568 ();
  no_overflow_outer_sum_6_to_9_implies_next_witness next3_source;
  ()

let next4_source : numeral 10 = next3_target

let next4_reversed : numeral 10 =
  [9; 7; 4; 9; 2; 7; 0; 9; 7; 7; 5; 4; 6; 8; 0; 1; 7; 1; 9; 5; 6; 8]

let next4_target : numeral 10 =
  [7; 4; 0; 9; 4; 4; 2; 9; 5; 4; 0; 0; 4; 6; 0; 2; 4; 4; 8; 0; 4; 8; 1]

let reverse_list_next4_source () : Lemma (rev next4_source == next4_reversed) =
  assert (rev [9] == [9]);
  rev_cons 7 [9];
  rev_cons 4 [7; 9];
  rev_cons 5 [4; 7; 9];
  rev_cons 9 [5; 4; 7; 9];
  rev_cons 1 [9; 5; 4; 7; 9];
  rev_cons 2 [1; 9; 5; 4; 7; 9];
  rev_cons 7 [2; 1; 9; 5; 4; 7; 9];
  rev_cons 0 [7; 2; 1; 9; 5; 4; 7; 9];
  rev_cons 9 [0; 7; 2; 1; 9; 5; 4; 7; 9];
  rev_cons 7 [9; 0; 7; 2; 1; 9; 5; 4; 7; 9];
  rev_cons 7 [7; 9; 0; 7; 2; 1; 9; 5; 4; 7; 9];
  rev_cons 6 [7; 7; 9; 0; 7; 2; 1; 9; 5; 4; 7; 9];
  rev_cons 4 [6; 7; 7; 9; 0; 7; 2; 1; 9; 5; 4; 7; 9];
  rev_cons 5 [4; 6; 7; 7; 9; 0; 7; 2; 1; 9; 5; 4; 7; 9];
  rev_cons 0 [5; 4; 6; 7; 7; 9; 0; 7; 2; 1; 9; 5; 4; 7; 9];
  rev_cons 1 [0; 5; 4; 6; 7; 7; 9; 0; 7; 2; 1; 9; 5; 4; 7; 9];
  rev_cons 7 [1; 0; 5; 4; 6; 7; 7; 9; 0; 7; 2; 1; 9; 5; 4; 7; 9];
  rev_cons 2 [7; 1; 0; 5; 4; 6; 7; 7; 9; 0; 7; 2; 1; 9; 5; 4; 7; 9];
  rev_cons 9 [2; 7; 1; 0; 5; 4; 6; 7; 7; 9; 0; 7; 2; 1; 9; 5; 4; 7; 9];
  rev_cons 8 [9; 2; 7; 1; 0; 5; 4; 6; 7; 7; 9; 0; 7; 2; 1; 9; 5; 4; 7; 9];
  ()

let value_next4_reversed () : Lemma (
    value next4_reversed == 8659171086457790729479) =
  value_cons #10 9 [7; 4; 9; 2; 7; 0; 9; 7; 7; 5; 4; 6; 8; 0; 1; 7; 1; 9; 5; 6; 8];
  value_cons #10 7 [4; 9; 2; 7; 0; 9; 7; 7; 5; 4; 6; 8; 0; 1; 7; 1; 9; 5; 6; 8];
  value_cons #10 4 [9; 2; 7; 0; 9; 7; 7; 5; 4; 6; 8; 0; 1; 7; 1; 9; 5; 6; 8];
  value_cons #10 9 [2; 7; 0; 9; 7; 7; 5; 4; 6; 8; 0; 1; 7; 1; 9; 5; 6; 8];
  value_cons #10 2 [7; 0; 9; 7; 7; 5; 4; 6; 8; 0; 1; 7; 1; 9; 5; 6; 8];
  value_cons #10 7 [0; 9; 7; 7; 5; 4; 6; 8; 0; 1; 7; 1; 9; 5; 6; 8];
  value_cons #10 0 [9; 7; 7; 5; 4; 6; 8; 0; 1; 7; 1; 9; 5; 6; 8];
  value_cons #10 9 [7; 7; 5; 4; 6; 8; 0; 1; 7; 1; 9; 5; 6; 8];
  value_cons #10 7 [7; 5; 4; 6; 8; 0; 1; 7; 1; 9; 5; 6; 8];
  value_cons #10 7 [5; 4; 6; 8; 0; 1; 7; 1; 9; 5; 6; 8];
  value_cons #10 5 [4; 6; 8; 0; 1; 7; 1; 9; 5; 6; 8];
  value_cons #10 4 [6; 8; 0; 1; 7; 1; 9; 5; 6; 8];
  value_cons #10 6 [8; 0; 1; 7; 1; 9; 5; 6; 8];
  value_cons #10 8 [0; 1; 7; 1; 9; 5; 6; 8];
  value_cons #10 0 [1; 7; 1; 9; 5; 6; 8];
  value_cons #10 1 [7; 1; 9; 5; 6; 8];
  value_cons #10 7 [1; 9; 5; 6; 8];
  value_cons #10 1 [9; 5; 6; 8];
  value_cons #10 9 [5; 6; 8];
  value_cons #10 5 [6; 8];
  value_cons #10 6 [8];
  value_cons #10 8 [];
  ()

let value_next4_target () : Lemma (
    value next4_target == 18408442064004592449047) =
  value_cons #10 7 [4; 0; 9; 4; 4; 2; 9; 5; 4; 0; 0; 4; 6; 0; 2; 4; 4; 8; 0; 4; 8; 1];
  value_cons #10 4 [0; 9; 4; 4; 2; 9; 5; 4; 0; 0; 4; 6; 0; 2; 4; 4; 8; 0; 4; 8; 1];
  value_cons #10 0 [9; 4; 4; 2; 9; 5; 4; 0; 0; 4; 6; 0; 2; 4; 4; 8; 0; 4; 8; 1];
  value_cons #10 9 [4; 4; 2; 9; 5; 4; 0; 0; 4; 6; 0; 2; 4; 4; 8; 0; 4; 8; 1];
  value_cons #10 4 [4; 2; 9; 5; 4; 0; 0; 4; 6; 0; 2; 4; 4; 8; 0; 4; 8; 1];
  value_cons #10 4 [2; 9; 5; 4; 0; 0; 4; 6; 0; 2; 4; 4; 8; 0; 4; 8; 1];
  value_cons #10 2 [9; 5; 4; 0; 0; 4; 6; 0; 2; 4; 4; 8; 0; 4; 8; 1];
  value_cons #10 9 [5; 4; 0; 0; 4; 6; 0; 2; 4; 4; 8; 0; 4; 8; 1];
  value_cons #10 5 [4; 0; 0; 4; 6; 0; 2; 4; 4; 8; 0; 4; 8; 1];
  value_cons #10 4 [0; 0; 4; 6; 0; 2; 4; 4; 8; 0; 4; 8; 1];
  value_cons #10 0 [0; 4; 6; 0; 2; 4; 4; 8; 0; 4; 8; 1];
  value_cons #10 0 [4; 6; 0; 2; 4; 4; 8; 0; 4; 8; 1];
  value_cons #10 4 [6; 0; 2; 4; 4; 8; 0; 4; 8; 1];
  value_cons #10 6 [0; 2; 4; 4; 8; 0; 4; 8; 1];
  value_cons #10 0 [2; 4; 4; 8; 0; 4; 8; 1];
  value_cons #10 2 [4; 4; 8; 0; 4; 8; 1];
  value_cons #10 4 [4; 8; 0; 4; 8; 1];
  value_cons #10 4 [8; 0; 4; 8; 1];
  value_cons #10 8 [0; 4; 8; 1];
  value_cons #10 0 [4; 8; 1];
  value_cons #10 4 [8; 1];
  value_cons #10 8 [1];
  value_cons #10 1 [];
  ()

let canonical_next4_reversed () : Lemma (canonical #10 next4_reversed) =
  assert (canonical #10 [8]);
  canonical_cons #10 6 [8];
  canonical_cons #10 5 [6; 8];
  canonical_cons #10 1 [5; 6; 8];
  canonical_cons #10 0 [1; 5; 6; 8];
  canonical_cons #10 7 [0; 1; 5; 6; 8];
  canonical_cons #10 1 [7; 0; 1; 5; 6; 8];
  canonical_cons #10 8 [1; 7; 0; 1; 5; 6; 8];
  canonical_cons #10 4 [8; 1; 7; 0; 1; 5; 6; 8];
  canonical_cons #10 5 [4; 8; 1; 7; 0; 1; 5; 6; 8];
  canonical_cons #10 7 [5; 4; 8; 1; 7; 0; 1; 5; 6; 8];
  canonical_cons #10 7 [7; 5; 4; 8; 1; 7; 0; 1; 5; 6; 8];
  canonical_cons #10 9 [7; 7; 5; 4; 8; 1; 7; 0; 1; 5; 6; 8];
  canonical_cons #10 0 [9; 7; 7; 5; 4; 8; 1; 7; 0; 1; 5; 6; 8];
  canonical_cons #10 7 [0; 9; 7; 7; 5; 4; 8; 1; 7; 0; 1; 5; 6; 8];
  canonical_cons #10 2 [7; 0; 9; 7; 7; 5; 4; 8; 1; 7; 0; 1; 5; 6; 8];
  canonical_cons #10 9 [2; 7; 0; 9; 7; 7; 5; 4; 8; 1; 7; 0; 1; 5; 6; 8];
  canonical_cons #10 4 [9; 2; 7; 0; 9; 7; 7; 5; 4; 8; 1; 7; 0; 1; 5; 6; 8];
  canonical_cons #10 7 [4; 9; 2; 7; 0; 9; 7; 7; 5; 4; 8; 1; 7; 0; 1; 5; 6; 8];
  canonical_cons #10 9 [7; 4; 9; 2; 7; 0; 9; 7; 7; 5; 4; 8; 1; 7; 0; 1; 5; 6; 8];
  ()

let canonical_next4_target () : Lemma (canonical #10 next4_target) =
  assert (canonical #10 [1]);
  canonical_cons #10 8 [1];
  canonical_cons #10 4 [8; 1];
  canonical_cons #10 0 [4; 8; 1];
  canonical_cons #10 8 [0; 4; 8; 1];
  canonical_cons #10 4 [8; 0; 4; 8; 1];
  canonical_cons #10 0 [4; 8; 0; 4; 8; 1];
  canonical_cons #10 6 [0; 4; 8; 0; 4; 8; 1];
  canonical_cons #10 4 [6; 0; 4; 8; 0; 4; 8; 1];
  canonical_cons #10 4 [4; 6; 0; 4; 8; 0; 4; 8; 1];
  canonical_cons #10 2 [4; 4; 6; 0; 4; 8; 0; 4; 8; 1];
  canonical_cons #10 0 [2; 4; 4; 6; 0; 4; 8; 0; 4; 8; 1];
  canonical_cons #10 0 [0; 2; 4; 4; 6; 0; 4; 8; 0; 4; 8; 1];
  canonical_cons #10 4 [0; 0; 2; 4; 4; 6; 0; 4; 8; 0; 4; 8; 1];
  canonical_cons #10 5 [4; 0; 0; 2; 4; 4; 6; 0; 4; 8; 0; 4; 8; 1];
  canonical_cons #10 9 [5; 4; 0; 0; 2; 4; 4; 6; 0; 4; 8; 0; 4; 8; 1];
  canonical_cons #10 2 [9; 5; 4; 0; 0; 2; 4; 4; 6; 0; 4; 8; 0; 4; 8; 1];
  canonical_cons #10 4 [2; 9; 5; 4; 0; 0; 2; 4; 4; 6; 0; 4; 8; 0; 4; 8; 1];
  canonical_cons #10 4 [4; 2; 9; 5; 4; 0; 0; 2; 4; 4; 6; 0; 4; 8; 0; 4; 8; 1];
  canonical_cons #10 9 [4; 4; 2; 9; 5; 4; 0; 0; 2; 4; 4; 6; 0; 4; 8; 0; 4; 8; 1];
  canonical_cons #10 4 [9; 4; 4; 2; 9; 5; 4; 0; 0; 2; 4; 4; 6; 0; 4; 8; 0; 4; 8; 1];
  canonical_cons #10 0 [4; 9; 4; 4; 2; 9; 5; 4; 0; 0; 2; 4; 4; 6; 0; 4; 8; 0; 4; 8; 1];
  canonical_cons #10 9 [0; 4; 9; 4; 4; 2; 9; 5; 4; 0; 0; 2; 4; 4; 6; 0; 4; 8; 0; 4; 8; 1];
  canonical_cons #10 7 [9; 0; 4; 9; 4; 4; 2; 9; 5; 4; 0; 0; 2; 4; 4; 6; 0; 4; 8; 0; 4; 8; 1];
  ()

let reverse_digits_next4_source () : Lemma (
    reverse_digits #10 next4_source == next4_reversed) =
  ReverseAddNext.canonical_next3_target ();
  reverse_list_next4_source ();
  value_next4_reversed ();
  canonical_next4_reversed ();
  reverse_digits_canonical #10 next4_source;
  normalize_value #10 (rev next4_source);
  assert (value (reverse_digits #10 next4_source) ==
    8659171086457790729479);
  digits_of_nat_of_canonical #10 (reverse_digits #10 next4_source);
  digits_of_nat_of_canonical #10 next4_reversed;
  assert (reverse_digits #10 next4_source == next4_reversed);
  ()

let reverse_add_9749270977546801719568_to_18408442064004592449047 () : Lemma (
    reverse_add #10 next4_source == next4_target) =
  ReverseAddNext.canonical_next3_target ();
  reverse_add_value #10 next4_source;
  ReverseAddNext.value_next3_target ();
  reverse_digits_next4_source ();
  value_next4_reversed ();
  value_next4_target ();
  assert (value (reverse_add #10 next4_source) ==
    18408442064004592449047);
  reverse_add_canonical #10 next4_source;
  digits_of_nat_of_canonical #10 (reverse_add #10 next4_source);
  canonical_next4_target ();
  digits_of_nat_of_canonical #10 next4_target;
  assert (reverse_add #10 next4_source == next4_target);
  ()

let trace_digits_profile_9749270977546801719568 () : Lemma (
    trace_digits next4_source == next4_target) =
  reverse_add_9749270977546801719568_to_18408442064004592449047 ();
  trace_digits_equals_reverse_add next4_source;
  assert (trace_digits next4_source == next4_target);
  ()

let trace_carries_next4_source () : Lemma (trace_carries next4_source ==
    [0; 1; 1; 1; 1; 0; 1; 0; 0; 1; 1; 1; 1; 1; 1; 1; 0; 1; 0; 1; 1; 1; 1]) =
  reverse_list_next4_source ();
  assert (trace_carries next4_source ==
    (add_trace #10 next4_source next4_reversed 0).carries);
  add_trace_carries_step #10 8 9
    [6; 5; 9; 1; 7; 1; 0; 8; 6; 4; 5; 7; 7; 9; 0; 7; 2; 9; 4; 7; 9]
    [7; 4; 9; 2; 7; 0; 9; 7; 7; 5; 4; 6; 8; 0; 1; 7; 1; 9; 5; 6; 8] 0;
  add_trace_carries_step #10 6 7
    [5; 9; 1; 7; 1; 0; 8; 6; 4; 5; 7; 7; 9; 0; 7; 2; 9; 4; 7; 9]
    [4; 9; 2; 7; 0; 9; 7; 7; 5; 4; 6; 8; 0; 1; 7; 1; 9; 5; 6; 8] 1;
  add_trace_carries_step #10 5 4
    [9; 1; 7; 1; 0; 8; 6; 4; 5; 7; 7; 9; 0; 7; 2; 9; 4; 7; 9]
    [9; 2; 7; 0; 9; 7; 7; 5; 4; 6; 8; 0; 1; 7; 1; 9; 5; 6; 8] 1;
  add_trace_carries_step #10 9 9
    [1; 7; 1; 0; 8; 6; 4; 5; 7; 7; 9; 0; 7; 2; 9; 4; 7; 9]
    [2; 7; 0; 9; 7; 7; 5; 4; 6; 8; 0; 1; 7; 1; 9; 5; 6; 8] 1;
  add_trace_carries_step #10 1 2
    [7; 1; 0; 8; 6; 4; 5; 7; 7; 9; 0; 7; 2; 9; 4; 7; 9]
    [7; 0; 9; 7; 7; 5; 4; 6; 8; 0; 1; 7; 1; 9; 5; 6; 8] 1;
  add_trace_carries_step #10 7 7
    [1; 0; 8; 6; 4; 5; 7; 7; 9; 0; 7; 2; 9; 4; 7; 9]
    [0; 9; 7; 7; 5; 4; 6; 8; 0; 1; 7; 1; 9; 5; 6; 8] 0;
  add_trace_carries_step #10 1 0
    [0; 8; 6; 4; 5; 7; 7; 9; 0; 7; 2; 9; 4; 7; 9]
    [9; 7; 7; 5; 4; 6; 8; 0; 1; 7; 1; 9; 5; 6; 8] 1;
  add_trace_carries_step #10 0 9
    [8; 6; 4; 5; 7; 7; 9; 0; 7; 2; 9; 4; 7; 9]
    [7; 7; 5; 4; 6; 8; 0; 1; 7; 1; 9; 5; 6; 8] 0;
  add_trace_carries_step #10 8 7
    [6; 4; 5; 7; 7; 9; 0; 7; 2; 9; 4; 7; 9]
    [7; 5; 4; 6; 8; 0; 1; 7; 1; 9; 5; 6; 8] 0;
  add_trace_carries_step #10 6 7
    [4; 5; 7; 7; 9; 0; 7; 2; 9; 4; 7; 9]
    [5; 4; 6; 8; 0; 1; 7; 1; 9; 5; 6; 8] 1;
  add_trace_carries_step #10 4 5
    [5; 7; 7; 9; 0; 7; 2; 9; 4; 7; 9]
    [4; 6; 8; 0; 1; 7; 1; 9; 5; 6; 8] 1;
  add_trace_carries_step #10 5 4
    [7; 7; 9; 0; 7; 2; 9; 4; 7; 9]
    [6; 8; 0; 1; 7; 1; 9; 5; 6; 8] 1;
  add_trace_carries_step #10 7 6
    [7; 9; 0; 7; 2; 9; 4; 7; 9]
    [8; 0; 1; 7; 1; 9; 5; 6; 8] 1;
  add_trace_carries_step #10 7 8
    [9; 0; 7; 2; 9; 4; 7; 9]
    [0; 1; 7; 1; 9; 5; 6; 8] 1;
  add_trace_carries_step #10 9 0
    [0; 7; 2; 9; 4; 7; 9]
    [1; 7; 1; 9; 5; 6; 8] 1;
  add_trace_carries_step #10 0 1
    [7; 2; 9; 4; 7; 9]
    [7; 1; 9; 5; 6; 8] 0;
  add_trace_carries_step #10 7 7
    [2; 9; 4; 7; 9]
    [1; 9; 5; 6; 8] 1;
  add_trace_carries_step #10 2 1
    [9; 4; 7; 9]
    [9; 5; 6; 8] 0;
  add_trace_carries_step #10 9 9
    [4; 7; 9]
    [5; 6; 8] 1;
  add_trace_carries_step #10 4 5
    [7; 9]
    [6; 8] 1;
  add_trace_carries_step #10 7 6
    [9]
    [8] 1;
  add_trace_carries_step #10 9 8 [] [] 1;
  assert ((add_trace #10 [] [] 1).carries == [1]);
  assert ((add_trace #10 next4_source next4_reversed 0).carries ==
    [0; 1; 1; 1; 1; 0; 1; 0; 0; 1; 1; 1; 1; 1; 1; 1; 0; 1; 0; 1; 1; 1; 1]);
  ()

let trace_profile_shape_9749270977546801719568 () : Lemma (
    length (trace_digits next4_source) == length next4_source + 1) =
  trace_digits_profile_9749270977546801719568 ();
  length_of_eq #(digit 10) (trace_digits next4_source) next4_target;
  assert (length next4_target == length next4_source + 1);
  ()

let trace_profile_final_carry_9749270977546801719568 () : Lemma (
    nth (trace_carries next4_source) (length next4_source) == Some 1) =
  trace_profile_shape_9749270977546801719568 ();
  ReverseAddContinuation.final_carry_from_overflow_length next4_source;
  ()

let trace_profile_sums_9749270977546801719568 () : Lemma (
    trace_sum_at next4_source 0 == 17 /\
    trace_sum_at next4_source 1 == 13 /\
    trace_sum_at next4_source 21 == 17) =
  reverse_list_next4_source ();
  ()

let trace_profile_carry_facts_9749270977546801719568 () : Lemma (
    trace_carry_at next4_source 1 == 1 /\
    trace_carry_at next4_source 21 == 1 /\
    trace_carry_at next4_source 2 == 1 /\
    trace_carry_at next4_source 22 == 1) =
  trace_carries_next4_source ();
  ()

let overflow_precondition_18408442064004592449047 () : Lemma (
    canonical #10 next4_source /\
    next4_source <> [] /\
    length (trace_digits next4_source) == length next4_source + 1 /\
    nth (trace_carries next4_source) (length next4_source) == Some 1 /\
    1 <= trace_sum_at next4_source 0 /\
    trace_sum_at next4_source 0 <= 18 /\
    trace_sum_at next4_source 0 <> 10 /\
    exists (i:nat). 0 < i /\ i < length next4_source /\
      trace_sum_at next4_source i +
          trace_sum_at next4_source (length next4_source - i) +
          trace_carry_at next4_source i +
          trace_carry_at next4_source (length next4_source - i) >=
        10 + 10 *
          (trace_carry_at next4_source (i + 1) +
           trace_carry_at next4_source (length next4_source - i + 1))) =
  ReverseAddNext.canonical_next3_target ();
  assert (canonical #10 next4_source);
  assert (next4_source <> []);
  trace_profile_shape_9749270977546801719568 ();
  trace_profile_final_carry_9749270977546801719568 ();
  trace_profile_sums_9749270977546801719568 ();
  trace_profile_carry_facts_9749270977546801719568 ();
  assert (length (trace_digits next4_source) == length next4_source + 1);
  assert (nth (trace_carries next4_source)
    (length next4_source) == Some 1);
  assert (trace_sum_at next4_source 0 == 17);
  assert (trace_sum_at next4_source 1 == 13);
  assert (trace_sum_at next4_source 21 == 17);
  assert (trace_carry_at next4_source 1 == 1);
  assert (trace_carry_at next4_source 21 == 1);
  assert (trace_carry_at next4_source 2 == 1);
  assert (trace_carry_at next4_source 22 == 1);
  assert (1 <= trace_sum_at next4_source 0 /\
    trace_sum_at next4_source 0 <= 18);
  assert (trace_sum_at next4_source 0 <> 10);
  let n : nat = length next4_source in
  assert (0 < 1 /\ 1 < n);
  assert (trace_sum_at next4_source 1 +
      trace_sum_at next4_source (n - 1) +
      trace_carry_at next4_source 1 +
      trace_carry_at next4_source (n - 1) >=
    10 + 10 *
      (trace_carry_at next4_source 2 +
       trace_carry_at next4_source (n - 1 + 1)));
  exists_intro
    (fun (i:nat) -> 0 < i /\ i < n /\
      trace_sum_at next4_source i +
          trace_sum_at next4_source (n - i) +
          trace_carry_at next4_source i +
          trace_carry_at next4_source (n - i) >=
        10 + 10 *
          (trace_carry_at next4_source (i + 1) +
           trace_carry_at next4_source (n - i + 1)))
    1;
  ()

let local_profile_witness_18408442064004592449047 () : Lemma (
    trace_local_profile_complement_witness next4_target) =
  overflow_precondition_18408442064004592449047 ();
  reverse_add_9749270977546801719568_to_18408442064004592449047 ();
  overflow_internal_cell_implies_next_witness next4_source;
  ()

let next5_source : numeral 10 = next4_target

let next5_reversed : numeral 10 =
  [1; 8; 4; 0; 8; 4; 4; 2; 0; 6; 4; 0; 0; 4; 5; 9; 2; 4; 4; 9; 0; 4; 7]

let next5_target : numeral 10 =
  [8; 2; 5; 9; 2; 9; 6; 1; 6; 0; 5; 0; 4; 0; 6; 1; 7; 8; 2; 0; 5; 2; 9]

let reverse_list_next5_source () : Lemma (rev next5_source == next5_reversed) =
  assert (rev [1] == [1]);
  rev_cons 8 [1];
  rev_cons 4 [8; 1];
  rev_cons 0 [4; 8; 1];
  rev_cons 9 [0; 4; 8; 1];
  rev_cons 4 [9; 0; 4; 8; 1];
  rev_cons 0 [4; 9; 0; 4; 8; 1];
  rev_cons 2 [0; 4; 9; 0; 4; 8; 1];
  rev_cons 4 [2; 0; 4; 9; 0; 4; 8; 1];
  rev_cons 5 [4; 2; 0; 4; 9; 0; 4; 8; 1];
  rev_cons 4 [5; 4; 2; 0; 4; 9; 0; 4; 8; 1];
  rev_cons 0 [4; 5; 4; 2; 0; 4; 9; 0; 4; 8; 1];
  rev_cons 6 [0; 4; 5; 4; 2; 0; 4; 9; 0; 4; 8; 1];
  rev_cons 0 [6; 0; 4; 5; 4; 2; 0; 4; 9; 0; 4; 8; 1];
  rev_cons 4 [0; 6; 0; 4; 5; 4; 2; 0; 4; 9; 0; 4; 8; 1];
  rev_cons 4 [4; 0; 6; 0; 4; 5; 4; 2; 0; 4; 9; 0; 4; 8; 1];
  rev_cons 9 [4; 4; 0; 6; 0; 4; 5; 4; 2; 0; 4; 9; 0; 4; 8; 1];
  rev_cons 2 [9; 4; 4; 0; 6; 0; 4; 5; 4; 2; 0; 4; 9; 0; 4; 8; 1];
  rev_cons 8 [2; 9; 4; 4; 0; 6; 0; 4; 5; 4; 2; 0; 4; 9; 0; 4; 8; 1];
  rev_cons 1 [8; 2; 9; 4; 4; 0; 6; 0; 4; 5; 4; 2; 0; 4; 9; 0; 4; 8; 1];
  rev_cons 9 [1; 8; 2; 9; 4; 4; 0; 6; 0; 4; 5; 4; 2; 0; 4; 9; 0; 4; 8; 1];
  rev_cons 8 [9; 1; 8; 2; 9; 4; 4; 0; 6; 0; 4; 5; 4; 2; 0; 4; 9; 0; 4; 8; 1];
  rev_cons 5 [8; 9; 1; 8; 2; 9; 4; 4; 0; 6; 0; 4; 5; 4; 2; 0; 4; 9; 0; 4; 8; 1];
  rev_cons 2 [5; 8; 9; 1; 8; 2; 9; 4; 4; 0; 6; 0; 4; 5; 4; 2; 0; 4; 9; 0; 4; 8; 1];
  rev_cons 9 [2; 5; 8; 9; 1; 8; 2; 9; 4; 4; 0; 6; 0; 4; 5; 4; 2; 0; 4; 9; 0; 4; 8; 1];
  ()

let value_next5_reversed () : Lemma (
    value next5_reversed == 74094429540046024480481) =
  value_cons #10 1 [8; 4; 0; 8; 4; 4; 2; 0; 6; 4; 0; 0; 4; 5; 9; 2; 4; 4; 9; 0; 4; 7];
  value_cons #10 8 [4; 0; 8; 4; 4; 2; 0; 6; 4; 0; 0; 4; 5; 9; 2; 4; 4; 9; 0; 4; 7];
  value_cons #10 4 [0; 8; 4; 4; 2; 0; 6; 4; 0; 0; 4; 5; 9; 2; 4; 4; 9; 0; 4; 7];
  value_cons #10 0 [8; 4; 4; 2; 0; 6; 4; 0; 0; 4; 5; 9; 2; 4; 4; 9; 0; 4; 7];
  value_cons #10 8 [4; 4; 2; 0; 6; 4; 0; 0; 4; 5; 9; 2; 4; 4; 9; 0; 4; 7];
  value_cons #10 4 [4; 2; 0; 6; 4; 0; 0; 4; 5; 9; 2; 4; 4; 9; 0; 4; 7];
  value_cons #10 4 [2; 0; 6; 4; 0; 0; 4; 5; 9; 2; 4; 4; 9; 0; 4; 7];
  value_cons #10 2 [0; 6; 4; 0; 0; 4; 5; 9; 2; 4; 4; 9; 0; 4; 7];
  value_cons #10 0 [6; 4; 0; 0; 4; 5; 9; 2; 4; 4; 9; 0; 4; 7];
  value_cons #10 6 [4; 0; 0; 4; 5; 9; 2; 4; 4; 9; 0; 4; 7];
  value_cons #10 4 [0; 0; 4; 5; 9; 2; 4; 4; 9; 0; 4; 7];
  value_cons #10 0 [0; 4; 5; 9; 2; 4; 4; 9; 0; 4; 7];
  value_cons #10 0 [4; 5; 9; 2; 4; 4; 9; 0; 4; 7];
  value_cons #10 4 [5; 9; 2; 4; 4; 9; 0; 4; 7];
  value_cons #10 5 [9; 2; 4; 4; 9; 0; 4; 7];
  value_cons #10 9 [2; 4; 4; 9; 0; 4; 7];
  value_cons #10 2 [4; 4; 9; 0; 4; 7];
  value_cons #10 4 [4; 9; 0; 4; 7];
  value_cons #10 4 [9; 0; 4; 7];
  value_cons #10 9 [0; 4; 7];
  value_cons #10 0 [4; 7];
  value_cons #10 4 [7];
  value_cons #10 7 [];
  ()

let value_next5_target () : Lemma (
    value next5_target == 92502871604050616929528) =
  value_cons #10 8 [2; 5; 9; 2; 9; 6; 1; 6; 0; 5; 0; 4; 0; 6; 1; 7; 8; 2; 0; 5; 2; 9];
  value_cons #10 2 [5; 9; 2; 9; 6; 1; 6; 0; 5; 0; 4; 0; 6; 1; 7; 8; 2; 0; 5; 2; 9];
  value_cons #10 5 [9; 2; 9; 6; 1; 6; 0; 5; 0; 4; 0; 6; 1; 7; 8; 2; 0; 5; 2; 9];
  value_cons #10 9 [2; 9; 6; 1; 6; 0; 5; 0; 4; 0; 6; 1; 7; 8; 2; 0; 5; 2; 9];
  value_cons #10 2 [9; 6; 1; 6; 0; 5; 0; 4; 0; 6; 1; 7; 8; 2; 0; 5; 2; 9];
  value_cons #10 9 [6; 1; 6; 0; 5; 0; 4; 0; 6; 1; 7; 8; 2; 0; 5; 2; 9];
  value_cons #10 6 [1; 6; 0; 5; 0; 4; 0; 6; 1; 7; 8; 2; 0; 5; 2; 9];
  value_cons #10 1 [6; 0; 5; 0; 4; 0; 6; 1; 7; 8; 2; 0; 5; 2; 9];
  value_cons #10 6 [0; 5; 0; 4; 0; 6; 1; 7; 8; 2; 0; 5; 2; 9];
  value_cons #10 0 [5; 0; 4; 0; 6; 1; 7; 8; 2; 0; 5; 2; 9];
  value_cons #10 5 [0; 4; 0; 6; 1; 7; 8; 2; 0; 5; 2; 9];
  value_cons #10 0 [4; 0; 6; 1; 7; 8; 2; 0; 5; 2; 9];
  value_cons #10 4 [0; 6; 1; 7; 8; 2; 0; 5; 2; 9];
  value_cons #10 0 [6; 1; 7; 8; 2; 0; 5; 2; 9];
  value_cons #10 6 [1; 7; 8; 2; 0; 5; 2; 9];
  value_cons #10 1 [7; 8; 2; 0; 5; 2; 9];
  value_cons #10 7 [8; 2; 0; 5; 2; 9];
  value_cons #10 8 [2; 0; 5; 2; 9];
  value_cons #10 2 [0; 5; 2; 9];
  value_cons #10 0 [5; 2; 9];
  value_cons #10 5 [2; 9];
  value_cons #10 2 [9];
  value_cons #10 9 [];
  ()

let canonical_next5_reversed () : Lemma (canonical #10 next5_reversed) =
  assert (canonical #10 [7]);
  canonical_cons #10 4 [7];
  canonical_cons #10 0 [4; 7];
  canonical_cons #10 9 [0; 4; 7];
  canonical_cons #10 4 [9; 0; 4; 7];
  canonical_cons #10 9 [4; 9; 0; 4; 7];
  canonical_cons #10 0 [9; 4; 9; 0; 4; 7];
  canonical_cons #10 2 [0; 9; 4; 9; 0; 4; 7];
  canonical_cons #10 4 [2; 0; 9; 4; 9; 0; 4; 7];
  canonical_cons #10 5 [4; 2; 0; 9; 4; 9; 0; 4; 7];
  canonical_cons #10 4 [5; 4; 2; 0; 9; 4; 9; 0; 4; 7];
  canonical_cons #10 0 [4; 5; 4; 2; 0; 9; 4; 9; 0; 4; 7];
  canonical_cons #10 6 [0; 4; 5; 4; 2; 0; 9; 4; 9; 0; 4; 7];
  canonical_cons #10 0 [6; 0; 4; 5; 4; 2; 0; 9; 4; 9; 0; 4; 7];
  canonical_cons #10 4 [0; 6; 0; 4; 5; 4; 2; 0; 9; 4; 9; 0; 4; 7];
  canonical_cons #10 4 [4; 0; 6; 0; 4; 5; 4; 2; 0; 9; 4; 9; 0; 4; 7];
  canonical_cons #10 9 [4; 4; 0; 6; 0; 4; 5; 4; 2; 0; 9; 4; 9; 0; 4; 7];
  canonical_cons #10 2 [9; 4; 4; 0; 6; 0; 4; 5; 4; 2; 0; 9; 4; 9; 0; 4; 7];
  canonical_cons #10 8 [2; 9; 4; 4; 0; 6; 0; 4; 5; 4; 2; 0; 9; 4; 9; 0; 4; 7];
  canonical_cons #10 1 [8; 2; 9; 4; 4; 0; 6; 0; 4; 5; 4; 2; 0; 9; 4; 9; 0; 4; 7];
  canonical_cons #10 9 [1; 8; 2; 9; 4; 4; 0; 6; 0; 4; 5; 4; 2; 0; 9; 4; 9; 0; 4; 7];
  canonical_cons #10 8 [9; 1; 8; 2; 9; 4; 4; 0; 6; 0; 4; 5; 4; 2; 0; 9; 4; 9; 0; 4; 7];
  canonical_cons #10 5 [8; 9; 1; 8; 2; 9; 4; 4; 0; 6; 0; 4; 5; 4; 2; 0; 9; 4; 9; 0; 4; 7];
  canonical_cons #10 2 [5; 8; 9; 1; 8; 2; 9; 4; 4; 0; 6; 0; 4; 5; 4; 2; 0; 9; 0; 4; 7];
  ()

let canonical_next5_target () : Lemma (canonical #10 next5_target) =
  assert (canonical #10 [9]);
  canonical_cons #10 2 [9];
  canonical_cons #10 5 [2; 9];
  canonical_cons #10 0 [5; 2; 9];
  canonical_cons #10 2 [0; 5; 2; 9];
  canonical_cons #10 8 [2; 0; 5; 2; 9];
  canonical_cons #10 7 [8; 2; 0; 5; 2; 9];
  canonical_cons #10 1 [7; 8; 2; 0; 5; 2; 9];
  canonical_cons #10 6 [1; 7; 8; 2; 0; 5; 2; 9];
  canonical_cons #10 0 [6; 1; 7; 8; 2; 0; 5; 2; 9];
  canonical_cons #10 4 [0; 6; 1; 7; 8; 2; 0; 5; 2; 9];
  canonical_cons #10 0 [4; 0; 6; 1; 7; 8; 2; 0; 5; 2; 9];
  canonical_cons #10 5 [0; 4; 0; 6; 1; 7; 8; 2; 0; 5; 2; 9];
  canonical_cons #10 0 [5; 0; 4; 0; 6; 1; 7; 8; 2; 0; 5; 2; 9];
  canonical_cons #10 6 [0; 5; 0; 4; 0; 6; 1; 7; 8; 2; 0; 5; 2; 9];
  canonical_cons #10 1 [6; 0; 5; 0; 4; 0; 6; 1; 7; 8; 2; 0; 5; 2; 9];
  canonical_cons #10 9 [1; 6; 0; 5; 0; 4; 0; 6; 1; 7; 8; 2; 0; 5; 2; 9];
  canonical_cons #10 2 [9; 1; 6; 0; 5; 0; 4; 0; 6; 1; 7; 8; 2; 0; 5; 2; 9];
  canonical_cons #10 9 [2; 9; 1; 6; 0; 5; 0; 4; 0; 6; 1; 7; 8; 2; 0; 5; 2; 9];
  canonical_cons #10 5 [9; 2; 9; 1; 6; 0; 5; 0; 4; 0; 6; 1; 7; 8; 2; 0; 5; 2; 9];
  canonical_cons #10 2 [5; 9; 2; 9; 1; 6; 0; 5; 0; 4; 0; 6; 1; 7; 8; 2; 0; 5; 2; 9];
  canonical_cons #10 9 [2; 5; 9; 2; 9; 1; 6; 0; 5; 0; 4; 0; 6; 1; 7; 8; 2; 0; 5; 2; 9];
  canonical_cons #10 6 [9; 2; 5; 9; 2; 9; 1; 6; 0; 5; 0; 4; 0; 6; 1; 7; 8; 2; 0; 5; 2; 9];
  canonical_cons #10 1 [6; 9; 2; 5; 9; 2; 9; 1; 6; 0; 5; 0; 4; 0; 6; 1; 7; 8; 2; 0; 5; 2; 9];
  ()

let reverse_digits_next5_source () : Lemma (
    reverse_digits #10 next5_source == next5_reversed) =
  ReverseAddNext.canonical_next4_target ();
  reverse_list_next5_source ();
  value_next5_reversed ();
  canonical_next5_reversed ();
  reverse_digits_canonical #10 next5_source;
  normalize_value #10 (rev next5_source);
  assert (value (reverse_digits #10 next5_source) ==
    74094429540046024480481);
  digits_of_nat_of_canonical #10 (reverse_digits #10 next5_source);
  digits_of_nat_of_canonical #10 next5_reversed;
  assert (reverse_digits #10 next5_source == next5_reversed);
  ()

let reverse_add_18408442064004592449047_to_92502871604050616929528 () : Lemma (
    reverse_add #10 next5_source == next5_target) =
  ReverseAddNext.canonical_next4_target ();
  reverse_add_value #10 next5_source;
  ReverseAddNext.value_next4_target ();
  reverse_digits_next5_source ();
  value_next5_reversed ();
  value_next5_target ();
  assert (value (reverse_add #10 next5_source) ==
    92502871604050616929528);
  reverse_add_canonical #10 next5_source;
  digits_of_nat_of_canonical #10 (reverse_add #10 next5_source);
  canonical_next5_target ();
  digits_of_nat_of_canonical #10 next5_target;
  assert (reverse_add #10 next5_source == next5_target);
  ()

let trace_digits_profile_18408442064004592449047 () : Lemma (
    trace_digits next5_source == next5_target) =
  reverse_add_18408442064004592449047_to_92502871604050616929528 ();
  trace_digits_equals_reverse_add next5_source;
  assert (trace_digits next5_source == next5_target);
  ()

let trace_profile_shape_18408442064004592449047 () : Lemma (
    length (trace_digits next5_source) == length next5_source) =
  trace_digits_profile_18408442064004592449047 ();
  length_of_eq #(digit 10) (trace_digits next5_source) next5_target;
  assert (length next5_target == length next5_source);
  ()

let trace_profile_final_carry_18408442064004592449047 () : Lemma (
    nth (trace_carries next5_source) (length next5_source) == Some 0) =
  trace_profile_shape_18408442064004592449047 ();
  final_carry_from_length next5_source;
  ()

let local_profile_witness_92502871604050616929528 () : Lemma (
    trace_local_profile_complement_witness next5_target) =
  ReverseAddNext.canonical_next4_target ();
  trace_profile_shape_18408442064004592449047 ();
  trace_profile_final_carry_18408442064004592449047 ();
  assert (trace_sum_at next5_source 0 == 8);
  reverse_add_18408442064004592449047_to_92502871604050616929528 ();
  no_overflow_outer_sum_6_to_9_implies_next_witness next5_source;
  ()

let next6_source : numeral 10 = next5_target

let next6_reversed : numeral 10 =
  [9; 2; 5; 0; 2; 8; 7; 1; 6; 0; 4; 0; 5; 0; 6; 1; 6; 9; 2; 9; 5; 2; 8]

let next6_target : numeral 10 =
  [7; 5; 0; 0; 5; 7; 4; 3; 2; 1; 9; 0; 9; 0; 2; 3; 3; 8; 5; 9; 0; 5; 7; 1]

let reverse_list_next6_source () : Lemma (rev next6_source == next6_reversed) =
  assert (rev [9] == [9]);
  rev_cons 2 [9];
  rev_cons 5 [2; 9];
  rev_cons 9 [5; 2; 9];
  rev_cons 0 [9; 5; 2; 9];
  rev_cons 2 [0; 9; 5; 2; 9];
  rev_cons 8 [2; 0; 9; 5; 2; 9];
  rev_cons 4 [8; 2; 0; 9; 5; 2; 9];
  rev_cons 0 [4; 8; 2; 0; 9; 5; 2; 9];
  rev_cons 6 [0; 4; 8; 2; 0; 9; 5; 2; 9];
  rev_cons 1 [6; 0; 4; 8; 2; 0; 9; 5; 2; 9];
  rev_cons 6 [1; 6; 0; 4; 8; 2; 0; 9; 5; 2; 9];
  rev_cons 0 [6; 1; 6; 0; 4; 8; 2; 0; 9; 5; 2; 9];
  rev_cons 5 [0; 6; 1; 6; 0; 4; 8; 2; 0; 9; 5; 2; 9];
  rev_cons 0 [5; 0; 6; 1; 6; 0; 4; 8; 2; 0; 9; 5; 2; 9];
  rev_cons 4 [0; 5; 0; 6; 1; 6; 0; 4; 8; 2; 0; 9; 5; 2; 9];
  rev_cons 0 [4; 0; 5; 0; 6; 1; 6; 0; 4; 8; 2; 0; 9; 5; 2; 9];
  rev_cons 6 [0; 4; 0; 5; 0; 6; 1; 6; 0; 4; 8; 2; 0; 9; 5; 2; 9];
  rev_cons 1 [6; 0; 4; 0; 5; 0; 6; 1; 6; 0; 4; 8; 2; 0; 9; 5; 2; 9];
  rev_cons 7 [1; 6; 0; 4; 0; 5; 0; 6; 1; 6; 0; 4; 8; 2; 0; 9; 5; 2; 9];
  rev_cons 8 [7; 1; 6; 0; 4; 0; 5; 0; 6; 1; 6; 0; 4; 8; 2; 0; 9; 5; 2; 9];
  rev_cons 2 [8; 7; 1; 6; 0; 4; 0; 5; 0; 6; 1; 6; 0; 4; 8; 2; 0; 9; 5; 2; 9];
  rev_cons 5 [2; 8; 7; 1; 6; 0; 4; 0; 5; 0; 6; 1; 6; 0; 4; 8; 2; 0; 9; 5; 2; 9];
  rev_cons 2 [5; 2; 8; 7; 1; 6; 0; 4; 0; 5; 0; 6; 1; 6; 0; 4; 8; 2; 0; 9; 5; 2; 9];
  rev_cons 9 [2; 5; 2; 8; 7; 1; 6; 0; 4; 0; 5; 0; 6; 1; 6; 0; 4; 8; 2; 0; 9; 5; 2; 9];
  ()

let value_next6_reversed () : Lemma (
    value next6_reversed == 82592961605040617820529) =
  value_cons #10 9 [2; 5; 0; 2; 8; 7; 1; 6; 0; 4; 0; 5; 0; 6; 1; 6; 9; 2; 9; 5; 2; 8];
  value_cons #10 2 [5; 0; 2; 8; 7; 1; 6; 0; 4; 0; 5; 0; 6; 1; 6; 9; 2; 9; 5; 2; 8];
  value_cons #10 5 [0; 2; 8; 7; 1; 6; 0; 4; 0; 5; 0; 6; 1; 6; 9; 2; 9; 5; 2; 8];
  value_cons #10 0 [2; 8; 7; 1; 6; 0; 4; 0; 5; 0; 6; 1; 6; 9; 2; 9; 5; 2; 8];
  value_cons #10 2 [8; 7; 1; 6; 0; 4; 0; 5; 0; 6; 1; 6; 9; 2; 9; 5; 2; 8];
  value_cons #10 8 [7; 1; 6; 0; 4; 0; 5; 0; 6; 1; 6; 9; 2; 9; 5; 2; 8];
  value_cons #10 7 [1; 6; 0; 4; 0; 5; 0; 6; 1; 6; 9; 2; 9; 5; 2; 8];
  value_cons #10 1 [6; 0; 4; 0; 5; 0; 6; 1; 6; 9; 2; 9; 5; 2; 8];
  value_cons #10 6 [0; 4; 0; 5; 0; 6; 1; 6; 9; 2; 9; 5; 2; 8];
  value_cons #10 0 [4; 0; 5; 0; 6; 1; 6; 9; 2; 9; 5; 2; 8];
  value_cons #10 4 [0; 5; 0; 6; 1; 6; 9; 2; 9; 5; 2; 8];
  value_cons #10 0 [5; 0; 6; 1; 6; 9; 2; 9; 5; 2; 8];
  value_cons #10 5 [0; 6; 1; 6; 9; 2; 9; 5; 2; 8];
  value_cons #10 0 [6; 1; 6; 9; 2; 9; 5; 2; 8];
  value_cons #10 6 [1; 6; 9; 2; 9; 5; 2; 8];
  value_cons #10 1 [6; 9; 2; 9; 5; 2; 8];
  value_cons #10 6 [9; 2; 9; 5; 2; 8];
  value_cons #10 9 [2; 9; 5; 2; 8];
  value_cons #10 2 [9; 5; 2; 8];
  value_cons #10 9 [5; 2; 8];
  value_cons #10 5 [2; 8];
  value_cons #10 2 [8];
  value_cons #10 8 [];
  ()

let value_next6_target () : Lemma (
    value next6_target == 175095833209091234750057) =
  value_cons #10 7 [5; 0; 0; 5; 7; 4; 3; 2; 1; 9; 0; 9; 0; 2; 3; 3; 8; 5; 9; 0; 5; 7; 1];
  value_cons #10 5 [0; 0; 5; 7; 4; 3; 2; 1; 9; 0; 9; 0; 2; 3; 3; 8; 5; 9; 0; 5; 7; 1];
  value_cons #10 0 [0; 5; 7; 4; 3; 2; 1; 9; 0; 9; 0; 2; 3; 3; 8; 5; 9; 0; 5; 7; 1];
  value_cons #10 0 [5; 7; 4; 3; 2; 1; 9; 0; 9; 0; 2; 3; 3; 8; 5; 9; 0; 5; 7; 1];
  value_cons #10 5 [7; 4; 3; 2; 1; 9; 0; 9; 0; 2; 3; 3; 8; 5; 9; 0; 5; 7; 1];
  value_cons #10 7 [4; 3; 2; 1; 9; 0; 9; 0; 2; 3; 3; 8; 5; 9; 0; 5; 7; 1];
  value_cons #10 4 [3; 2; 1; 9; 0; 9; 0; 2; 3; 3; 8; 5; 9; 0; 5; 7; 1];
  value_cons #10 3 [2; 1; 9; 0; 9; 0; 2; 3; 3; 8; 5; 9; 0; 5; 7; 1];
  value_cons #10 2 [1; 9; 0; 9; 0; 2; 3; 3; 8; 5; 9; 0; 5; 7; 1];
  value_cons #10 1 [9; 0; 9; 0; 2; 3; 3; 8; 5; 9; 0; 5; 7; 1];
  value_cons #10 9 [0; 9; 0; 2; 3; 3; 8; 5; 9; 0; 5; 7; 1];
  value_cons #10 0 [9; 0; 2; 3; 3; 8; 5; 9; 0; 5; 7; 1];
  value_cons #10 9 [0; 2; 3; 3; 8; 5; 9; 0; 5; 7; 1];
  value_cons #10 0 [2; 3; 3; 8; 5; 9; 0; 5; 7; 1];
  value_cons #10 2 [3; 3; 8; 5; 9; 0; 5; 7; 1];
  value_cons #10 3 [3; 8; 5; 9; 0; 5; 7; 1];
  value_cons #10 3 [8; 5; 9; 0; 5; 7; 1];
  value_cons #10 8 [5; 9; 0; 5; 7; 1];
  value_cons #10 5 [9; 0; 5; 7; 1];
  value_cons #10 9 [0; 5; 7; 1];
  value_cons #10 0 [5; 7; 1];
  value_cons #10 5 [7; 1];
  value_cons #10 7 [1];
  value_cons #10 1 [];
  ()

let canonical_next6_reversed () : Lemma (canonical #10 next6_reversed) =
  assert (canonical #10 [8]);
  canonical_cons #10 2 [8];
  canonical_cons #10 5 [2; 8];
  canonical_cons #10 9 [5; 2; 8];
  canonical_cons #10 0 [9; 5; 2; 8];
  canonical_cons #10 2 [0; 9; 5; 2; 8];
  canonical_cons #10 9 [2; 0; 9; 5; 2; 8];
  canonical_cons #10 4 [9; 2; 0; 9; 5; 2; 8];
  canonical_cons #10 0 [4; 9; 2; 0; 9; 5; 2; 8];
  canonical_cons #10 6 [0; 4; 9; 2; 0; 9; 5; 2; 8];
  canonical_cons #10 1 [6; 0; 4; 9; 2; 0; 9; 5; 2; 8];
  canonical_cons #10 6 [1; 6; 0; 4; 9; 2; 0; 9; 5; 2; 8];
  canonical_cons #10 0 [6; 1; 6; 0; 4; 9; 2; 0; 9; 5; 2; 8];
  canonical_cons #10 5 [0; 6; 1; 6; 0; 4; 9; 2; 0; 9; 5; 2; 8];
  canonical_cons #10 0 [5; 0; 6; 1; 6; 0; 4; 9; 2; 0; 9; 5; 2; 8];
  canonical_cons #10 4 [0; 5; 0; 6; 1; 6; 0; 4; 9; 2; 0; 9; 5; 2; 8];
  canonical_cons #10 0 [4; 0; 5; 0; 6; 1; 6; 0; 4; 9; 2; 0; 9; 5; 2; 8];
  canonical_cons #10 6 [0; 4; 0; 5; 0; 6; 1; 6; 0; 4; 9; 2; 0; 9; 5; 2; 8];
  canonical_cons #10 1 [6; 0; 4; 0; 5; 0; 6; 1; 6; 0; 4; 9; 2; 0; 9; 5; 2; 8];
  canonical_cons #10 6 [1; 6; 0; 4; 0; 5; 0; 6; 1; 6; 0; 4; 9; 2; 0; 9; 5; 2; 8];
  canonical_cons #10 9 [6; 1; 6; 0; 4; 0; 5; 0; 6; 1; 6; 0; 4; 9; 2; 0; 9; 5; 2; 8];
  canonical_cons #10 2 [9; 6; 1; 6; 0; 4; 0; 5; 0; 6; 1; 6; 0; 4; 9; 2; 0; 9; 5; 2; 8];
  canonical_cons #10 5 [2; 9; 6; 1; 6; 0; 4; 0; 5; 0; 6; 1; 6; 0; 4; 9; 2; 0; 9; 5; 2; 8];
  canonical_cons #10 2 [5; 2; 9; 6; 1; 6; 0; 4; 0; 5; 0; 6; 1; 6; 0; 4; 9; 2; 0; 9; 5; 2; 8];
  ()

let canonical_next6_target () : Lemma (canonical #10 next6_target) =
  assert (canonical #10 [1]);
  canonical_cons #10 7 [1];
  canonical_cons #10 5 [7; 1];
  canonical_cons #10 0 [5; 7; 1];
  canonical_cons #10 9 [0; 5; 7; 1];
  canonical_cons #10 5 [9; 0; 5; 7; 1];
  canonical_cons #10 8 [5; 9; 0; 5; 7; 1];
  canonical_cons #10 3 [8; 5; 9; 0; 5; 7; 1];
  canonical_cons #10 3 [3; 8; 5; 9; 0; 5; 7; 1];
  canonical_cons #10 2 [3; 3; 8; 5; 9; 0; 5; 7; 1];
  canonical_cons #10 0 [2; 3; 3; 8; 5; 9; 0; 5; 7; 1];
  canonical_cons #10 9 [0; 2; 3; 3; 8; 5; 9; 0; 5; 7; 1];
  canonical_cons #10 1 [9; 0; 2; 3; 3; 8; 5; 9; 0; 5; 7; 1];
  canonical_cons #10 2 [1; 9; 0; 2; 3; 3; 8; 5; 9; 0; 5; 7; 1];
  canonical_cons #10 4 [2; 1; 9; 0; 2; 3; 3; 8; 5; 9; 0; 5; 7; 1];
  canonical_cons #10 0 [4; 2; 1; 9; 0; 2; 3; 3; 8; 5; 9; 0; 5; 7; 1];
  canonical_cons #10 9 [0; 4; 2; 1; 9; 0; 2; 3; 3; 8; 5; 9; 0; 5; 7; 1];
  canonical_cons #10 7 [9; 0; 4; 2; 1; 9; 0; 2; 3; 3; 8; 5; 9; 0; 5; 7; 1];
  canonical_cons #10 5 [7; 9; 0; 4; 2; 1; 9; 0; 2; 3; 3; 8; 5; 9; 0; 5; 7; 1];
  canonical_cons #10 0 [5; 7; 9; 0; 4; 2; 1; 9; 0; 2; 3; 3; 8; 5; 9; 0; 5; 7; 1];
  canonical_cons #10 5 [0; 5; 7; 9; 0; 4; 2; 1; 9; 0; 2; 3; 3; 8; 5; 9; 0; 5; 7; 1];
  canonical_cons #10 7 [5; 0; 5; 7; 9; 0; 4; 2; 1; 9; 0; 2; 3; 3; 8; 5; 9; 0; 5; 7; 1];
  canonical_cons #10 5 [7; 5; 0; 5; 7; 9; 0; 4; 2; 1; 9; 0; 2; 3; 3; 8; 5; 9; 0; 5; 7; 1];
  canonical_cons #10 7 [5; 7; 5; 0; 5; 7; 9; 0; 4; 2; 1; 9; 0; 2; 3; 3; 8; 5; 9; 0; 5; 7; 1];
  ()

let reverse_digits_next6_source () : Lemma (
    reverse_digits #10 next6_source == next6_reversed) =
  ReverseAddNext.canonical_next5_target ();
  reverse_list_next6_source ();
  value_next6_reversed ();
  canonical_next6_reversed ();
  reverse_digits_canonical #10 next6_source;
  normalize_value #10 (rev next6_source);
  assert (value (reverse_digits #10 next6_source) ==
    82592961605040617820529);
  digits_of_nat_of_canonical #10 (reverse_digits #10 next6_source);
  digits_of_nat_of_canonical #10 next6_reversed;
  assert (reverse_digits #10 next6_source == next6_reversed);
  ()

let reverse_add_92502871604050616929528_to_175095833209091234750057 () : Lemma (
    reverse_add #10 next6_source == next6_target) =
  ReverseAddNext.canonical_next5_target ();
  reverse_add_value #10 next6_source;
  ReverseAddNext.value_next5_target ();
  reverse_digits_next6_source ();
  value_next6_reversed ();
  value_next6_target ();
  assert (value (reverse_add #10 next6_source) ==
    175095833209091234750057);
  reverse_add_canonical #10 next6_source;
  digits_of_nat_of_canonical #10 (reverse_add #10 next6_source);
  canonical_next6_target ();
  digits_of_nat_of_canonical #10 next6_target;
  assert (reverse_add #10 next6_source == next6_target);
  ()

let trace_digits_profile_92502871604050616929528 () : Lemma (
    trace_digits next6_source == next6_target) =
  reverse_add_92502871604050616929528_to_175095833209091234750057 ();
  trace_digits_equals_reverse_add next6_source;
  assert (trace_digits next6_source == next6_target);
  ()

let trace_carries_next6_source () : Lemma (trace_carries next6_source ==
    [0; 1; 0; 1; 1; 0; 1; 1; 0; 1; 0; 0; 0; 0; 0; 1; 0; 1; 1; 0; 0; 1; 0; 1]) =
  reverse_list_next6_source ();
  assert (trace_carries next6_source ==
    (add_trace #10 next6_source next6_reversed 0).carries);
  add_trace_carries_step #10 8 9
    [2; 5; 9; 2; 9; 6; 1; 6; 0; 5; 0; 4; 0; 6; 1; 7; 8; 2; 0; 5; 2; 9]
    [2; 5; 0; 2; 8; 7; 1; 6; 0; 4; 0; 5; 0; 6; 1; 6; 9; 2; 9; 5; 2; 8] 0;
  add_trace_carries_step #10 2 2
    [5; 9; 2; 9; 6; 1; 6; 0; 5; 0; 4; 0; 6; 1; 7; 8; 2; 0; 5; 2; 9]
    [5; 0; 2; 8; 7; 1; 6; 0; 4; 0; 5; 0; 6; 1; 6; 9; 2; 9; 5; 2; 8] 1;
  add_trace_carries_step #10 5 5
    [9; 2; 9; 6; 1; 6; 0; 5; 0; 4; 0; 6; 1; 7; 8; 2; 0; 5; 2; 9]
    [0; 2; 8; 7; 1; 6; 0; 4; 0; 5; 0; 6; 1; 6; 9; 2; 9; 5; 2; 8] 0;
  add_trace_carries_step #10 9 0
    [2; 9; 6; 1; 6; 0; 5; 0; 4; 0; 6; 1; 7; 8; 2; 0; 5; 2; 9]
    [2; 8; 7; 1; 6; 0; 4; 0; 5; 0; 6; 1; 6; 9; 2; 9; 5; 2; 8] 1;
  add_trace_carries_step #10 2 2
    [9; 6; 1; 6; 0; 5; 0; 4; 0; 6; 1; 7; 8; 2; 0; 5; 2; 9]
    [8; 7; 1; 6; 0; 4; 0; 5; 0; 6; 1; 6; 9; 2; 9; 5; 2; 8] 1;
  add_trace_carries_step #10 9 8
    [6; 1; 6; 0; 5; 0; 4; 0; 6; 1; 7; 8; 2; 0; 5; 2; 9]
    [7; 1; 6; 0; 4; 0; 5; 0; 6; 1; 6; 9; 2; 9; 5; 2; 8] 0;
  add_trace_carries_step #10 6 7
    [1; 6; 0; 5; 0; 4; 0; 6; 1; 7; 8; 2; 0; 5; 2; 9]
    [1; 6; 0; 4; 0; 5; 0; 6; 1; 6; 9; 2; 9; 5; 2; 8] 1;
  add_trace_carries_step #10 1 1
    [6; 0; 5; 0; 4; 0; 6; 1; 7; 8; 2; 0; 5; 2; 9]
    [6; 0; 4; 0; 5; 0; 6; 1; 6; 9; 2; 9; 5; 2; 8] 1;
  add_trace_carries_step #10 6 6
    [0; 5; 0; 4; 0; 6; 1; 7; 8; 2; 0; 5; 2; 9]
    [0; 4; 0; 5; 0; 6; 1; 6; 9; 2; 9; 5; 2; 8] 0;
  add_trace_carries_step #10 0 0
    [5; 0; 4; 0; 6; 1; 7; 8; 2; 0; 5; 2; 9]
    [4; 0; 5; 0; 6; 1; 6; 9; 2; 9; 5; 2; 8] 1;
  add_trace_carries_step #10 5 4
    [0; 4; 0; 6; 1; 7; 8; 2; 0; 5; 2; 9]
    [0; 5; 0; 6; 1; 6; 9; 2; 9; 5; 2; 8] 0;
  add_trace_carries_step #10 0 0
    [4; 0; 6; 1; 7; 8; 2; 0; 5; 2; 9]
    [5; 0; 6; 1; 6; 9; 2; 9; 5; 2; 8] 0;
  add_trace_carries_step #10 4 5
    [0; 6; 1; 7; 8; 2; 0; 5; 2; 9]
    [0; 6; 1; 6; 9; 2; 9; 5; 2; 8] 0;
  add_trace_carries_step #10 0 0
    [6; 1; 7; 8; 2; 0; 5; 2; 9]
    [6; 1; 6; 9; 2; 9; 5; 2; 8] 0;
  add_trace_carries_step #10 6 6
    [1; 7; 8; 2; 0; 5; 2; 9]
    [1; 6; 9; 2; 9; 5; 2; 8] 0;
  add_trace_carries_step #10 1 1
    [7; 8; 2; 0; 5; 2; 9]
    [6; 9; 2; 9; 5; 2; 8] 1;
  add_trace_carries_step #10 7 6
    [8; 2; 0; 5; 2; 9]
    [9; 2; 9; 5; 2; 8] 0;
  add_trace_carries_step #10 8 9
    [2; 0; 5; 2; 9]
    [2; 9; 5; 2; 8] 1;
  add_trace_carries_step #10 2 2
    [0; 5; 2; 9]
    [9; 5; 2; 8] 1;
  add_trace_carries_step #10 0 9
    [5; 2; 9]
    [5; 2; 8] 0;
  add_trace_carries_step #10 5 5
    [2; 9]
    [2; 8] 0;
  add_trace_carries_step #10 2 2
    [9]
    [8] 1;
  add_trace_carries_step #10 9 8 [] [] 0;
  assert ((add_trace #10 [] [] 1).carries == [1]);
  assert ((add_trace #10 next6_source next6_reversed 0).carries ==
    [0; 1; 0; 1; 1; 0; 1; 1; 0; 1; 0; 0; 0; 0; 0; 1; 0; 1; 1; 0; 0; 1; 0; 1]);
  ()

let trace_profile_shape_92502871604050616929528 () : Lemma (
    length (trace_digits next6_source) == length next6_source + 1) =
  trace_digits_profile_92502871604050616929528 ();
  length_of_eq #(digit 10) (trace_digits next6_source) next6_target;
  assert (length next6_target == length next6_source + 1);
  ()

let trace_profile_final_carry_92502871604050616929528 () : Lemma (
    nth (trace_carries next6_source) (length next6_source) == Some 1) =
  trace_profile_shape_92502871604050616929528 ();
  ReverseAddContinuation.final_carry_from_overflow_length next6_source;
  ()

let trace_profile_sums_92502871604050616929528 () : Lemma (
    trace_sum_at next6_source 0 == 17 /\
    trace_sum_at next6_source 1 == 4 /\
    trace_sum_at next6_source 22 == 17) =
  reverse_list_next6_source ();
  ()

let trace_profile_carry_facts_92502871604050616929528 () : Lemma (
    trace_carry_at next6_source 1 == 1 /\
    trace_carry_at next6_source 22 == 0 /\
    trace_carry_at next6_source 2 == 0 /\
    trace_carry_at next6_source 23 == 1) =
  trace_carries_next6_source ();
  ()

let overflow_precondition_175095833209091234750057 () : Lemma (
    canonical #10 next6_source /\
    next6_source <> [] /\
    length (trace_digits next6_source) == length next6_source + 1 /\
    nth (trace_carries next6_source) (length next6_source) == Some 1 /\
    1 <= trace_sum_at next6_source 0 /\
    trace_sum_at next6_source 0 <= 18 /\
    trace_sum_at next6_source 0 <> 10 /\
    exists (i:nat). 0 < i /\ i < length next6_source /\
      trace_sum_at next6_source i +
          trace_sum_at next6_source (length next6_source - i) +
          trace_carry_at next6_source i +
          trace_carry_at next6_source (length next6_source - i) >=
        10 + 10 *
          (trace_carry_at next6_source (i + 1) +
           trace_carry_at next6_source (length next6_source - i + 1))) =
  ReverseAddNext.canonical_next5_target ();
  assert (canonical #10 next6_source);
  assert (next6_source <> []);
  trace_profile_shape_92502871604050616929528 ();
  trace_profile_final_carry_92502871604050616929528 ();
  trace_profile_sums_92502871604050616929528 ();
  trace_profile_carry_facts_92502871604050616929528 ();
  assert (length (trace_digits next6_source) == length next6_source + 1);
  assert (nth (trace_carries next6_source)
    (length next6_source) == Some 1);
  assert (trace_sum_at next6_source 0 == 17);
  assert (trace_sum_at next6_source 1 == 4);
  assert (trace_sum_at next6_source 22 == 17);
  assert (trace_carry_at next6_source 1 == 1);
  assert (trace_carry_at next6_source 22 == 0);
  assert (trace_carry_at next6_source 2 == 0);
  assert (trace_carry_at next6_source 23 == 1);
  assert (1 <= trace_sum_at next6_source 0 /\
    trace_sum_at next6_source 0 <= 18);
  assert (trace_sum_at next6_source 0 <> 10);
  let n : nat = length next6_source in
  assert (0 < 1 /\ 1 < n);
  assert (trace_sum_at next6_source 1 +
      trace_sum_at next6_source (n - 1) +
      trace_carry_at next6_source 1 +
      trace_carry_at next6_source (n - 1) >=
    10 + 10 *
      (trace_carry_at next6_source 2 +
       trace_carry_at next6_source (n - 1 + 1)));
  exists_intro
    (fun (i:nat) -> 0 < i /\ i < n /\
      trace_sum_at next6_source i +
          trace_sum_at next6_source (n - i) +
          trace_carry_at next6_source i +
          trace_carry_at next6_source (n - i) >=
        10 + 10 *
          (trace_carry_at next6_source (i + 1) +
           trace_carry_at next6_source (n - i + 1)))
    1;
  ()

let local_profile_witness_175095833209091234750057 () : Lemma (
    trace_local_profile_complement_witness next6_target) =
  overflow_precondition_175095833209091234750057 ();
  reverse_add_92502871604050616929528_to_175095833209091234750057 ();
  overflow_internal_cell_implies_next_witness next6_source;
  ()

let next7_source : numeral 10 = next6_target

let next7_reversed : numeral 10 =
  [1; 7; 5; 0; 9; 5; 8; 3; 3; 2; 0; 9; 0; 9; 1; 2; 3; 4; 7; 5; 0; 0; 5; 7]

let next7_target : numeral 10 =
  [8; 2; 6; 0; 4; 3; 3; 7; 5; 3; 9; 9; 9; 9; 3; 5; 6; 2; 3; 5; 1; 5; 2; 9]

let reverse_list_next7_source () : Lemma (rev next7_source == next7_reversed) =
  assert (rev [1] == [1]);
  rev_cons 7 [1];
  rev_cons 5 [7; 1];
  rev_cons 0 [5; 7; 1];
  rev_cons 9 [0; 5; 7; 1];
  rev_cons 5 [9; 0; 5; 7; 1];
  rev_cons 8 [5; 9; 0; 5; 7; 1];
  rev_cons 3 [8; 5; 9; 0; 5; 7; 1];
  rev_cons 3 [3; 8; 5; 9; 0; 5; 7; 1];
  rev_cons 2 [3; 3; 8; 5; 9; 0; 5; 7; 1];
  rev_cons 0 [2; 3; 3; 8; 5; 9; 0; 5; 7; 1];
  rev_cons 9 [0; 2; 3; 3; 8; 5; 9; 0; 5; 7; 1];
  rev_cons 0 [9; 0; 2; 3; 3; 8; 5; 9; 0; 5; 7; 1];
  rev_cons 9 [0; 9; 0; 2; 3; 3; 8; 5; 9; 0; 5; 7; 1];
  rev_cons 1 [9; 0; 9; 0; 2; 3; 3; 8; 5; 9; 0; 5; 7; 1];
  rev_cons 2 [1; 9; 0; 9; 0; 2; 3; 3; 8; 5; 9; 0; 5; 7; 1];
  rev_cons 3 [2; 1; 9; 0; 9; 0; 2; 3; 3; 8; 5; 9; 0; 5; 7; 1];
  rev_cons 4 [3; 2; 1; 9; 0; 9; 0; 2; 3; 3; 8; 5; 9; 0; 5; 7; 1];
  rev_cons 7 [4; 3; 2; 1; 9; 0; 9; 0; 2; 3; 3; 8; 5; 9; 0; 5; 7; 1];
  rev_cons 5 [7; 4; 3; 2; 1; 9; 0; 9; 0; 2; 3; 3; 8; 5; 9; 0; 5; 7; 1];
  rev_cons 0 [5; 7; 4; 3; 2; 1; 9; 0; 9; 0; 2; 3; 3; 8; 5; 9; 0; 5; 7; 1];
  rev_cons 0 [0; 5; 7; 4; 3; 2; 1; 9; 0; 9; 0; 2; 3; 3; 8; 5; 9; 0; 5; 7; 1];
  rev_cons 5 [0; 0; 5; 7; 4; 3; 2; 1; 9; 0; 9; 0; 2; 3; 3; 8; 5; 9; 0; 5; 7; 1];
  rev_cons 7 [5; 0; 0; 5; 7; 4; 3; 2; 1; 9; 0; 9; 0; 2; 3; 3; 8; 5; 9; 0; 5; 7; 1];
  ()

let value_next7_reversed () : Lemma (
    value next7_reversed == 750057432190902338590571) =
  value_cons #10 1 [7; 5; 0; 9; 5; 8; 3; 3; 2; 0; 9; 0; 9; 1; 2; 3; 4; 7; 5; 0; 0; 5; 7];
  value_cons #10 7 [5; 0; 9; 5; 8; 3; 3; 2; 0; 9; 0; 9; 1; 2; 3; 4; 7; 5; 0; 0; 5; 7];
  value_cons #10 5 [0; 9; 5; 8; 3; 3; 2; 0; 9; 0; 9; 1; 2; 3; 4; 7; 5; 0; 0; 5; 7];
  value_cons #10 0 [9; 5; 8; 3; 3; 2; 0; 9; 0; 9; 1; 2; 3; 4; 7; 5; 0; 0; 5; 7];
  value_cons #10 9 [5; 8; 3; 3; 2; 0; 9; 0; 9; 1; 2; 3; 4; 7; 5; 0; 0; 5; 7];
  value_cons #10 5 [8; 3; 3; 2; 0; 9; 0; 9; 1; 2; 3; 4; 7; 5; 0; 0; 5; 7];
  value_cons #10 8 [3; 3; 2; 0; 9; 0; 9; 1; 2; 3; 4; 7; 5; 0; 0; 5; 7];
  value_cons #10 3 [3; 2; 0; 9; 0; 9; 1; 2; 3; 4; 7; 5; 0; 0; 5; 7];
  value_cons #10 3 [2; 0; 9; 0; 9; 1; 2; 3; 4; 7; 5; 0; 0; 5; 7];
  value_cons #10 2 [0; 9; 0; 9; 1; 2; 3; 4; 7; 5; 0; 0; 5; 7];
  value_cons #10 0 [9; 0; 9; 1; 2; 3; 4; 7; 5; 0; 0; 5; 7];
  value_cons #10 9 [0; 9; 1; 2; 3; 4; 7; 5; 0; 0; 5; 7];
  value_cons #10 0 [9; 1; 2; 3; 4; 7; 5; 0; 0; 5; 7];
  value_cons #10 9 [1; 2; 3; 4; 7; 5; 0; 0; 5; 7];
  value_cons #10 1 [2; 3; 4; 7; 5; 0; 0; 5; 7];
  value_cons #10 2 [3; 4; 7; 5; 0; 0; 5; 7];
  value_cons #10 3 [4; 7; 5; 0; 0; 5; 7];
  value_cons #10 4 [7; 5; 0; 0; 5; 7];
  value_cons #10 7 [5; 0; 0; 5; 7];
  value_cons #10 5 [0; 0; 5; 7];
  value_cons #10 0 [0; 5; 7];
  value_cons #10 0 [5; 7];
  value_cons #10 5 [7];
  value_cons #10 7 [];
  ()

let value_next7_target () : Lemma (
    value next7_target == 925153265399993573340628) =
  value_cons #10 8 [2; 6; 0; 4; 3; 3; 7; 5; 3; 9; 9; 9; 9; 3; 5; 6; 2; 3; 5; 1; 5; 2; 9];
  value_cons #10 2 [6; 0; 4; 3; 3; 7; 5; 3; 9; 9; 9; 9; 3; 5; 6; 2; 3; 5; 1; 5; 2; 9];
  value_cons #10 6 [0; 4; 3; 3; 7; 5; 3; 9; 9; 9; 9; 3; 5; 6; 2; 3; 5; 1; 5; 2; 9];
  value_cons #10 0 [4; 3; 3; 7; 5; 3; 9; 9; 9; 9; 3; 5; 6; 2; 3; 5; 1; 5; 2; 9];
  value_cons #10 4 [3; 3; 7; 5; 3; 9; 9; 9; 9; 3; 5; 6; 2; 3; 5; 1; 5; 2; 9];
  value_cons #10 3 [3; 7; 5; 3; 9; 9; 9; 9; 3; 5; 6; 2; 3; 5; 1; 5; 2; 9];
  value_cons #10 3 [7; 5; 3; 9; 9; 9; 9; 3; 5; 6; 2; 3; 5; 1; 5; 2; 9];
  value_cons #10 7 [5; 3; 9; 9; 9; 9; 3; 5; 6; 2; 3; 5; 1; 5; 2; 9];
  value_cons #10 5 [3; 9; 9; 9; 9; 3; 5; 6; 2; 3; 5; 1; 5; 2; 9];
  value_cons #10 3 [9; 9; 9; 9; 3; 5; 6; 2; 3; 5; 1; 5; 2; 9];
  value_cons #10 9 [9; 9; 9; 3; 5; 6; 2; 3; 5; 1; 5; 2; 9];
  value_cons #10 9 [9; 9; 3; 5; 6; 2; 3; 5; 1; 5; 2; 9];
  value_cons #10 9 [9; 3; 5; 6; 2; 3; 5; 1; 5; 2; 9];
  value_cons #10 9 [3; 5; 6; 2; 3; 5; 1; 5; 2; 9];
  value_cons #10 3 [5; 6; 2; 3; 5; 1; 5; 2; 9];
  value_cons #10 5 [6; 2; 3; 5; 1; 5; 2; 9];
  value_cons #10 6 [2; 3; 5; 1; 5; 2; 9];
  value_cons #10 2 [3; 5; 1; 5; 2; 9];
  value_cons #10 3 [5; 1; 5; 2; 9];
  value_cons #10 5 [1; 5; 2; 9];
  value_cons #10 1 [5; 2; 9];
  value_cons #10 5 [2; 9];
  value_cons #10 2 [9];
  value_cons #10 9 [];
  ()

let canonical_next7_reversed () : Lemma (canonical #10 next7_reversed) =
  assert (canonical #10 [7]);
  canonical_cons #10 5 [7];
  canonical_cons #10 0 [5; 7];
  canonical_cons #10 0 [0; 5; 7];
  canonical_cons #10 5 [0; 0; 5; 7];
  canonical_cons #10 7 [5; 0; 0; 5; 7];
  canonical_cons #10 4 [7; 5; 0; 0; 5; 7];
  canonical_cons #10 3 [4; 7; 5; 0; 0; 5; 7];
  canonical_cons #10 2 [3; 4; 7; 5; 0; 0; 5; 7];
  canonical_cons #10 1 [2; 3; 4; 7; 5; 0; 0; 5; 7];
  canonical_cons #10 9 [1; 2; 3; 4; 7; 5; 0; 0; 5; 7];
  canonical_cons #10 0 [9; 1; 2; 3; 4; 7; 5; 0; 0; 5; 7];
  canonical_cons #10 9 [0; 9; 1; 2; 3; 4; 7; 5; 0; 0; 5; 7];
  canonical_cons #10 0 [9; 0; 9; 1; 2; 3; 4; 7; 5; 0; 0; 5; 7];
  canonical_cons #10 2 [0; 9; 0; 9; 1; 2; 3; 4; 7; 5; 0; 0; 5; 7];
  canonical_cons #10 3 [2; 0; 9; 0; 9; 1; 2; 3; 4; 7; 5; 0; 0; 5; 7];
  canonical_cons #10 3 [3; 2; 0; 9; 0; 9; 1; 2; 3; 4; 7; 5; 0; 0; 5; 7];
  canonical_cons #10 8 [3; 3; 2; 0; 9; 0; 9; 1; 2; 3; 4; 7; 5; 0; 0; 5; 7];
  canonical_cons #10 5 [8; 3; 3; 2; 0; 9; 0; 9; 1; 2; 3; 4; 7; 5; 0; 0; 5; 7];
  canonical_cons #10 9 [5; 8; 3; 3; 2; 0; 9; 0; 9; 1; 2; 3; 4; 7; 5; 0; 0; 5; 7];
  canonical_cons #10 0 [9; 5; 8; 3; 3; 2; 0; 9; 0; 9; 1; 2; 3; 4; 7; 5; 0; 0; 5; 7];
  canonical_cons #10 5 [0; 9; 5; 8; 3; 3; 2; 0; 9; 0; 9; 1; 2; 3; 4; 7; 5; 0; 0; 5; 7];
  canonical_cons #10 7 [5; 0; 9; 5; 8; 3; 3; 2; 0; 9; 0; 9; 1; 2; 3; 4; 7; 5; 0; 0; 5; 7];
  canonical_cons #10 1 [7; 5; 0; 9; 5; 8; 3; 3; 2; 0; 9; 0; 9; 1; 2; 3; 4; 7; 5; 0; 0; 5; 7];
  ()

let canonical_next7_target () : Lemma (canonical #10 next7_target) =
  assert (canonical #10 [9]);
  canonical_cons #10 2 [9];
  canonical_cons #10 5 [2; 9];
  canonical_cons #10 1 [5; 2; 9];
  canonical_cons #10 5 [1; 5; 2; 9];
  canonical_cons #10 3 [5; 1; 5; 2; 9];
  canonical_cons #10 2 [3; 5; 1; 5; 2; 9];
  canonical_cons #10 6 [2; 3; 5; 1; 5; 2; 9];
  canonical_cons #10 5 [6; 2; 3; 5; 1; 5; 2; 9];
  canonical_cons #10 3 [5; 6; 2; 3; 5; 1; 5; 2; 9];
  canonical_cons #10 9 [3; 5; 6; 2; 3; 5; 1; 5; 2; 9];
  canonical_cons #10 9 [9; 3; 5; 6; 2; 3; 5; 1; 5; 2; 9];
  canonical_cons #10 9 [9; 9; 3; 5; 6; 2; 3; 5; 1; 5; 2; 9];
  canonical_cons #10 9 [9; 9; 9; 3; 5; 6; 2; 3; 5; 1; 5; 2; 9];
  canonical_cons #10 3 [9; 9; 9; 9; 3; 5; 6; 2; 3; 5; 1; 5; 2; 9];
  canonical_cons #10 5 [3; 9; 9; 9; 9; 3; 5; 6; 2; 3; 5; 1; 5; 2; 9];
  canonical_cons #10 7 [5; 3; 9; 9; 9; 9; 3; 5; 6; 2; 3; 5; 1; 5; 2; 9];
  canonical_cons #10 3 [7; 5; 3; 9; 9; 9; 9; 3; 5; 6; 2; 3; 5; 1; 5; 2; 9];
  canonical_cons #10 3 [3; 7; 5; 3; 9; 9; 9; 9; 3; 5; 6; 2; 3; 5; 1; 5; 2; 9];
  canonical_cons #10 4 [3; 3; 7; 5; 3; 9; 9; 9; 9; 3; 5; 6; 2; 3; 5; 1; 5; 2; 9];
  canonical_cons #10 0 [4; 3; 3; 7; 5; 3; 9; 9; 9; 9; 3; 5; 6; 2; 3; 5; 1; 5; 2; 9];
  canonical_cons #10 6 [0; 4; 3; 3; 7; 5; 3; 9; 9; 9; 9; 3; 5; 6; 2; 3; 5; 1; 5; 2; 9];
  canonical_cons #10 2 [6; 0; 4; 3; 3; 7; 5; 3; 9; 9; 9; 9; 3; 5; 6; 2; 3; 5; 1; 5; 2; 9];
  canonical_cons #10 8 [2; 6; 0; 4; 3; 3; 7; 5; 3; 9; 9; 9; 9; 3; 5; 6; 2; 3; 5; 1; 5; 2; 9];
  ()

let reverse_digits_next7_source () : Lemma (
    reverse_digits #10 next7_source == next7_reversed) =
  ReverseAddNext.canonical_next6_target ();
  reverse_list_next7_source ();
  value_next7_reversed ();
  canonical_next7_reversed ();
  reverse_digits_canonical #10 next7_source;
  normalize_value #10 (rev next7_source);
  assert (value (reverse_digits #10 next7_source) ==
    750057432190902338590571);
  digits_of_nat_of_canonical #10 (reverse_digits #10 next7_source);
  digits_of_nat_of_canonical #10 next7_reversed;
  assert (reverse_digits #10 next7_source == next7_reversed);
  ()

let reverse_add_175095833209091234750057_to_925153265399993573340628 () : Lemma (
    reverse_add #10 next7_source == next7_target) =
  ReverseAddNext.canonical_next6_target ();
  reverse_add_value #10 next7_source;
  ReverseAddNext.value_next6_target ();
  reverse_digits_next7_source ();
  value_next7_reversed ();
  value_next7_target ();
  assert (value (reverse_add #10 next7_source) ==
    925153265399993573340628);
  reverse_add_canonical #10 next7_source;
  digits_of_nat_of_canonical #10 (reverse_add #10 next7_source);
  canonical_next7_target ();
  digits_of_nat_of_canonical #10 next7_target;
  assert (reverse_add #10 next7_source == next7_target);
  ()

let trace_digits_profile_175095833209091234750057 () : Lemma (
    trace_digits next7_source == next7_target) =
  reverse_add_175095833209091234750057_to_925153265399993573340628 ();
  trace_digits_equals_reverse_add next7_source;
  assert (trace_digits next7_source == next7_target);
  ()

let trace_profile_shape_175095833209091234750057 () : Lemma (
    length (trace_digits next7_source) == length next7_source) =
  trace_digits_profile_175095833209091234750057 ();
  length_of_eq #(digit 10) (trace_digits next7_source) next7_target;
  assert (length next7_target == length next7_source);
  ()

let trace_profile_final_carry_175095833209091234750057 () : Lemma (
    nth (trace_carries next7_source) (length next7_source) == Some 0) =
  trace_profile_shape_175095833209091234750057 ();
  final_carry_from_length next7_source;
  ()

let local_profile_witness_925153265399993573340628 () : Lemma (
    trace_local_profile_complement_witness next7_target) =
  ReverseAddNext.canonical_next6_target ();
  assert (next7_source <> []);
  trace_profile_shape_175095833209091234750057 ();
  trace_profile_final_carry_175095833209091234750057 ();
  assert (trace_sum_at next7_source 0 == 8);
  reverse_add_175095833209091234750057_to_925153265399993573340628 ();
  no_overflow_outer_sum_6_to_9_implies_next_witness next7_source;
  ()

let next8_source : numeral 10 = next7_target

let next8_reversed : numeral 10 =
  [9; 2; 5; 1; 5; 3; 2; 6; 5; 3; 9; 9; 9; 9; 3; 5; 7; 3; 3; 4; 0; 6; 2; 8]

let next8_target : numeral 10 =
  [7; 5; 1; 2; 9; 6; 5; 3; 1; 7; 8; 9; 9; 9; 7; 0; 4; 6; 6; 9; 1; 1; 5; 7; 1]

let reverse_list_next8_source () : Lemma (rev next8_source == next8_reversed) =
  assert (rev [9] == [9]);
  rev_cons 2 [9];
  rev_cons 5 [2; 9];
  rev_cons 1 [5; 2; 9];
  rev_cons 5 [1; 5; 2; 9];
  rev_cons 3 [5; 1; 5; 2; 9];
  rev_cons 2 [3; 5; 1; 5; 2; 9];
  rev_cons 6 [2; 3; 5; 1; 5; 2; 9];
  rev_cons 5 [6; 2; 3; 5; 1; 5; 2; 9];
  rev_cons 3 [5; 6; 2; 3; 5; 1; 5; 2; 9];
  rev_cons 9 [3; 5; 6; 2; 3; 5; 1; 5; 2; 9];
  rev_cons 9 [9; 3; 5; 6; 2; 3; 5; 1; 5; 2; 9];
  rev_cons 9 [9; 9; 3; 5; 6; 2; 3; 5; 1; 5; 2; 9];
  rev_cons 9 [9; 9; 9; 3; 5; 6; 2; 3; 5; 1; 5; 2; 9];
  rev_cons 3 [9; 9; 9; 9; 3; 5; 6; 2; 3; 5; 1; 5; 2; 9];
  rev_cons 5 [3; 9; 9; 9; 9; 3; 5; 6; 2; 3; 5; 1; 5; 2; 9];
  rev_cons 7 [5; 3; 9; 9; 9; 9; 3; 5; 6; 2; 3; 5; 1; 5; 2; 9];
  rev_cons 3 [7; 5; 3; 9; 9; 9; 9; 3; 5; 6; 2; 3; 5; 1; 5; 2; 9];
  rev_cons 3 [3; 7; 5; 3; 9; 9; 9; 9; 3; 5; 6; 2; 3; 5; 1; 5; 2; 9];
  rev_cons 4 [3; 3; 7; 5; 3; 9; 9; 9; 9; 3; 5; 6; 2; 3; 5; 1; 5; 2; 9];
  rev_cons 0 [4; 3; 3; 7; 5; 3; 9; 9; 9; 9; 3; 5; 6; 2; 3; 5; 1; 5; 2; 9];
  rev_cons 6 [0; 4; 3; 3; 7; 5; 3; 9; 9; 9; 9; 3; 5; 6; 2; 3; 5; 1; 5; 2; 9];
  rev_cons 2 [6; 0; 4; 3; 3; 7; 5; 3; 9; 9; 9; 9; 3; 5; 6; 2; 3; 5; 1; 5; 2; 9];
  rev_cons 8 [2; 6; 0; 4; 3; 3; 7; 5; 3; 9; 9; 9; 9; 3; 5; 6; 2; 3; 5; 1; 5; 2; 9];
  ()

let value_next8_reversed () : Lemma (
    value next8_reversed == 826043375399993562351529) =
  value_cons #10 9 [2; 5; 1; 5; 3; 2; 6; 5; 3; 9; 9; 9; 9; 3; 5; 7; 3; 3; 4; 0; 6; 2; 8];
  value_cons #10 2 [5; 1; 5; 3; 2; 6; 5; 3; 9; 9; 9; 9; 3; 5; 7; 3; 3; 4; 0; 6; 2; 8];
  value_cons #10 5 [1; 5; 3; 2; 6; 5; 3; 9; 9; 9; 9; 3; 5; 7; 3; 3; 4; 0; 6; 2; 8];
  value_cons #10 1 [5; 3; 2; 6; 5; 3; 9; 9; 9; 9; 3; 5; 7; 3; 3; 4; 0; 6; 2; 8];
  value_cons #10 5 [3; 2; 6; 5; 3; 9; 9; 9; 9; 3; 5; 7; 3; 3; 4; 0; 6; 2; 8];
  value_cons #10 3 [2; 6; 5; 3; 9; 9; 9; 9; 3; 5; 7; 3; 3; 4; 0; 6; 2; 8];
  value_cons #10 2 [6; 5; 3; 9; 9; 9; 9; 3; 5; 7; 3; 3; 4; 0; 6; 2; 8];
  value_cons #10 6 [5; 3; 9; 9; 9; 9; 3; 5; 7; 3; 3; 4; 0; 6; 2; 8];
  value_cons #10 5 [3; 9; 9; 9; 9; 3; 5; 7; 3; 3; 4; 0; 6; 2; 8];
  value_cons #10 3 [9; 9; 9; 9; 3; 5; 7; 3; 3; 4; 0; 6; 2; 8];
  value_cons #10 9 [9; 9; 9; 3; 5; 7; 3; 3; 4; 0; 6; 2; 8];
  value_cons #10 9 [9; 9; 3; 5; 7; 3; 3; 4; 0; 6; 2; 8];
  value_cons #10 9 [9; 3; 5; 7; 3; 3; 4; 0; 6; 2; 8];
  value_cons #10 9 [3; 5; 7; 3; 3; 4; 0; 6; 2; 8];
  value_cons #10 3 [5; 7; 3; 3; 4; 0; 6; 2; 8];
  value_cons #10 5 [7; 3; 3; 4; 0; 6; 2; 8];
  value_cons #10 7 [3; 3; 4; 0; 6; 2; 8];
  value_cons #10 3 [3; 4; 0; 6; 2; 8];
  value_cons #10 3 [4; 0; 6; 2; 8];
  value_cons #10 4 [0; 6; 2; 8];
  value_cons #10 0 [6; 2; 8];
  value_cons #10 6 [2; 8];
  value_cons #10 2 [8];
  value_cons #10 8 [];
  ()

let value_next8_target () : Lemma (
    value next8_target == 1751196640799987135692157) =
  value_cons #10 7 [5; 1; 2; 9; 6; 5; 3; 1; 7; 8; 9; 9; 9; 7; 0; 4; 6; 6; 9; 1; 1; 5; 7; 1];
  value_cons #10 5 [1; 2; 9; 6; 5; 3; 1; 7; 8; 9; 9; 9; 7; 0; 4; 6; 6; 9; 1; 1; 5; 7; 1];
  value_cons #10 1 [2; 9; 6; 5; 3; 1; 7; 8; 9; 9; 9; 7; 0; 4; 6; 6; 9; 1; 1; 5; 7; 1];
  value_cons #10 2 [9; 6; 5; 3; 1; 7; 8; 9; 9; 9; 7; 0; 4; 6; 6; 9; 1; 1; 5; 7; 1];
  value_cons #10 9 [6; 5; 3; 1; 7; 8; 9; 9; 9; 7; 0; 4; 6; 6; 9; 1; 1; 5; 7; 1];
  value_cons #10 6 [5; 3; 1; 7; 8; 9; 9; 9; 7; 0; 4; 6; 6; 9; 1; 1; 5; 7; 1];
  value_cons #10 5 [3; 1; 7; 8; 9; 9; 9; 7; 0; 4; 6; 6; 9; 1; 1; 5; 7; 1];
  value_cons #10 3 [1; 7; 8; 9; 9; 9; 7; 0; 4; 6; 6; 9; 1; 1; 5; 7; 1];
  value_cons #10 1 [7; 8; 9; 9; 9; 7; 0; 4; 6; 6; 9; 1; 1; 5; 7; 1];
  value_cons #10 7 [8; 9; 9; 9; 7; 0; 4; 6; 6; 9; 1; 1; 5; 7; 1];
  value_cons #10 8 [9; 9; 9; 7; 0; 4; 6; 6; 9; 1; 1; 5; 7; 1];
  value_cons #10 9 [9; 9; 7; 0; 4; 6; 6; 9; 1; 1; 5; 7; 1];
  value_cons #10 9 [9; 7; 0; 4; 6; 6; 9; 1; 1; 5; 7; 1];
  value_cons #10 9 [7; 0; 4; 6; 6; 9; 1; 1; 5; 7; 1];
  value_cons #10 7 [0; 4; 6; 6; 9; 1; 1; 5; 7; 1];
  value_cons #10 0 [4; 6; 6; 9; 1; 1; 5; 7; 1];
  value_cons #10 4 [6; 6; 9; 1; 1; 5; 7; 1];
  value_cons #10 6 [6; 9; 1; 1; 5; 7; 1];
  value_cons #10 6 [9; 1; 1; 5; 7; 1];
  value_cons #10 9 [1; 1; 5; 7; 1];
  value_cons #10 1 [1; 5; 7; 1];
  value_cons #10 1 [5; 7; 1];
  value_cons #10 5 [7; 1];
  value_cons #10 7 [1];
  value_cons #10 1 [];
  ()

let canonical_next8_reversed () : Lemma (canonical #10 next8_reversed) =
  assert (canonical #10 [8]);
  canonical_cons #10 2 [8];
  canonical_cons #10 6 [2; 8];
  canonical_cons #10 0 [6; 2; 8];
  canonical_cons #10 4 [0; 6; 2; 8];
  canonical_cons #10 3 [4; 0; 6; 2; 8];
  canonical_cons #10 3 [3; 4; 0; 6; 2; 8];
  canonical_cons #10 7 [3; 3; 4; 0; 6; 2; 8];
  canonical_cons #10 5 [7; 3; 3; 4; 0; 6; 2; 8];
  canonical_cons #10 3 [5; 7; 3; 3; 4; 0; 6; 2; 8];
  canonical_cons #10 9 [3; 5; 7; 3; 3; 4; 0; 6; 2; 8];
  canonical_cons #10 9 [9; 3; 5; 7; 3; 3; 4; 0; 6; 2; 8];
  canonical_cons #10 9 [9; 9; 3; 5; 7; 3; 3; 4; 0; 6; 2; 8];
  canonical_cons #10 9 [9; 9; 9; 3; 5; 7; 3; 3; 4; 0; 6; 2; 8];
  canonical_cons #10 3 [9; 9; 9; 9; 3; 5; 7; 3; 3; 4; 0; 6; 2; 8];
  canonical_cons #10 5 [3; 9; 9; 9; 9; 3; 5; 7; 3; 3; 4; 0; 6; 2; 8];
  canonical_cons #10 6 [5; 3; 9; 9; 9; 9; 3; 5; 7; 3; 3; 4; 0; 6; 2; 8];
  canonical_cons #10 2 [6; 5; 3; 9; 9; 9; 9; 3; 5; 7; 3; 3; 4; 0; 6; 2; 8];
  canonical_cons #10 3 [2; 6; 5; 3; 9; 9; 9; 9; 3; 5; 7; 3; 3; 4; 0; 6; 2; 8];
  canonical_cons #10 5 [3; 2; 6; 5; 3; 9; 9; 9; 9; 3; 5; 7; 3; 3; 4; 0; 6; 2; 8];
  canonical_cons #10 1 [5; 3; 2; 6; 5; 3; 9; 9; 9; 9; 3; 5; 7; 3; 3; 4; 0; 6; 2; 8];
  canonical_cons #10 5 [1; 5; 3; 2; 6; 5; 3; 9; 9; 9; 9; 3; 5; 7; 3; 3; 4; 0; 6; 2; 8];
  canonical_cons #10 2 [5; 1; 5; 3; 2; 6; 5; 3; 9; 9; 9; 9; 3; 5; 7; 3; 3; 4; 0; 6; 2; 8];
  canonical_cons #10 9 [2; 5; 1; 5; 3; 2; 6; 5; 3; 9; 9; 9; 9; 3; 5; 7; 3; 3; 4; 0; 6; 2; 8];
  ()

let canonical_next8_target () : Lemma (canonical #10 next8_target) =
  assert (canonical #10 [1]);
  canonical_cons #10 7 [1];
  canonical_cons #10 5 [7; 1];
  canonical_cons #10 1 [5; 7; 1];
  canonical_cons #10 1 [1; 5; 7; 1];
  canonical_cons #10 9 [1; 1; 5; 7; 1];
  canonical_cons #10 6 [9; 1; 1; 5; 7; 1];
  canonical_cons #10 6 [6; 9; 1; 1; 5; 7; 1];
  canonical_cons #10 4 [6; 6; 9; 1; 1; 5; 7; 1];
  canonical_cons #10 0 [4; 6; 6; 9; 1; 1; 5; 7; 1];
  canonical_cons #10 7 [0; 4; 6; 6; 9; 1; 1; 5; 7; 1];
  canonical_cons #10 9 [7; 0; 4; 6; 6; 9; 1; 1; 5; 7; 1];
  canonical_cons #10 9 [9; 7; 0; 4; 6; 6; 9; 1; 1; 5; 7; 1];
  canonical_cons #10 9 [9; 9; 7; 0; 4; 6; 6; 9; 1; 1; 5; 7; 1];
  canonical_cons #10 8 [9; 9; 9; 7; 0; 4; 6; 6; 9; 1; 1; 5; 7; 1];
  canonical_cons #10 7 [8; 9; 9; 9; 7; 0; 4; 6; 6; 9; 1; 1; 5; 7; 1];
  canonical_cons #10 1 [7; 8; 9; 9; 9; 7; 0; 4; 6; 6; 9; 1; 1; 5; 7; 1];
  canonical_cons #10 3 [1; 7; 8; 9; 9; 9; 7; 0; 4; 6; 6; 9; 1; 1; 5; 7; 1];
  canonical_cons #10 5 [3; 1; 7; 8; 9; 9; 9; 7; 0; 4; 6; 6; 9; 1; 1; 5; 7; 1];
  canonical_cons #10 6 [5; 3; 1; 7; 8; 9; 9; 9; 7; 0; 4; 6; 6; 9; 1; 1; 5; 7; 1];
  canonical_cons #10 9 [6; 5; 3; 1; 7; 8; 9; 9; 9; 7; 0; 4; 6; 6; 9; 1; 1; 5; 7; 1];
  canonical_cons #10 2 [9; 6; 5; 3; 1; 7; 8; 9; 9; 9; 7; 0; 4; 6; 6; 9; 1; 1; 5; 7; 1];
  canonical_cons #10 1 [2; 9; 6; 5; 3; 1; 7; 8; 9; 9; 9; 7; 0; 4; 6; 6; 9; 1; 1; 5; 7; 1];
  canonical_cons #10 5 [1; 2; 9; 6; 5; 3; 1; 7; 8; 9; 9; 9; 7; 0; 4; 6; 6; 9; 1; 1; 5; 7; 1];
  canonical_cons #10 7 [5; 1; 2; 9; 6; 5; 3; 1; 7; 8; 9; 9; 9; 7; 0; 4; 6; 6; 9; 1; 1; 5; 7; 1];
  ()

let reverse_digits_next8_source () : Lemma (
    reverse_digits #10 next8_source == next8_reversed) =
  ReverseAddNext.canonical_next7_target ();
  reverse_list_next8_source ();
  value_next8_reversed ();
  canonical_next8_reversed ();
  reverse_digits_canonical #10 next8_source;
  normalize_value #10 (rev next8_source);
  assert (value (reverse_digits #10 next8_source) ==
    826043375399993562351529);
  digits_of_nat_of_canonical #10 (reverse_digits #10 next8_source);
  digits_of_nat_of_canonical #10 next8_reversed;
  assert (reverse_digits #10 next8_source == next8_reversed);
  ()

let reverse_add_925153265399993573340628_to_1751196640799987135692157 () : Lemma (
    reverse_add #10 next8_source == next8_target) =
  ReverseAddNext.canonical_next7_target ();
  reverse_add_value #10 next8_source;
  ReverseAddNext.value_next7_target ();
  reverse_digits_next8_source ();
  value_next8_reversed ();
  value_next8_target ();
  assert (value (reverse_add #10 next8_source) ==
    1751196640799987135692157);
  reverse_add_canonical #10 next8_source;
  digits_of_nat_of_canonical #10 (reverse_add #10 next8_source);
  canonical_next8_target ();
  digits_of_nat_of_canonical #10 next8_target;
  assert (reverse_add #10 next8_source == next8_target);
  ()

let trace_digits_profile_925153265399993573340628 () : Lemma (
    trace_digits next8_source == next8_target) =
  reverse_add_925153265399993573340628_to_1751196640799987135692157 ();
  trace_digits_equals_reverse_add next8_source;
  assert (trace_digits next8_source == next8_target);
  ()

let trace_carries_next8_source () : Lemma (trace_carries next8_source ==
    [0; 1; 0; 1; 0; 0; 0; 0; 1; 1; 0; 1; 1; 1; 1; 0; 1; 1; 0; 0; 0; 0; 1; 0; 1]) =
  reverse_list_next8_source ();
  assert (trace_carries next8_source ==
    (add_trace #10 next8_source next8_reversed 0).carries);
  add_trace_carries_step #10 8 9
    [2; 6; 0; 4; 3; 3; 7; 5; 3; 9; 9; 9; 9; 3; 5; 6; 2; 3; 5; 1; 5; 2; 9]
    [2; 5; 1; 5; 3; 2; 6; 5; 3; 9; 9; 9; 9; 3; 5; 7; 3; 3; 4; 0; 6; 2; 8] 0;
  add_trace_carries_step #10 2 2
    [6; 0; 4; 3; 3; 7; 5; 3; 9; 9; 9; 9; 3; 5; 6; 2; 3; 5; 1; 5; 2; 9]
    [5; 1; 5; 3; 2; 6; 5; 3; 9; 9; 9; 9; 3; 5; 7; 3; 3; 4; 0; 6; 2; 8] 1;
  add_trace_carries_step #10 6 5
    [0; 4; 3; 3; 7; 5; 3; 9; 9; 9; 9; 3; 5; 6; 2; 3; 5; 1; 5; 2; 9]
    [1; 5; 3; 2; 6; 5; 3; 9; 9; 9; 9; 3; 5; 7; 3; 3; 4; 0; 6; 2; 8] 0;
  add_trace_carries_step #10 0 1
    [4; 3; 3; 7; 5; 3; 9; 9; 9; 9; 3; 5; 6; 2; 3; 5; 1; 5; 2; 9]
    [5; 3; 2; 6; 5; 3; 9; 9; 9; 9; 3; 5; 7; 3; 3; 4; 0; 6; 2; 8] 1;
  add_trace_carries_step #10 4 5
    [3; 3; 7; 5; 3; 9; 9; 9; 9; 3; 5; 6; 2; 3; 5; 1; 5; 2; 9]
    [3; 2; 6; 5; 3; 9; 9; 9; 9; 3; 5; 7; 3; 3; 4; 0; 6; 2; 8] 0;
  add_trace_carries_step #10 3 3
    [3; 7; 5; 3; 9; 9; 9; 9; 3; 5; 6; 2; 3; 5; 1; 5; 2; 9]
    [2; 6; 5; 3; 9; 9; 9; 9; 3; 5; 7; 3; 3; 4; 0; 6; 2; 8] 0;
  add_trace_carries_step #10 3 2
    [7; 5; 3; 9; 9; 9; 9; 3; 5; 6; 2; 3; 5; 1; 5; 2; 9]
    [6; 5; 3; 9; 9; 9; 9; 3; 5; 7; 3; 3; 4; 0; 6; 2; 8] 0;
  add_trace_carries_step #10 7 6
    [5; 3; 9; 9; 9; 9; 3; 5; 6; 2; 3; 5; 1; 5; 2; 9]
    [5; 3; 9; 9; 9; 9; 3; 5; 7; 3; 3; 4; 0; 6; 2; 8] 0;
  add_trace_carries_step #10 5 5
    [3; 9; 9; 9; 9; 3; 5; 6; 2; 3; 5; 1; 5; 2; 9]
    [3; 9; 9; 9; 9; 3; 5; 7; 3; 3; 4; 0; 6; 2; 8] 1;
  add_trace_carries_step #10 3 3
    [9; 9; 9; 9; 3; 5; 6; 2; 3; 5; 1; 5; 2; 9]
    [9; 9; 9; 9; 3; 5; 7; 3; 3; 4; 0; 6; 2; 8] 1;
  add_trace_carries_step #10 9 9
    [9; 9; 9; 3; 5; 6; 2; 3; 5; 1; 5; 2; 9]
    [9; 9; 9; 3; 5; 7; 3; 3; 4; 0; 6; 2; 8] 0;
  add_trace_carries_step #10 9 9
    [9; 9; 3; 5; 6; 2; 3; 5; 1; 5; 2; 9]
    [9; 9; 3; 5; 7; 3; 3; 4; 0; 6; 2; 8] 1;
  add_trace_carries_step #10 9 9
    [9; 3; 5; 6; 2; 3; 5; 1; 5; 2; 9]
    [9; 3; 5; 7; 3; 3; 4; 0; 6; 2; 8] 1;
  add_trace_carries_step #10 9 9
    [3; 5; 6; 2; 3; 5; 1; 5; 2; 9]
    [3; 5; 7; 3; 3; 4; 0; 6; 2; 8] 1;
  add_trace_carries_step #10 3 3
    [5; 6; 2; 3; 5; 1; 5; 2; 9]
    [5; 7; 3; 3; 4; 0; 6; 2; 8] 1;
  add_trace_carries_step #10 5 5
    [6; 2; 3; 5; 1; 5; 2; 9]
    [7; 3; 3; 4; 0; 6; 2; 8] 0;
  add_trace_carries_step #10 6 7
    [2; 3; 5; 1; 5; 2; 9]
    [3; 3; 4; 0; 6; 2; 8] 1;
  add_trace_carries_step #10 2 3
    [3; 5; 1; 5; 2; 9]
    [3; 4; 0; 6; 2; 8] 1;
  add_trace_carries_step #10 3 3
    [5; 1; 5; 2; 9]
    [4; 0; 6; 2; 8] 0;
  add_trace_carries_step #10 5 4
    [1; 5; 2; 9]
    [0; 6; 2; 8] 0;
  add_trace_carries_step #10 1 0
    [5; 2; 9]
    [6; 2; 8] 0;
  add_trace_carries_step #10 5 6
    [2; 9]
    [2; 8] 0;
  add_trace_carries_step #10 2 2
    [9]
    [8] 1;
  add_trace_carries_step #10 9 8
    []
    [] 0;
  assert ((add_trace #10 [] [] 1).carries == [1]);
  assert ((add_trace #10 next8_source next8_reversed 0).carries ==
    [0; 1; 0; 1; 0; 0; 0; 0; 1; 1; 0; 1; 1; 1; 1; 0; 1; 1; 0; 0; 0; 0; 1; 0; 1]);
  ()

let trace_profile_shape_925153265399993573340628 () : Lemma (
    length (trace_digits next8_source) == length next8_source + 1) =
  trace_digits_profile_925153265399993573340628 ();
  length_of_eq #(digit 10) (trace_digits next8_source) next8_target;
  assert (length next8_target == length next8_source + 1);
  ()

let trace_profile_final_carry_925153265399993573340628 () : Lemma (
    nth (trace_carries next8_source) (length next8_source) == Some 1) =
  trace_profile_shape_925153265399993573340628 ();
  ReverseAddContinuation.final_carry_from_overflow_length next8_source;
  ()

let trace_profile_sums_925153265399993573340628 () : Lemma (
    trace_sum_at next8_source 0 == 17 /\
    trace_sum_at next8_source 1 == 4 /\
    trace_sum_at next8_source 23 == 17) =
  reverse_list_next8_source ();
  ()

let trace_profile_carry_facts_925153265399993573340628 () : Lemma (
    trace_carry_at next8_source 1 == 1 /\
    trace_carry_at next8_source 23 == 0 /\
    trace_carry_at next8_source 2 == 0 /\
    trace_carry_at next8_source 24 == 1) =
  trace_carries_next8_source ();
  ()

let overflow_precondition_925153265399993573340628 () : Lemma (
    canonical #10 next8_source /\
    next8_source <> [] /\
    length (trace_digits next8_source) == length next8_source + 1 /\
    nth (trace_carries next8_source) (length next8_source) == Some 1 /\
    1 <= trace_sum_at next8_source 0 /\
    trace_sum_at next8_source 0 <= 18 /\
    trace_sum_at next8_source 0 <> 10 /\
    exists (i:nat). 0 < i /\ i < length next8_source /\
      trace_sum_at next8_source i +
          trace_sum_at next8_source (length next8_source - i) +
          trace_carry_at next8_source i +
          trace_carry_at next8_source (length next8_source - i) >=
        10 + 10 *
          (trace_carry_at next8_source (i + 1) +
           trace_carry_at next8_source (length next8_source - i + 1))) =
  ReverseAddNext.canonical_next7_target ();
  assert (next8_source <> []);
  trace_profile_shape_925153265399993573340628 ();
  trace_profile_final_carry_925153265399993573340628 ();
  trace_profile_sums_925153265399993573340628 ();
  trace_profile_carry_facts_925153265399993573340628 ();
  assert (length (trace_digits next8_source) == length next8_source + 1);
  assert (nth (trace_carries next8_source)
    (length next8_source) == Some 1);
  assert (trace_sum_at next8_source 0 == 17);
  assert (trace_sum_at next8_source 1 == 4);
  assert (trace_sum_at next8_source 23 == 17);
  assert (trace_carry_at next8_source 1 == 1);
  assert (trace_carry_at next8_source 23 == 0);
  assert (trace_carry_at next8_source 2 == 0);
  assert (trace_carry_at next8_source 24 == 1);
  assert (1 <= trace_sum_at next8_source 0 /\
    trace_sum_at next8_source 0 <= 18);
  assert (trace_sum_at next8_source 0 <> 10);
  let n : nat = length next8_source in
  assert (0 < 1 /\ 1 < n);
  assert (trace_sum_at next8_source 1 +
      trace_sum_at next8_source (n - 1) +
      trace_carry_at next8_source 1 +
      trace_carry_at next8_source (n - 1) >=
    10 + 10 *
      (trace_carry_at next8_source 2 +
       trace_carry_at next8_source (n - 1 + 1)));
  exists_intro
    (fun (i:nat) -> 0 < i /\ i < n /\
      trace_sum_at next8_source i +
          trace_sum_at next8_source (n - i) +
          trace_carry_at next8_source i +
          trace_carry_at next8_source (n - i) >=
        10 + 10 *
          (trace_carry_at next8_source (i + 1) +
           trace_carry_at next8_source (n - i + 1)))
    1;
  ()

let local_profile_witness_1751196640799987135692157 () : Lemma (
    trace_local_profile_complement_witness next8_target) =
  overflow_precondition_925153265399993573340628 ();
  reverse_add_925153265399993573340628_to_1751196640799987135692157 ();
  overflow_internal_cell_implies_next_witness next8_source;
  ()

let next9_source : numeral 10 = next8_target

let next9_reversed : numeral 10 =
  [1; 7; 5; 1; 1; 9; 6; 6; 4; 0; 7; 9; 9; 9; 8; 7; 1; 3; 5; 6; 9; 2; 1; 5; 7]

let next9_target : numeral 10 =
  [8; 2; 7; 3; 0; 6; 2; 0; 6; 7; 5; 9; 9; 9; 6; 8; 5; 9; 1; 6; 1; 4; 6; 2; 9]

let reverse_list_next9_source () : Lemma (rev next9_source == next9_reversed) =
  assert (rev [1] == [1]);
  rev_cons 7 [1];
  rev_cons 5 [7; 1];
  rev_cons 1 [5; 7; 1];
  rev_cons 1 [1; 5; 7; 1];
  rev_cons 9 [1; 1; 5; 7; 1];
  rev_cons 6 [9; 1; 1; 5; 7; 1];
  rev_cons 6 [6; 9; 1; 1; 5; 7; 1];
  rev_cons 4 [6; 6; 9; 1; 1; 5; 7; 1];
  rev_cons 0 [4; 6; 6; 9; 1; 1; 5; 7; 1];
  rev_cons 7 [0; 4; 6; 6; 9; 1; 1; 5; 7; 1];
  rev_cons 9 [7; 0; 4; 6; 6; 9; 1; 1; 5; 7; 1];
  rev_cons 9 [9; 7; 0; 4; 6; 6; 9; 1; 1; 5; 7; 1];
  rev_cons 9 [9; 9; 7; 0; 4; 6; 6; 9; 1; 1; 5; 7; 1];
  rev_cons 8 [9; 9; 9; 7; 0; 4; 6; 6; 9; 1; 1; 5; 7; 1];
  rev_cons 7 [8; 9; 9; 9; 7; 0; 4; 6; 6; 9; 1; 1; 5; 7; 1];
  rev_cons 1 [7; 8; 9; 9; 9; 7; 0; 4; 6; 6; 9; 1; 1; 5; 7; 1];
  rev_cons 3 [1; 7; 8; 9; 9; 9; 7; 0; 4; 6; 6; 9; 1; 1; 5; 7; 1];
  rev_cons 5 [3; 1; 7; 8; 9; 9; 9; 7; 0; 4; 6; 6; 9; 1; 1; 5; 7; 1];
  rev_cons 6 [5; 3; 1; 7; 8; 9; 9; 9; 7; 0; 4; 6; 6; 9; 1; 1; 5; 7; 1];
  rev_cons 9 [6; 5; 3; 1; 7; 8; 9; 9; 9; 7; 0; 4; 6; 6; 9; 1; 1; 5; 7; 1];
  rev_cons 2 [9; 6; 5; 3; 1; 7; 8; 9; 9; 9; 7; 0; 4; 6; 6; 9; 1; 1; 5; 7; 1];
  rev_cons 1 [2; 9; 6; 5; 3; 1; 7; 8; 9; 9; 9; 7; 0; 4; 6; 6; 9; 1; 1; 5; 7; 1];
  rev_cons 5 [1; 2; 9; 6; 5; 3; 1; 7; 8; 9; 9; 9; 7; 0; 4; 6; 6; 9; 1; 1; 5; 7; 1];
  rev_cons 7 [5; 1; 2; 9; 6; 5; 3; 1; 7; 8; 9; 9; 9; 7; 0; 4; 6; 6; 9; 1; 1; 5; 7; 1];
  ()

let value_next9_reversed () : Lemma (
    value next9_reversed == 7512965317899970466911571) =
  value_cons #10 1 [7; 5; 1; 1; 9; 6; 6; 4; 0; 7; 9; 9; 9; 8; 7; 1; 3; 5; 6; 9; 2; 1; 5; 7];
  value_cons #10 7 [5; 1; 1; 9; 6; 6; 4; 0; 7; 9; 9; 9; 8; 7; 1; 3; 5; 6; 9; 2; 1; 5; 7];
  value_cons #10 5 [1; 1; 9; 6; 6; 4; 0; 7; 9; 9; 9; 8; 7; 1; 3; 5; 6; 9; 2; 1; 5; 7];
  value_cons #10 1 [1; 9; 6; 6; 4; 0; 7; 9; 9; 9; 8; 7; 1; 3; 5; 6; 9; 2; 1; 5; 7];
  value_cons #10 1 [9; 6; 6; 4; 0; 7; 9; 9; 9; 8; 7; 1; 3; 5; 6; 9; 2; 1; 5; 7];
  value_cons #10 9 [6; 6; 4; 0; 7; 9; 9; 9; 8; 7; 1; 3; 5; 6; 9; 2; 1; 5; 7];
  value_cons #10 6 [6; 4; 0; 7; 9; 9; 9; 8; 7; 1; 3; 5; 6; 9; 2; 1; 5; 7];
  value_cons #10 6 [4; 0; 7; 9; 9; 9; 8; 7; 1; 3; 5; 6; 9; 2; 1; 5; 7];
  value_cons #10 4 [0; 7; 9; 9; 9; 8; 7; 1; 3; 5; 6; 9; 2; 1; 5; 7];
  value_cons #10 0 [7; 9; 9; 9; 8; 7; 1; 3; 5; 6; 9; 2; 1; 5; 7];
  value_cons #10 7 [9; 9; 9; 8; 7; 1; 3; 5; 6; 9; 2; 1; 5; 7];
  value_cons #10 9 [9; 9; 8; 7; 1; 3; 5; 6; 9; 2; 1; 5; 7];
  value_cons #10 9 [9; 8; 7; 1; 3; 5; 6; 9; 2; 1; 5; 7];
  value_cons #10 9 [8; 7; 1; 3; 5; 6; 9; 2; 1; 5; 7];
  value_cons #10 8 [7; 1; 3; 5; 6; 9; 2; 1; 5; 7];
  value_cons #10 7 [1; 3; 5; 6; 9; 2; 1; 5; 7];
  value_cons #10 1 [3; 5; 6; 9; 2; 1; 5; 7];
  value_cons #10 3 [5; 6; 9; 2; 1; 5; 7];
  value_cons #10 5 [6; 9; 2; 1; 5; 7];
  value_cons #10 6 [9; 2; 1; 5; 7];
  value_cons #10 9 [2; 1; 5; 7];
  value_cons #10 2 [1; 5; 7];
  value_cons #10 1 [5; 7];
  value_cons #10 5 [7];
  value_cons #10 7 [];
  ()

let value_next9_target () : Lemma (
    value next9_target == 9264161958699957602603728) =
  value_cons #10 8 [2; 7; 3; 0; 6; 2; 0; 6; 7; 5; 9; 9; 9; 6; 8; 5; 9; 1; 6; 1; 4; 6; 2; 9];
  value_cons #10 2 [7; 3; 0; 6; 2; 0; 6; 7; 5; 9; 9; 9; 6; 8; 5; 9; 1; 6; 1; 4; 6; 2; 9];
  value_cons #10 7 [3; 0; 6; 2; 0; 6; 7; 5; 9; 9; 9; 6; 8; 5; 9; 1; 6; 1; 4; 6; 2; 9];
  value_cons #10 3 [0; 6; 2; 0; 6; 7; 5; 9; 9; 9; 6; 8; 5; 9; 1; 6; 1; 4; 6; 2; 9];
  value_cons #10 0 [6; 2; 0; 6; 7; 5; 9; 9; 9; 6; 8; 5; 9; 1; 6; 1; 4; 6; 2; 9];
  value_cons #10 6 [2; 0; 6; 7; 5; 9; 9; 9; 6; 8; 5; 9; 1; 6; 1; 4; 6; 2; 9];
  value_cons #10 2 [0; 6; 7; 5; 9; 9; 9; 6; 8; 5; 9; 1; 6; 1; 4; 6; 2; 9];
  value_cons #10 0 [6; 7; 5; 9; 9; 9; 6; 8; 5; 9; 1; 6; 1; 4; 6; 2; 9];
  value_cons #10 6 [7; 5; 9; 9; 9; 6; 8; 5; 9; 1; 6; 1; 4; 6; 2; 9];
  value_cons #10 7 [5; 9; 9; 9; 6; 8; 5; 9; 1; 6; 1; 4; 6; 2; 9];
  value_cons #10 5 [9; 9; 9; 6; 8; 5; 9; 1; 6; 1; 4; 6; 2; 9];
  value_cons #10 9 [9; 9; 6; 8; 5; 9; 1; 6; 1; 4; 6; 2; 9];
  value_cons #10 9 [9; 6; 8; 5; 9; 1; 6; 1; 4; 6; 2; 9];
  value_cons #10 9 [6; 8; 5; 9; 1; 6; 1; 4; 6; 2; 9];
  value_cons #10 6 [8; 5; 9; 1; 6; 1; 4; 6; 2; 9];
  value_cons #10 8 [5; 9; 1; 6; 1; 4; 6; 2; 9];
  value_cons #10 5 [9; 1; 6; 1; 4; 6; 2; 9];
  value_cons #10 9 [1; 6; 1; 4; 6; 2; 9];
  value_cons #10 1 [6; 1; 4; 6; 2; 9];
  value_cons #10 6 [1; 4; 6; 2; 9];
  value_cons #10 1 [4; 6; 2; 9];
  value_cons #10 4 [6; 2; 9];
  value_cons #10 6 [2; 9];
  value_cons #10 2 [9];
  value_cons #10 9 [];
  ()

let canonical_next9_reversed () : Lemma (canonical #10 next9_reversed) =
  assert (canonical #10 [7]);
  canonical_cons #10 5 [7];
  canonical_cons #10 1 [5; 7];
  canonical_cons #10 2 [1; 5; 7];
  canonical_cons #10 9 [2; 1; 5; 7];
  canonical_cons #10 6 [9; 2; 1; 5; 7];
  canonical_cons #10 5 [6; 9; 2; 1; 5; 7];
  canonical_cons #10 3 [5; 6; 9; 2; 1; 5; 7];
  canonical_cons #10 1 [3; 5; 6; 9; 2; 1; 5; 7];
  canonical_cons #10 7 [1; 3; 5; 6; 9; 2; 1; 5; 7];
  canonical_cons #10 8 [7; 1; 3; 5; 6; 9; 2; 1; 5; 7];
  canonical_cons #10 9 [8; 7; 1; 3; 5; 6; 9; 2; 1; 5; 7];
  canonical_cons #10 9 [9; 8; 7; 1; 3; 5; 6; 9; 2; 1; 5; 7];
  canonical_cons #10 9 [9; 9; 8; 7; 1; 3; 5; 6; 9; 2; 1; 5; 7];
  canonical_cons #10 7 [9; 9; 9; 8; 7; 1; 3; 5; 6; 9; 2; 1; 5; 7];
  canonical_cons #10 0 [7; 9; 9; 9; 8; 7; 1; 3; 5; 6; 9; 2; 1; 5; 7];
  canonical_cons #10 4 [0; 7; 9; 9; 9; 8; 7; 1; 3; 5; 6; 9; 2; 1; 5; 7];
  canonical_cons #10 6 [4; 0; 7; 9; 9; 9; 8; 7; 1; 3; 5; 6; 9; 2; 1; 5; 7];
  canonical_cons #10 6 [6; 4; 0; 7; 9; 9; 9; 8; 7; 1; 3; 5; 6; 9; 2; 1; 5; 7];
  canonical_cons #10 9 [6; 6; 4; 0; 7; 9; 9; 9; 8; 7; 1; 3; 5; 6; 9; 2; 1; 5; 7];
  canonical_cons #10 1 [9; 6; 6; 4; 0; 7; 9; 9; 9; 8; 7; 1; 3; 5; 6; 9; 2; 1; 5; 7];
  canonical_cons #10 1 [1; 9; 6; 6; 4; 0; 7; 9; 9; 9; 8; 7; 1; 3; 5; 6; 9; 2; 1; 5; 7];
  canonical_cons #10 5 [1; 1; 9; 6; 6; 4; 0; 7; 9; 9; 9; 8; 7; 1; 3; 5; 6; 9; 2; 1; 5; 7];
  canonical_cons #10 7 [5; 1; 1; 9; 6; 6; 4; 0; 7; 9; 9; 9; 8; 7; 1; 3; 5; 6; 9; 2; 1; 5; 7];
  canonical_cons #10 1 [7; 5; 1; 1; 9; 6; 6; 4; 0; 7; 9; 9; 9; 8; 7; 1; 3; 5; 6; 9; 2; 1; 5; 7];
  ()

let canonical_next9_target () : Lemma (canonical #10 next9_target) =
  assert (canonical #10 [9]);
  canonical_cons #10 2 [9];
  canonical_cons #10 6 [2; 9];
  canonical_cons #10 4 [6; 2; 9];
  canonical_cons #10 1 [4; 6; 2; 9];
  canonical_cons #10 6 [1; 4; 6; 2; 9];
  canonical_cons #10 1 [6; 1; 4; 6; 2; 9];
  canonical_cons #10 9 [1; 6; 1; 4; 6; 2; 9];
  canonical_cons #10 5 [9; 1; 6; 1; 4; 6; 2; 9];
  canonical_cons #10 8 [5; 9; 1; 6; 1; 4; 6; 2; 9];
  canonical_cons #10 6 [8; 5; 9; 1; 6; 1; 4; 6; 2; 9];
  canonical_cons #10 9 [6; 8; 5; 9; 1; 6; 1; 4; 6; 2; 9];
  canonical_cons #10 9 [9; 6; 8; 5; 9; 1; 6; 1; 4; 6; 2; 9];
  canonical_cons #10 9 [9; 9; 6; 8; 5; 9; 1; 6; 1; 4; 6; 2; 9];
  canonical_cons #10 5 [9; 9; 9; 6; 8; 5; 9; 1; 6; 1; 4; 6; 2; 9];
  canonical_cons #10 7 [5; 9; 9; 9; 6; 8; 5; 9; 1; 6; 1; 4; 6; 2; 9];
  canonical_cons #10 6 [7; 5; 9; 9; 9; 6; 8; 5; 9; 1; 6; 1; 4; 6; 2; 9];
  canonical_cons #10 0 [6; 7; 5; 9; 9; 9; 6; 8; 5; 9; 1; 6; 1; 4; 6; 2; 9];
  canonical_cons #10 2 [0; 6; 7; 5; 9; 9; 9; 6; 8; 5; 9; 1; 6; 1; 4; 6; 2; 9];
  canonical_cons #10 6 [2; 0; 6; 7; 5; 9; 9; 9; 6; 8; 5; 9; 1; 6; 1; 4; 6; 2; 9];
  canonical_cons #10 0 [6; 2; 0; 6; 7; 5; 9; 9; 9; 6; 8; 5; 9; 1; 6; 1; 4; 6; 2; 9];
  canonical_cons #10 3 [0; 6; 2; 0; 6; 7; 5; 9; 9; 9; 6; 8; 5; 9; 1; 6; 1; 4; 6; 2; 9];
  canonical_cons #10 7 [3; 0; 6; 2; 0; 6; 7; 5; 9; 9; 9; 6; 8; 5; 9; 1; 6; 1; 4; 6; 2; 9];
  canonical_cons #10 2 [7; 3; 0; 6; 2; 0; 6; 7; 5; 9; 9; 9; 6; 8; 5; 9; 1; 6; 1; 4; 6; 2; 9];
  canonical_cons #10 8 [2; 7; 3; 0; 6; 2; 0; 6; 7; 5; 9; 9; 9; 6; 8; 5; 9; 1; 6; 1; 4; 6; 2; 9];
  ()

let reverse_digits_next9_source () : Lemma (
    reverse_digits #10 next9_source == next9_reversed) =
  ReverseAddNext.canonical_next8_target ();
  reverse_list_next9_source ();
  value_next9_reversed ();
  canonical_next9_reversed ();
  reverse_digits_canonical #10 next9_source;
  normalize_value #10 (rev next9_source);
  assert (value (reverse_digits #10 next9_source) ==
    7512965317899970466911571);
  digits_of_nat_of_canonical #10 (reverse_digits #10 next9_source);
  digits_of_nat_of_canonical #10 next9_reversed;
  assert (reverse_digits #10 next9_source == next9_reversed);
  ()

let reverse_add_1751196640799987135692157_to_9264161958699957602603728 () : Lemma (
    reverse_add #10 next9_source == next9_target) =
  ReverseAddNext.canonical_next8_target ();
  reverse_add_value #10 next9_source;
  ReverseAddNext.value_next8_target ();
  reverse_digits_next9_source ();
  value_next9_reversed ();
  value_next9_target ();
  assert (value (reverse_add #10 next9_source) ==
    9264161958699957602603728);
  reverse_add_canonical #10 next9_source;
  digits_of_nat_of_canonical #10 (reverse_add #10 next9_source);
  canonical_next9_target ();
  digits_of_nat_of_canonical #10 next9_target;
  assert (reverse_add #10 next9_source == next9_target);
  ()

let trace_digits_profile_1751196640799987135692157 () : Lemma (
    trace_digits next9_source == next9_target) =
  reverse_add_1751196640799987135692157_to_9264161958699957602603728 ();
  trace_digits_equals_reverse_add next9_source;
  assert (trace_digits next9_source == next9_target);
  ()

let trace_profile_shape_1751196640799987135692157 () : Lemma (
    length (trace_digits next9_source) == length next9_source) =
  trace_digits_profile_1751196640799987135692157 ();
  length_of_eq #(digit 10) (trace_digits next9_source) next9_target;
  assert (length next9_target == length next9_source);
  ()

let trace_profile_final_carry_1751196640799987135692157 () : Lemma (
    nth (trace_carries next9_source) (length next9_source) == Some 0) =
  trace_profile_shape_1751196640799987135692157 ();
  final_carry_from_length next9_source;
  ()

let local_profile_witness_9264161958699957602603728 () : Lemma (
    trace_local_profile_complement_witness next9_target) =
  ReverseAddNext.canonical_next8_target ();
  assert (next9_source <> []);
  trace_profile_shape_1751196640799987135692157 ();
  trace_profile_final_carry_1751196640799987135692157 ();
  assert (trace_sum_at next9_source 0 == 8);
  reverse_add_1751196640799987135692157_to_9264161958699957602603728 ();
  no_overflow_outer_sum_6_to_9_implies_next_witness next9_source;
  ()

let next10_source : numeral 10 = next9_target

let next10_reversed : numeral 10 =
  [9; 2; 6; 4; 1; 6; 1; 9; 5; 8; 6; 9; 9; 9; 5; 7; 6; 0; 2; 6; 0; 3; 7; 2; 8]

let next10_target : numeral 10 =
  [7; 5; 3; 8; 1; 2; 4; 9; 1; 6; 2; 9; 9; 9; 2; 6; 2; 0; 4; 2; 2; 7; 3; 5; 7; 1]

let reverse_list_next10_source () : Lemma (rev next10_source == next10_reversed) =
  assert (rev [9] == [9]);
  rev_cons 2 [9];
  rev_cons 6 [2; 9];
  rev_cons 4 [6; 2; 9];
  rev_cons 1 [4; 6; 2; 9];
  rev_cons 6 [1; 4; 6; 2; 9];
  rev_cons 1 [6; 1; 4; 6; 2; 9];
  rev_cons 9 [1; 6; 1; 4; 6; 2; 9];
  rev_cons 5 [9; 1; 6; 1; 4; 6; 2; 9];
  rev_cons 8 [5; 9; 1; 6; 1; 4; 6; 2; 9];
  rev_cons 6 [8; 5; 9; 1; 6; 1; 4; 6; 2; 9];
  rev_cons 9 [6; 8; 5; 9; 1; 6; 1; 4; 6; 2; 9];
  rev_cons 9 [9; 6; 8; 5; 9; 1; 6; 1; 4; 6; 2; 9];
  rev_cons 9 [9; 9; 6; 8; 5; 9; 1; 6; 1; 4; 6; 2; 9];
  rev_cons 5 [9; 9; 9; 6; 8; 5; 9; 1; 6; 1; 4; 6; 2; 9];
  rev_cons 7 [5; 9; 9; 9; 6; 8; 5; 9; 1; 6; 1; 4; 6; 2; 9];
  rev_cons 6 [7; 5; 9; 9; 9; 6; 8; 5; 9; 1; 6; 1; 4; 6; 2; 9];
  rev_cons 0 [6; 7; 5; 9; 9; 9; 6; 8; 5; 9; 1; 6; 1; 4; 6; 2; 9];
  rev_cons 2 [0; 6; 7; 5; 9; 9; 9; 6; 8; 5; 9; 1; 6; 1; 4; 6; 2; 9];
  rev_cons 6 [2; 0; 6; 7; 5; 9; 9; 9; 6; 8; 5; 9; 1; 6; 1; 4; 6; 2; 9];
  rev_cons 0 [6; 2; 0; 6; 7; 5; 9; 9; 9; 6; 8; 5; 9; 1; 6; 1; 4; 6; 2; 9];
  rev_cons 3 [0; 6; 2; 0; 6; 7; 5; 9; 9; 9; 6; 8; 5; 9; 1; 6; 1; 4; 6; 2; 9];
  rev_cons 7 [3; 0; 6; 2; 0; 6; 7; 5; 9; 9; 9; 6; 8; 5; 9; 1; 6; 1; 4; 6; 2; 9];
  rev_cons 2 [7; 3; 0; 6; 2; 0; 6; 7; 5; 9; 9; 9; 6; 8; 5; 9; 1; 6; 1; 4; 6; 2; 9];
  rev_cons 8 [2; 7; 3; 0; 6; 2; 0; 6; 7; 5; 9; 9; 9; 6; 8; 5; 9; 1; 6; 1; 4; 6; 2; 9];
  ()

let value_next10_reversed () : Lemma (
    value next10_reversed == 8273062067599968591614629) =
  value_cons #10 9 [2; 6; 4; 1; 6; 1; 9; 5; 8; 6; 9; 9; 9; 5; 7; 6; 0; 2; 6; 0; 3; 7; 2; 8];
  value_cons #10 2 [6; 4; 1; 6; 1; 9; 5; 8; 6; 9; 9; 9; 5; 7; 6; 0; 2; 6; 0; 3; 7; 2; 8];
  value_cons #10 6 [4; 1; 6; 1; 9; 5; 8; 6; 9; 9; 9; 5; 7; 6; 0; 2; 6; 0; 3; 7; 2; 8];
  value_cons #10 4 [1; 6; 1; 9; 5; 8; 6; 9; 9; 9; 5; 7; 6; 0; 2; 6; 0; 3; 7; 2; 8];
  value_cons #10 1 [6; 1; 9; 5; 8; 6; 9; 9; 9; 5; 7; 6; 0; 2; 6; 0; 3; 7; 2; 8];
  value_cons #10 6 [1; 9; 5; 8; 6; 9; 9; 9; 5; 7; 6; 0; 2; 6; 0; 3; 7; 2; 8];
  value_cons #10 1 [9; 5; 8; 6; 9; 9; 9; 5; 7; 6; 0; 2; 6; 0; 3; 7; 2; 8];
  value_cons #10 9 [5; 8; 6; 9; 9; 9; 5; 7; 6; 0; 2; 6; 0; 3; 7; 2; 8];
  value_cons #10 5 [8; 6; 9; 9; 9; 5; 7; 6; 0; 2; 6; 0; 3; 7; 2; 8];
  value_cons #10 8 [6; 9; 9; 9; 5; 7; 6; 0; 2; 6; 0; 3; 7; 2; 8];
  value_cons #10 6 [9; 9; 9; 5; 7; 6; 0; 2; 6; 0; 3; 7; 2; 8];
  value_cons #10 9 [9; 9; 5; 7; 6; 0; 2; 6; 0; 3; 7; 2; 8];
  value_cons #10 9 [9; 5; 7; 6; 0; 2; 6; 0; 3; 7; 2; 8];
  value_cons #10 9 [5; 7; 6; 0; 2; 6; 0; 3; 7; 2; 8];
  value_cons #10 5 [7; 6; 0; 2; 6; 0; 3; 7; 2; 8];
  value_cons #10 7 [6; 0; 2; 6; 0; 3; 7; 2; 8];
  value_cons #10 6 [0; 2; 6; 0; 3; 7; 2; 8];
  value_cons #10 0 [2; 6; 0; 3; 7; 2; 8];
  value_cons #10 2 [6; 0; 3; 7; 2; 8];
  value_cons #10 6 [0; 3; 7; 2; 8];
  value_cons #10 0 [3; 7; 2; 8];
  value_cons #10 3 [7; 2; 8];
  value_cons #10 7 [2; 8];
  value_cons #10 2 [8];
  value_cons #10 8 [];
  ()

let value_next10_target () : Lemma (
    value next10_target == 17537224026299926194218357) =
  value_cons #10 7 [5; 3; 8; 1; 2; 4; 9; 1; 6; 2; 9; 9; 9; 2; 6; 2; 0; 4; 2; 2; 7; 3; 5; 7; 1];
  value_cons #10 5 [3; 8; 1; 2; 4; 9; 1; 6; 2; 9; 9; 9; 2; 6; 2; 0; 4; 2; 2; 7; 3; 5; 7; 1];
  value_cons #10 3 [8; 1; 2; 4; 9; 1; 6; 2; 9; 9; 9; 2; 6; 2; 0; 4; 2; 2; 7; 3; 5; 7; 1];
  value_cons #10 8 [1; 2; 4; 9; 1; 6; 2; 9; 9; 9; 2; 6; 2; 0; 4; 2; 2; 7; 3; 5; 7; 1];
  value_cons #10 1 [2; 4; 9; 1; 6; 2; 9; 9; 9; 2; 6; 2; 0; 4; 2; 2; 7; 3; 5; 7; 1];
  value_cons #10 2 [4; 9; 1; 6; 2; 9; 9; 9; 2; 6; 2; 0; 4; 2; 2; 7; 3; 5; 7; 1];
  value_cons #10 4 [9; 1; 6; 2; 9; 9; 9; 2; 6; 2; 0; 4; 2; 2; 7; 3; 5; 7; 1];
  value_cons #10 9 [1; 6; 2; 9; 9; 9; 2; 6; 2; 0; 4; 2; 2; 7; 3; 5; 7; 1];
  value_cons #10 1 [6; 2; 9; 9; 9; 2; 6; 2; 0; 4; 2; 2; 7; 3; 5; 7; 1];
  value_cons #10 6 [2; 9; 9; 9; 2; 6; 2; 0; 4; 2; 2; 7; 3; 5; 7; 1];
  value_cons #10 2 [9; 9; 9; 2; 6; 2; 0; 4; 2; 2; 7; 3; 5; 7; 1];
  value_cons #10 9 [9; 9; 2; 6; 2; 0; 4; 2; 2; 7; 3; 5; 7; 1];
  value_cons #10 9 [9; 2; 6; 2; 0; 4; 2; 2; 7; 3; 5; 7; 1];
  value_cons #10 9 [2; 6; 2; 0; 4; 2; 2; 7; 3; 5; 7; 1];
  value_cons #10 2 [6; 2; 0; 4; 2; 2; 7; 3; 5; 7; 1];
  value_cons #10 6 [2; 0; 4; 2; 2; 7; 3; 5; 7; 1];
  value_cons #10 2 [0; 4; 2; 2; 7; 3; 5; 7; 1];
  value_cons #10 0 [4; 2; 2; 7; 3; 5; 7; 1];
  value_cons #10 4 [2; 2; 7; 3; 5; 7; 1];
  value_cons #10 2 [2; 7; 3; 5; 7; 1];
  value_cons #10 2 [7; 3; 5; 7; 1];
  value_cons #10 7 [3; 5; 7; 1];
  value_cons #10 3 [5; 7; 1];
  value_cons #10 5 [7; 1];
  value_cons #10 7 [1];
  value_cons #10 1 [];
  ()

let canonical_next10_reversed () : Lemma (canonical #10 next10_reversed) =
  assert (canonical #10 [8]);
  canonical_cons #10 2 [8];
  canonical_cons #10 7 [2; 8];
  canonical_cons #10 3 [7; 2; 8];
  canonical_cons #10 0 [3; 7; 2; 8];
  canonical_cons #10 6 [0; 3; 7; 2; 8];
  canonical_cons #10 2 [6; 0; 3; 7; 2; 8];
  canonical_cons #10 0 [2; 6; 0; 3; 7; 2; 8];
  canonical_cons #10 6 [0; 2; 6; 0; 3; 7; 2; 8];
  canonical_cons #10 7 [6; 0; 2; 6; 0; 3; 7; 2; 8];
  canonical_cons #10 5 [7; 6; 0; 2; 6; 0; 3; 7; 2; 8];
  canonical_cons #10 9 [5; 7; 6; 0; 2; 6; 0; 3; 7; 2; 8];
  canonical_cons #10 9 [9; 5; 7; 6; 0; 2; 6; 0; 3; 7; 2; 8];
  canonical_cons #10 9 [9; 9; 5; 7; 6; 0; 2; 6; 0; 3; 7; 2; 8];
  canonical_cons #10 6 [9; 9; 9; 5; 7; 6; 0; 2; 6; 0; 3; 7; 2; 8];
  canonical_cons #10 8 [6; 9; 9; 9; 5; 7; 6; 0; 2; 6; 0; 3; 7; 2; 8];
  canonical_cons #10 5 [8; 6; 9; 9; 9; 5; 7; 6; 0; 2; 6; 0; 3; 7; 2; 8];
  canonical_cons #10 9 [5; 8; 6; 9; 9; 9; 5; 7; 6; 0; 2; 6; 0; 3; 7; 2; 8];
  canonical_cons #10 1 [9; 5; 8; 6; 9; 9; 9; 5; 7; 6; 0; 2; 6; 0; 3; 7; 2; 8];
  canonical_cons #10 6 [1; 9; 5; 8; 6; 9; 9; 9; 5; 7; 6; 0; 2; 6; 0; 3; 7; 2; 8];
  canonical_cons #10 1 [6; 1; 9; 5; 8; 6; 9; 9; 9; 5; 7; 6; 0; 2; 6; 0; 3; 7; 2; 8];
  canonical_cons #10 4 [1; 6; 1; 9; 5; 8; 6; 9; 9; 9; 5; 7; 6; 0; 2; 6; 0; 3; 7; 2; 8];
  canonical_cons #10 6 [4; 1; 6; 1; 9; 5; 8; 6; 9; 9; 9; 5; 7; 6; 0; 2; 6; 0; 3; 7; 2; 8];
  canonical_cons #10 2 [6; 4; 1; 6; 1; 9; 5; 8; 6; 9; 9; 9; 5; 7; 6; 0; 2; 6; 0; 3; 7; 2; 8];
  canonical_cons #10 9 [2; 6; 4; 1; 6; 1; 9; 5; 8; 6; 9; 9; 9; 5; 7; 6; 0; 2; 6; 0; 3; 7; 2; 8];
  ()

let canonical_next10_target () : Lemma (canonical #10 next10_target) =
  assert (canonical #10 [1]);
  canonical_cons #10 7 [1];
  canonical_cons #10 5 [7; 1];
  canonical_cons #10 3 [5; 7; 1];
  canonical_cons #10 7 [3; 5; 7; 1];
  canonical_cons #10 2 [7; 3; 5; 7; 1];
  canonical_cons #10 2 [2; 7; 3; 5; 7; 1];
  canonical_cons #10 4 [2; 2; 7; 3; 5; 7; 1];
  canonical_cons #10 0 [4; 2; 2; 7; 3; 5; 7; 1];
  canonical_cons #10 2 [0; 4; 2; 2; 7; 3; 5; 7; 1];
  canonical_cons #10 6 [2; 0; 4; 2; 2; 7; 3; 5; 7; 1];
  canonical_cons #10 2 [6; 2; 0; 4; 2; 2; 7; 3; 5; 7; 1];
  canonical_cons #10 9 [2; 6; 2; 0; 4; 2; 2; 7; 3; 5; 7; 1];
  canonical_cons #10 9 [9; 2; 6; 2; 0; 4; 2; 2; 7; 3; 5; 7; 1];
  canonical_cons #10 9 [9; 9; 2; 6; 2; 0; 4; 2; 2; 7; 3; 5; 7; 1];
  canonical_cons #10 2 [9; 9; 9; 2; 6; 2; 0; 4; 2; 2; 7; 3; 5; 7; 1];
  canonical_cons #10 6 [2; 9; 9; 9; 2; 6; 2; 0; 4; 2; 2; 7; 3; 5; 7; 1];
  canonical_cons #10 1 [6; 2; 9; 9; 9; 2; 6; 2; 0; 4; 2; 2; 7; 3; 5; 7; 1];
  canonical_cons #10 9 [1; 6; 2; 9; 9; 9; 2; 6; 2; 0; 4; 2; 2; 7; 3; 5; 7; 1];
  canonical_cons #10 4 [9; 1; 6; 2; 9; 9; 9; 2; 6; 2; 0; 4; 2; 2; 7; 3; 5; 7; 1];
  canonical_cons #10 2 [4; 9; 1; 6; 2; 9; 9; 9; 2; 6; 2; 0; 4; 2; 2; 7; 3; 5; 7; 1];
  canonical_cons #10 1 [2; 4; 9; 1; 6; 2; 9; 9; 9; 2; 6; 2; 0; 4; 2; 2; 7; 3; 5; 7; 1];
  canonical_cons #10 8 [1; 2; 4; 9; 1; 6; 2; 9; 9; 9; 2; 6; 2; 0; 4; 2; 2; 7; 3; 5; 7; 1];
  canonical_cons #10 3 [8; 1; 2; 4; 9; 1; 6; 2; 9; 9; 9; 2; 6; 2; 0; 4; 2; 2; 7; 3; 5; 7; 1];
  canonical_cons #10 5 [3; 8; 1; 2; 4; 9; 1; 6; 2; 9; 9; 9; 2; 6; 2; 0; 4; 2; 2; 7; 3; 5; 7; 1];
  canonical_cons #10 7 [5; 3; 8; 1; 2; 4; 9; 1; 6; 2; 9; 9; 9; 2; 6; 2; 0; 4; 2; 2; 7; 3; 5; 7; 1];
  ()

let reverse_digits_next10_source () : Lemma (
    reverse_digits #10 next10_source == next10_reversed) =
  ReverseAddNext.canonical_next9_target ();
  reverse_list_next10_source ();
  value_next10_reversed ();
  canonical_next10_reversed ();
  reverse_digits_canonical #10 next10_source;
  normalize_value #10 (rev next10_source);
  assert (value (reverse_digits #10 next10_source) ==
    8273062067599968591614629);
  digits_of_nat_of_canonical #10 (reverse_digits #10 next10_source);
  digits_of_nat_of_canonical #10 next10_reversed;
  assert (reverse_digits #10 next10_source == next10_reversed);
  ()

let reverse_add_9264161958699957602603728_to_17537224026299926194218357 () : Lemma (
    reverse_add #10 next10_source == next10_target) =
  ReverseAddNext.canonical_next9_target ();
  reverse_add_value #10 next10_source;
  ReverseAddNext.value_next9_target ();
  reverse_digits_next10_source ();
  value_next10_reversed ();
  value_next10_target ();
  assert (value (reverse_add #10 next10_source) ==
    17537224026299926194218357);
  reverse_add_canonical #10 next10_source;
  digits_of_nat_of_canonical #10 (reverse_add #10 next10_source);
  canonical_next10_target ();
  digits_of_nat_of_canonical #10 next10_target;
  assert (reverse_add #10 next10_source == next10_target);
  ()

let trace_digits_profile_9264161958699957602603728 () : Lemma (
    trace_digits next10_source == next10_target) =
  reverse_add_9264161958699957602603728_to_17537224026299926194218357 ();
  trace_digits_equals_reverse_add next10_source;
  assert (trace_digits next10_source == next10_target);
  ()

let trace_carries_next10_source () : Lemma (trace_carries next10_source ==
    [0; 1; 0; 1; 0; 0; 1; 0; 0; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 0; 1; 0; 0; 1; 0; 1]) =
  reverse_list_next10_source ();
  assert (trace_carries next10_source ==
    (add_trace #10 next10_source next10_reversed 0).carries);
  add_trace_carries_step #10 8 9
    [2; 7; 3; 0; 6; 2; 0; 6; 7; 5; 9; 9; 9; 6; 8; 5; 9; 1; 6; 1; 4; 6; 2; 9]
    [2; 6; 4; 1; 6; 1; 9; 5; 8; 6; 9; 9; 9; 5; 7; 6; 0; 2; 6; 0; 3; 7; 2; 8] 0;
  add_trace_carries_step #10 2 2
    [7; 3; 0; 6; 2; 0; 6; 7; 5; 9; 9; 9; 6; 8; 5; 9; 1; 6; 1; 4; 6; 2; 9]
    [6; 4; 1; 6; 1; 9; 5; 8; 6; 9; 9; 9; 5; 7; 6; 0; 2; 6; 0; 3; 7; 2; 8] 1;
  add_trace_carries_step #10 7 6
    [3; 0; 6; 2; 0; 6; 7; 5; 9; 9; 9; 6; 8; 5; 9; 1; 6; 1; 4; 6; 2; 9]
    [4; 1; 6; 1; 9; 5; 8; 6; 9; 9; 9; 5; 7; 6; 0; 2; 6; 0; 3; 7; 2; 8] 0;
  add_trace_carries_step #10 3 4
    [0; 6; 2; 0; 6; 7; 5; 9; 9; 9; 6; 8; 5; 9; 1; 6; 1; 4; 6; 2; 9]
    [1; 6; 1; 9; 5; 8; 6; 9; 9; 9; 5; 7; 6; 0; 2; 6; 0; 3; 7; 2; 8] 1;
  add_trace_carries_step #10 0 1
    [6; 2; 0; 6; 7; 5; 9; 9; 9; 6; 8; 5; 9; 1; 6; 1; 4; 6; 2; 9]
    [6; 1; 9; 5; 8; 6; 9; 9; 9; 5; 7; 6; 0; 2; 6; 0; 3; 7; 2; 8] 0;
  add_trace_carries_step #10 6 6
    [2; 0; 6; 7; 5; 9; 9; 9; 6; 8; 5; 9; 1; 6; 1; 4; 6; 2; 9]
    [1; 9; 5; 8; 6; 9; 9; 9; 5; 7; 6; 0; 2; 6; 0; 3; 7; 2; 8] 0;
  add_trace_carries_step #10 2 1
    [0; 6; 7; 5; 9; 9; 9; 6; 8; 5; 9; 1; 6; 1; 4; 6; 2; 9]
    [9; 5; 8; 6; 9; 9; 9; 5; 7; 6; 0; 2; 6; 0; 3; 7; 2; 8] 1;
  add_trace_carries_step #10 0 9
    [6; 7; 5; 9; 9; 9; 6; 8; 5; 9; 1; 6; 1; 4; 6; 2; 9]
    [5; 8; 6; 9; 9; 9; 5; 7; 6; 0; 2; 6; 0; 3; 7; 2; 8] 0;
  add_trace_carries_step #10 6 5
    [7; 5; 9; 9; 9; 6; 8; 5; 9; 1; 6; 1; 4; 6; 2; 9]
    [8; 6; 9; 9; 9; 5; 7; 6; 0; 2; 6; 0; 3; 7; 2; 8] 0;
  add_trace_carries_step #10 7 8
    [5; 9; 9; 9; 6; 8; 5; 9; 1; 6; 1; 4; 6; 2; 9]
    [6; 9; 9; 9; 5; 7; 6; 0; 2; 6; 0; 3; 7; 2; 8] 1;
  add_trace_carries_step #10 5 6
    [9; 9; 9; 6; 8; 5; 9; 1; 6; 1; 4; 6; 2; 9]
    [9; 9; 9; 5; 7; 6; 0; 2; 6; 0; 3; 7; 2; 8] 1;
  add_trace_carries_step #10 9 9
    [9; 9; 6; 8; 5; 9; 1; 6; 1; 4; 6; 2; 9]
    [9; 9; 5; 7; 6; 0; 2; 6; 0; 3; 7; 2; 8] 1;
  add_trace_carries_step #10 9 9
    [9; 6; 8; 5; 9; 1; 6; 1; 4; 6; 2; 9]
    [9; 5; 7; 6; 0; 2; 6; 0; 3; 7; 2; 8] 1;
  add_trace_carries_step #10 9 9
    [6; 8; 5; 9; 1; 6; 1; 4; 6; 2; 9]
    [5; 7; 6; 0; 2; 6; 0; 3; 7; 2; 8] 1;
  add_trace_carries_step #10 6 5
    [8; 5; 9; 1; 6; 1; 4; 6; 2; 9]
    [7; 6; 0; 2; 6; 0; 3; 7; 2; 8] 1;
  add_trace_carries_step #10 8 7
    [5; 9; 1; 6; 1; 4; 6; 2; 9]
    [6; 0; 2; 6; 0; 3; 7; 2; 8] 1;
  add_trace_carries_step #10 5 6
    [9; 1; 6; 1; 4; 6; 2; 9]
    [0; 2; 6; 0; 3; 7; 2; 8] 1;
  add_trace_carries_step #10 9 0
    [1; 6; 1; 4; 6; 2; 9]
    [2; 6; 0; 3; 7; 2; 8] 1;
  add_trace_carries_step #10 1 2
    [6; 1; 4; 6; 2; 9]
    [6; 0; 3; 7; 2; 8] 1;
  add_trace_carries_step #10 6 6
    [1; 4; 6; 2; 9]
    [0; 3; 7; 2; 8] 0;
  add_trace_carries_step #10 1 0
    [4; 6; 2; 9]
    [3; 7; 2; 8] 1;
  add_trace_carries_step #10 4 3
    [6; 2; 9]
    [7; 2; 8] 0;
  add_trace_carries_step #10 6 7
    [2; 9]
    [2; 8] 0;
  add_trace_carries_step #10 2 2
    [9]
    [8] 1;
  add_trace_carries_step #10 9 8
    []
    [] 0;
  assert ((add_trace #10 [] [] 1).carries == [1]);
  assert ((add_trace #10 next10_source next10_reversed 0).carries ==
    [0; 1; 0; 1; 0; 0; 1; 0; 0; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 0; 1; 0; 0; 1; 0; 1]);
  ()

let trace_profile_shape_9264161958699957602603728 () : Lemma (
    length (trace_digits next10_source) == length next10_source + 1) =
  trace_digits_profile_9264161958699957602603728 ();
  length_of_eq #(digit 10) (trace_digits next10_source) next10_target;
  assert (length next10_target == length next10_source + 1);
  ()

let trace_profile_final_carry_9264161958699957602603728 () : Lemma (
    nth (trace_carries next10_source) (length next10_source) == Some 1) =
  trace_profile_shape_9264161958699957602603728 ();
  ReverseAddContinuation.final_carry_from_overflow_length next10_source;
  ()

let trace_profile_sums_9264161958699957602603728 () : Lemma (
    trace_sum_at next10_source 0 == 17 /\
    trace_sum_at next10_source 1 == 4 /\
    trace_sum_at next10_source 24 == 17) =
  reverse_list_next10_source ();
  ()

let trace_profile_carry_facts_9264161958699957602603728 () : Lemma (
    trace_carry_at next10_source 1 == 1 /\
    trace_carry_at next10_source 24 == 0 /\
    trace_carry_at next10_source 2 == 0 /\
    trace_carry_at next10_source 25 == 1) =
  trace_carries_next10_source ();
  ()

let overflow_precondition_9264161958699957602603728 () : Lemma (
    canonical #10 next10_source /\
    next10_source <> [] /\
    length (trace_digits next10_source) == length next10_source + 1 /\
    nth (trace_carries next10_source) (length next10_source) == Some 1 /\
    1 <= trace_sum_at next10_source 0 /\
    trace_sum_at next10_source 0 <= 18 /\
    trace_sum_at next10_source 0 <> 10 /\
    exists (i:nat). 0 < i /\ i < length next10_source /\
      trace_sum_at next10_source i +
          trace_sum_at next10_source (length next10_source - i) +
          trace_carry_at next10_source i +
          trace_carry_at next10_source (length next10_source - i) >=
        10 + 10 *
          (trace_carry_at next10_source (i + 1) +
           trace_carry_at next10_source (length next10_source - i + 1))) =
  ReverseAddNext.canonical_next9_target ();
  assert (next10_source <> []);
  trace_profile_shape_9264161958699957602603728 ();
  trace_profile_final_carry_9264161958699957602603728 ();
  trace_profile_sums_9264161958699957602603728 ();
  trace_profile_carry_facts_9264161958699957602603728 ();
  assert (length (trace_digits next10_source) == length next10_source + 1);
  assert (nth (trace_carries next10_source)
    (length next10_source) == Some 1);
  assert (trace_sum_at next10_source 0 == 17);
  assert (trace_sum_at next10_source 1 == 4);
  assert (trace_sum_at next10_source 24 == 17);
  assert (trace_carry_at next10_source 1 == 1);
  assert (trace_carry_at next10_source 24 == 0);
  assert (trace_carry_at next10_source 2 == 0);
  assert (trace_carry_at next10_source 25 == 1);
  assert (1 <= trace_sum_at next10_source 0 /\
    trace_sum_at next10_source 0 <= 18);
  assert (trace_sum_at next10_source 0 <> 10);
  let n : nat = length next10_source in
  assert (0 < 1 /\ 1 < n);
  assert (trace_sum_at next10_source 1 +
      trace_sum_at next10_source (n - 1) +
      trace_carry_at next10_source 1 +
      trace_carry_at next10_source (n - 1) >=
    10 + 10 *
      (trace_carry_at next10_source 2 +
       trace_carry_at next10_source (n - 1 + 1)));
  exists_intro
    (fun (i:nat) -> 0 < i /\ i < n /\
      trace_sum_at next10_source i +
          trace_sum_at next10_source (n - i) +
          trace_carry_at next10_source i +
          trace_carry_at next10_source (n - i) >=
        10 + 10 *
          (trace_carry_at next10_source (i + 1) +
           trace_carry_at next10_source (n - i + 1)))
    1;
  ()

let local_profile_witness_17537224026299926194218357 () : Lemma (
    trace_local_profile_complement_witness next10_target) =
  overflow_precondition_9264161958699957602603728 ();
  reverse_add_9264161958699957602603728_to_17537224026299926194218357 ();
  overflow_internal_cell_implies_next_witness next10_source;
  ()

let next11_source : numeral 10 = next10_target

let next11_reversed : numeral 10 =
  [1; 7; 5; 3; 7; 2; 2; 4; 0; 2; 6; 2; 9; 9; 9; 2; 6; 1; 9; 4; 2; 1; 8; 3; 5; 7]

let next11_target : numeral 10 =
  [8; 2; 9; 1; 9; 4; 6; 3; 2; 8; 8; 1; 9; 9; 2; 9; 8; 1; 3; 7; 4; 8; 1; 9; 2; 9]

let reverse_list_next11_source () : Lemma (rev next11_source == next11_reversed) =
  assert (rev [1] == [1]);
  rev_cons 7 [1];
  rev_cons 5 [7; 1];
  rev_cons 3 [5; 7; 1];
  rev_cons 7 [3; 5; 7; 1];
  rev_cons 2 [7; 3; 5; 7; 1];
  rev_cons 2 [2; 7; 3; 5; 7; 1];
  rev_cons 4 [2; 2; 7; 3; 5; 7; 1];
  rev_cons 0 [4; 2; 2; 7; 3; 5; 7; 1];
  rev_cons 2 [0; 4; 2; 2; 7; 3; 5; 7; 1];
  rev_cons 6 [2; 0; 4; 2; 2; 7; 3; 5; 7; 1];
  rev_cons 2 [6; 2; 0; 4; 2; 2; 7; 3; 5; 7; 1];
  rev_cons 9 [2; 6; 2; 0; 4; 2; 2; 7; 3; 5; 7; 1];
  rev_cons 9 [9; 2; 6; 2; 0; 4; 2; 2; 7; 3; 5; 7; 1];
  rev_cons 9 [9; 9; 2; 6; 2; 0; 4; 2; 2; 7; 3; 5; 7; 1];
  rev_cons 2 [9; 9; 9; 2; 6; 2; 0; 4; 2; 2; 7; 3; 5; 7; 1];
  rev_cons 6 [2; 9; 9; 9; 2; 6; 2; 0; 4; 2; 2; 7; 3; 5; 7; 1];
  rev_cons 1 [6; 2; 9; 9; 9; 2; 6; 2; 0; 4; 2; 2; 7; 3; 5; 7; 1];
  rev_cons 9 [1; 6; 2; 9; 9; 9; 2; 6; 2; 0; 4; 2; 2; 7; 3; 5; 7; 1];
  rev_cons 4 [9; 1; 6; 2; 9; 9; 9; 2; 6; 2; 0; 4; 2; 2; 7; 3; 5; 7; 1];
  rev_cons 2 [4; 9; 1; 6; 2; 9; 9; 9; 2; 6; 2; 0; 4; 2; 2; 7; 3; 5; 7; 1];
  rev_cons 1 [2; 4; 9; 1; 6; 2; 9; 9; 9; 2; 6; 2; 0; 4; 2; 2; 7; 3; 5; 7; 1];
  rev_cons 8 [1; 2; 4; 9; 1; 6; 2; 9; 9; 9; 2; 6; 2; 0; 4; 2; 2; 7; 3; 5; 7; 1];
  rev_cons 3 [8; 1; 2; 4; 9; 1; 6; 2; 9; 9; 9; 2; 6; 2; 0; 4; 2; 2; 7; 3; 5; 7; 1];
  rev_cons 5 [3; 8; 1; 2; 4; 9; 1; 6; 2; 9; 9; 9; 2; 6; 2; 0; 4; 2; 2; 7; 3; 5; 7; 1];
  rev_cons 7 [5; 3; 8; 1; 2; 4; 9; 1; 6; 2; 9; 9; 9; 2; 6; 2; 0; 4; 2; 2; 7; 3; 5; 7; 1];
  ()

let value_next11_reversed () : Lemma (
    value next11_reversed == 75381249162999262042273571) =
  value_cons #10 1 [7; 5; 3; 7; 2; 2; 4; 0; 2; 6; 2; 9; 9; 9; 2; 6; 1; 9; 4; 2; 1; 8; 3; 5; 7];
  value_cons #10 7 [5; 3; 7; 2; 2; 4; 0; 2; 6; 2; 9; 9; 9; 2; 6; 1; 9; 4; 2; 1; 8; 3; 5; 7];
  value_cons #10 5 [3; 7; 2; 2; 4; 0; 2; 6; 2; 9; 9; 9; 2; 6; 1; 9; 4; 2; 1; 8; 3; 5; 7];
  value_cons #10 3 [7; 2; 2; 4; 0; 2; 6; 2; 9; 9; 9; 2; 6; 1; 9; 4; 2; 1; 8; 3; 5; 7];
  value_cons #10 7 [2; 2; 4; 0; 2; 6; 2; 9; 9; 9; 2; 6; 1; 9; 4; 2; 1; 8; 3; 5; 7];
  value_cons #10 2 [2; 4; 0; 2; 6; 2; 9; 9; 9; 2; 6; 1; 9; 4; 2; 1; 8; 3; 5; 7];
  value_cons #10 2 [4; 0; 2; 6; 2; 9; 9; 9; 2; 6; 1; 9; 4; 2; 1; 8; 3; 5; 7];
  value_cons #10 4 [0; 2; 6; 2; 9; 9; 9; 2; 6; 1; 9; 4; 2; 1; 8; 3; 5; 7];
  value_cons #10 0 [2; 6; 2; 9; 9; 9; 2; 6; 1; 9; 4; 2; 1; 8; 3; 5; 7];
  value_cons #10 2 [6; 2; 9; 9; 9; 2; 6; 1; 9; 4; 2; 1; 8; 3; 5; 7];
  value_cons #10 6 [2; 9; 9; 9; 2; 6; 1; 9; 4; 2; 1; 8; 3; 5; 7];
  value_cons #10 2 [9; 9; 9; 2; 6; 1; 9; 4; 2; 1; 8; 3; 5; 7];
  value_cons #10 9 [9; 9; 2; 6; 1; 9; 4; 2; 1; 8; 3; 5; 7];
  value_cons #10 9 [9; 2; 6; 1; 9; 4; 2; 1; 8; 3; 5; 7];
  value_cons #10 9 [2; 6; 1; 9; 4; 2; 1; 8; 3; 5; 7];
  value_cons #10 2 [6; 1; 9; 4; 2; 1; 8; 3; 5; 7];
  value_cons #10 6 [1; 9; 4; 2; 1; 8; 3; 5; 7];
  value_cons #10 1 [9; 4; 2; 1; 8; 3; 5; 7];
  value_cons #10 9 [4; 2; 1; 8; 3; 5; 7];
  value_cons #10 4 [2; 1; 8; 3; 5; 7];
  value_cons #10 2 [1; 8; 3; 5; 7];
  value_cons #10 1 [8; 3; 5; 7];
  value_cons #10 8 [3; 5; 7];
  value_cons #10 3 [5; 7];
  value_cons #10 5 [7];
  value_cons #10 7 [];
  ()

let value_next11_target () : Lemma (
    value next11_target == 92918473189299188236491928) =
  value_cons #10 8 [2; 9; 1; 9; 4; 6; 3; 2; 8; 8; 1; 9; 9; 2; 9; 8; 1; 3; 7; 4; 8; 1; 9; 2; 9];
  value_cons #10 2 [9; 1; 9; 4; 6; 3; 2; 8; 8; 1; 9; 9; 2; 9; 8; 1; 3; 7; 4; 8; 1; 9; 2; 9];
  value_cons #10 9 [1; 9; 4; 6; 3; 2; 8; 8; 1; 9; 9; 2; 9; 8; 1; 3; 7; 4; 8; 1; 9; 2; 9];
  value_cons #10 1 [9; 4; 6; 3; 2; 8; 8; 1; 9; 9; 2; 9; 8; 1; 3; 7; 4; 8; 1; 9; 2; 9];
  value_cons #10 9 [4; 6; 3; 2; 8; 8; 1; 9; 9; 2; 9; 8; 1; 3; 7; 4; 8; 1; 9; 2; 9];
  value_cons #10 4 [6; 3; 2; 8; 8; 1; 9; 9; 2; 9; 8; 1; 3; 7; 4; 8; 1; 9; 2; 9];
  value_cons #10 6 [3; 2; 8; 8; 1; 9; 9; 2; 9; 8; 1; 3; 7; 4; 8; 1; 9; 2; 9];
  value_cons #10 3 [2; 8; 8; 1; 9; 9; 2; 9; 8; 1; 3; 7; 4; 8; 1; 9; 2; 9];
  value_cons #10 2 [8; 8; 1; 9; 9; 2; 9; 8; 1; 3; 7; 4; 8; 1; 9; 2; 9];
  value_cons #10 8 [8; 1; 9; 9; 2; 9; 8; 1; 3; 7; 4; 8; 1; 9; 2; 9];
  value_cons #10 8 [1; 9; 9; 2; 9; 8; 1; 3; 7; 4; 8; 1; 9; 2; 9];
  value_cons #10 1 [9; 9; 2; 9; 8; 1; 3; 7; 4; 8; 1; 9; 2; 9];
  value_cons #10 9 [9; 2; 9; 8; 1; 3; 7; 4; 8; 1; 9; 2; 9];
  value_cons #10 9 [2; 9; 8; 1; 3; 7; 4; 8; 1; 9; 2; 9];
  value_cons #10 2 [9; 8; 1; 3; 7; 4; 8; 1; 9; 2; 9];
  value_cons #10 9 [8; 1; 3; 7; 4; 8; 1; 9; 2; 9];
  value_cons #10 8 [1; 3; 7; 4; 8; 1; 9; 2; 9];
  value_cons #10 1 [3; 7; 4; 8; 1; 9; 2; 9];
  value_cons #10 3 [7; 4; 8; 1; 9; 2; 9];
  value_cons #10 7 [4; 8; 1; 9; 2; 9];
  value_cons #10 4 [8; 1; 9; 2; 9];
  value_cons #10 8 [1; 9; 2; 9];
  value_cons #10 1 [9; 2; 9];
  value_cons #10 9 [2; 9];
  value_cons #10 2 [9];
  value_cons #10 9 [];
  ()

let canonical_next11_reversed () : Lemma (canonical #10 next11_reversed) =
  assert (canonical #10 [7]);
  canonical_cons #10 5 [7];
  canonical_cons #10 3 [5; 7];
  canonical_cons #10 8 [3; 5; 7];
  canonical_cons #10 1 [8; 3; 5; 7];
  canonical_cons #10 2 [1; 8; 3; 5; 7];
  canonical_cons #10 4 [2; 1; 8; 3; 5; 7];
  canonical_cons #10 9 [4; 2; 1; 8; 3; 5; 7];
  canonical_cons #10 1 [9; 4; 2; 1; 8; 3; 5; 7];
  canonical_cons #10 6 [1; 9; 4; 2; 1; 8; 3; 5; 7];
  canonical_cons #10 2 [6; 1; 9; 4; 2; 1; 8; 3; 5; 7];
  canonical_cons #10 9 [2; 6; 1; 9; 4; 2; 1; 8; 3; 5; 7];
  canonical_cons #10 9 [9; 2; 6; 1; 9; 4; 2; 1; 8; 3; 5; 7];
  canonical_cons #10 9 [9; 9; 2; 6; 1; 9; 4; 2; 1; 8; 3; 5; 7];
  canonical_cons #10 2 [9; 9; 9; 2; 6; 1; 9; 4; 2; 1; 8; 3; 5; 7];
  canonical_cons #10 6 [2; 9; 9; 9; 2; 6; 1; 9; 4; 2; 1; 8; 3; 5; 7];
  canonical_cons #10 2 [6; 2; 9; 9; 9; 2; 6; 1; 9; 4; 2; 1; 8; 3; 5; 7];
  canonical_cons #10 0 [2; 6; 2; 9; 9; 9; 2; 6; 1; 9; 4; 2; 1; 8; 3; 5; 7];
  canonical_cons #10 4 [0; 2; 6; 2; 9; 9; 9; 2; 6; 1; 9; 4; 2; 1; 8; 3; 5; 7];
  canonical_cons #10 2 [4; 0; 2; 6; 2; 9; 9; 9; 2; 6; 1; 9; 4; 2; 1; 8; 3; 5; 7];
  canonical_cons #10 2 [2; 4; 0; 2; 6; 2; 9; 9; 9; 2; 6; 1; 9; 4; 2; 1; 8; 3; 5; 7];
  canonical_cons #10 7 [2; 2; 4; 0; 2; 6; 2; 9; 9; 9; 2; 6; 1; 9; 4; 2; 1; 8; 3; 5; 7];
  canonical_cons #10 3 [7; 2; 2; 4; 0; 2; 6; 2; 9; 9; 9; 2; 6; 1; 9; 4; 2; 1; 8; 3; 5; 7];
  canonical_cons #10 5 [3; 7; 2; 2; 4; 0; 2; 6; 2; 9; 9; 9; 2; 6; 1; 9; 4; 2; 1; 8; 3; 5; 7];
  canonical_cons #10 7 [5; 3; 7; 2; 2; 4; 0; 2; 6; 2; 9; 9; 9; 2; 6; 1; 9; 4; 2; 1; 8; 3; 5; 7];
  canonical_cons #10 1 [7; 5; 3; 7; 2; 2; 4; 0; 2; 6; 2; 9; 9; 9; 2; 6; 1; 9; 4; 2; 1; 8; 3; 5; 7];
  ()

let canonical_next11_target () : Lemma (canonical #10 next11_target) =
  assert (canonical #10 [9]);
  canonical_cons #10 2 [9];
  canonical_cons #10 9 [2; 9];
  canonical_cons #10 1 [9; 2; 9];
  canonical_cons #10 8 [1; 9; 2; 9];
  canonical_cons #10 4 [8; 1; 9; 2; 9];
  canonical_cons #10 7 [4; 8; 1; 9; 2; 9];
  canonical_cons #10 3 [7; 4; 8; 1; 9; 2; 9];
  canonical_cons #10 1 [3; 7; 4; 8; 1; 9; 2; 9];
  canonical_cons #10 8 [1; 3; 7; 4; 8; 1; 9; 2; 9];
  canonical_cons #10 9 [8; 1; 3; 7; 4; 8; 1; 9; 2; 9];
  canonical_cons #10 2 [9; 8; 1; 3; 7; 4; 8; 1; 9; 2; 9];
  canonical_cons #10 9 [2; 9; 8; 1; 3; 7; 4; 8; 1; 9; 2; 9];
  canonical_cons #10 9 [9; 2; 9; 8; 1; 3; 7; 4; 8; 1; 9; 2; 9];
  canonical_cons #10 1 [9; 9; 2; 9; 8; 1; 3; 7; 4; 8; 1; 9; 2; 9];
  canonical_cons #10 8 [1; 9; 9; 2; 9; 8; 1; 3; 7; 4; 8; 1; 9; 2; 9];
  canonical_cons #10 8 [8; 1; 9; 9; 2; 9; 8; 1; 3; 7; 4; 8; 1; 9; 2; 9];
  canonical_cons #10 2 [8; 8; 1; 9; 9; 2; 9; 8; 1; 3; 7; 4; 8; 1; 9; 2; 9];
  canonical_cons #10 3 [2; 8; 8; 1; 9; 9; 2; 9; 8; 1; 3; 7; 4; 8; 1; 9; 2; 9];
  canonical_cons #10 6 [3; 2; 8; 8; 1; 9; 9; 2; 9; 8; 1; 3; 7; 4; 8; 1; 9; 2; 9];
  canonical_cons #10 4 [6; 3; 2; 8; 8; 1; 9; 9; 2; 9; 8; 1; 3; 7; 4; 8; 1; 9; 2; 9];
  canonical_cons #10 9 [4; 6; 3; 2; 8; 8; 1; 9; 9; 2; 9; 8; 1; 3; 7; 4; 8; 1; 9; 2; 9];
  canonical_cons #10 1 [9; 4; 6; 3; 2; 8; 8; 1; 9; 9; 2; 9; 8; 1; 3; 7; 4; 8; 1; 9; 2; 9];
  canonical_cons #10 9 [1; 9; 4; 6; 3; 2; 8; 8; 1; 9; 9; 2; 9; 8; 1; 3; 7; 4; 8; 1; 9; 2; 9];
  canonical_cons #10 2 [9; 1; 9; 4; 6; 3; 2; 8; 8; 1; 9; 9; 2; 9; 8; 1; 3; 7; 4; 8; 1; 9; 2; 9];
  canonical_cons #10 8 [2; 9; 1; 9; 4; 6; 3; 2; 8; 8; 1; 9; 9; 2; 9; 8; 1; 3; 7; 4; 8; 1; 9; 2; 9];
  ()

let reverse_digits_next11_source () : Lemma (
    reverse_digits #10 next11_source == next11_reversed) =
  ReverseAddNext.canonical_next10_target ();
  reverse_list_next11_source ();
  value_next11_reversed ();
  canonical_next11_reversed ();
  reverse_digits_canonical #10 next11_source;
  normalize_value #10 (rev next11_source);
  assert (value (reverse_digits #10 next11_source) ==
    75381249162999262042273571);
  digits_of_nat_of_canonical #10 (reverse_digits #10 next11_source);
  digits_of_nat_of_canonical #10 next11_reversed;
  assert (reverse_digits #10 next11_source == next11_reversed);
  ()

let reverse_add_17537224026299926194218357_to_92918473189299188236491928 () : Lemma (
    reverse_add #10 next11_source == next11_target) =
  ReverseAddNext.canonical_next10_target ();
  reverse_add_value #10 next11_source;
  ReverseAddNext.value_next10_target ();
  reverse_digits_next11_source ();
  value_next11_reversed ();
  value_next11_target ();
  assert (value (reverse_add #10 next11_source) ==
    92918473189299188236491928);
  reverse_add_canonical #10 next11_source;
  digits_of_nat_of_canonical #10 (reverse_add #10 next11_source);
  canonical_next11_target ();
  digits_of_nat_of_canonical #10 next11_target;
  assert (reverse_add #10 next11_source == next11_target);
  ()

let trace_digits_profile_17537224026299926194218357 () : Lemma (
    trace_digits next11_source == next11_target) =
  reverse_add_17537224026299926194218357_to_92918473189299188236491928 ();
  trace_digits_equals_reverse_add next11_source;
  assert (trace_digits next11_source == next11_target);
  ()

let trace_profile_shape_17537224026299926194218357 () : Lemma (
    length (trace_digits next11_source) == length next11_source) =
  trace_digits_profile_17537224026299926194218357 ();
  length_of_eq #(digit 10) (trace_digits next11_source) next11_target;
  assert (length next11_target == length next11_source);
  ()

let trace_profile_final_carry_17537224026299926194218357 () : Lemma (
    nth (trace_carries next11_source) (length next11_source) == Some 0) =
  trace_profile_shape_17537224026299926194218357 ();
  final_carry_from_length next11_source;
  ()

let local_profile_witness_92918473189299188236491928 () : Lemma (
    trace_local_profile_complement_witness next11_target) =
  ReverseAddNext.canonical_next10_target ();
  assert (next11_source <> []);
  trace_profile_shape_17537224026299926194218357 ();
  trace_profile_final_carry_17537224026299926194218357 ();
  assert (trace_sum_at next11_source 0 == 8);
  reverse_add_17537224026299926194218357_to_92918473189299188236491928 ();
  no_overflow_outer_sum_6_to_9_implies_next_witness next11_source;
  ()

let next12_source : numeral 10 = next11_target

let next12_reversed : numeral 10 =
  [9; 2; 9; 1; 8; 4; 7; 3; 1; 8; 9; 2; 9; 9; 1; 8; 8; 2; 3; 6; 4; 9; 1; 9; 2; 8]

let next12_target : numeral 10 =
  [7; 5; 8; 3; 7; 9; 3; 7; 3; 6; 8; 4; 8; 9; 4; 7; 7; 4; 6; 3; 9; 7; 3; 8; 5; 7; 1]

let reverse_list_next12_source () : Lemma (rev next12_source == next12_reversed) =
  assert (rev [9] == [9]);
  rev_cons 2 [9];
  rev_cons 9 [2; 9];
  rev_cons 1 [9; 2; 9];
  rev_cons 8 [1; 9; 2; 9];
  rev_cons 4 [8; 1; 9; 2; 9];
  rev_cons 7 [4; 8; 1; 9; 2; 9];
  rev_cons 3 [7; 4; 8; 1; 9; 2; 9];
  rev_cons 1 [3; 7; 4; 8; 1; 9; 2; 9];
  rev_cons 8 [1; 3; 7; 4; 8; 1; 9; 2; 9];
  rev_cons 9 [8; 1; 3; 7; 4; 8; 1; 9; 2; 9];
  rev_cons 2 [9; 8; 1; 3; 7; 4; 8; 1; 9; 2; 9];
  rev_cons 9 [2; 9; 8; 1; 3; 7; 4; 8; 1; 9; 2; 9];
  rev_cons 9 [9; 2; 9; 8; 1; 3; 7; 4; 8; 1; 9; 2; 9];
  rev_cons 1 [9; 9; 2; 9; 8; 1; 3; 7; 4; 8; 1; 9; 2; 9];
  rev_cons 8 [1; 9; 9; 2; 9; 8; 1; 3; 7; 4; 8; 1; 9; 2; 9];
  rev_cons 8 [8; 1; 9; 9; 2; 9; 8; 1; 3; 7; 4; 8; 1; 9; 2; 9];
  rev_cons 2 [8; 8; 1; 9; 9; 2; 9; 8; 1; 3; 7; 4; 8; 1; 9; 2; 9];
  rev_cons 3 [2; 8; 8; 1; 9; 9; 2; 9; 8; 1; 3; 7; 4; 8; 1; 9; 2; 9];
  rev_cons 6 [3; 2; 8; 8; 1; 9; 9; 2; 9; 8; 1; 3; 7; 4; 8; 1; 9; 2; 9];
  rev_cons 4 [6; 3; 2; 8; 8; 1; 9; 9; 2; 9; 8; 1; 3; 7; 4; 8; 1; 9; 2; 9];
  rev_cons 9 [4; 6; 3; 2; 8; 8; 1; 9; 9; 2; 9; 8; 1; 3; 7; 4; 8; 1; 9; 2; 9];
  rev_cons 1 [9; 4; 6; 3; 2; 8; 8; 1; 9; 9; 2; 9; 8; 1; 3; 7; 4; 8; 1; 9; 2; 9];
  rev_cons 9 [1; 9; 4; 6; 3; 2; 8; 8; 1; 9; 9; 2; 9; 8; 1; 3; 7; 4; 8; 1; 9; 2; 9];
  rev_cons 2 [9; 1; 9; 4; 6; 3; 2; 8; 8; 1; 9; 9; 2; 9; 8; 1; 3; 7; 4; 8; 1; 9; 2; 9];
  rev_cons 8 [2; 9; 1; 9; 4; 6; 3; 2; 8; 8; 1; 9; 9; 2; 9; 8; 1; 3; 7; 4; 8; 1; 9; 2; 9];
  ()

let value_next12_reversed () : Lemma (
    value next12_reversed == 82919463288199298137481929) =
  value_cons #10 9 [2; 9; 1; 8; 4; 7; 3; 1; 8; 9; 2; 9; 9; 1; 8; 8; 2; 3; 6; 4; 9; 1; 9; 2; 8];
  value_cons #10 2 [9; 1; 8; 4; 7; 3; 1; 8; 9; 2; 9; 9; 1; 8; 8; 2; 3; 6; 4; 9; 1; 9; 2; 8];
  value_cons #10 9 [1; 8; 4; 7; 3; 1; 8; 9; 2; 9; 9; 1; 8; 8; 2; 3; 6; 4; 9; 1; 9; 2; 8];
  value_cons #10 1 [8; 4; 7; 3; 1; 8; 9; 2; 9; 9; 1; 8; 8; 2; 3; 6; 4; 9; 1; 9; 2; 8];
  value_cons #10 8 [4; 7; 3; 1; 8; 9; 2; 9; 9; 1; 8; 8; 2; 3; 6; 4; 9; 1; 9; 2; 8];
  value_cons #10 4 [7; 3; 1; 8; 9; 2; 9; 9; 1; 8; 8; 2; 3; 6; 4; 9; 1; 9; 2; 8];
  value_cons #10 7 [3; 1; 8; 9; 2; 9; 9; 1; 8; 8; 2; 3; 6; 4; 9; 1; 9; 2; 8];
  value_cons #10 3 [1; 8; 9; 2; 9; 9; 1; 8; 8; 2; 3; 6; 4; 9; 1; 9; 2; 8];
  value_cons #10 1 [8; 9; 2; 9; 9; 1; 8; 8; 2; 3; 6; 4; 9; 1; 9; 2; 8];
  value_cons #10 8 [9; 2; 9; 9; 1; 8; 8; 2; 3; 6; 4; 9; 1; 9; 2; 8];
  value_cons #10 9 [2; 9; 9; 1; 8; 8; 2; 3; 6; 4; 9; 1; 9; 2; 8];
  value_cons #10 2 [9; 9; 1; 8; 8; 2; 3; 6; 4; 9; 1; 9; 2; 8];
  value_cons #10 9 [9; 1; 8; 8; 2; 3; 6; 4; 9; 1; 9; 2; 8];
  value_cons #10 9 [1; 8; 8; 2; 3; 6; 4; 9; 1; 9; 2; 8];
  value_cons #10 1 [8; 8; 2; 3; 6; 4; 9; 1; 9; 2; 8];
  value_cons #10 8 [8; 2; 3; 6; 4; 9; 1; 9; 2; 8];
  value_cons #10 8 [2; 3; 6; 4; 9; 1; 9; 2; 8];
  value_cons #10 2 [3; 6; 4; 9; 1; 9; 2; 8];
  value_cons #10 3 [6; 4; 9; 1; 9; 2; 8];
  value_cons #10 6 [4; 9; 1; 9; 2; 8];
  value_cons #10 4 [9; 1; 9; 2; 8];
  value_cons #10 9 [1; 9; 2; 8];
  value_cons #10 1 [9; 2; 8];
  value_cons #10 9 [2; 8];
  value_cons #10 2 [8];
  value_cons #10 8 [];
  ()

let value_next12_target () : Lemma (
    value next12_target == 175837936477498486373973857) =
  value_cons #10 7 [5; 8; 3; 7; 9; 3; 7; 3; 6; 8; 4; 8; 9; 4; 7; 7; 4; 6; 3; 9; 7; 3; 8; 5; 7; 1];
  value_cons #10 5 [8; 3; 7; 9; 3; 7; 3; 6; 8; 4; 8; 9; 4; 7; 7; 4; 6; 3; 9; 7; 3; 8; 5; 7; 1];
  value_cons #10 8 [3; 7; 9; 3; 7; 3; 6; 8; 4; 8; 9; 4; 7; 7; 4; 6; 3; 9; 7; 3; 8; 5; 7; 1];
  value_cons #10 3 [7; 9; 3; 7; 3; 6; 8; 4; 8; 9; 4; 7; 7; 4; 6; 3; 9; 7; 3; 8; 5; 7; 1];
  value_cons #10 7 [9; 3; 7; 3; 6; 8; 4; 8; 9; 4; 7; 7; 4; 6; 3; 9; 7; 3; 8; 5; 7; 1];
  value_cons #10 9 [3; 7; 3; 6; 8; 4; 8; 9; 4; 7; 7; 4; 6; 3; 9; 7; 3; 8; 5; 7; 1];
  value_cons #10 3 [7; 3; 6; 8; 4; 8; 9; 4; 7; 7; 4; 6; 3; 9; 7; 3; 8; 5; 7; 1];
  value_cons #10 7 [3; 6; 8; 4; 8; 9; 4; 7; 7; 4; 6; 3; 9; 7; 3; 8; 5; 7; 1];
  value_cons #10 3 [6; 8; 4; 8; 9; 4; 7; 7; 4; 6; 3; 9; 7; 3; 8; 5; 7; 1];
  value_cons #10 6 [8; 4; 8; 9; 4; 7; 7; 4; 6; 3; 9; 7; 3; 8; 5; 7; 1];
  value_cons #10 8 [4; 8; 9; 4; 7; 7; 4; 6; 3; 9; 7; 3; 8; 5; 7; 1];
  value_cons #10 4 [8; 9; 4; 7; 7; 4; 6; 3; 9; 7; 3; 8; 5; 7; 1];
  value_cons #10 8 [9; 4; 7; 7; 4; 6; 3; 9; 7; 3; 8; 5; 7; 1];
  value_cons #10 9 [4; 7; 7; 4; 6; 3; 9; 7; 3; 8; 5; 7; 1];
  value_cons #10 4 [7; 7; 4; 6; 3; 9; 7; 3; 8; 5; 7; 1];
  value_cons #10 7 [7; 4; 6; 3; 9; 7; 3; 8; 5; 7; 1];
  value_cons #10 7 [4; 6; 3; 9; 7; 3; 8; 5; 7; 1];
  value_cons #10 4 [6; 3; 9; 7; 3; 8; 5; 7; 1];
  value_cons #10 6 [3; 9; 7; 3; 8; 5; 7; 1];
  value_cons #10 3 [9; 7; 3; 8; 5; 7; 1];
  value_cons #10 9 [7; 3; 8; 5; 7; 1];
  value_cons #10 7 [3; 8; 5; 7; 1];
  value_cons #10 3 [8; 5; 7; 1];
  value_cons #10 8 [5; 7; 1];
  value_cons #10 5 [7; 1];
  value_cons #10 7 [1];
  value_cons #10 1 [];
  ()

let canonical_next12_reversed () : Lemma (canonical #10 next12_reversed) =
  assert (canonical #10 [8]);
  canonical_cons #10 2 [8];
  canonical_cons #10 9 [2; 8];
  canonical_cons #10 1 [9; 2; 8];
  canonical_cons #10 9 [1; 9; 2; 8];
  canonical_cons #10 4 [9; 1; 9; 2; 8];
  canonical_cons #10 6 [4; 9; 1; 9; 2; 8];
  canonical_cons #10 3 [6; 4; 9; 1; 9; 2; 8];
  canonical_cons #10 2 [3; 6; 4; 9; 1; 9; 2; 8];
  canonical_cons #10 8 [2; 3; 6; 4; 9; 1; 9; 2; 8];
  canonical_cons #10 8 [8; 2; 3; 6; 4; 9; 1; 9; 2; 8];
  canonical_cons #10 1 [8; 8; 2; 3; 6; 4; 9; 1; 9; 2; 8];
  canonical_cons #10 9 [1; 8; 8; 2; 3; 6; 4; 9; 1; 9; 2; 8];
  canonical_cons #10 9 [9; 1; 8; 8; 2; 3; 6; 4; 9; 1; 9; 2; 8];
  canonical_cons #10 2 [9; 9; 1; 8; 8; 2; 3; 6; 4; 9; 1; 9; 2; 8];
  canonical_cons #10 9 [2; 9; 9; 1; 8; 8; 2; 3; 6; 4; 9; 1; 9; 2; 8];
  canonical_cons #10 8 [9; 2; 9; 9; 1; 8; 8; 2; 3; 6; 4; 9; 1; 9; 2; 8];
  canonical_cons #10 1 [8; 9; 2; 9; 9; 1; 8; 8; 2; 3; 6; 4; 9; 1; 9; 2; 8];
  canonical_cons #10 3 [1; 8; 9; 2; 9; 9; 1; 8; 8; 2; 3; 6; 4; 9; 1; 9; 2; 8];
  canonical_cons #10 7 [3; 1; 8; 9; 2; 9; 9; 1; 8; 8; 2; 3; 6; 4; 9; 1; 9; 2; 8];
  canonical_cons #10 4 [7; 3; 1; 8; 9; 2; 9; 9; 1; 8; 8; 2; 3; 6; 4; 9; 1; 9; 2; 8];
  canonical_cons #10 8 [4; 7; 3; 1; 8; 9; 2; 9; 9; 1; 8; 8; 2; 3; 6; 4; 9; 1; 9; 2; 8];
  canonical_cons #10 1 [8; 4; 7; 3; 1; 8; 9; 2; 9; 9; 1; 8; 8; 2; 3; 6; 4; 9; 1; 9; 2; 8];
  canonical_cons #10 9 [1; 8; 4; 7; 3; 1; 8; 9; 2; 9; 9; 1; 8; 8; 2; 3; 6; 4; 9; 1; 9; 2; 8];
  canonical_cons #10 2 [9; 1; 8; 4; 7; 3; 1; 8; 9; 2; 9; 9; 1; 8; 8; 2; 3; 6; 4; 9; 1; 9; 2; 8];
  canonical_cons #10 9 [2; 9; 1; 8; 4; 7; 3; 1; 8; 9; 2; 9; 9; 1; 8; 8; 2; 3; 6; 4; 9; 1; 9; 2; 8];
  ()

let canonical_next12_target () : Lemma (canonical #10 next12_target) =
  assert (canonical #10 [1]);
  canonical_cons #10 7 [1];
  canonical_cons #10 5 [7; 1];
  canonical_cons #10 8 [5; 7; 1];
  canonical_cons #10 3 [8; 5; 7; 1];
  canonical_cons #10 7 [3; 8; 5; 7; 1];
  canonical_cons #10 9 [7; 3; 8; 5; 7; 1];
  canonical_cons #10 3 [9; 7; 3; 8; 5; 7; 1];
  canonical_cons #10 6 [3; 9; 7; 3; 8; 5; 7; 1];
  canonical_cons #10 4 [6; 3; 9; 7; 3; 8; 5; 7; 1];
  canonical_cons #10 7 [4; 6; 3; 9; 7; 3; 8; 5; 7; 1];
  canonical_cons #10 7 [7; 4; 6; 3; 9; 7; 3; 8; 5; 7; 1];
  canonical_cons #10 4 [7; 7; 4; 6; 3; 9; 7; 3; 8; 5; 7; 1];
  canonical_cons #10 9 [4; 7; 7; 4; 6; 3; 9; 7; 3; 8; 5; 7; 1];
  canonical_cons #10 8 [9; 4; 7; 7; 4; 6; 3; 9; 7; 3; 8; 5; 7; 1];
  canonical_cons #10 4 [8; 9; 4; 7; 7; 4; 6; 3; 9; 7; 3; 8; 5; 7; 1];
  canonical_cons #10 8 [4; 8; 9; 4; 7; 7; 4; 6; 3; 9; 7; 3; 8; 5; 7; 1];
  canonical_cons #10 6 [8; 4; 8; 9; 4; 7; 7; 4; 6; 3; 9; 7; 3; 8; 5; 7; 1];
  canonical_cons #10 3 [6; 8; 4; 8; 9; 4; 7; 7; 4; 6; 3; 9; 7; 3; 8; 5; 7; 1];
  canonical_cons #10 7 [3; 6; 8; 4; 8; 9; 4; 7; 7; 4; 6; 3; 9; 7; 3; 8; 5; 7; 1];
  canonical_cons #10 3 [7; 3; 6; 8; 4; 8; 9; 4; 7; 7; 4; 6; 3; 9; 7; 3; 8; 5; 7; 1];
  canonical_cons #10 9 [3; 7; 3; 6; 8; 4; 8; 9; 4; 7; 7; 4; 6; 3; 9; 7; 3; 8; 5; 7; 1];
  canonical_cons #10 7 [9; 3; 7; 3; 6; 8; 4; 8; 9; 4; 7; 7; 4; 6; 3; 9; 7; 3; 8; 5; 7; 1];
  canonical_cons #10 3 [7; 9; 3; 7; 3; 6; 8; 4; 8; 9; 4; 7; 7; 4; 6; 3; 9; 7; 3; 8; 5; 7; 1];
  canonical_cons #10 8 [3; 7; 9; 3; 7; 3; 6; 8; 4; 8; 9; 4; 7; 7; 4; 6; 3; 9; 7; 3; 8; 5; 7; 1];
  canonical_cons #10 5 [8; 3; 7; 9; 3; 7; 3; 6; 8; 4; 8; 9; 4; 7; 7; 4; 6; 3; 9; 7; 3; 8; 5; 7; 1];
  canonical_cons #10 7 [5; 8; 3; 7; 9; 3; 7; 3; 6; 8; 4; 8; 9; 4; 7; 7; 4; 6; 3; 9; 7; 3; 8; 5; 7; 1];
  ()

let reverse_digits_next12_source () : Lemma (
    reverse_digits #10 next12_source == next12_reversed) =
  ReverseAddNext.canonical_next11_target ();
  reverse_list_next12_source ();
  value_next12_reversed ();
  canonical_next12_reversed ();
  reverse_digits_canonical #10 next12_source;
  normalize_value #10 (rev next12_source);
  assert (value (reverse_digits #10 next12_source) ==
    82919463288199298137481929);
  digits_of_nat_of_canonical #10 (reverse_digits #10 next12_source);
  digits_of_nat_of_canonical #10 next12_reversed;
  assert (reverse_digits #10 next12_source == next12_reversed);
  ()

let reverse_add_92918473189299188236491928_to_175837936477498486373973857 () : Lemma (
    reverse_add #10 next12_source == next12_target) =
  ReverseAddNext.canonical_next11_target ();
  reverse_add_value #10 next12_source;
  ReverseAddNext.value_next11_target ();
  reverse_digits_next12_source ();
  value_next12_reversed ();
  value_next12_target ();
  assert (value (reverse_add #10 next12_source) ==
    175837936477498486373973857);
  reverse_add_canonical #10 next12_source;
  digits_of_nat_of_canonical #10 (reverse_add #10 next12_source);
  canonical_next12_target ();
  digits_of_nat_of_canonical #10 next12_target;
  assert (reverse_add #10 next12_source == next12_target);
  ()

let trace_digits_profile_92918473189299188236491928 () : Lemma (
    trace_digits next12_source == next12_target) =
  reverse_add_92918473189299188236491928_to_175837936477498486373973857 ();
  trace_digits_equals_reverse_add next12_source;
  assert (trace_digits next12_source == next12_target);
  ()

let trace_carries_next12_source () : Lemma (trace_carries next12_source ==
    [0; 1; 0; 1; 0; 1; 0; 1; 0; 0; 1; 1; 0; 1; 1; 0; 1; 1; 0; 0; 1; 0; 1; 0; 1; 0; 1]) =
  reverse_list_next12_source ();
  assert (trace_carries next12_source ==
    (add_trace #10 next12_source next12_reversed 0).carries);
  add_trace_carries_step #10 8 9
    [2; 9; 1; 9; 4; 6; 3; 2; 8; 8; 1; 9; 9; 2; 9; 8; 1; 3; 7; 4; 8; 1; 9; 2; 9]
    [2; 9; 1; 8; 4; 7; 3; 1; 8; 9; 2; 9; 9; 1; 8; 8; 2; 3; 6; 4; 9; 1; 9; 2; 8] 0;
  add_trace_carries_step #10 2 2
    [9; 1; 9; 4; 6; 3; 2; 8; 8; 1; 9; 9; 2; 9; 8; 1; 3; 7; 4; 8; 1; 9; 2; 9]
    [9; 1; 8; 4; 7; 3; 1; 8; 9; 2; 9; 9; 1; 8; 8; 2; 3; 6; 4; 9; 1; 9; 2; 8] 1;
  add_trace_carries_step #10 9 9
    [1; 9; 4; 6; 3; 2; 8; 8; 1; 9; 9; 2; 9; 8; 1; 3; 7; 4; 8; 1; 9; 2; 9]
    [1; 8; 4; 7; 3; 1; 8; 9; 2; 9; 9; 1; 8; 8; 2; 3; 6; 4; 9; 1; 9; 2; 8] 0;
  add_trace_carries_step #10 1 1
    [9; 4; 6; 3; 2; 8; 8; 1; 9; 9; 2; 9; 8; 1; 3; 7; 4; 8; 1; 9; 2; 9]
    [8; 4; 7; 3; 1; 8; 9; 2; 9; 9; 1; 8; 8; 2; 3; 6; 4; 9; 1; 9; 2; 8] 1;
  add_trace_carries_step #10 9 8
    [4; 6; 3; 2; 8; 8; 1; 9; 9; 2; 9; 8; 1; 3; 7; 4; 8; 1; 9; 2; 9]
    [4; 7; 3; 1; 8; 9; 2; 9; 9; 1; 8; 8; 2; 3; 6; 4; 9; 1; 9; 2; 8] 0;
  add_trace_carries_step #10 4 4
    [6; 3; 2; 8; 8; 1; 9; 9; 2; 9; 8; 1; 3; 7; 4; 8; 1; 9; 2; 9]
    [7; 3; 1; 8; 9; 2; 9; 9; 1; 8; 8; 2; 3; 6; 4; 9; 1; 9; 2; 8] 1;
  add_trace_carries_step #10 6 7
    [3; 2; 8; 8; 1; 9; 9; 2; 9; 8; 1; 3; 7; 4; 8; 1; 9; 2; 9]
    [3; 1; 8; 9; 2; 9; 9; 1; 8; 8; 2; 3; 6; 4; 9; 1; 9; 2; 8] 0;
  add_trace_carries_step #10 3 3
    [2; 8; 8; 1; 9; 9; 2; 9; 8; 1; 3; 7; 4; 8; 1; 9; 2; 9]
    [1; 8; 9; 2; 9; 9; 1; 8; 8; 2; 3; 6; 4; 9; 1; 9; 2; 8] 1;
  add_trace_carries_step #10 2 1
    [8; 8; 1; 9; 9; 2; 9; 8; 1; 3; 7; 4; 8; 1; 9; 2; 9]
    [8; 9; 2; 9; 9; 1; 8; 8; 2; 3; 6; 4; 9; 1; 9; 2; 8] 0;
  add_trace_carries_step #10 8 8
    [8; 1; 9; 9; 2; 9; 8; 1; 3; 7; 4; 8; 1; 9; 2; 9]
    [9; 2; 9; 9; 1; 8; 8; 2; 3; 6; 4; 9; 1; 9; 2; 8] 0;
  add_trace_carries_step #10 8 9
    [1; 9; 9; 2; 9; 8; 1; 3; 7; 4; 8; 1; 9; 2; 9]
    [2; 9; 9; 1; 8; 8; 2; 3; 6; 4; 9; 1; 9; 2; 8] 1;
  add_trace_carries_step #10 1 2
    [9; 9; 2; 9; 8; 1; 3; 7; 4; 8; 1; 9; 2; 9]
    [9; 9; 1; 8; 8; 2; 3; 6; 4; 9; 1; 9; 2; 8] 1;
  add_trace_carries_step #10 9 9
    [9; 2; 9; 8; 1; 3; 7; 4; 8; 1; 9; 2; 9]
    [9; 1; 8; 8; 2; 3; 6; 4; 9; 1; 9; 2; 8] 0;
  add_trace_carries_step #10 9 9
    [2; 9; 8; 1; 3; 7; 4; 8; 1; 9; 2; 9]
    [1; 8; 8; 2; 3; 6; 4; 9; 1; 9; 2; 8] 1;
  add_trace_carries_step #10 2 1
    [9; 8; 1; 3; 7; 4; 8; 1; 9; 2; 9]
    [8; 8; 2; 3; 6; 4; 9; 1; 9; 2; 8] 1;
  add_trace_carries_step #10 9 8
    [8; 1; 3; 7; 4; 8; 1; 9; 2; 9]
    [8; 2; 3; 6; 4; 9; 1; 9; 2; 8] 0;
  add_trace_carries_step #10 8 8
    [1; 3; 7; 4; 8; 1; 9; 2; 9]
    [2; 3; 6; 4; 9; 1; 9; 2; 8] 1;
  add_trace_carries_step #10 1 2
    [3; 7; 4; 8; 1; 9; 2; 9]
    [3; 6; 4; 9; 1; 9; 2; 8] 1;
  add_trace_carries_step #10 3 3
    [7; 4; 8; 1; 9; 2; 9]
    [6; 4; 9; 1; 9; 2; 8] 0;
  add_trace_carries_step #10 7 6
    [4; 8; 1; 9; 2; 9]
    [4; 9; 1; 9; 2; 8] 0;
  add_trace_carries_step #10 4 4
    [8; 1; 9; 2; 9]
    [9; 1; 9; 2; 8] 1;
  add_trace_carries_step #10 8 9
    [1; 9; 2; 9]
    [1; 9; 2; 8] 0;
  add_trace_carries_step #10 1 1
    [9; 2; 9]
    [9; 2; 8] 1;
  add_trace_carries_step #10 9 9
    [2; 9]
    [2; 8] 0;
  add_trace_carries_step #10 2 2
    [9]
    [8] 1;
  add_trace_carries_step #10 9 8
    []
    [] 0;
  assert ((add_trace #10 [] [] 1).carries == [1]);
  assert ((add_trace #10 next12_source next12_reversed 0).carries ==
    [0; 1; 0; 1; 0; 1; 0; 1; 0; 0; 1; 1; 0; 1; 1; 0; 1; 1; 0; 0; 1; 0; 1; 0; 1; 0; 1]);
  ()

let trace_profile_shape_92918473189299188236491928 () : Lemma (
    length (trace_digits next12_source) == length next12_source + 1) =
  trace_digits_profile_92918473189299188236491928 ();
  length_of_eq #(digit 10) (trace_digits next12_source) next12_target;
  assert (length next12_target == length next12_source + 1);
  ()

let trace_profile_final_carry_92918473189299188236491928 () : Lemma (
    nth (trace_carries next12_source) (length next12_source) == Some 1) =
  trace_profile_shape_92918473189299188236491928 ();
  ReverseAddContinuation.final_carry_from_overflow_length next12_source;
  ()

let trace_profile_sums_92918473189299188236491928 () : Lemma (
    trace_sum_at next12_source 0 == 17 /\
    trace_sum_at next12_source 1 == 4 /\
    trace_sum_at next12_source 25 == 17) =
  reverse_list_next12_source ();
  ()

let trace_profile_carry_facts_92918473189299188236491928 () : Lemma (
    trace_carry_at next12_source 1 == 1 /\
    trace_carry_at next12_source 25 == 0 /\
    trace_carry_at next12_source 2 == 0 /\
    trace_carry_at next12_source 26 == 1) =
  trace_carries_next12_source ();
  ()

let overflow_precondition_92918473189299188236491928 () : Lemma (
    canonical #10 next12_source /\
    next12_source <> [] /\
    length (trace_digits next12_source) == length next12_source + 1 /\
    nth (trace_carries next12_source) (length next12_source) == Some 1 /\
    1 <= trace_sum_at next12_source 0 /\
    trace_sum_at next12_source 0 <= 18 /\
    trace_sum_at next12_source 0 <> 10 /\
    exists (i:nat). 0 < i /\ i < length next12_source /\
      trace_sum_at next12_source i +
          trace_sum_at next12_source (length next12_source - i) +
          trace_carry_at next12_source i +
          trace_carry_at next12_source (length next12_source - i) >=
        10 + 10 *
          (trace_carry_at next12_source (i + 1) +
           trace_carry_at next12_source (length next12_source - i + 1))) =
  ReverseAddNext.canonical_next11_target ();
  assert (next12_source <> []);
  trace_profile_shape_92918473189299188236491928 ();
  trace_profile_final_carry_92918473189299188236491928 ();
  trace_profile_sums_92918473189299188236491928 ();
  trace_profile_carry_facts_92918473189299188236491928 ();
  assert (length (trace_digits next12_source) == length next12_source + 1);
  assert (nth (trace_carries next12_source)
    (length next12_source) == Some 1);
  assert (trace_sum_at next12_source 0 == 17);
  assert (trace_sum_at next12_source 1 == 4);
  assert (trace_sum_at next12_source 25 == 17);
  assert (trace_carry_at next12_source 1 == 1);
  assert (trace_carry_at next12_source 25 == 0);
  assert (trace_carry_at next12_source 2 == 0);
  assert (trace_carry_at next12_source 26 == 1);
  assert (1 <= trace_sum_at next12_source 0 /\
    trace_sum_at next12_source 0 <= 18);
  assert (trace_sum_at next12_source 0 <> 10);
  let n : nat = length next12_source in
  assert (0 < 1 /\ 1 < n);
  assert (trace_sum_at next12_source 1 +
      trace_sum_at next12_source (n - 1) +
      trace_carry_at next12_source 1 +
      trace_carry_at next12_source (n - 1) >=
    10 + 10 *
      (trace_carry_at next12_source 2 +
       trace_carry_at next12_source (n - 1 + 1)));
  exists_intro
    (fun (i:nat) -> 0 < i /\ i < n /\
      trace_sum_at next12_source i +
          trace_sum_at next12_source (n - i) +
          trace_carry_at next12_source i +
          trace_carry_at next12_source (n - i) >=
        10 + 10 *
          (trace_carry_at next12_source (i + 1) +
           trace_carry_at next12_source (n - i + 1)))
    1;
  ()

let local_profile_witness_175837936477498486373973857 () : Lemma (
    trace_local_profile_complement_witness next12_target) =
  overflow_precondition_92918473189299188236491928 ();
  reverse_add_92918473189299188236491928_to_175837936477498486373973857 ();
  overflow_internal_cell_implies_next_witness next12_source;
  ()

let next13_source : numeral 10 = next12_target

let next13_reversed : numeral 10 =
  [1; 7; 5; 8; 3; 7; 9; 3; 6; 4; 7; 7; 4; 9; 8; 4; 8; 6; 3; 7; 3; 9; 7; 3; 8; 5; 7]

let next13_target : numeral 10 =
  [8; 2; 4; 2; 1; 7; 3; 1; 0; 1; 6; 2; 3; 9; 3; 2; 6; 1; 0; 1; 3; 7; 1; 2; 4; 3; 9]

let reverse_list_next13_source () : Lemma (rev next13_source == next13_reversed) =
  assert (rev [1] == [1]);
  rev_cons 7 [1];
  rev_cons 5 [7; 1];
  rev_cons 8 [5; 7; 1];
  rev_cons 3 [8; 5; 7; 1];
  rev_cons 7 [3; 8; 5; 7; 1];
  rev_cons 9 [7; 3; 8; 5; 7; 1];
  rev_cons 3 [9; 7; 3; 8; 5; 7; 1];
  rev_cons 6 [3; 9; 7; 3; 8; 5; 7; 1];
  rev_cons 4 [6; 3; 9; 7; 3; 8; 5; 7; 1];
  rev_cons 7 [4; 6; 3; 9; 7; 3; 8; 5; 7; 1];
  rev_cons 7 [7; 4; 6; 3; 9; 7; 3; 8; 5; 7; 1];
  rev_cons 4 [7; 7; 4; 6; 3; 9; 7; 3; 8; 5; 7; 1];
  rev_cons 9 [4; 7; 7; 4; 6; 3; 9; 7; 3; 8; 5; 7; 1];
  rev_cons 8 [9; 4; 7; 7; 4; 6; 3; 9; 7; 3; 8; 5; 7; 1];
  rev_cons 4 [8; 9; 4; 7; 7; 4; 6; 3; 9; 7; 3; 8; 5; 7; 1];
  rev_cons 8 [4; 8; 9; 4; 7; 7; 4; 6; 3; 9; 7; 3; 8; 5; 7; 1];
  rev_cons 6 [8; 4; 8; 9; 4; 7; 7; 4; 6; 3; 9; 7; 3; 8; 5; 7; 1];
  rev_cons 3 [6; 8; 4; 8; 9; 4; 7; 7; 4; 6; 3; 9; 7; 3; 8; 5; 7; 1];
  rev_cons 7 [3; 6; 8; 4; 8; 9; 4; 7; 7; 4; 6; 3; 9; 7; 3; 8; 5; 7; 1];
  rev_cons 3 [7; 3; 6; 8; 4; 8; 9; 4; 7; 7; 4; 6; 3; 9; 7; 3; 8; 5; 7; 1];
  rev_cons 9 [3; 7; 3; 6; 8; 4; 8; 9; 4; 7; 7; 4; 6; 3; 9; 7; 3; 8; 5; 7; 1];
  rev_cons 7 [9; 3; 7; 3; 6; 8; 4; 8; 9; 4; 7; 7; 4; 6; 3; 9; 7; 3; 8; 5; 7; 1];
  rev_cons 3 [7; 9; 3; 7; 3; 6; 8; 4; 8; 9; 4; 7; 7; 4; 6; 3; 9; 7; 3; 8; 5; 7; 1];
  rev_cons 8 [3; 7; 9; 3; 7; 3; 6; 8; 4; 8; 9; 4; 7; 7; 4; 6; 3; 9; 7; 3; 8; 5; 7; 1];
  rev_cons 5 [8; 3; 7; 9; 3; 7; 3; 6; 8; 4; 8; 9; 4; 7; 7; 4; 6; 3; 9; 7; 3; 8; 5; 7; 1];
  rev_cons 7 [5; 8; 3; 7; 9; 3; 7; 3; 6; 8; 4; 8; 9; 4; 7; 7; 4; 6; 3; 9; 7; 3; 8; 5; 7; 1];
  ()

let value_next13_reversed () : Lemma (
    value next13_reversed == 758379373684894774639738571) =
  value_cons #10 1 [7; 5; 8; 3; 7; 9; 3; 6; 4; 7; 7; 4; 9; 8; 4; 8; 6; 3; 7; 3; 9; 7; 3; 8; 5; 7];
  value_cons #10 7 [5; 8; 3; 7; 9; 3; 6; 4; 7; 7; 4; 9; 8; 4; 8; 6; 3; 7; 3; 9; 7; 3; 8; 5; 7];
  value_cons #10 5 [8; 3; 7; 9; 3; 6; 4; 7; 7; 4; 9; 8; 4; 8; 6; 3; 7; 3; 9; 7; 3; 8; 5; 7];
  value_cons #10 8 [3; 7; 9; 3; 6; 4; 7; 7; 4; 9; 8; 4; 8; 6; 3; 7; 3; 9; 7; 3; 8; 5; 7];
  value_cons #10 3 [7; 9; 3; 6; 4; 7; 7; 4; 9; 8; 4; 8; 6; 3; 7; 3; 9; 7; 3; 8; 5; 7];
  value_cons #10 7 [9; 3; 6; 4; 7; 7; 4; 9; 8; 4; 8; 6; 3; 7; 3; 9; 7; 3; 8; 5; 7];
  value_cons #10 9 [3; 6; 4; 7; 7; 4; 9; 8; 4; 8; 6; 3; 7; 3; 9; 7; 3; 8; 5; 7];
  value_cons #10 3 [6; 4; 7; 7; 4; 9; 8; 4; 8; 6; 3; 7; 3; 9; 7; 3; 8; 5; 7];
  value_cons #10 6 [4; 7; 7; 4; 9; 8; 4; 8; 6; 3; 7; 3; 9; 7; 3; 8; 5; 7];
  value_cons #10 4 [7; 7; 4; 9; 8; 4; 8; 6; 3; 7; 3; 9; 7; 3; 8; 5; 7];
  value_cons #10 7 [7; 4; 9; 8; 4; 8; 6; 3; 7; 3; 9; 7; 3; 8; 5; 7];
  value_cons #10 7 [4; 9; 8; 4; 8; 6; 3; 7; 3; 9; 7; 3; 8; 5; 7];
  value_cons #10 4 [9; 8; 4; 8; 6; 3; 7; 3; 9; 7; 3; 8; 5; 7];
  value_cons #10 9 [8; 4; 8; 6; 3; 7; 3; 9; 7; 3; 8; 5; 7];
  value_cons #10 8 [4; 8; 6; 3; 7; 3; 9; 7; 3; 8; 5; 7];
  value_cons #10 4 [8; 6; 3; 7; 3; 9; 7; 3; 8; 5; 7];
  value_cons #10 8 [6; 3; 7; 3; 9; 7; 3; 8; 5; 7];
  value_cons #10 6 [3; 7; 3; 9; 7; 3; 8; 5; 7];
  value_cons #10 3 [7; 3; 9; 7; 3; 8; 5; 7];
  value_cons #10 7 [3; 9; 7; 3; 8; 5; 7];
  value_cons #10 3 [9; 7; 3; 8; 5; 7];
  value_cons #10 9 [7; 3; 8; 5; 7];
  value_cons #10 7 [3; 8; 5; 7];
  value_cons #10 3 [8; 5; 7];
  value_cons #10 8 [5; 7];
  value_cons #10 5 [7];
  value_cons #10 7 [];
  ()

let value_next13_target_tail_18 () : Lemma (
    value #10 [1; 6; 2; 3; 9; 3; 2; 6; 1; 0; 1; 3; 7; 1; 2; 4; 3; 9] == 934217310162393261) =
  value_cons #10 1 [6; 2; 3; 9; 3; 2; 6; 1; 0; 1; 3; 7; 1; 2; 4; 3; 9];
  value_cons #10 6 [2; 3; 9; 3; 2; 6; 1; 0; 1; 3; 7; 1; 2; 4; 3; 9];
  value_cons #10 2 [3; 9; 3; 2; 6; 1; 0; 1; 3; 7; 1; 2; 4; 3; 9];
  value_cons #10 3 [9; 3; 2; 6; 1; 0; 1; 3; 7; 1; 2; 4; 3; 9];
  value_cons #10 9 [3; 2; 6; 1; 0; 1; 3; 7; 1; 2; 4; 3; 9];
  value_cons #10 3 [2; 6; 1; 0; 1; 3; 7; 1; 2; 4; 3; 9];
  value_cons #10 2 [6; 1; 0; 1; 3; 7; 1; 2; 4; 3; 9];
  value_cons #10 6 [1; 0; 1; 3; 7; 1; 2; 4; 3; 9];
  value_cons #10 1 [0; 1; 3; 7; 1; 2; 4; 3; 9];
  value_cons #10 0 [1; 3; 7; 1; 2; 4; 3; 9];
  value_cons #10 1 [3; 7; 1; 2; 4; 3; 9];
  value_cons #10 3 [7; 1; 2; 4; 3; 9];
  value_cons #10 7 [1; 2; 4; 3; 9];
  value_cons #10 1 [2; 4; 3; 9];
  value_cons #10 2 [4; 3; 9];
  value_cons #10 4 [3; 9];
  value_cons #10 3 [9];
  value_cons #10 9 [];
  ()

let value_next13_target () : Lemma (
    value next13_target == 934217310162393261013712428) =
  value_cons #10 8 [2; 4; 2; 1; 7; 3; 1; 0; 1; 6; 2; 3; 9; 3; 2; 6; 1; 0; 1; 3; 7; 1; 2; 4; 3; 9];
  value_cons #10 2 [4; 2; 1; 7; 3; 1; 0; 1; 6; 2; 3; 9; 3; 2; 6; 1; 0; 1; 3; 7; 1; 2; 4; 3; 9];
  value_cons #10 4 [2; 1; 7; 3; 1; 0; 1; 6; 2; 3; 9; 3; 2; 6; 1; 0; 1; 3; 7; 1; 2; 4; 3; 9];
  value_cons #10 2 [1; 7; 3; 1; 0; 1; 6; 2; 3; 9; 3; 2; 6; 1; 0; 1; 3; 7; 1; 2; 4; 3; 9];
  value_cons #10 1 [7; 3; 1; 0; 1; 6; 2; 3; 9; 3; 2; 6; 1; 0; 1; 3; 7; 1; 2; 4; 3; 9];
  value_cons #10 7 [3; 1; 0; 1; 6; 2; 3; 9; 3; 2; 6; 1; 0; 1; 3; 7; 1; 2; 4; 3; 9];
  value_cons #10 3 [1; 0; 1; 6; 2; 3; 9; 3; 2; 6; 1; 0; 1; 3; 7; 1; 2; 4; 3; 9];
  value_cons #10 1 [0; 1; 6; 2; 3; 9; 3; 2; 6; 1; 0; 1; 3; 7; 1; 2; 4; 3; 9];
  value_cons #10 0 [1; 6; 2; 3; 9; 3; 2; 6; 1; 0; 1; 3; 7; 1; 2; 4; 3; 9];
  value_next13_target_tail_18 ();
  ()

let canonical_next13_reversed () : Lemma (canonical #10 next13_reversed) =
  assert (canonical #10 [7]);
  canonical_cons #10 5 [7];
  canonical_cons #10 8 [5; 7];
  canonical_cons #10 3 [8; 5; 7];
  canonical_cons #10 7 [3; 8; 5; 7];
  canonical_cons #10 9 [7; 3; 8; 5; 7];
  canonical_cons #10 3 [9; 7; 3; 8; 5; 7];
  canonical_cons #10 7 [3; 9; 7; 3; 8; 5; 7];
  canonical_cons #10 3 [7; 3; 9; 7; 3; 8; 5; 7];
  canonical_cons #10 6 [3; 7; 3; 9; 7; 3; 8; 5; 7];
  canonical_cons #10 8 [6; 3; 7; 3; 9; 7; 3; 8; 5; 7];
  canonical_cons #10 4 [8; 6; 3; 7; 3; 9; 7; 3; 8; 5; 7];
  canonical_cons #10 8 [4; 8; 6; 3; 7; 3; 9; 7; 3; 8; 5; 7];
  canonical_cons #10 9 [8; 4; 8; 6; 3; 7; 3; 9; 7; 3; 8; 5; 7];
  canonical_cons #10 4 [9; 8; 4; 8; 6; 3; 7; 3; 9; 7; 3; 8; 5; 7];
  canonical_cons #10 7 [4; 9; 8; 4; 8; 6; 3; 7; 3; 9; 7; 3; 8; 5; 7];
  canonical_cons #10 7 [7; 4; 9; 8; 4; 8; 6; 3; 7; 3; 9; 7; 3; 8; 5; 7];
  canonical_cons #10 4 [7; 7; 4; 9; 8; 4; 8; 6; 3; 7; 3; 9; 7; 3; 8; 5; 7];
  canonical_cons #10 6 [4; 7; 7; 4; 9; 8; 4; 8; 6; 3; 7; 3; 9; 7; 3; 8; 5; 7];
  canonical_cons #10 3 [6; 4; 7; 7; 4; 9; 8; 4; 8; 6; 3; 7; 3; 9; 7; 3; 8; 5; 7];
  canonical_cons #10 9 [3; 6; 4; 7; 7; 4; 9; 8; 4; 8; 6; 3; 7; 3; 9; 7; 3; 8; 5; 7];
  canonical_cons #10 7 [9; 3; 6; 4; 7; 7; 4; 9; 8; 4; 8; 6; 3; 7; 3; 9; 7; 3; 8; 5; 7];
  canonical_cons #10 3 [7; 9; 3; 6; 4; 7; 7; 4; 9; 8; 4; 8; 6; 3; 7; 3; 9; 7; 3; 8; 5; 7];
  canonical_cons #10 8 [3; 7; 9; 3; 6; 4; 7; 7; 4; 9; 8; 4; 8; 6; 3; 7; 3; 9; 7; 3; 8; 5; 7];
  canonical_cons #10 5 [8; 3; 7; 9; 3; 6; 4; 7; 7; 4; 9; 8; 4; 8; 6; 3; 7; 3; 9; 7; 3; 8; 5; 7];
  canonical_cons #10 7 [5; 8; 3; 7; 9; 3; 6; 4; 7; 7; 4; 9; 8; 4; 8; 6; 3; 7; 3; 9; 7; 3; 8; 5; 7];
  canonical_cons #10 1 [7; 5; 8; 3; 7; 9; 3; 6; 4; 7; 7; 4; 9; 8; 4; 8; 6; 3; 7; 3; 9; 7; 3; 8; 5; 7];
  ()

let canonical_next13_target () : Lemma (canonical #10 next13_target) =
  assert (canonical #10 [9]);
  canonical_cons #10 3 [9];
  canonical_cons #10 4 [3; 9];
  canonical_cons #10 2 [4; 3; 9];
  canonical_cons #10 1 [2; 4; 3; 9];
  canonical_cons #10 7 [1; 2; 4; 3; 9];
  canonical_cons #10 3 [7; 1; 2; 4; 3; 9];
  canonical_cons #10 1 [3; 7; 1; 2; 4; 3; 9];
  canonical_cons #10 0 [1; 3; 7; 1; 2; 4; 3; 9];
  canonical_cons #10 1 [0; 1; 3; 7; 1; 2; 4; 3; 9];
  canonical_cons #10 6 [1; 0; 1; 3; 7; 1; 2; 4; 3; 9];
  canonical_cons #10 2 [6; 1; 0; 1; 3; 7; 1; 2; 4; 3; 9];
  canonical_cons #10 3 [2; 6; 1; 0; 1; 3; 7; 1; 2; 4; 3; 9];
  canonical_cons #10 9 [3; 2; 6; 1; 0; 1; 3; 7; 1; 2; 4; 3; 9];
  canonical_cons #10 3 [9; 3; 2; 6; 1; 0; 1; 3; 7; 1; 2; 4; 3; 9];
  canonical_cons #10 2 [3; 9; 3; 2; 6; 1; 0; 1; 3; 7; 1; 2; 4; 3; 9];
  canonical_cons #10 6 [2; 3; 9; 3; 2; 6; 1; 0; 1; 3; 7; 1; 2; 4; 3; 9];
  canonical_cons #10 1 [6; 2; 3; 9; 3; 2; 6; 1; 0; 1; 3; 7; 1; 2; 4; 3; 9];
  canonical_cons #10 0 [1; 6; 2; 3; 9; 3; 2; 6; 1; 0; 1; 3; 7; 1; 2; 4; 3; 9];
  canonical_cons #10 1 [0; 1; 6; 2; 3; 9; 3; 2; 6; 1; 0; 1; 3; 7; 1; 2; 4; 3; 9];
  canonical_cons #10 3 [1; 0; 1; 6; 2; 3; 9; 3; 2; 6; 1; 0; 1; 3; 7; 1; 2; 4; 3; 9];
  canonical_cons #10 7 [3; 1; 0; 1; 6; 2; 3; 9; 3; 2; 6; 1; 0; 1; 3; 7; 1; 2; 4; 3; 9];
  canonical_cons #10 1 [7; 3; 1; 0; 1; 6; 2; 3; 9; 3; 2; 6; 1; 0; 1; 3; 7; 1; 2; 4; 3; 9];
  canonical_cons #10 2 [1; 7; 3; 1; 0; 1; 6; 2; 3; 9; 3; 2; 6; 1; 0; 1; 3; 7; 1; 2; 4; 3; 9];
  canonical_cons #10 4 [2; 1; 7; 3; 1; 0; 1; 6; 2; 3; 9; 3; 2; 6; 1; 0; 1; 3; 7; 1; 2; 4; 3; 9];
  canonical_cons #10 2 [4; 2; 1; 7; 3; 1; 0; 1; 6; 2; 3; 9; 3; 2; 6; 1; 0; 1; 3; 7; 1; 2; 4; 3; 9];
  canonical_cons #10 8 [2; 4; 2; 1; 7; 3; 1; 0; 1; 6; 2; 3; 9; 3; 2; 6; 1; 0; 1; 3; 7; 1; 2; 4; 3; 9];
  ()

let reverse_digits_next13_source () : Lemma (
    reverse_digits #10 next13_source == next13_reversed) =
  ReverseAddNext.canonical_next12_target ();
  reverse_list_next13_source ();
  value_next13_reversed ();
  canonical_next13_reversed ();
  reverse_digits_canonical #10 next13_source;
  normalize_value #10 (rev next13_source);
  assert (value (reverse_digits #10 next13_source) ==
    758379373684894774639738571);
  digits_of_nat_of_canonical #10 (reverse_digits #10 next13_source);
  digits_of_nat_of_canonical #10 next13_reversed;
  assert (reverse_digits #10 next13_source == next13_reversed);
  ()

let reverse_add_175837936477498486373973857_to_934217310162393261013712428 () : Lemma (
    reverse_add #10 next13_source == next13_target) =
  ReverseAddNext.canonical_next12_target ();
  reverse_add_value #10 next13_source;
  ReverseAddNext.value_next12_target ();
  reverse_digits_next13_source ();
  value_next13_reversed ();
  value_next13_target ();
  assert (value (reverse_add #10 next13_source) ==
    934217310162393261013712428);
  reverse_add_canonical #10 next13_source;
  digits_of_nat_of_canonical #10 (reverse_add #10 next13_source);
  canonical_next13_target ();
  digits_of_nat_of_canonical #10 next13_target;
  assert (reverse_add #10 next13_source == next13_target);
  ()

let trace_digits_profile_175837936477498486373973857 () : Lemma (
    trace_digits next13_source == next13_target) =
  reverse_add_175837936477498486373973857_to_934217310162393261013712428 ();
  trace_digits_equals_reverse_add next13_source;
  assert (trace_digits next13_source == next13_target);
  ()

let trace_profile_shape_175837936477498486373973857 () : Lemma (
    length (trace_digits next13_source) == length next13_source) =
  trace_digits_profile_175837936477498486373973857 ();
  length_of_eq #(digit 10) (trace_digits next13_source) next13_target;
  assert (length next13_target == length next13_source);
  ()

let trace_profile_final_carry_175837936477498486373973857 () : Lemma (
    nth (trace_carries next13_source) (length next13_source) == Some 0) =
  trace_profile_shape_175837936477498486373973857 ();
  final_carry_from_length next13_source;
  ()

let local_profile_witness_934217310162393261013712428 () : Lemma (
    trace_local_profile_complement_witness next13_target) =
  ReverseAddNext.canonical_next12_target ();
  assert (next13_source <> []);
  trace_profile_shape_175837936477498486373973857 ();
  trace_profile_final_carry_175837936477498486373973857 ();
  assert (trace_sum_at next13_source 0 == 8);
  reverse_add_175837936477498486373973857_to_934217310162393261013712428 ();
  no_overflow_outer_sum_6_to_9_implies_next_witness next13_source;
  ()

let next14_source : numeral 10 = next13_target

let next14_reversed : numeral 10 =
  [9; 3; 4; 2; 1; 7; 3; 1; 0; 1; 6; 2; 3; 9; 3; 2; 6; 1; 0; 1; 3; 7; 1; 2; 4; 2; 8]

let next14_target : numeral 10 =
  [7; 6; 8; 4; 2; 4; 7; 2; 0; 2; 2; 5; 6; 8; 7; 4; 2; 3; 0; 2; 6; 4; 3; 4; 8; 5; 7; 1]

let reverse_list_next14_source () : Lemma (rev next14_source == next14_reversed) =
  assert (rev [9] == [9]);
  rev_cons 3 [9];
  rev_cons 4 [3; 9];
  rev_cons 2 [4; 3; 9];
  rev_cons 1 [2; 4; 3; 9];
  rev_cons 7 [1; 2; 4; 3; 9];
  rev_cons 3 [7; 1; 2; 4; 3; 9];
  rev_cons 1 [3; 7; 1; 2; 4; 3; 9];
  rev_cons 0 [1; 3; 7; 1; 2; 4; 3; 9];
  rev_cons 1 [0; 1; 3; 7; 1; 2; 4; 3; 9];
  rev_cons 6 [1; 0; 1; 3; 7; 1; 2; 4; 3; 9];
  rev_cons 2 [6; 1; 0; 1; 3; 7; 1; 2; 4; 3; 9];
  rev_cons 3 [2; 6; 1; 0; 1; 3; 7; 1; 2; 4; 3; 9];
  rev_cons 9 [3; 2; 6; 1; 0; 1; 3; 7; 1; 2; 4; 3; 9];
  rev_cons 3 [9; 3; 2; 6; 1; 0; 1; 3; 7; 1; 2; 4; 3; 9];
  rev_cons 2 [3; 9; 3; 2; 6; 1; 0; 1; 3; 7; 1; 2; 4; 3; 9];
  rev_cons 6 [2; 3; 9; 3; 2; 6; 1; 0; 1; 3; 7; 1; 2; 4; 3; 9];
  rev_cons 1 [6; 2; 3; 9; 3; 2; 6; 1; 0; 1; 3; 7; 1; 2; 4; 3; 9];
  rev_cons 0 [1; 6; 2; 3; 9; 3; 2; 6; 1; 0; 1; 3; 7; 1; 2; 4; 3; 9];
  rev_cons 1 [0; 1; 6; 2; 3; 9; 3; 2; 6; 1; 0; 1; 3; 7; 1; 2; 4; 3; 9];
  rev_cons 3 [1; 0; 1; 6; 2; 3; 9; 3; 2; 6; 1; 0; 1; 3; 7; 1; 2; 4; 3; 9];
  rev_cons 7 [3; 1; 0; 1; 6; 2; 3; 9; 3; 2; 6; 1; 0; 1; 3; 7; 1; 2; 4; 3; 9];
  rev_cons 1 [7; 3; 1; 0; 1; 6; 2; 3; 9; 3; 2; 6; 1; 0; 1; 3; 7; 1; 2; 4; 3; 9];
  rev_cons 2 [1; 7; 3; 1; 0; 1; 6; 2; 3; 9; 3; 2; 6; 1; 0; 1; 3; 7; 1; 2; 4; 3; 9];
  rev_cons 4 [2; 1; 7; 3; 1; 0; 1; 6; 2; 3; 9; 3; 2; 6; 1; 0; 1; 3; 7; 1; 2; 4; 3; 9];
  rev_cons 2 [4; 2; 1; 7; 3; 1; 0; 1; 6; 2; 3; 9; 3; 2; 6; 1; 0; 1; 3; 7; 1; 2; 4; 3; 9];
  rev_cons 8 [2; 4; 2; 1; 7; 3; 1; 0; 1; 6; 2; 3; 9; 3; 2; 6; 1; 0; 1; 3; 7; 1; 2; 4; 3; 9];
  ()

let value_next14_reversed () : Lemma (
    value next14_reversed == 824217310162393261013712439) =
  value_cons #10 9 [3; 4; 2; 1; 7; 3; 1; 0; 1; 6; 2; 3; 9; 3; 2; 6; 1; 0; 1; 3; 7; 1; 2; 4; 2; 8];
  value_cons #10 3 [4; 2; 1; 7; 3; 1; 0; 1; 6; 2; 3; 9; 3; 2; 6; 1; 0; 1; 3; 7; 1; 2; 4; 2; 8];
  value_cons #10 4 [2; 1; 7; 3; 1; 0; 1; 6; 2; 3; 9; 3; 2; 6; 1; 0; 1; 3; 7; 1; 2; 4; 2; 8];
  value_cons #10 2 [1; 7; 3; 1; 0; 1; 6; 2; 3; 9; 3; 2; 6; 1; 0; 1; 3; 7; 1; 2; 4; 2; 8];
  value_cons #10 1 [7; 3; 1; 0; 1; 6; 2; 3; 9; 3; 2; 6; 1; 0; 1; 3; 7; 1; 2; 4; 2; 8];
  value_cons #10 7 [3; 1; 0; 1; 6; 2; 3; 9; 3; 2; 6; 1; 0; 1; 3; 7; 1; 2; 4; 2; 8];
  value_cons #10 3 [1; 0; 1; 6; 2; 3; 9; 3; 2; 6; 1; 0; 1; 3; 7; 1; 2; 4; 2; 8];
  value_cons #10 1 [0; 1; 6; 2; 3; 9; 3; 2; 6; 1; 0; 1; 3; 7; 1; 2; 4; 2; 8];
  value_cons #10 0 [1; 6; 2; 3; 9; 3; 2; 6; 1; 0; 1; 3; 7; 1; 2; 4; 2; 8];
  value_cons #10 1 [6; 2; 3; 9; 3; 2; 6; 1; 0; 1; 3; 7; 1; 2; 4; 2; 8];
  value_cons #10 6 [2; 3; 9; 3; 2; 6; 1; 0; 1; 3; 7; 1; 2; 4; 2; 8];
  value_cons #10 2 [3; 9; 3; 2; 6; 1; 0; 1; 3; 7; 1; 2; 4; 2; 8];
  value_cons #10 3 [9; 3; 2; 6; 1; 0; 1; 3; 7; 1; 2; 4; 2; 8];
  value_cons #10 9 [3; 2; 6; 1; 0; 1; 3; 7; 1; 2; 4; 2; 8];
  value_cons #10 3 [2; 6; 1; 0; 1; 3; 7; 1; 2; 4; 2; 8];
  value_cons #10 2 [6; 1; 0; 1; 3; 7; 1; 2; 4; 2; 8];
  value_cons #10 6 [1; 0; 1; 3; 7; 1; 2; 4; 2; 8];
  value_cons #10 1 [0; 1; 3; 7; 1; 2; 4; 2; 8];
  value_cons #10 0 [1; 3; 7; 1; 2; 4; 2; 8];
  value_cons #10 1 [3; 7; 1; 2; 4; 2; 8];
  value_cons #10 3 [7; 1; 2; 4; 2; 8];
  value_cons #10 7 [1; 2; 4; 2; 8];
  value_cons #10 1 [2; 4; 2; 8];
  value_cons #10 2 [4; 2; 8];
  value_cons #10 4 [2; 8];
  value_cons #10 2 [8];
  value_cons #10 8 [];
  ()
let value_next14_target_tail_18 () : Lemma (
    value #10 [2; 5; 6; 8; 7; 4; 2; 3; 0; 2; 6; 4; 3; 4; 8; 5; 7; 1] == 175843462032478652) =
  value_cons #10 2 [5; 6; 8; 7; 4; 2; 3; 0; 2; 6; 4; 3; 4; 8; 5; 7; 1];
  value_cons #10 5 [6; 8; 7; 4; 2; 3; 0; 2; 6; 4; 3; 4; 8; 5; 7; 1];
  value_cons #10 6 [8; 7; 4; 2; 3; 0; 2; 6; 4; 3; 4; 8; 5; 7; 1];
  value_cons #10 8 [7; 4; 2; 3; 0; 2; 6; 4; 3; 4; 8; 5; 7; 1];
  value_cons #10 7 [4; 2; 3; 0; 2; 6; 4; 3; 4; 8; 5; 7; 1];
  value_cons #10 4 [2; 3; 0; 2; 6; 4; 3; 4; 8; 5; 7; 1];
  value_cons #10 2 [3; 0; 2; 6; 4; 3; 4; 8; 5; 7; 1];
  value_cons #10 3 [0; 2; 6; 4; 3; 4; 8; 5; 7; 1];
  value_cons #10 0 [2; 6; 4; 3; 4; 8; 5; 7; 1];
  value_cons #10 2 [6; 4; 3; 4; 8; 5; 7; 1];
  value_cons #10 6 [4; 3; 4; 8; 5; 7; 1];
  value_cons #10 4 [3; 4; 8; 5; 7; 1];
  value_cons #10 3 [4; 8; 5; 7; 1];
  value_cons #10 4 [8; 5; 7; 1];
  value_cons #10 8 [5; 7; 1];
  value_cons #10 5 [7; 1];
  value_cons #10 7 [1];
  value_cons #10 1 [];
  ()

let value_next14_target () : Lemma (
    value next14_target == 1758434620324786522027424867) =
  value_cons #10 7 [6; 8; 4; 2; 4; 7; 2; 0; 2; 2; 5; 6; 8; 7; 4; 2; 3; 0; 2; 6; 4; 3; 4; 8; 5; 7; 1];
  value_cons #10 6 [8; 4; 2; 4; 7; 2; 0; 2; 2; 5; 6; 8; 7; 4; 2; 3; 0; 2; 6; 4; 3; 4; 8; 5; 7; 1];
  value_cons #10 8 [4; 2; 4; 7; 2; 0; 2; 2; 5; 6; 8; 7; 4; 2; 3; 0; 2; 6; 4; 3; 4; 8; 5; 7; 1];
  value_cons #10 4 [2; 4; 7; 2; 0; 2; 2; 5; 6; 8; 7; 4; 2; 3; 0; 2; 6; 4; 3; 4; 8; 5; 7; 1];
  value_cons #10 2 [4; 7; 2; 0; 2; 2; 5; 6; 8; 7; 4; 2; 3; 0; 2; 6; 4; 3; 4; 8; 5; 7; 1];
  value_cons #10 4 [7; 2; 0; 2; 2; 5; 6; 8; 7; 4; 2; 3; 0; 2; 6; 4; 3; 4; 8; 5; 7; 1];
  value_cons #10 7 [2; 0; 2; 2; 5; 6; 8; 7; 4; 2; 3; 0; 2; 6; 4; 3; 4; 8; 5; 7; 1];
  value_cons #10 2 [0; 2; 2; 5; 6; 8; 7; 4; 2; 3; 0; 2; 6; 4; 3; 4; 8; 5; 7; 1];
  value_cons #10 0 [2; 2; 5; 6; 8; 7; 4; 2; 3; 0; 2; 6; 4; 3; 4; 8; 5; 7; 1];
  value_cons #10 2 [2; 5; 6; 8; 7; 4; 2; 3; 0; 2; 6; 4; 3; 4; 8; 5; 7; 1];
  value_next14_target_tail_18 ();
  ()

let canonical_next14_reversed () : Lemma (canonical #10 next14_reversed) =
  assert (canonical #10 [8]);
  canonical_cons #10 2 [8];
  canonical_cons #10 4 [2; 8];
  canonical_cons #10 2 [4; 2; 8];
  canonical_cons #10 1 [2; 4; 2; 8];
  canonical_cons #10 7 [1; 2; 4; 2; 8];
  canonical_cons #10 3 [7; 1; 2; 4; 2; 8];
  canonical_cons #10 1 [3; 7; 1; 2; 4; 2; 8];
  canonical_cons #10 0 [1; 3; 7; 1; 2; 4; 2; 8];
  canonical_cons #10 1 [0; 1; 3; 7; 1; 2; 4; 2; 8];
  canonical_cons #10 6 [1; 0; 1; 3; 7; 1; 2; 4; 2; 8];
  canonical_cons #10 2 [6; 1; 0; 1; 3; 7; 1; 2; 4; 2; 8];
  canonical_cons #10 3 [2; 6; 1; 0; 1; 3; 7; 1; 2; 4; 2; 8];
  canonical_cons #10 9 [3; 2; 6; 1; 0; 1; 3; 7; 1; 2; 4; 2; 8];
  canonical_cons #10 3 [9; 3; 2; 6; 1; 0; 1; 3; 7; 1; 2; 4; 2; 8];
  canonical_cons #10 2 [3; 9; 3; 2; 6; 1; 0; 1; 3; 7; 1; 2; 4; 2; 8];
  canonical_cons #10 6 [2; 3; 9; 3; 2; 6; 1; 0; 1; 3; 7; 1; 2; 4; 2; 8];
  canonical_cons #10 1 [6; 2; 3; 9; 3; 2; 6; 1; 0; 1; 3; 7; 1; 2; 4; 2; 8];
  canonical_cons #10 0 [1; 6; 2; 3; 9; 3; 2; 6; 1; 0; 1; 3; 7; 1; 2; 4; 2; 8];
  canonical_cons #10 1 [0; 1; 6; 2; 3; 9; 3; 2; 6; 1; 0; 1; 3; 7; 1; 2; 4; 2; 8];
  canonical_cons #10 3 [1; 0; 1; 6; 2; 3; 9; 3; 2; 6; 1; 0; 1; 3; 7; 1; 2; 4; 2; 8];
  canonical_cons #10 7 [3; 1; 0; 1; 6; 2; 3; 9; 3; 2; 6; 1; 0; 1; 3; 7; 1; 2; 4; 2; 8];
  canonical_cons #10 1 [7; 3; 1; 0; 1; 6; 2; 3; 9; 3; 2; 6; 1; 0; 1; 3; 7; 1; 2; 4; 2; 8];
  canonical_cons #10 2 [1; 7; 3; 1; 0; 1; 6; 2; 3; 9; 3; 2; 6; 1; 0; 1; 3; 7; 1; 2; 4; 2; 8];
  canonical_cons #10 4 [2; 1; 7; 3; 1; 0; 1; 6; 2; 3; 9; 3; 2; 6; 1; 0; 1; 3; 7; 1; 2; 4; 2; 8];
  canonical_cons #10 3 [4; 2; 1; 7; 3; 1; 0; 1; 6; 2; 3; 9; 3; 2; 6; 1; 0; 1; 3; 7; 1; 2; 4; 2; 8];
  canonical_cons #10 9 [3; 4; 2; 1; 7; 3; 1; 0; 1; 6; 2; 3; 9; 3; 2; 6; 1; 0; 1; 3; 7; 1; 2; 4; 2; 8];
  ()

let canonical_next14_target () : Lemma (canonical #10 next14_target) =
  assert (canonical #10 [1]);
  canonical_cons #10 7 [1];
  canonical_cons #10 5 [7; 1];
  canonical_cons #10 8 [5; 7; 1];
  canonical_cons #10 4 [8; 5; 7; 1];
  canonical_cons #10 3 [4; 8; 5; 7; 1];
  canonical_cons #10 4 [3; 4; 8; 5; 7; 1];
  canonical_cons #10 6 [4; 3; 4; 8; 5; 7; 1];
  canonical_cons #10 2 [6; 4; 3; 4; 8; 5; 7; 1];
  canonical_cons #10 0 [2; 6; 4; 3; 4; 8; 5; 7; 1];
  canonical_cons #10 3 [0; 2; 6; 4; 3; 4; 8; 5; 7; 1];
  canonical_cons #10 2 [3; 0; 2; 6; 4; 3; 4; 8; 5; 7; 1];
  canonical_cons #10 4 [2; 3; 0; 2; 6; 4; 3; 4; 8; 5; 7; 1];
  canonical_cons #10 7 [4; 2; 3; 0; 2; 6; 4; 3; 4; 8; 5; 7; 1];
  canonical_cons #10 8 [7; 4; 2; 3; 0; 2; 6; 4; 3; 4; 8; 5; 7; 1];
  canonical_cons #10 6 [8; 7; 4; 2; 3; 0; 2; 6; 4; 3; 4; 8; 5; 7; 1];
  canonical_cons #10 5 [6; 8; 7; 4; 2; 3; 0; 2; 6; 4; 3; 4; 8; 5; 7; 1];
  canonical_cons #10 2 [5; 6; 8; 7; 4; 2; 3; 0; 2; 6; 4; 3; 4; 8; 5; 7; 1];
  canonical_cons #10 2 [2; 5; 6; 8; 7; 4; 2; 3; 0; 2; 6; 4; 3; 4; 8; 5; 7; 1];
  canonical_cons #10 0 [2; 2; 5; 6; 8; 7; 4; 2; 3; 0; 2; 6; 4; 3; 4; 8; 5; 7; 1];
  canonical_cons #10 2 [0; 2; 2; 5; 6; 8; 7; 4; 2; 3; 0; 2; 6; 4; 3; 4; 8; 5; 7; 1];
  canonical_cons #10 7 [2; 0; 2; 2; 5; 6; 8; 7; 4; 2; 3; 0; 2; 6; 4; 3; 4; 8; 5; 7; 1];
  canonical_cons #10 4 [7; 2; 0; 2; 2; 5; 6; 8; 7; 4; 2; 3; 0; 2; 6; 4; 3; 4; 8; 5; 7; 1];
  canonical_cons #10 2 [4; 7; 2; 0; 2; 2; 5; 6; 8; 7; 4; 2; 3; 0; 2; 6; 4; 3; 4; 8; 5; 7; 1];
  canonical_cons #10 4 [2; 4; 7; 2; 0; 2; 2; 5; 6; 8; 7; 4; 2; 3; 0; 2; 6; 4; 3; 4; 8; 5; 7; 1];
  canonical_cons #10 8 [4; 2; 4; 7; 2; 0; 2; 2; 5; 6; 8; 7; 4; 2; 3; 0; 2; 6; 4; 3; 4; 8; 5; 7; 1];
  canonical_cons #10 6 [8; 4; 2; 4; 7; 2; 0; 2; 2; 5; 6; 8; 7; 4; 2; 3; 0; 2; 6; 4; 3; 4; 8; 5; 7; 1];
  canonical_cons #10 7 [6; 8; 4; 2; 4; 7; 2; 0; 2; 2; 5; 6; 8; 7; 4; 2; 3; 0; 2; 6; 4; 3; 4; 8; 5; 7; 1];
  ()

let reverse_digits_next14_source () : Lemma (
    reverse_digits #10 next14_source == next14_reversed) =
  ReverseAddNext.canonical_next13_target ();
  reverse_list_next14_source ();
  value_next14_reversed ();
  canonical_next14_reversed ();
  reverse_digits_canonical #10 next14_source;
  normalize_value #10 (rev next14_source);
  assert (value (reverse_digits #10 next14_source) ==
    824217310162393261013712439);
  digits_of_nat_of_canonical #10 (reverse_digits #10 next14_source);
  digits_of_nat_of_canonical #10 next14_reversed;
  assert (reverse_digits #10 next14_source == next14_reversed);
  ()

let reverse_add_934217310162393261013712428_to_1758434620324786522027424867 () : Lemma (
    reverse_add #10 next14_source == next14_target) =
  ReverseAddNext.canonical_next13_target ();
  reverse_add_value #10 next14_source;
  ReverseAddNext.value_next13_target ();
  reverse_digits_next14_source ();
  value_next14_reversed ();
  value_next14_target ();
  assert (value (reverse_add #10 next14_source) ==
    1758434620324786522027424867);
  reverse_add_canonical #10 next14_source;
  digits_of_nat_of_canonical #10 (reverse_add #10 next14_source);
  canonical_next14_target ();
  digits_of_nat_of_canonical #10 next14_target;
  assert (reverse_add #10 next14_source == next14_target);
  ()

let trace_digits_profile_934217310162393261013712428 () : Lemma (
    trace_digits next14_source == next14_target) =
  reverse_add_934217310162393261013712428_to_1758434620324786522027424867 ();
  trace_digits_equals_reverse_add next14_source;
  assert (trace_digits next14_source == next14_target);
  ()

let trace_carries_next14_source () : Lemma (trace_carries next14_source ==
    [0; 1; 0; 0; 0; 0; 1; 0; 0; 0; 0; 1; 0; 0; 1; 0; 0; 1; 0; 0; 0; 0; 1; 0; 0; 0; 0; 1]) =
  reverse_list_next14_source ();
  assert (trace_carries next14_source ==
    (add_trace #10 next14_source next14_reversed 0).carries);
  add_trace_carries_step #10 8 9
    [2; 4; 2; 1; 7; 3; 1; 0; 1; 6; 2; 3; 9; 3; 2; 6; 1; 0; 1; 3; 7; 1; 2; 4; 3; 9]
    [3; 4; 2; 1; 7; 3; 1; 0; 1; 6; 2; 3; 9; 3; 2; 6; 1; 0; 1; 3; 7; 1; 2; 4; 2; 8] 0;
  add_trace_carries_step #10 2 3
    [4; 2; 1; 7; 3; 1; 0; 1; 6; 2; 3; 9; 3; 2; 6; 1; 0; 1; 3; 7; 1; 2; 4; 3; 9]
    [4; 2; 1; 7; 3; 1; 0; 1; 6; 2; 3; 9; 3; 2; 6; 1; 0; 1; 3; 7; 1; 2; 4; 2; 8] 1;
  add_trace_carries_step #10 4 4
    [2; 1; 7; 3; 1; 0; 1; 6; 2; 3; 9; 3; 2; 6; 1; 0; 1; 3; 7; 1; 2; 4; 3; 9]
    [2; 1; 7; 3; 1; 0; 1; 6; 2; 3; 9; 3; 2; 6; 1; 0; 1; 3; 7; 1; 2; 4; 2; 8] 0;
  add_trace_carries_step #10 2 2
    [1; 7; 3; 1; 0; 1; 6; 2; 3; 9; 3; 2; 6; 1; 0; 1; 3; 7; 1; 2; 4; 3; 9]
    [1; 7; 3; 1; 0; 1; 6; 2; 3; 9; 3; 2; 6; 1; 0; 1; 3; 7; 1; 2; 4; 2; 8] 0;
  add_trace_carries_step #10 1 1
    [7; 3; 1; 0; 1; 6; 2; 3; 9; 3; 2; 6; 1; 0; 1; 3; 7; 1; 2; 4; 3; 9]
    [7; 3; 1; 0; 1; 6; 2; 3; 9; 3; 2; 6; 1; 0; 1; 3; 7; 1; 2; 4; 2; 8] 0;
  add_trace_carries_step #10 7 7
    [3; 1; 0; 1; 6; 2; 3; 9; 3; 2; 6; 1; 0; 1; 3; 7; 1; 2; 4; 3; 9]
    [3; 1; 0; 1; 6; 2; 3; 9; 3; 2; 6; 1; 0; 1; 3; 7; 1; 2; 4; 2; 8] 0;
  add_trace_carries_step #10 3 3
    [1; 0; 1; 6; 2; 3; 9; 3; 2; 6; 1; 0; 1; 3; 7; 1; 2; 4; 3; 9]
    [1; 0; 1; 6; 2; 3; 9; 3; 2; 6; 1; 0; 1; 3; 7; 1; 2; 4; 2; 8] 1;
  add_trace_carries_step #10 1 1
    [0; 1; 6; 2; 3; 9; 3; 2; 6; 1; 0; 1; 3; 7; 1; 2; 4; 3; 9]
    [0; 1; 6; 2; 3; 9; 3; 2; 6; 1; 0; 1; 3; 7; 1; 2; 4; 2; 8] 0;
  add_trace_carries_step #10 0 0
    [1; 6; 2; 3; 9; 3; 2; 6; 1; 0; 1; 3; 7; 1; 2; 4; 3; 9]
    [1; 6; 2; 3; 9; 3; 2; 6; 1; 0; 1; 3; 7; 1; 2; 4; 2; 8] 0;
  add_trace_carries_step #10 1 1
    [6; 2; 3; 9; 3; 2; 6; 1; 0; 1; 3; 7; 1; 2; 4; 3; 9]
    [6; 2; 3; 9; 3; 2; 6; 1; 0; 1; 3; 7; 1; 2; 4; 2; 8] 0;
  add_trace_carries_step #10 6 6
    [2; 3; 9; 3; 2; 6; 1; 0; 1; 3; 7; 1; 2; 4; 3; 9]
    [2; 3; 9; 3; 2; 6; 1; 0; 1; 3; 7; 1; 2; 4; 2; 8] 0;
  add_trace_carries_step #10 2 2
    [3; 9; 3; 2; 6; 1; 0; 1; 3; 7; 1; 2; 4; 3; 9]
    [3; 9; 3; 2; 6; 1; 0; 1; 3; 7; 1; 2; 4; 2; 8] 1;
  add_trace_carries_step #10 3 3
    [9; 3; 2; 6; 1; 0; 1; 3; 7; 1; 2; 4; 3; 9]
    [9; 3; 2; 6; 1; 0; 1; 3; 7; 1; 2; 4; 2; 8] 0;
  add_trace_carries_step #10 9 9
    [3; 2; 6; 1; 0; 1; 3; 7; 1; 2; 4; 3; 9]
    [3; 2; 6; 1; 0; 1; 3; 7; 1; 2; 4; 2; 8] 0;
  add_trace_carries_step #10 3 3
    [2; 6; 1; 0; 1; 3; 7; 1; 2; 4; 3; 9]
    [2; 6; 1; 0; 1; 3; 7; 1; 2; 4; 2; 8] 1;
  add_trace_carries_step #10 2 2
    [6; 1; 0; 1; 3; 7; 1; 2; 4; 3; 9]
    [6; 1; 0; 1; 3; 7; 1; 2; 4; 2; 8] 0;
  add_trace_carries_step #10 6 6
    [1; 0; 1; 3; 7; 1; 2; 4; 3; 9]
    [1; 0; 1; 3; 7; 1; 2; 4; 2; 8] 0;
  add_trace_carries_step #10 1 1
    [0; 1; 3; 7; 1; 2; 4; 3; 9]
    [0; 1; 3; 7; 1; 2; 4; 2; 8] 1;
  add_trace_carries_step #10 0 0
    [1; 3; 7; 1; 2; 4; 3; 9]
    [1; 3; 7; 1; 2; 4; 2; 8] 0;
  add_trace_carries_step #10 1 1
    [3; 7; 1; 2; 4; 3; 9]
    [3; 7; 1; 2; 4; 2; 8] 0;
  add_trace_carries_step #10 3 3
    [7; 1; 2; 4; 3; 9]
    [7; 1; 2; 4; 2; 8] 0;
  add_trace_carries_step #10 7 7
    [1; 2; 4; 3; 9]
    [1; 2; 4; 2; 8] 0;
  add_trace_carries_step #10 1 1
    [2; 4; 3; 9]
    [2; 4; 2; 8] 1;
  add_trace_carries_step #10 2 2
    [4; 3; 9]
    [4; 2; 8] 0;
  add_trace_carries_step #10 4 4
    [3; 9]
    [2; 8] 0;
  add_trace_carries_step #10 3 2
    [9]
    [8] 0;
  add_trace_carries_step #10 9 8
    []
    [] 0;
  assert ((add_trace #10 [] [] 1).carries == [1]);
  assert ((add_trace #10 next14_source next14_reversed 0).carries ==
    [0; 1; 0; 0; 0; 0; 1; 0; 0; 0; 0; 1; 0; 0; 1; 0; 0; 1; 0; 0; 0; 0; 1; 0; 0; 0; 0; 1]);
  ()

let trace_profile_shape_934217310162393261013712428 () : Lemma (
    length (trace_digits next14_source) == length next14_source + 1) =
  trace_digits_profile_934217310162393261013712428 ();
  length_of_eq #(digit 10) (trace_digits next14_source) next14_target;
  assert (length next14_target == length next14_source + 1);
  ()

let trace_profile_final_carry_934217310162393261013712428 () : Lemma (
    nth (trace_carries next14_source) (length next14_source) == Some 1) =
  trace_profile_shape_934217310162393261013712428 ();
  ReverseAddContinuation.final_carry_from_overflow_length next14_source;
  ()

let trace_profile_sums_934217310162393261013712428 () : Lemma (
    trace_sum_at next14_source 0 == 17 /\
    trace_sum_at next14_source 1 == 5 /\
    trace_sum_at next14_source 26 == 17) =
  reverse_list_next14_source ();
  ()

let trace_profile_carry_facts_934217310162393261013712428 () : Lemma (
    trace_carry_at next14_source 1 == 1 /\
    trace_carry_at next14_source 26 == 0 /\
    trace_carry_at next14_source 2 == 0 /\
    trace_carry_at next14_source 27 == 1) =
  trace_carries_next14_source ();
  assert (trace_carries next14_source ==
    [0; 1; 0; 0; 0; 0; 1; 0; 0; 0; 0; 1; 0; 0; 1; 0; 0; 1; 0; 0; 0; 0; 1; 0; 0; 0; 0; 1]);
  ()

let overflow_precondition_934217310162393261013712428 () : Lemma (
    canonical #10 next14_source /\
    next14_source <> [] /\
    length (trace_digits next14_source) == length next14_source + 1 /\
    nth (trace_carries next14_source) (length next14_source) == Some 1 /\
    1 <= trace_sum_at next14_source 0 /\
    trace_sum_at next14_source 0 <= 18 /\
    trace_sum_at next14_source 0 <> 10 /\
    exists (i:nat). 0 < i /\ i < length next14_source /\
      trace_sum_at next14_source i +
          trace_sum_at next14_source (length next14_source - i) +
          trace_carry_at next14_source i +
          trace_carry_at next14_source (length next14_source - i) >=
        10 + 10 *
          (trace_carry_at next14_source (i + 1) +
           trace_carry_at next14_source (length next14_source - i + 1))) =
  ReverseAddNext.canonical_next13_target ();
  assert (next14_source <> []);
  trace_profile_shape_934217310162393261013712428 ();
  trace_profile_final_carry_934217310162393261013712428 ();
  trace_profile_sums_934217310162393261013712428 ();
  trace_profile_carry_facts_934217310162393261013712428 ();
  assert (length (trace_digits next14_source) == length next14_source + 1);
  assert (nth (trace_carries next14_source)
    (length next14_source) == Some 1);
  assert (trace_sum_at next14_source 0 == 17);
  assert (trace_sum_at next14_source 1 == 5);
  assert (trace_sum_at next14_source 26 == 17);
  assert (trace_carry_at next14_source 1 == 1);
  assert (trace_carry_at next14_source 26 == 0);
  assert (trace_carry_at next14_source 2 == 0);
  assert (trace_carry_at next14_source 27 == 1);
  assert (1 <= trace_sum_at next14_source 0 /\
    trace_sum_at next14_source 0 <= 18);
  assert (trace_sum_at next14_source 0 <> 10);
  let n : nat = length next14_source in
  assert (0 < 1 /\ 1 < n);
  assert (trace_sum_at next14_source 1 +
      trace_sum_at next14_source (n - 1) +
      trace_carry_at next14_source 1 +
      trace_carry_at next14_source (n - 1) >=
    10 + 10 *
      (trace_carry_at next14_source 2 +
       trace_carry_at next14_source (n - 1 + 1)));
  exists_intro
    (fun (i:nat) -> 0 < i /\ i < n /\
      trace_sum_at next14_source i +
          trace_sum_at next14_source (n - i) +
          trace_carry_at next14_source i +
          trace_carry_at next14_source (n - i) >=
        10 + 10 *
          (trace_carry_at next14_source (i + 1) +
           trace_carry_at next14_source (n - i + 1)))
    1;
  ()

let local_profile_witness_1758434620324786522027424867 () : Lemma (
    trace_local_profile_complement_witness next14_target) =
  overflow_precondition_934217310162393261013712428 ();
  reverse_add_934217310162393261013712428_to_1758434620324786522027424867 ();
  overflow_internal_cell_implies_next_witness next14_source;
  ()

let next15_source : numeral 10 = next14_target

let next15_reversed : numeral 10 =
  [1; 7; 5; 8; 4; 3; 4; 6; 2; 0; 3; 2; 4; 7; 8; 6; 5; 2; 2; 0; 2; 7; 4; 2; 4; 8; 6; 7]

let next15_target : numeral 10 =
  [8; 3; 4; 3; 7; 7; 1; 9; 2; 2; 5; 7; 0; 6; 6; 1; 8; 5; 2; 2; 8; 1; 8; 6; 2; 4; 4; 9]

let reverse_list_next15_source () : Lemma (rev next15_source == next15_reversed) =
  assert (rev [1] == [1]);
  rev_cons 7 [1];
  rev_cons 5 [7; 1];
  rev_cons 8 [5; 7; 1];
  rev_cons 4 [8; 5; 7; 1];
  rev_cons 3 [4; 8; 5; 7; 1];
  rev_cons 4 [3; 4; 8; 5; 7; 1];
  rev_cons 6 [4; 3; 4; 8; 5; 7; 1];
  rev_cons 2 [6; 4; 3; 4; 8; 5; 7; 1];
  rev_cons 0 [2; 6; 4; 3; 4; 8; 5; 7; 1];
  rev_cons 3 [0; 2; 6; 4; 3; 4; 8; 5; 7; 1];
  rev_cons 2 [3; 0; 2; 6; 4; 3; 4; 8; 5; 7; 1];
  rev_cons 4 [2; 3; 0; 2; 6; 4; 3; 4; 8; 5; 7; 1];
  rev_cons 7 [4; 2; 3; 0; 2; 6; 4; 3; 4; 8; 5; 7; 1];
  rev_cons 8 [7; 4; 2; 3; 0; 2; 6; 4; 3; 4; 8; 5; 7; 1];
  rev_cons 6 [8; 7; 4; 2; 3; 0; 2; 6; 4; 3; 4; 8; 5; 7; 1];
  rev_cons 5 [6; 8; 7; 4; 2; 3; 0; 2; 6; 4; 3; 4; 8; 5; 7; 1];
  rev_cons 2 [5; 6; 8; 7; 4; 2; 3; 0; 2; 6; 4; 3; 4; 8; 5; 7; 1];
  rev_cons 2 [2; 5; 6; 8; 7; 4; 2; 3; 0; 2; 6; 4; 3; 4; 8; 5; 7; 1];
  rev_cons 0 [2; 2; 5; 6; 8; 7; 4; 2; 3; 0; 2; 6; 4; 3; 4; 8; 5; 7; 1];
  rev_cons 2 [0; 2; 2; 5; 6; 8; 7; 4; 2; 3; 0; 2; 6; 4; 3; 4; 8; 5; 7; 1];
  rev_cons 7 [2; 0; 2; 2; 5; 6; 8; 7; 4; 2; 3; 0; 2; 6; 4; 3; 4; 8; 5; 7; 1];
  rev_cons 4 [7; 2; 0; 2; 2; 5; 6; 8; 7; 4; 2; 3; 0; 2; 6; 4; 3; 4; 8; 5; 7; 1];
  rev_cons 2 [4; 7; 2; 0; 2; 2; 5; 6; 8; 7; 4; 2; 3; 0; 2; 6; 4; 3; 4; 8; 5; 7; 1];
  rev_cons 4 [2; 4; 7; 2; 0; 2; 2; 5; 6; 8; 7; 4; 2; 3; 0; 2; 6; 4; 3; 4; 8; 5; 7; 1];
  rev_cons 8 [4; 2; 4; 7; 2; 0; 2; 2; 5; 6; 8; 7; 4; 2; 3; 0; 2; 6; 4; 3; 4; 8; 5; 7; 1];
  rev_cons 6 [8; 4; 2; 4; 7; 2; 0; 2; 2; 5; 6; 8; 7; 4; 2; 3; 0; 2; 6; 4; 3; 4; 8; 5; 7; 1];
  rev_cons 7 [6; 8; 4; 2; 4; 7; 2; 0; 2; 2; 5; 6; 8; 7; 4; 2; 3; 0; 2; 6; 4; 3; 4; 8; 5; 7; 1];
  ()

let value_next15_reversed_tail_18 () : Lemma (
    value #10 [3; 2; 4; 7; 8; 6; 5; 2; 2; 0; 2; 7; 4; 2; 4; 8; 6; 7] == 768424720225687423) =
  value_cons #10 3 [2; 4; 7; 8; 6; 5; 2; 2; 0; 2; 7; 4; 2; 4; 8; 6; 7];
  value_cons #10 2 [4; 7; 8; 6; 5; 2; 2; 0; 2; 7; 4; 2; 4; 8; 6; 7];
  value_cons #10 4 [7; 8; 6; 5; 2; 2; 0; 2; 7; 4; 2; 4; 8; 6; 7];
  value_cons #10 7 [8; 6; 5; 2; 2; 0; 2; 7; 4; 2; 4; 8; 6; 7];
  value_cons #10 8 [6; 5; 2; 2; 0; 2; 7; 4; 2; 4; 8; 6; 7];
  value_cons #10 6 [5; 2; 2; 0; 2; 7; 4; 2; 4; 8; 6; 7];
  value_cons #10 5 [2; 2; 0; 2; 7; 4; 2; 4; 8; 6; 7];
  value_cons #10 2 [2; 0; 2; 7; 4; 2; 4; 8; 6; 7];
  value_cons #10 2 [0; 2; 7; 4; 2; 4; 8; 6; 7];
  value_cons #10 0 [2; 7; 4; 2; 4; 8; 6; 7];
  value_cons #10 2 [7; 4; 2; 4; 8; 6; 7];
  value_cons #10 7 [4; 2; 4; 8; 6; 7];
  value_cons #10 4 [2; 4; 8; 6; 7];
  value_cons #10 2 [4; 8; 6; 7];
  value_cons #10 4 [8; 6; 7];
  value_cons #10 8 [6; 7];
  value_cons #10 6 [7];
  value_cons #10 7 [];
  ()

let value_next15_reversed () : Lemma (
    value next15_reversed == 7684247202256874230264348571) =
  value_cons #10 1 [7; 5; 8; 4; 3; 4; 6; 2; 0; 3; 2; 4; 7; 8; 6; 5; 2; 2; 0; 2; 7; 4; 2; 4; 8; 6; 7];
  value_cons #10 7 [5; 8; 4; 3; 4; 6; 2; 0; 3; 2; 4; 7; 8; 6; 5; 2; 2; 0; 2; 7; 4; 2; 4; 8; 6; 7];
  value_cons #10 5 [8; 4; 3; 4; 6; 2; 0; 3; 2; 4; 7; 8; 6; 5; 2; 2; 0; 2; 7; 4; 2; 4; 8; 6; 7];
  value_cons #10 8 [4; 3; 4; 6; 2; 0; 3; 2; 4; 7; 8; 6; 5; 2; 2; 0; 2; 7; 4; 2; 4; 8; 6; 7];
  value_cons #10 4 [3; 4; 6; 2; 0; 3; 2; 4; 7; 8; 6; 5; 2; 2; 0; 2; 7; 4; 2; 4; 8; 6; 7];
  value_cons #10 3 [4; 6; 2; 0; 3; 2; 4; 7; 8; 6; 5; 2; 2; 0; 2; 7; 4; 2; 4; 8; 6; 7];
  value_cons #10 4 [6; 2; 0; 3; 2; 4; 7; 8; 6; 5; 2; 2; 0; 2; 7; 4; 2; 4; 8; 6; 7];
  value_cons #10 6 [2; 0; 3; 2; 4; 7; 8; 6; 5; 2; 2; 0; 2; 7; 4; 2; 4; 8; 6; 7];
  value_cons #10 2 [0; 3; 2; 4; 7; 8; 6; 5; 2; 2; 0; 2; 7; 4; 2; 4; 8; 6; 7];
  value_cons #10 0 [3; 2; 4; 7; 8; 6; 5; 2; 2; 0; 2; 7; 4; 2; 4; 8; 6; 7];
  value_next15_reversed_tail_18 ();
  ()

let value_next15_target_tail_18 () : Lemma (
    value #10 [5; 7; 0; 6; 6; 1; 8; 5; 2; 2; 8; 1; 8; 6; 2; 4; 4; 9] == 944268182258166075) =
  value_cons #10 5 [7; 0; 6; 6; 1; 8; 5; 2; 2; 8; 1; 8; 6; 2; 4; 4; 9];
  value_cons #10 7 [0; 6; 6; 1; 8; 5; 2; 2; 8; 1; 8; 6; 2; 4; 4; 9];
  value_cons #10 0 [6; 6; 1; 8; 5; 2; 2; 8; 1; 8; 6; 2; 4; 4; 9];
  value_cons #10 6 [6; 1; 8; 5; 2; 2; 8; 1; 8; 6; 2; 4; 4; 9];
  value_cons #10 6 [1; 8; 5; 2; 2; 8; 1; 8; 6; 2; 4; 4; 9];
  value_cons #10 1 [8; 5; 2; 2; 8; 1; 8; 6; 2; 4; 4; 9];
  value_cons #10 8 [5; 2; 2; 8; 1; 8; 6; 2; 4; 4; 9];
  value_cons #10 5 [2; 2; 8; 1; 8; 6; 2; 4; 4; 9];
  value_cons #10 2 [2; 8; 1; 8; 6; 2; 4; 4; 9];
  value_cons #10 2 [8; 1; 8; 6; 2; 4; 4; 9];
  value_cons #10 8 [1; 8; 6; 2; 4; 4; 9];
  value_cons #10 1 [8; 6; 2; 4; 4; 9];
  value_cons #10 8 [6; 2; 4; 4; 9];
  value_cons #10 6 [2; 4; 4; 9];
  value_cons #10 2 [4; 4; 9];
  value_cons #10 4 [4; 9];
  value_cons #10 4 [9];
  value_cons #10 9 [];
  ()

let value_next15_target () : Lemma (
    value next15_target == 9442681822581660752291773438) =
  value_cons #10 8 [3; 4; 3; 7; 7; 1; 9; 2; 2; 5; 7; 0; 6; 6; 1; 8; 5; 2; 2; 8; 1; 8; 6; 2; 4; 4; 9];
  value_cons #10 3 [4; 3; 7; 7; 1; 9; 2; 2; 5; 7; 0; 6; 6; 1; 8; 5; 2; 2; 8; 1; 8; 6; 2; 4; 4; 9];
  value_cons #10 4 [3; 7; 7; 1; 9; 2; 2; 5; 7; 0; 6; 6; 1; 8; 5; 2; 2; 8; 1; 8; 6; 2; 4; 4; 9];
  value_cons #10 3 [7; 7; 1; 9; 2; 2; 5; 7; 0; 6; 6; 1; 8; 5; 2; 2; 8; 1; 8; 6; 2; 4; 4; 9];
  value_cons #10 7 [7; 1; 9; 2; 2; 5; 7; 0; 6; 6; 1; 8; 5; 2; 2; 8; 1; 8; 6; 2; 4; 4; 9];
  value_cons #10 7 [1; 9; 2; 2; 5; 7; 0; 6; 6; 1; 8; 5; 2; 2; 8; 1; 8; 6; 2; 4; 4; 9];
  value_cons #10 1 [9; 2; 2; 5; 7; 0; 6; 6; 1; 8; 5; 2; 2; 8; 1; 8; 6; 2; 4; 4; 9];
  value_cons #10 9 [2; 2; 5; 7; 0; 6; 6; 1; 8; 5; 2; 2; 8; 1; 8; 6; 2; 4; 4; 9];
  value_cons #10 2 [2; 5; 7; 0; 6; 6; 1; 8; 5; 2; 2; 8; 1; 8; 6; 2; 4; 4; 9];
  value_cons #10 2 [5; 7; 0; 6; 6; 1; 8; 5; 2; 2; 8; 1; 8; 6; 2; 4; 4; 9];
  value_next15_target_tail_18 ();
  ()

let canonical_next15_reversed () : Lemma (canonical #10 next15_reversed) =
  assert (canonical #10 [7]);
  canonical_cons #10 6 [7];
  canonical_cons #10 8 [6; 7];
  canonical_cons #10 4 [8; 6; 7];
  canonical_cons #10 2 [4; 8; 6; 7];
  canonical_cons #10 4 [2; 4; 8; 6; 7];
  canonical_cons #10 7 [4; 2; 4; 8; 6; 7];
  canonical_cons #10 2 [7; 4; 2; 4; 8; 6; 7];
  canonical_cons #10 0 [2; 7; 4; 2; 4; 8; 6; 7];
  canonical_cons #10 2 [0; 2; 7; 4; 2; 4; 8; 6; 7];
  canonical_cons #10 2 [2; 0; 2; 7; 4; 2; 4; 8; 6; 7];
  canonical_cons #10 5 [2; 2; 0; 2; 7; 4; 2; 4; 8; 6; 7];
  canonical_cons #10 6 [5; 2; 2; 0; 2; 7; 4; 2; 4; 8; 6; 7];
  canonical_cons #10 8 [6; 5; 2; 2; 0; 2; 7; 4; 2; 4; 8; 6; 7];
  canonical_cons #10 7 [8; 6; 5; 2; 2; 0; 2; 7; 4; 2; 4; 8; 6; 7];
  canonical_cons #10 4 [7; 8; 6; 5; 2; 2; 0; 2; 7; 4; 2; 4; 8; 6; 7];
  canonical_cons #10 2 [4; 7; 8; 6; 5; 2; 2; 0; 2; 7; 4; 2; 4; 8; 6; 7];
  canonical_cons #10 3 [2; 4; 7; 8; 6; 5; 2; 2; 0; 2; 7; 4; 2; 4; 8; 6; 7];
  canonical_cons #10 0 [3; 2; 4; 7; 8; 6; 5; 2; 2; 0; 2; 7; 4; 2; 4; 8; 6; 7];
  canonical_cons #10 2 [0; 3; 2; 4; 7; 8; 6; 5; 2; 2; 0; 2; 7; 4; 2; 4; 8; 6; 7];
  canonical_cons #10 6 [2; 0; 3; 2; 4; 7; 8; 6; 5; 2; 2; 0; 2; 7; 4; 2; 4; 8; 6; 7];
  canonical_cons #10 4 [6; 2; 0; 3; 2; 4; 7; 8; 6; 5; 2; 2; 0; 2; 7; 4; 2; 4; 8; 6; 7];
  canonical_cons #10 3 [4; 6; 2; 0; 3; 2; 4; 7; 8; 6; 5; 2; 2; 0; 2; 7; 4; 2; 4; 8; 6; 7];
  canonical_cons #10 4 [3; 4; 6; 2; 0; 3; 2; 4; 7; 8; 6; 5; 2; 2; 0; 2; 7; 4; 2; 4; 8; 6; 7];
  canonical_cons #10 8 [4; 3; 4; 6; 2; 0; 3; 2; 4; 7; 8; 6; 5; 2; 2; 0; 2; 7; 4; 2; 4; 8; 6; 7];
  canonical_cons #10 5 [8; 4; 3; 4; 6; 2; 0; 3; 2; 4; 7; 8; 6; 5; 2; 2; 0; 2; 7; 4; 2; 4; 8; 6; 7];
  canonical_cons #10 7 [5; 8; 4; 3; 4; 6; 2; 0; 3; 2; 4; 7; 8; 6; 5; 2; 2; 0; 2; 7; 4; 2; 4; 8; 6; 7];
  canonical_cons #10 1 [7; 5; 8; 4; 3; 4; 6; 2; 0; 3; 2; 4; 7; 8; 6; 5; 2; 2; 0; 2; 7; 4; 2; 4; 8; 6; 7];
  ()

let canonical_next15_target () : Lemma (canonical #10 next15_target) =
  assert (canonical #10 [9]);
  canonical_cons #10 4 [9];
  canonical_cons #10 4 [4; 9];
  canonical_cons #10 2 [4; 4; 9];
  canonical_cons #10 6 [2; 4; 4; 9];
  canonical_cons #10 8 [6; 2; 4; 4; 9];
  canonical_cons #10 1 [8; 6; 2; 4; 4; 9];
  canonical_cons #10 8 [1; 8; 6; 2; 4; 4; 9];
  canonical_cons #10 2 [8; 1; 8; 6; 2; 4; 4; 9];
  canonical_cons #10 2 [2; 8; 1; 8; 6; 2; 4; 4; 9];
  canonical_cons #10 5 [2; 2; 8; 1; 8; 6; 2; 4; 4; 9];
  canonical_cons #10 8 [5; 2; 2; 8; 1; 8; 6; 2; 4; 4; 9];
  canonical_cons #10 1 [8; 5; 2; 2; 8; 1; 8; 6; 2; 4; 4; 9];
  canonical_cons #10 6 [1; 8; 5; 2; 2; 8; 1; 8; 6; 2; 4; 4; 9];
  canonical_cons #10 6 [6; 1; 8; 5; 2; 2; 8; 1; 8; 6; 2; 4; 4; 9];
  canonical_cons #10 0 [6; 6; 1; 8; 5; 2; 2; 8; 1; 8; 6; 2; 4; 4; 9];
  canonical_cons #10 7 [0; 6; 6; 1; 8; 5; 2; 2; 8; 1; 8; 6; 2; 4; 4; 9];
  canonical_cons #10 5 [7; 0; 6; 6; 1; 8; 5; 2; 2; 8; 1; 8; 6; 2; 4; 4; 9];
  canonical_cons #10 2 [5; 7; 0; 6; 6; 1; 8; 5; 2; 2; 8; 1; 8; 6; 2; 4; 4; 9];
  canonical_cons #10 2 [2; 5; 7; 0; 6; 6; 1; 8; 5; 2; 2; 8; 1; 8; 6; 2; 4; 4; 9];
  canonical_cons #10 9 [2; 2; 5; 7; 0; 6; 6; 1; 8; 5; 2; 2; 8; 1; 8; 6; 2; 4; 4; 9];
  canonical_cons #10 1 [9; 2; 2; 5; 7; 0; 6; 6; 1; 8; 5; 2; 2; 8; 1; 8; 6; 2; 4; 4; 9];
  canonical_cons #10 7 [1; 9; 2; 2; 5; 7; 0; 6; 6; 1; 8; 5; 2; 2; 8; 1; 8; 6; 2; 4; 4; 9];
  canonical_cons #10 7 [7; 1; 9; 2; 2; 5; 7; 0; 6; 6; 1; 8; 5; 2; 2; 8; 1; 8; 6; 2; 4; 4; 9];
  canonical_cons #10 3 [7; 7; 1; 9; 2; 2; 5; 7; 0; 6; 6; 1; 8; 5; 2; 2; 8; 1; 8; 6; 2; 4; 4; 9];
  canonical_cons #10 4 [3; 7; 7; 1; 9; 2; 2; 5; 7; 0; 6; 6; 1; 8; 5; 2; 2; 8; 1; 8; 6; 2; 4; 4; 9];
  canonical_cons #10 3 [4; 3; 7; 7; 1; 9; 2; 2; 5; 7; 0; 6; 6; 1; 8; 5; 2; 2; 8; 1; 8; 6; 2; 4; 4; 9];
  canonical_cons #10 8 [3; 4; 3; 7; 7; 1; 9; 2; 2; 5; 7; 0; 6; 6; 1; 8; 5; 2; 2; 8; 1; 8; 6; 2; 4; 4; 9];
  ()

let reverse_digits_next15_source () : Lemma (
    reverse_digits #10 next15_source == next15_reversed) =
  ReverseAddNext.canonical_next14_target ();
  reverse_list_next15_source ();
  value_next15_reversed ();
  canonical_next15_reversed ();
  reverse_digits_canonical #10 next15_source;
  normalize_value #10 (rev next15_source);
  assert (value (reverse_digits #10 next15_source) ==
    7684247202256874230264348571);
  digits_of_nat_of_canonical #10 (reverse_digits #10 next15_source);
  digits_of_nat_of_canonical #10 next15_reversed;
  assert (reverse_digits #10 next15_source == next15_reversed);
  ()

let reverse_add_1758434620324786522027424867_to_9442681822581660752291773438 () : Lemma (
    reverse_add #10 next15_source == next15_target) =
  ReverseAddNext.canonical_next14_target ();
  reverse_add_value #10 next15_source;
  ReverseAddNext.value_next14_target ();
  reverse_digits_next15_source ();
  value_next15_reversed ();
  value_next15_target ();
  assert (value (reverse_add #10 next15_source) ==
    9442681822581660752291773438);
  reverse_add_canonical #10 next15_source;
  digits_of_nat_of_canonical #10 (reverse_add #10 next15_source);
  canonical_next15_target ();
  digits_of_nat_of_canonical #10 next15_target;
  assert (reverse_add #10 next15_source == next15_target);
  ()

let trace_digits_profile_1758434620324786522027424867 () : Lemma (
    trace_digits next15_source == next15_target) =
  reverse_add_1758434620324786522027424867_to_9442681822581660752291773438 ();
  trace_digits_equals_reverse_add next15_source;
  assert (trace_digits next15_source == next15_target);
  ()

let trace_profile_shape_1758434620324786522027424867 () : Lemma (
    length (trace_digits next15_source) == length next15_source) =
  trace_digits_profile_1758434620324786522027424867 ();
  length_of_eq #(digit 10) (trace_digits next15_source) next15_target;
  assert (length next15_target == length next15_source);
  ()

let trace_profile_final_carry_1758434620324786522027424867 () : Lemma (
    nth (trace_carries next15_source) (length next15_source) == Some 0) =
  trace_profile_shape_1758434620324786522027424867 ();
  final_carry_from_length next15_source;
  ()

let local_profile_witness_9442681822581660752291773438 () : Lemma (
    trace_local_profile_complement_witness next15_target) =
  ReverseAddNext.canonical_next14_target ();
  assert (next15_source <> []);
  trace_profile_shape_1758434620324786522027424867 ();
  trace_profile_final_carry_1758434620324786522027424867 ();
  assert (trace_sum_at next15_source 0 == 8);
  reverse_add_1758434620324786522027424867_to_9442681822581660752291773438 ();
  no_overflow_outer_sum_6_to_9_implies_next_witness next15_source;
  ()

let next16_source : numeral 10 = next15_target

let next16_reversed : numeral 10 =
  [9; 4; 4; 2; 6; 8; 1; 8; 2; 2; 5; 8; 1; 6; 6; 0; 7; 5; 2; 2; 9; 1; 7; 7; 3; 4; 3; 8]

let next16_target : numeral 10 =
  [7; 8; 8; 5; 3; 6; 3; 7; 5; 4; 0; 6; 2; 2; 3; 2; 5; 1; 5; 4; 7; 3; 5; 4; 6; 8; 7; 7; 1]

let reverse_list_next16_source () : Lemma (rev next16_source == next16_reversed) =
  assert (rev [9] == [9]);
  rev_cons 4 [9];
  rev_cons 4 [4; 9];
  rev_cons 2 [4; 4; 9];
  rev_cons 6 [2; 4; 4; 9];
  rev_cons 8 [6; 2; 4; 4; 9];
  rev_cons 1 [8; 6; 2; 4; 4; 9];
  rev_cons 8 [1; 8; 6; 2; 4; 4; 9];
  rev_cons 2 [8; 1; 8; 6; 2; 4; 4; 9];
  rev_cons 2 [2; 8; 1; 8; 6; 2; 4; 4; 9];
  rev_cons 5 [2; 2; 8; 1; 8; 6; 2; 4; 4; 9];
  rev_cons 8 [5; 2; 2; 8; 1; 8; 6; 2; 4; 4; 9];
  rev_cons 1 [8; 5; 2; 2; 8; 1; 8; 6; 2; 4; 4; 9];
  rev_cons 6 [1; 8; 5; 2; 2; 8; 1; 8; 6; 2; 4; 4; 9];
  rev_cons 6 [6; 1; 8; 5; 2; 2; 8; 1; 8; 6; 2; 4; 4; 9];
  rev_cons 0 [6; 6; 1; 8; 5; 2; 2; 8; 1; 8; 6; 2; 4; 4; 9];
  rev_cons 7 [0; 6; 6; 1; 8; 5; 2; 2; 8; 1; 8; 6; 2; 4; 4; 9];
  rev_cons 5 [7; 0; 6; 6; 1; 8; 5; 2; 2; 8; 1; 8; 6; 2; 4; 4; 9];
  rev_cons 2 [5; 7; 0; 6; 6; 1; 8; 5; 2; 2; 8; 1; 8; 6; 2; 4; 4; 9];
  rev_cons 2 [2; 5; 7; 0; 6; 6; 1; 8; 5; 2; 2; 8; 1; 8; 6; 2; 4; 4; 9];
  rev_cons 9 [2; 2; 5; 7; 0; 6; 6; 1; 8; 5; 2; 2; 8; 1; 8; 6; 2; 4; 4; 9];
  rev_cons 1 [9; 2; 2; 5; 7; 0; 6; 6; 1; 8; 5; 2; 2; 8; 1; 8; 6; 2; 4; 4; 9];
  rev_cons 7 [1; 9; 2; 2; 5; 7; 0; 6; 6; 1; 8; 5; 2; 2; 8; 1; 8; 6; 2; 4; 4; 9];
  rev_cons 7 [7; 1; 9; 2; 2; 5; 7; 0; 6; 6; 1; 8; 5; 2; 2; 8; 1; 8; 6; 2; 4; 4; 9];
  rev_cons 3 [7; 7; 1; 9; 2; 2; 5; 7; 0; 6; 6; 1; 8; 5; 2; 2; 8; 1; 8; 6; 2; 4; 4; 9];
  rev_cons 4 [3; 7; 7; 1; 9; 2; 2; 5; 7; 0; 6; 6; 1; 8; 5; 2; 2; 8; 1; 8; 6; 2; 4; 4; 9];
  rev_cons 3 [4; 3; 7; 7; 1; 9; 2; 2; 5; 7; 0; 6; 6; 1; 8; 5; 2; 2; 8; 1; 8; 6; 2; 4; 4; 9];
  rev_cons 8 [3; 4; 3; 7; 7; 1; 9; 2; 2; 5; 7; 0; 6; 6; 1; 8; 5; 2; 2; 8; 1; 8; 6; 2; 4; 4; 9];
  ()

let value_next16_reversed_tail_18 () : Lemma (
    value #10 [5; 8; 1; 6; 6; 0; 7; 5; 2; 2; 9; 1; 7; 7; 3; 4; 3; 8] == 834377192257066185) =
  value_cons #10 5 [8; 1; 6; 6; 0; 7; 5; 2; 2; 9; 1; 7; 7; 3; 4; 3; 8];
  value_cons #10 8 [1; 6; 6; 0; 7; 5; 2; 2; 9; 1; 7; 7; 3; 4; 3; 8];
  value_cons #10 1 [6; 6; 0; 7; 5; 2; 2; 9; 1; 7; 7; 3; 4; 3; 8];
  value_cons #10 6 [6; 0; 7; 5; 2; 2; 9; 1; 7; 7; 3; 4; 3; 8];
  value_cons #10 6 [0; 7; 5; 2; 2; 9; 1; 7; 7; 3; 4; 3; 8];
  value_cons #10 0 [7; 5; 2; 2; 9; 1; 7; 7; 3; 4; 3; 8];
  value_cons #10 7 [5; 2; 2; 9; 1; 7; 7; 3; 4; 3; 8];
  value_cons #10 5 [2; 2; 9; 1; 7; 7; 3; 4; 3; 8];
  value_cons #10 2 [2; 9; 1; 7; 7; 3; 4; 3; 8];
  value_cons #10 2 [9; 1; 7; 7; 3; 4; 3; 8];
  value_cons #10 9 [1; 7; 7; 3; 4; 3; 8];
  value_cons #10 1 [7; 7; 3; 4; 3; 8];
  value_cons #10 7 [7; 3; 4; 3; 8];
  value_cons #10 7 [3; 4; 3; 8];
  value_cons #10 3 [4; 3; 8];
  value_cons #10 4 [3; 8];
  value_cons #10 3 [8];
  value_cons #10 8 [];
  ()

let value_next16_reversed () : Lemma (
    value next16_reversed == 8343771922570661852281862449) =
  value_cons #10 9 [4; 4; 2; 6; 8; 1; 8; 2; 2; 5; 8; 1; 6; 6; 0; 7; 5; 2; 2; 9; 1; 7; 7; 3; 4; 3; 8];
  value_cons #10 4 [4; 2; 6; 8; 1; 8; 2; 2; 5; 8; 1; 6; 6; 0; 7; 5; 2; 2; 9; 1; 7; 7; 3; 4; 3; 8];
  value_cons #10 4 [2; 6; 8; 1; 8; 2; 2; 5; 8; 1; 6; 6; 0; 7; 5; 2; 2; 9; 1; 7; 7; 3; 4; 3; 8];
  value_cons #10 2 [6; 8; 1; 8; 2; 2; 5; 8; 1; 6; 6; 0; 7; 5; 2; 2; 9; 1; 7; 7; 3; 4; 3; 8];
  value_cons #10 6 [8; 1; 8; 2; 2; 5; 8; 1; 6; 6; 0; 7; 5; 2; 2; 9; 1; 7; 7; 3; 4; 3; 8];
  value_cons #10 8 [1; 8; 2; 2; 5; 8; 1; 6; 6; 0; 7; 5; 2; 2; 9; 1; 7; 7; 3; 4; 3; 8];
  value_cons #10 1 [8; 2; 2; 5; 8; 1; 6; 6; 0; 7; 5; 2; 2; 9; 1; 7; 7; 3; 4; 3; 8];
  value_cons #10 8 [2; 2; 5; 8; 1; 6; 6; 0; 7; 5; 2; 2; 9; 1; 7; 7; 3; 4; 3; 8];
  value_cons #10 2 [2; 5; 8; 1; 6; 6; 0; 7; 5; 2; 2; 9; 1; 7; 7; 3; 4; 3; 8];
  value_cons #10 2 [5; 8; 1; 6; 6; 0; 7; 5; 2; 2; 9; 1; 7; 7; 3; 4; 3; 8];
  value_next16_reversed_tail_18 ();
  ()

let value_next16_target_tail_19 () : Lemma (
    value #10 [0; 6; 2; 2; 3; 2; 5; 1; 5; 4; 7; 3; 5; 4; 6; 8; 7; 7; 1] == 1778645374515232260) =
  value_cons #10 0 [6; 2; 2; 3; 2; 5; 1; 5; 4; 7; 3; 5; 4; 6; 8; 7; 7; 1];
  value_cons #10 6 [2; 2; 3; 2; 5; 1; 5; 4; 7; 3; 5; 4; 6; 8; 7; 7; 1];
  value_cons #10 2 [2; 3; 2; 5; 1; 5; 4; 7; 3; 5; 4; 6; 8; 7; 7; 1];
  value_cons #10 2 [3; 2; 5; 1; 5; 4; 7; 3; 5; 4; 6; 8; 7; 7; 1];
  value_cons #10 3 [2; 5; 1; 5; 4; 7; 3; 5; 4; 6; 8; 7; 7; 1];
  value_cons #10 2 [5; 1; 5; 4; 7; 3; 5; 4; 6; 8; 7; 7; 1];
  value_cons #10 5 [1; 5; 4; 7; 3; 5; 4; 6; 8; 7; 7; 1];
  value_cons #10 1 [5; 4; 7; 3; 5; 4; 6; 8; 7; 7; 1];
  value_cons #10 5 [4; 7; 3; 5; 4; 6; 8; 7; 7; 1];
  value_cons #10 4 [7; 3; 5; 4; 6; 8; 7; 7; 1];
  value_cons #10 7 [3; 5; 4; 6; 8; 7; 7; 1];
  value_cons #10 3 [5; 4; 6; 8; 7; 7; 1];
  value_cons #10 5 [4; 6; 8; 7; 7; 1];
  value_cons #10 4 [6; 8; 7; 7; 1];
  value_cons #10 6 [8; 7; 7; 1];
  value_cons #10 8 [7; 7; 1];
  value_cons #10 7 [7; 1];
  value_cons #10 7 [1];
  value_cons #10 1 [];
  ()

let value_next16_target () : Lemma (
    value next16_target == 17786453745152322604573635887) =
  value_cons #10 7 [8; 8; 5; 3; 6; 3; 7; 5; 4; 0; 6; 2; 2; 3; 2; 5; 1; 5; 4; 7; 3; 5; 4; 6; 8; 7; 7; 1];
  value_cons #10 8 [8; 5; 3; 6; 3; 7; 5; 4; 0; 6; 2; 2; 3; 2; 5; 1; 5; 4; 7; 3; 5; 4; 6; 8; 7; 7; 1];
  value_cons #10 8 [5; 3; 6; 3; 7; 5; 4; 0; 6; 2; 2; 3; 2; 5; 1; 5; 4; 7; 3; 5; 4; 6; 8; 7; 7; 1];
  value_cons #10 5 [3; 6; 3; 7; 5; 4; 0; 6; 2; 2; 3; 2; 5; 1; 5; 4; 7; 3; 5; 4; 6; 8; 7; 7; 1];
  value_cons #10 3 [6; 3; 7; 5; 4; 0; 6; 2; 2; 3; 2; 5; 1; 5; 4; 7; 3; 5; 4; 6; 8; 7; 7; 1];
  value_cons #10 6 [3; 7; 5; 4; 0; 6; 2; 2; 3; 2; 5; 1; 5; 4; 7; 3; 5; 4; 6; 8; 7; 7; 1];
  value_cons #10 3 [7; 5; 4; 0; 6; 2; 2; 3; 2; 5; 1; 5; 4; 7; 3; 5; 4; 6; 8; 7; 7; 1];
  value_cons #10 7 [5; 4; 0; 6; 2; 2; 3; 2; 5; 1; 5; 4; 7; 3; 5; 4; 6; 8; 7; 7; 1];
  value_cons #10 5 [4; 0; 6; 2; 2; 3; 2; 5; 1; 5; 4; 7; 3; 5; 4; 6; 8; 7; 7; 1];
  value_cons #10 4 [0; 6; 2; 2; 3; 2; 5; 1; 5; 4; 7; 3; 5; 4; 6; 8; 7; 7; 1];
  value_next16_target_tail_19 ();
  ()

let canonical_next16_reversed () : Lemma (canonical #10 next16_reversed) =
  assert (canonical #10 [8]);
  canonical_cons #10 3 [8];
  canonical_cons #10 4 [3; 8];
  canonical_cons #10 3 [4; 3; 8];
  canonical_cons #10 7 [3; 4; 3; 8];
  canonical_cons #10 7 [7; 3; 4; 3; 8];
  canonical_cons #10 1 [7; 7; 3; 4; 3; 8];
  canonical_cons #10 9 [1; 7; 7; 3; 4; 3; 8];
  canonical_cons #10 2 [9; 1; 7; 7; 3; 4; 3; 8];
  canonical_cons #10 2 [2; 9; 1; 7; 7; 3; 4; 3; 8];
  canonical_cons #10 5 [2; 2; 9; 1; 7; 7; 3; 4; 3; 8];
  canonical_cons #10 7 [5; 2; 2; 9; 1; 7; 7; 3; 4; 3; 8];
  canonical_cons #10 0 [7; 5; 2; 2; 9; 1; 7; 7; 3; 4; 3; 8];
  canonical_cons #10 6 [0; 7; 5; 2; 2; 9; 1; 7; 7; 3; 4; 3; 8];
  canonical_cons #10 6 [6; 0; 7; 5; 2; 2; 9; 1; 7; 7; 3; 4; 3; 8];
  canonical_cons #10 1 [6; 6; 0; 7; 5; 2; 2; 9; 1; 7; 7; 3; 4; 3; 8];
  canonical_cons #10 8 [1; 6; 6; 0; 7; 5; 2; 2; 9; 1; 7; 7; 3; 4; 3; 8];
  canonical_cons #10 5 [8; 1; 6; 6; 0; 7; 5; 2; 2; 9; 1; 7; 7; 3; 4; 3; 8];
  canonical_cons #10 2 [5; 8; 1; 6; 6; 0; 7; 5; 2; 2; 9; 1; 7; 7; 3; 4; 3; 8];
  canonical_cons #10 2 [2; 5; 8; 1; 6; 6; 0; 7; 5; 2; 2; 9; 1; 7; 7; 3; 4; 3; 8];
  canonical_cons #10 8 [2; 2; 5; 8; 1; 6; 6; 0; 7; 5; 2; 2; 9; 1; 7; 7; 3; 4; 3; 8];
  canonical_cons #10 1 [8; 2; 2; 5; 8; 1; 6; 6; 0; 7; 5; 2; 2; 9; 1; 7; 7; 3; 4; 3; 8];
  canonical_cons #10 8 [1; 8; 2; 2; 5; 8; 1; 6; 6; 0; 7; 5; 2; 2; 9; 1; 7; 7; 3; 4; 3; 8];
  canonical_cons #10 6 [8; 1; 8; 2; 2; 5; 8; 1; 6; 6; 0; 7; 5; 2; 2; 9; 1; 7; 7; 3; 4; 3; 8];
  canonical_cons #10 2 [6; 8; 1; 8; 2; 2; 5; 8; 1; 6; 6; 0; 7; 5; 2; 2; 9; 1; 7; 7; 3; 4; 3; 8];
  canonical_cons #10 4 [2; 6; 8; 1; 8; 2; 2; 5; 8; 1; 6; 6; 0; 7; 5; 2; 2; 9; 1; 7; 7; 3; 4; 3; 8];
  canonical_cons #10 4 [4; 2; 6; 8; 1; 8; 2; 2; 5; 8; 1; 6; 6; 0; 7; 5; 2; 2; 9; 1; 7; 7; 3; 4; 3; 8];
  canonical_cons #10 9 [4; 4; 2; 6; 8; 1; 8; 2; 2; 5; 8; 1; 6; 6; 0; 7; 5; 2; 2; 9; 1; 7; 7; 3; 4; 3; 8];
  ()

let canonical_next16_target () : Lemma (canonical #10 next16_target) =
  assert (canonical #10 [1]);
  canonical_cons #10 7 [1];
  canonical_cons #10 7 [7; 1];
  canonical_cons #10 8 [7; 7; 1];
  canonical_cons #10 6 [8; 7; 7; 1];
  canonical_cons #10 4 [6; 8; 7; 7; 1];
  canonical_cons #10 5 [4; 6; 8; 7; 7; 1];
  canonical_cons #10 3 [5; 4; 6; 8; 7; 7; 1];
  canonical_cons #10 7 [3; 5; 4; 6; 8; 7; 7; 1];
  canonical_cons #10 4 [7; 3; 5; 4; 6; 8; 7; 7; 1];
  canonical_cons #10 5 [4; 7; 3; 5; 4; 6; 8; 7; 7; 1];
  canonical_cons #10 1 [5; 4; 7; 3; 5; 4; 6; 8; 7; 7; 1];
  canonical_cons #10 5 [1; 5; 4; 7; 3; 5; 4; 6; 8; 7; 7; 1];
  canonical_cons #10 2 [5; 1; 5; 4; 7; 3; 5; 4; 6; 8; 7; 7; 1];
  canonical_cons #10 3 [2; 5; 1; 5; 4; 7; 3; 5; 4; 6; 8; 7; 7; 1];
  canonical_cons #10 2 [3; 2; 5; 1; 5; 4; 7; 3; 5; 4; 6; 8; 7; 7; 1];
  canonical_cons #10 2 [2; 3; 2; 5; 1; 5; 4; 7; 3; 5; 4; 6; 8; 7; 7; 1];
  canonical_cons #10 6 [2; 2; 3; 2; 5; 1; 5; 4; 7; 3; 5; 4; 6; 8; 7; 7; 1];
  canonical_cons #10 0 [6; 2; 2; 3; 2; 5; 1; 5; 4; 7; 3; 5; 4; 6; 8; 7; 7; 1];
  canonical_cons #10 4 [0; 6; 2; 2; 3; 2; 5; 1; 5; 4; 7; 3; 5; 4; 6; 8; 7; 7; 1];
  canonical_cons #10 5 [4; 0; 6; 2; 2; 3; 2; 5; 1; 5; 4; 7; 3; 5; 4; 6; 8; 7; 7; 1];
  canonical_cons #10 7 [5; 4; 0; 6; 2; 2; 3; 2; 5; 1; 5; 4; 7; 3; 5; 4; 6; 8; 7; 7; 1];
  canonical_cons #10 3 [7; 5; 4; 0; 6; 2; 2; 3; 2; 5; 1; 5; 4; 7; 3; 5; 4; 6; 8; 7; 7; 1];
  canonical_cons #10 6 [3; 7; 5; 4; 0; 6; 2; 2; 3; 2; 5; 1; 5; 4; 7; 3; 5; 4; 6; 8; 7; 7; 1];
  canonical_cons #10 3 [6; 3; 7; 5; 4; 0; 6; 2; 2; 3; 2; 5; 1; 5; 4; 7; 3; 5; 4; 6; 8; 7; 7; 1];
  canonical_cons #10 5 [3; 6; 3; 7; 5; 4; 0; 6; 2; 2; 3; 2; 5; 1; 5; 4; 7; 3; 5; 4; 6; 8; 7; 7; 1];
  canonical_cons #10 8 [5; 3; 6; 3; 7; 5; 4; 0; 6; 2; 2; 3; 2; 5; 1; 5; 4; 7; 3; 5; 4; 6; 8; 7; 7; 1];
  canonical_cons #10 8 [8; 5; 3; 6; 3; 7; 5; 4; 0; 6; 2; 2; 3; 2; 5; 1; 5; 4; 7; 3; 5; 4; 6; 8; 7; 7; 1];
  canonical_cons #10 7 [8; 8; 5; 3; 6; 3; 7; 5; 4; 0; 6; 2; 2; 3; 2; 5; 1; 5; 4; 7; 3; 5; 4; 6; 8; 7; 7; 1];
  ()

let reverse_digits_next16_source () : Lemma (
    reverse_digits #10 next16_source == next16_reversed) =
  ReverseAddNext.canonical_next15_target ();
  reverse_list_next16_source ();
  value_next16_reversed ();
  canonical_next16_reversed ();
  reverse_digits_canonical #10 next16_source;
  normalize_value #10 (rev next16_source);
  assert (value (reverse_digits #10 next16_source) ==
    8343771922570661852281862449);
  digits_of_nat_of_canonical #10 (reverse_digits #10 next16_source);
  digits_of_nat_of_canonical #10 next16_reversed;
  assert (reverse_digits #10 next16_source == next16_reversed);
  ()

let reverse_add_9442681822581660752291773438_to_17786453745152322604573635887 () : Lemma (
    reverse_add #10 next16_source == next16_target) =
  ReverseAddNext.canonical_next15_target ();
  reverse_add_value #10 next16_source;
  ReverseAddNext.value_next15_target ();
  reverse_digits_next16_source ();
  value_next16_reversed ();
  value_next16_target ();
  assert (value (reverse_add #10 next16_source) ==
    17786453745152322604573635887);
  reverse_add_canonical #10 next16_source;
  digits_of_nat_of_canonical #10 (reverse_add #10 next16_source);
  canonical_next16_target ();
  digits_of_nat_of_canonical #10 next16_target;
  assert (reverse_add #10 next16_source == next16_target);
  ()

let trace_digits_profile_9442681822581660752291773438 () : Lemma (
    trace_digits next16_source == next16_target) =
  reverse_add_9442681822581660752291773438_to_17786453745152322604573635887 ();
  trace_digits_equals_reverse_add next16_source;
  assert (trace_digits next16_source == next16_target);
  ()

let trace_carries_next16_source () : Lemma (trace_carries next16_source ==
    [0; 1; 0; 0; 0; 1; 1; 0; 1; 0; 0; 1; 1; 0; 1; 1; 0; 1; 1; 0; 0; 1; 0; 1; 1; 0; 0; 0; 1]) =
  reverse_list_next16_source ();
  assert (trace_carries next16_source ==
    (add_trace #10 next16_source next16_reversed 0).carries);
  add_trace_carries_step #10 8 9
    [3; 4; 3; 7; 7; 1; 9; 2; 2; 5; 7; 0; 6; 6; 1; 8; 5; 2; 2; 8; 1; 8; 6; 2; 4; 4; 9]
    [4; 4; 2; 6; 8; 1; 8; 2; 2; 5; 8; 1; 6; 6; 0; 7; 5; 2; 2; 9; 1; 7; 7; 3; 4; 3; 8] 0;
  add_trace_carries_step #10 3 4
    [4; 3; 7; 7; 1; 9; 2; 2; 5; 7; 0; 6; 6; 1; 8; 5; 2; 2; 8; 1; 8; 6; 2; 4; 4; 9]
    [4; 2; 6; 8; 1; 8; 2; 2; 5; 8; 1; 6; 6; 0; 7; 5; 2; 2; 9; 1; 7; 7; 3; 4; 3; 8] 1;
  add_trace_carries_step #10 4 4
    [3; 7; 7; 1; 9; 2; 2; 5; 7; 0; 6; 6; 1; 8; 5; 2; 2; 8; 1; 8; 6; 2; 4; 4; 9]
    [2; 6; 8; 1; 8; 2; 2; 5; 8; 1; 6; 6; 0; 7; 5; 2; 2; 9; 1; 7; 7; 3; 4; 3; 8] 0;
  add_trace_carries_step #10 3 2
    [7; 7; 1; 9; 2; 2; 5; 7; 0; 6; 6; 1; 8; 5; 2; 2; 8; 1; 8; 6; 2; 4; 4; 9]
    [6; 8; 1; 8; 2; 2; 5; 8; 1; 6; 6; 0; 7; 5; 2; 2; 9; 1; 7; 7; 3; 4; 3; 8] 0;
  add_trace_carries_step #10 7 6
    [7; 1; 9; 2; 2; 5; 7; 0; 6; 6; 1; 8; 5; 2; 2; 8; 1; 8; 6; 2; 4; 4; 9]
    [8; 1; 8; 2; 2; 5; 8; 1; 6; 6; 0; 7; 5; 2; 2; 9; 1; 7; 7; 3; 4; 3; 8] 0;
  add_trace_carries_step #10 7 8
    [1; 9; 2; 2; 5; 7; 0; 6; 6; 1; 8; 5; 2; 2; 8; 1; 8; 6; 2; 4; 4; 9]
    [1; 8; 2; 2; 5; 8; 1; 6; 6; 0; 7; 5; 2; 2; 9; 1; 7; 7; 3; 4; 3; 8] 1;
  add_trace_carries_step #10 1 1
    [9; 2; 2; 5; 7; 0; 6; 6; 1; 8; 5; 2; 2; 8; 1; 8; 6; 2; 4; 4; 9]
    [8; 2; 2; 5; 8; 1; 6; 6; 0; 7; 5; 2; 2; 9; 1; 7; 7; 3; 4; 3; 8] 1;
  add_trace_carries_step #10 9 8
    [2; 2; 5; 7; 0; 6; 6; 1; 8; 5; 2; 2; 8; 1; 8; 6; 2; 4; 4; 9]
    [2; 2; 5; 8; 1; 6; 6; 0; 7; 5; 2; 2; 9; 1; 7; 7; 3; 4; 3; 8] 0;
  add_trace_carries_step #10 2 2
    [2; 5; 7; 0; 6; 6; 1; 8; 5; 2; 2; 8; 1; 8; 6; 2; 4; 4; 9]
    [2; 5; 8; 1; 6; 6; 0; 7; 5; 2; 2; 9; 1; 7; 7; 3; 4; 3; 8] 1;
  add_trace_carries_step #10 2 2
    [5; 7; 0; 6; 6; 1; 8; 5; 2; 2; 8; 1; 8; 6; 2; 4; 4; 9]
    [5; 8; 1; 6; 6; 0; 7; 5; 2; 2; 9; 1; 7; 7; 3; 4; 3; 8] 0;
  add_trace_carries_step #10 5 5
    [7; 0; 6; 6; 1; 8; 5; 2; 2; 8; 1; 8; 6; 2; 4; 4; 9]
    [8; 1; 6; 6; 0; 7; 5; 2; 2; 9; 1; 7; 7; 3; 4; 3; 8] 0;
  add_trace_carries_step #10 7 8
    [0; 6; 6; 1; 8; 5; 2; 2; 8; 1; 8; 6; 2; 4; 4; 9]
    [1; 6; 6; 0; 7; 5; 2; 2; 9; 1; 7; 7; 3; 4; 3; 8] 1;
  add_trace_carries_step #10 0 1
    [6; 6; 1; 8; 5; 2; 2; 8; 1; 8; 6; 2; 4; 4; 9]
    [6; 6; 0; 7; 5; 2; 2; 9; 1; 7; 7; 3; 4; 3; 8] 1;
  add_trace_carries_step #10 6 6
    [6; 1; 8; 5; 2; 2; 8; 1; 8; 6; 2; 4; 4; 9]
    [6; 0; 7; 5; 2; 2; 9; 1; 7; 7; 3; 4; 3; 8] 0;
  add_trace_carries_step #10 6 6
    [1; 8; 5; 2; 2; 8; 1; 8; 6; 2; 4; 4; 9]
    [0; 7; 5; 2; 2; 9; 1; 7; 7; 3; 4; 3; 8] 1;
  add_trace_carries_step #10 1 0
    [8; 5; 2; 2; 8; 1; 8; 6; 2; 4; 4; 9]
    [7; 5; 2; 2; 9; 1; 7; 7; 3; 4; 3; 8] 1;
  add_trace_carries_step #10 8 7
    [5; 2; 2; 8; 1; 8; 6; 2; 4; 4; 9]
    [5; 2; 2; 9; 1; 7; 7; 3; 4; 3; 8] 0;
  add_trace_carries_step #10 5 5
    [2; 2; 8; 1; 8; 6; 2; 4; 4; 9]
    [2; 2; 9; 1; 7; 7; 3; 4; 3; 8] 1;
  add_trace_carries_step #10 2 2
    [2; 8; 1; 8; 6; 2; 4; 4; 9]
    [2; 9; 1; 7; 7; 3; 4; 3; 8] 1;
  add_trace_carries_step #10 2 2
    [8; 1; 8; 6; 2; 4; 4; 9]
    [9; 1; 7; 7; 3; 4; 3; 8] 0;
  add_trace_carries_step #10 8 9
    [1; 8; 6; 2; 4; 4; 9]
    [1; 7; 7; 3; 4; 3; 8] 0;
  add_trace_carries_step #10 1 1
    [8; 6; 2; 4; 4; 9]
    [7; 7; 3; 4; 3; 8] 1;
  add_trace_carries_step #10 8 7
    [6; 2; 4; 4; 9]
    [7; 3; 4; 3; 8] 0;
  add_trace_carries_step #10 6 7
    [2; 4; 4; 9]
    [3; 4; 3; 8] 1;
  add_trace_carries_step #10 2 3
    [4; 4; 9]
    [4; 3; 8] 1;
  add_trace_carries_step #10 4 4
    [4; 9]
    [3; 8] 0;
  add_trace_carries_step #10 4 3
    [9]
    [8] 0;
  add_trace_carries_step #10 9 8
    []
    [] 0;
  assert ((add_trace #10 [] [] 1).carries == [1]);
  assert ((add_trace #10 next16_source next16_reversed 0).carries ==
    [0; 1; 0; 0; 0; 1; 1; 0; 1; 0; 0; 1; 1; 0; 1; 1; 0; 1; 1; 0; 0; 1; 0; 1; 1; 0; 0; 0; 1]);
  ()

let trace_profile_shape_9442681822581660752291773438 () : Lemma (
    length (trace_digits next16_source) == length next16_source + 1) =
  trace_digits_profile_9442681822581660752291773438 ();
  length_of_eq #(digit 10) (trace_digits next16_source) next16_target;
  assert (length next16_target == length next16_source + 1);
  ()

let trace_profile_final_carry_9442681822581660752291773438 () : Lemma (
    nth (trace_carries next16_source) (length next16_source) == Some 1) =
  trace_profile_shape_9442681822581660752291773438 ();
  ReverseAddContinuation.final_carry_from_overflow_length next16_source;
  ()

let trace_profile_sums_9442681822581660752291773438 () : Lemma (
    trace_sum_at next16_source 0 == 17 /\
    trace_sum_at next16_source 1 == 7 /\
    trace_sum_at next16_source 27 == 17) =
  reverse_list_next16_source ();
  ()

let trace_profile_carry_facts_9442681822581660752291773438 () : Lemma (
    trace_carry_at next16_source 1 == 1 /\
    trace_carry_at next16_source 27 == 0 /\
    trace_carry_at next16_source 2 == 0 /\
    trace_carry_at next16_source 28 == 1) =
  trace_carries_next16_source ();
  assert (trace_carries next16_source ==
    [0; 1; 0; 0; 0; 1; 1; 0; 1; 0; 0; 1; 1; 0; 1; 1; 0; 1; 1; 0; 0; 1; 0; 1; 1; 0; 0; 0; 1]);
  ()

let overflow_precondition_9442681822581660752291773438 () : Lemma (
    canonical #10 next16_source /\
    next16_source <> [] /\
    length (trace_digits next16_source) == length next16_source + 1 /\
    nth (trace_carries next16_source) (length next16_source) == Some 1 /\
    1 <= trace_sum_at next16_source 0 /\
    trace_sum_at next16_source 0 <= 18 /\
    trace_sum_at next16_source 0 <> 10 /\
    exists (i:nat). 0 < i /\ i < length next16_source /\
      trace_sum_at next16_source i +
          trace_sum_at next16_source (length next16_source - i) +
          trace_carry_at next16_source i +
          trace_carry_at next16_source (length next16_source - i) >=
        10 + 10 *
          (trace_carry_at next16_source (i + 1) +
           trace_carry_at next16_source (length next16_source - i + 1))) =
  ReverseAddNext.canonical_next15_target ();
  assert (next16_source <> []);
  trace_profile_shape_9442681822581660752291773438 ();
  trace_profile_final_carry_9442681822581660752291773438 ();
  trace_profile_sums_9442681822581660752291773438 ();
  trace_profile_carry_facts_9442681822581660752291773438 ();
  assert (length (trace_digits next16_source) == length next16_source + 1);
  assert (nth (trace_carries next16_source)
    (length next16_source) == Some 1);
  assert (trace_sum_at next16_source 0 == 17);
  assert (trace_sum_at next16_source 1 == 7);
  assert (trace_sum_at next16_source 27 == 17);
  assert (trace_carry_at next16_source 1 == 1);
  assert (trace_carry_at next16_source 27 == 0);
  assert (trace_carry_at next16_source 2 == 0);
  assert (trace_carry_at next16_source 28 == 1);
  assert (1 <= trace_sum_at next16_source 0 /\
    trace_sum_at next16_source 0 <= 18);
  assert (trace_sum_at next16_source 0 <> 10);
  let n : nat = length next16_source in
  assert (0 < 1 /\ 1 < n);
  assert (trace_sum_at next16_source 1 +
      trace_sum_at next16_source (n - 1) +
      trace_carry_at next16_source 1 +
      trace_carry_at next16_source (n - 1) >=
    10 + 10 *
      (trace_carry_at next16_source 2 +
       trace_carry_at next16_source (n - 1 + 1)));
  exists_intro
    (fun (i:nat) -> 0 < i /\ i < n /\
      trace_sum_at next16_source i +
          trace_sum_at next16_source (n - i) +
          trace_carry_at next16_source i +
          trace_carry_at next16_source (n - i) >=
        10 + 10 *
          (trace_carry_at next16_source (i + 1) +
           trace_carry_at next16_source (n - i + 1)))
    1;
  ()

let local_profile_witness_17786453745152322604573635887 () : Lemma (
    trace_local_profile_complement_witness next16_target) =
  overflow_precondition_9442681822581660752291773438 ();
  reverse_add_9442681822581660752291773438_to_17786453745152322604573635887 ();
  overflow_internal_cell_implies_next_witness next16_source;
  ()

let next17_source : numeral 10 = next16_target

let next17_reversed : numeral 10 =
  [1; 7; 7; 8; 6; 4; 5; 3; 7; 4; 5; 1; 5; 2; 3; 2; 2; 6; 0; 4; 5; 7; 3; 6; 3; 5; 8; 8; 7]

let next17_target : numeral 10 =
  [8; 5; 6; 4; 0; 1; 9; 0; 3; 9; 5; 7; 7; 4; 6; 4; 7; 7; 5; 8; 2; 1; 9; 0; 0; 4; 6; 6; 9]

let reverse_list_next17_source () : Lemma (rev next17_source == next17_reversed) =
  assert (rev [1] == [1]);
  rev_cons 7 [1];
  rev_cons 7 [7; 1];
  rev_cons 8 [7; 7; 1];
  rev_cons 6 [8; 7; 7; 1];
  rev_cons 4 [6; 8; 7; 7; 1];
  rev_cons 5 [4; 6; 8; 7; 7; 1];
  rev_cons 3 [5; 4; 6; 8; 7; 7; 1];
  rev_cons 7 [3; 5; 4; 6; 8; 7; 7; 1];
  rev_cons 4 [7; 3; 5; 4; 6; 8; 7; 7; 1];
  rev_cons 5 [4; 7; 3; 5; 4; 6; 8; 7; 7; 1];
  rev_cons 1 [5; 4; 7; 3; 5; 4; 6; 8; 7; 7; 1];
  rev_cons 5 [1; 5; 4; 7; 3; 5; 4; 6; 8; 7; 7; 1];
  rev_cons 2 [5; 1; 5; 4; 7; 3; 5; 4; 6; 8; 7; 7; 1];
  rev_cons 3 [2; 5; 1; 5; 4; 7; 3; 5; 4; 6; 8; 7; 7; 1];
  rev_cons 2 [3; 2; 5; 1; 5; 4; 7; 3; 5; 4; 6; 8; 7; 7; 1];
  rev_cons 2 [2; 3; 2; 5; 1; 5; 4; 7; 3; 5; 4; 6; 8; 7; 7; 1];
  rev_cons 6 [2; 2; 3; 2; 5; 1; 5; 4; 7; 3; 5; 4; 6; 8; 7; 7; 1];
  rev_cons 0 [6; 2; 2; 3; 2; 5; 1; 5; 4; 7; 3; 5; 4; 6; 8; 7; 7; 1];
  rev_cons 4 [0; 6; 2; 2; 3; 2; 5; 1; 5; 4; 7; 3; 5; 4; 6; 8; 7; 7; 1];
  rev_cons 5 [4; 0; 6; 2; 2; 3; 2; 5; 1; 5; 4; 7; 3; 5; 4; 6; 8; 7; 7; 1];
  rev_cons 7 [5; 4; 0; 6; 2; 2; 3; 2; 5; 1; 5; 4; 7; 3; 5; 4; 6; 8; 7; 7; 1];
  rev_cons 3 [7; 5; 4; 0; 6; 2; 2; 3; 2; 5; 1; 5; 4; 7; 3; 5; 4; 6; 8; 7; 7; 1];
  rev_cons 6 [3; 7; 5; 4; 0; 6; 2; 2; 3; 2; 5; 1; 5; 4; 7; 3; 5; 4; 6; 8; 7; 7; 1];
  rev_cons 3 [6; 3; 7; 5; 4; 0; 6; 2; 2; 3; 2; 5; 1; 5; 4; 7; 3; 5; 4; 6; 8; 7; 7; 1];
  rev_cons 5 [3; 6; 3; 7; 5; 4; 0; 6; 2; 2; 3; 2; 5; 1; 5; 4; 7; 3; 5; 4; 6; 8; 7; 7; 1];
  rev_cons 8 [5; 3; 6; 3; 7; 5; 4; 0; 6; 2; 2; 3; 2; 5; 1; 5; 4; 7; 3; 5; 4; 6; 8; 7; 7; 1];
  rev_cons 8 [8; 5; 3; 6; 3; 7; 5; 4; 0; 6; 2; 2; 3; 2; 5; 1; 5; 4; 7; 3; 5; 4; 6; 8; 7; 7; 1];
  rev_cons 7 [8; 8; 5; 3; 6; 3; 7; 5; 4; 0; 6; 2; 2; 3; 2; 5; 1; 5; 4; 7; 3; 5; 4; 6; 8; 7; 7; 1];
  ()

let value_next17_reversed_tail_19 () : Lemma (
    value #10 [5; 1; 5; 2; 3; 2; 2; 6; 0; 4; 5; 7; 3; 6; 3; 5; 8; 8; 7] == 7885363754062232515) =
  value_cons #10 5 [1; 5; 2; 3; 2; 2; 6; 0; 4; 5; 7; 3; 6; 3; 5; 8; 8; 7];
  value_cons #10 1 [5; 2; 3; 2; 2; 6; 0; 4; 5; 7; 3; 6; 3; 5; 8; 8; 7];
  value_cons #10 5 [2; 3; 2; 2; 6; 0; 4; 5; 7; 3; 6; 3; 5; 8; 8; 7];
  value_cons #10 2 [3; 2; 2; 6; 0; 4; 5; 7; 3; 6; 3; 5; 8; 8; 7];
  value_cons #10 3 [2; 2; 6; 0; 4; 5; 7; 3; 6; 3; 5; 8; 8; 7];
  value_cons #10 2 [2; 6; 0; 4; 5; 7; 3; 6; 3; 5; 8; 8; 7];
  value_cons #10 2 [6; 0; 4; 5; 7; 3; 6; 3; 5; 8; 8; 7];
  value_cons #10 6 [0; 4; 5; 7; 3; 6; 3; 5; 8; 8; 7];
  value_cons #10 0 [4; 5; 7; 3; 6; 3; 5; 8; 8; 7];
  value_cons #10 4 [5; 7; 3; 6; 3; 5; 8; 8; 7];
  value_cons #10 5 [7; 3; 6; 3; 5; 8; 8; 7];
  value_cons #10 7 [3; 6; 3; 5; 8; 8; 7];
  value_cons #10 3 [6; 3; 5; 8; 8; 7];
  value_cons #10 6 [3; 5; 8; 8; 7];
  value_cons #10 3 [5; 8; 8; 7];
  value_cons #10 5 [8; 8; 7];
  value_cons #10 8 [8; 7];
  value_cons #10 8 [7];
  value_cons #10 7 [];
  ()

let value_next17_reversed () : Lemma (
    value next17_reversed == 78853637540622325154735468771) =
  value_cons #10 1 [7; 7; 8; 6; 4; 5; 3; 7; 4; 5; 1; 5; 2; 3; 2; 2; 6; 0; 4; 5; 7; 3; 6; 3; 5; 8; 8; 7];
  value_cons #10 7 [7; 8; 6; 4; 5; 3; 7; 4; 5; 1; 5; 2; 3; 2; 2; 6; 0; 4; 5; 7; 3; 6; 3; 5; 8; 8; 7];
  value_cons #10 7 [8; 6; 4; 5; 3; 7; 4; 5; 1; 5; 2; 3; 2; 2; 6; 0; 4; 5; 7; 3; 6; 3; 5; 8; 8; 7];
  value_cons #10 8 [6; 4; 5; 3; 7; 4; 5; 1; 5; 2; 3; 2; 2; 6; 0; 4; 5; 7; 3; 6; 3; 5; 8; 8; 7];
  value_cons #10 6 [4; 5; 3; 7; 4; 5; 1; 5; 2; 3; 2; 2; 6; 0; 4; 5; 7; 3; 6; 3; 5; 8; 8; 7];
  value_cons #10 4 [5; 3; 7; 4; 5; 1; 5; 2; 3; 2; 2; 6; 0; 4; 5; 7; 3; 6; 3; 5; 8; 8; 7];
  value_cons #10 5 [3; 7; 4; 5; 1; 5; 2; 3; 2; 2; 6; 0; 4; 5; 7; 3; 6; 3; 5; 8; 8; 7];
  value_cons #10 3 [7; 4; 5; 1; 5; 2; 3; 2; 2; 6; 0; 4; 5; 7; 3; 6; 3; 5; 8; 8; 7];
  value_cons #10 7 [4; 5; 1; 5; 2; 3; 2; 2; 6; 0; 4; 5; 7; 3; 6; 3; 5; 8; 8; 7];
  value_cons #10 4 [5; 1; 5; 2; 3; 2; 2; 6; 0; 4; 5; 7; 3; 6; 3; 5; 8; 8; 7];
  value_next17_reversed_tail_19 ();
  ()

let value_next17_target_tail_19 () : Lemma (
    value #10 [5; 7; 7; 4; 6; 4; 7; 7; 5; 8; 2; 1; 9; 0; 0; 4; 6; 6; 9] == 9664009128577464775) =
  value_cons #10 5 [7; 7; 4; 6; 4; 7; 7; 5; 8; 2; 1; 9; 0; 0; 4; 6; 6; 9];
  value_cons #10 7 [7; 4; 6; 4; 7; 7; 5; 8; 2; 1; 9; 0; 0; 4; 6; 6; 9];
  value_cons #10 7 [4; 6; 4; 7; 7; 5; 8; 2; 1; 9; 0; 0; 4; 6; 6; 9];
  value_cons #10 4 [6; 4; 7; 7; 5; 8; 2; 1; 9; 0; 0; 4; 6; 6; 9];
  value_cons #10 6 [4; 7; 7; 5; 8; 2; 1; 9; 0; 0; 4; 6; 6; 9];
  value_cons #10 4 [7; 7; 5; 8; 2; 1; 9; 0; 0; 4; 6; 6; 9];
  value_cons #10 7 [7; 5; 8; 2; 1; 9; 0; 0; 4; 6; 6; 9];
  value_cons #10 7 [5; 8; 2; 1; 9; 0; 0; 4; 6; 6; 9];
  value_cons #10 5 [8; 2; 1; 9; 0; 0; 4; 6; 6; 9];
  value_cons #10 8 [2; 1; 9; 0; 0; 4; 6; 6; 9];
  value_cons #10 2 [1; 9; 0; 0; 4; 6; 6; 9];
  value_cons #10 1 [9; 0; 0; 4; 6; 6; 9];
  value_cons #10 9 [0; 0; 4; 6; 6; 9];
  value_cons #10 0 [0; 4; 6; 6; 9];
  value_cons #10 0 [4; 6; 6; 9];
  value_cons #10 4 [6; 6; 9];
  value_cons #10 6 [6; 9];
  value_cons #10 6 [9];
  value_cons #10 9 [];
  ()

let value_next17_target () : Lemma (
    value next17_target == 96640091285774647759309104658) =
  value_cons #10 8 [5; 6; 4; 0; 1; 9; 0; 3; 9; 5; 7; 7; 4; 6; 4; 7; 7; 5; 8; 2; 1; 9; 0; 0; 4; 6; 6; 9];
  value_cons #10 5 [6; 4; 0; 1; 9; 0; 3; 9; 5; 7; 7; 4; 6; 4; 7; 7; 5; 8; 2; 1; 9; 0; 0; 4; 6; 6; 9];
  value_cons #10 6 [4; 0; 1; 9; 0; 3; 9; 5; 7; 7; 4; 6; 4; 7; 7; 5; 8; 2; 1; 9; 0; 0; 4; 6; 6; 9];
  value_cons #10 4 [0; 1; 9; 0; 3; 9; 5; 7; 7; 4; 6; 4; 7; 7; 5; 8; 2; 1; 9; 0; 0; 4; 6; 6; 9];
  value_cons #10 0 [1; 9; 0; 3; 9; 5; 7; 7; 4; 6; 4; 7; 7; 5; 8; 2; 1; 9; 0; 0; 4; 6; 6; 9];
  value_cons #10 1 [9; 0; 3; 9; 5; 7; 7; 4; 6; 4; 7; 7; 5; 8; 2; 1; 9; 0; 0; 4; 6; 6; 9];
  value_cons #10 9 [0; 3; 9; 5; 7; 7; 4; 6; 4; 7; 7; 5; 8; 2; 1; 9; 0; 0; 4; 6; 6; 9];
  value_cons #10 0 [3; 9; 5; 7; 7; 4; 6; 4; 7; 7; 5; 8; 2; 1; 9; 0; 0; 4; 6; 6; 9];
  value_cons #10 3 [9; 5; 7; 7; 4; 6; 4; 7; 7; 5; 8; 2; 1; 9; 0; 0; 4; 6; 6; 9];
  value_cons #10 9 [5; 7; 7; 4; 6; 4; 7; 7; 5; 8; 2; 1; 9; 0; 0; 4; 6; 6; 9];
  value_next17_target_tail_19 ();
  ()

let canonical_next17_reversed () : Lemma (canonical #10 next17_reversed) =
  assert (canonical #10 [7]);
  canonical_cons #10 8 [7];
  canonical_cons #10 8 [8; 7];
  canonical_cons #10 5 [8; 8; 7];
  canonical_cons #10 3 [5; 8; 8; 7];
  canonical_cons #10 6 [3; 5; 8; 8; 7];
  canonical_cons #10 3 [6; 3; 5; 8; 8; 7];
  canonical_cons #10 7 [3; 6; 3; 5; 8; 8; 7];
  canonical_cons #10 5 [7; 3; 6; 3; 5; 8; 8; 7];
  canonical_cons #10 4 [5; 7; 3; 6; 3; 5; 8; 8; 7];
  canonical_cons #10 0 [4; 5; 7; 3; 6; 3; 5; 8; 8; 7];
  canonical_cons #10 6 [0; 4; 5; 7; 3; 6; 3; 5; 8; 8; 7];
  canonical_cons #10 2 [6; 0; 4; 5; 7; 3; 6; 3; 5; 8; 8; 7];
  canonical_cons #10 2 [2; 6; 0; 4; 5; 7; 3; 6; 3; 5; 8; 8; 7];
  canonical_cons #10 3 [2; 2; 6; 0; 4; 5; 7; 3; 6; 3; 5; 8; 8; 7];
  canonical_cons #10 2 [3; 2; 2; 6; 0; 4; 5; 7; 3; 6; 3; 5; 8; 8; 7];
  canonical_cons #10 5 [2; 3; 2; 2; 6; 0; 4; 5; 7; 3; 6; 3; 5; 8; 8; 7];
  canonical_cons #10 1 [5; 2; 3; 2; 2; 6; 0; 4; 5; 7; 3; 6; 3; 5; 8; 8; 7];
  canonical_cons #10 5 [1; 5; 2; 3; 2; 2; 6; 0; 4; 5; 7; 3; 6; 3; 5; 8; 8; 7];
  canonical_cons #10 4 [5; 1; 5; 2; 3; 2; 2; 6; 0; 4; 5; 7; 3; 6; 3; 5; 8; 8; 7];
  canonical_cons #10 7 [4; 5; 1; 5; 2; 3; 2; 2; 6; 0; 4; 5; 7; 3; 6; 3; 5; 8; 8; 7];
  canonical_cons #10 3 [7; 4; 5; 1; 5; 2; 3; 2; 2; 6; 0; 4; 5; 7; 3; 6; 3; 5; 8; 8; 7];
  canonical_cons #10 5 [3; 7; 4; 5; 1; 5; 2; 3; 2; 2; 6; 0; 4; 5; 7; 3; 6; 3; 5; 8; 8; 7];
  canonical_cons #10 4 [5; 3; 7; 4; 5; 1; 5; 2; 3; 2; 2; 6; 0; 4; 5; 7; 3; 6; 3; 5; 8; 8; 7];
  canonical_cons #10 6 [4; 5; 3; 7; 4; 5; 1; 5; 2; 3; 2; 2; 6; 0; 4; 5; 7; 3; 6; 3; 5; 8; 8; 7];
  canonical_cons #10 8 [6; 4; 5; 3; 7; 4; 5; 1; 5; 2; 3; 2; 2; 6; 0; 4; 5; 7; 3; 6; 3; 5; 8; 8; 7];
  canonical_cons #10 7 [8; 6; 4; 5; 3; 7; 4; 5; 1; 5; 2; 3; 2; 2; 6; 0; 4; 5; 7; 3; 6; 3; 5; 8; 8; 7];
  canonical_cons #10 7 [7; 8; 6; 4; 5; 3; 7; 4; 5; 1; 5; 2; 3; 2; 2; 6; 0; 4; 5; 7; 3; 6; 3; 5; 8; 8; 7];
  canonical_cons #10 1 [7; 7; 8; 6; 4; 5; 3; 7; 4; 5; 1; 5; 2; 3; 2; 2; 6; 0; 4; 5; 7; 3; 6; 3; 5; 8; 8; 7];
  ()

let canonical_next17_target () : Lemma (canonical #10 next17_target) =
  assert (canonical #10 [9]);
  canonical_cons #10 6 [9];
  canonical_cons #10 6 [6; 9];
  canonical_cons #10 4 [6; 6; 9];
  canonical_cons #10 0 [4; 6; 6; 9];
  canonical_cons #10 0 [0; 4; 6; 6; 9];
  canonical_cons #10 9 [0; 0; 4; 6; 6; 9];
  canonical_cons #10 1 [9; 0; 0; 4; 6; 6; 9];
  canonical_cons #10 2 [1; 9; 0; 0; 4; 6; 6; 9];
  canonical_cons #10 8 [2; 1; 9; 0; 0; 4; 6; 6; 9];
  canonical_cons #10 5 [8; 2; 1; 9; 0; 0; 4; 6; 6; 9];
  canonical_cons #10 7 [5; 8; 2; 1; 9; 0; 0; 4; 6; 6; 9];
  canonical_cons #10 7 [7; 5; 8; 2; 1; 9; 0; 0; 4; 6; 6; 9];
  canonical_cons #10 4 [7; 7; 5; 8; 2; 1; 9; 0; 0; 4; 6; 6; 9];
  canonical_cons #10 6 [4; 7; 7; 5; 8; 2; 1; 9; 0; 0; 4; 6; 6; 9];
  canonical_cons #10 4 [6; 4; 7; 7; 5; 8; 2; 1; 9; 0; 0; 4; 6; 6; 9];
  canonical_cons #10 7 [4; 6; 4; 7; 7; 5; 8; 2; 1; 9; 0; 0; 4; 6; 6; 9];
  canonical_cons #10 7 [7; 4; 6; 4; 7; 7; 5; 8; 2; 1; 9; 0; 0; 4; 6; 6; 9];
  canonical_cons #10 5 [7; 7; 4; 6; 4; 7; 7; 5; 8; 2; 1; 9; 0; 0; 4; 6; 6; 9];
  canonical_cons #10 9 [5; 7; 7; 4; 6; 4; 7; 7; 5; 8; 2; 1; 9; 0; 0; 4; 6; 6; 9];
  canonical_cons #10 3 [9; 5; 7; 7; 4; 6; 4; 7; 7; 5; 8; 2; 1; 9; 0; 0; 4; 6; 6; 9];
  canonical_cons #10 0 [3; 9; 5; 7; 7; 4; 6; 4; 7; 7; 5; 8; 2; 1; 9; 0; 0; 4; 6; 6; 9];
  canonical_cons #10 9 [0; 3; 9; 5; 7; 7; 4; 6; 4; 7; 7; 5; 8; 2; 1; 9; 0; 0; 4; 6; 6; 9];
  canonical_cons #10 1 [9; 0; 3; 9; 5; 7; 7; 4; 6; 4; 7; 7; 5; 8; 2; 1; 9; 0; 0; 4; 6; 6; 9];
  canonical_cons #10 0 [1; 9; 0; 3; 9; 5; 7; 7; 4; 6; 4; 7; 7; 5; 8; 2; 1; 9; 0; 0; 4; 6; 6; 9];
  canonical_cons #10 4 [0; 1; 9; 0; 3; 9; 5; 7; 7; 4; 6; 4; 7; 7; 5; 8; 2; 1; 9; 0; 0; 4; 6; 6; 9];
  canonical_cons #10 6 [4; 0; 1; 9; 0; 3; 9; 5; 7; 7; 4; 6; 4; 7; 7; 5; 8; 2; 1; 9; 0; 0; 4; 6; 6; 9];
  canonical_cons #10 5 [6; 4; 0; 1; 9; 0; 3; 9; 5; 7; 7; 4; 6; 4; 7; 7; 5; 8; 2; 1; 9; 0; 0; 4; 6; 6; 9];
  canonical_cons #10 8 [5; 6; 4; 0; 1; 9; 0; 3; 9; 5; 7; 7; 4; 6; 4; 7; 7; 5; 8; 2; 1; 9; 0; 0; 4; 6; 6; 9];
  ()

let reverse_digits_next17_source () : Lemma (
    reverse_digits #10 next17_source == next17_reversed) =
  ReverseAddNext.canonical_next16_target ();
  reverse_list_next17_source ();
  value_next17_reversed ();
  canonical_next17_reversed ();
  reverse_digits_canonical #10 next17_source;
  normalize_value #10 (rev next17_source);
  assert (value (reverse_digits #10 next17_source) ==
    78853637540622325154735468771);
  digits_of_nat_of_canonical #10 (reverse_digits #10 next17_source);
  digits_of_nat_of_canonical #10 next17_reversed;
  assert (reverse_digits #10 next17_source == next17_reversed);
  ()

let reverse_add_17786453745152322604573635887_to_96640091285774647759309104658 () : Lemma (
    reverse_add #10 next17_source == next17_target) =
  ReverseAddNext.canonical_next16_target ();
  reverse_add_value #10 next17_source;
  ReverseAddNext.value_next16_target ();
  reverse_digits_next17_source ();
  value_next17_reversed ();
  value_next17_target ();
  assert (value (reverse_add #10 next17_source) ==
    96640091285774647759309104658);
  reverse_add_canonical #10 next17_source;
  digits_of_nat_of_canonical #10 (reverse_add #10 next17_source);
  canonical_next17_target ();
  digits_of_nat_of_canonical #10 next17_target;
  assert (reverse_add #10 next17_source == next17_target);
  ()

let trace_digits_profile_17786453745152322604573635887 () : Lemma (
    trace_digits next17_source == next17_target) =
  reverse_add_17786453745152322604573635887_to_96640091285774647759309104658 ();
  trace_digits_equals_reverse_add next17_source;
  assert (trace_digits next17_source == next17_target);
  ()

let trace_profile_shape_17786453745152322604573635887 () : Lemma (
    length (trace_digits next17_source) == length next17_source) =
  trace_digits_profile_17786453745152322604573635887 ();
  length_of_eq #(digit 10) (trace_digits next17_source) next17_target;
  assert (length next17_target == length next17_source);
  ()

let trace_profile_final_carry_17786453745152322604573635887 () : Lemma (
    nth (trace_carries next17_source) (length next17_source) == Some 0) =
  trace_profile_shape_17786453745152322604573635887 ();
  final_carry_from_length next17_source;
  ()

let local_profile_witness_96640091285774647759309104658 () : Lemma (
    trace_local_profile_complement_witness next17_target) =
  ReverseAddNext.canonical_next16_target ();
  assert (next17_source <> []);
  trace_profile_shape_17786453745152322604573635887 ();
  trace_profile_final_carry_17786453745152322604573635887 ();
  assert (trace_sum_at next17_source 0 == 8);
  reverse_add_17786453745152322604573635887_to_96640091285774647759309104658 ();
  no_overflow_outer_sum_6_to_9_implies_next_witness next17_source;
  ()

let next18_source : numeral 10 = next17_target

let next18_reversed : numeral 10 =
  [9; 6; 6; 4; 0; 0; 9; 1; 2; 8; 5; 7; 7; 4; 6; 4; 7; 7; 5; 9; 3; 0; 9; 1; 0; 4; 6; 5; 8]

let next18_target : numeral 10 =
  [7; 2; 3; 9; 0; 1; 8; 2; 5; 7; 1; 5; 5; 9; 2; 9; 4; 5; 1; 8; 6; 1; 8; 2; 0; 8; 2; 2; 8; 1]

let reverse_list_next18_source () : Lemma (rev next18_source == next18_reversed) =
  assert (rev [9] == [9]);
  rev_cons 6 [9];
  rev_cons 6 [6; 9];
  rev_cons 4 [6; 6; 9];
  rev_cons 0 [4; 6; 6; 9];
  rev_cons 0 [0; 4; 6; 6; 9];
  rev_cons 9 [0; 0; 4; 6; 6; 9];
  rev_cons 1 [9; 0; 0; 4; 6; 6; 9];
  rev_cons 2 [1; 9; 0; 0; 4; 6; 6; 9];
  rev_cons 8 [2; 1; 9; 0; 0; 4; 6; 6; 9];
  rev_cons 5 [8; 2; 1; 9; 0; 0; 4; 6; 6; 9];
  rev_cons 7 [5; 8; 2; 1; 9; 0; 0; 4; 6; 6; 9];
  rev_cons 7 [7; 5; 8; 2; 1; 9; 0; 0; 4; 6; 6; 9];
  rev_cons 4 [7; 7; 5; 8; 2; 1; 9; 0; 0; 4; 6; 6; 9];
  rev_cons 6 [4; 7; 7; 5; 8; 2; 1; 9; 0; 0; 4; 6; 6; 9];
  rev_cons 4 [6; 4; 7; 7; 5; 8; 2; 1; 9; 0; 0; 4; 6; 6; 9];
  rev_cons 7 [4; 6; 4; 7; 7; 5; 8; 2; 1; 9; 0; 0; 4; 6; 6; 9];
  rev_cons 7 [7; 4; 6; 4; 7; 7; 5; 8; 2; 1; 9; 0; 0; 4; 6; 6; 9];
  rev_cons 5 [7; 7; 4; 6; 4; 7; 7; 5; 8; 2; 1; 9; 0; 0; 4; 6; 6; 9];
  rev_cons 9 [5; 7; 7; 4; 6; 4; 7; 7; 5; 8; 2; 1; 9; 0; 0; 4; 6; 6; 9];
  rev_cons 3 [9; 5; 7; 7; 4; 6; 4; 7; 7; 5; 8; 2; 1; 9; 0; 0; 4; 6; 6; 9];
  rev_cons 0 [3; 9; 5; 7; 7; 4; 6; 4; 7; 7; 5; 8; 2; 1; 9; 0; 0; 4; 6; 6; 9];
  rev_cons 9 [0; 3; 9; 5; 7; 7; 4; 6; 4; 7; 7; 5; 8; 2; 1; 9; 0; 0; 4; 6; 6; 9];
  rev_cons 1 [9; 0; 3; 9; 5; 7; 7; 4; 6; 4; 7; 7; 5; 8; 2; 1; 9; 0; 0; 4; 6; 6; 9];
  rev_cons 0 [1; 9; 0; 3; 9; 5; 7; 7; 4; 6; 4; 7; 7; 5; 8; 2; 1; 9; 0; 0; 4; 6; 6; 9];
  rev_cons 4 [0; 1; 9; 0; 3; 9; 5; 7; 7; 4; 6; 4; 7; 7; 5; 8; 2; 1; 9; 0; 0; 4; 6; 6; 9];
  rev_cons 6 [4; 0; 1; 9; 0; 3; 9; 5; 7; 7; 4; 6; 4; 7; 7; 5; 8; 2; 1; 9; 0; 0; 4; 6; 6; 9];
  rev_cons 5 [6; 4; 0; 1; 9; 0; 3; 9; 5; 7; 7; 4; 6; 4; 7; 7; 5; 8; 2; 1; 9; 0; 0; 4; 6; 6; 9];
  rev_cons 8 [5; 6; 4; 0; 1; 9; 0; 3; 9; 5; 7; 7; 4; 6; 4; 7; 7; 5; 8; 2; 1; 9; 0; 0; 4; 6; 6; 9];
  ()

let value_next18_reversed_tail_19 () : Lemma (
    value #10 [5; 7; 7; 4; 6; 4; 7; 7; 5; 9; 3; 0; 9; 1; 0; 4; 6; 5; 8] == 8564019039577464775) =
  value_cons #10 5 [7; 7; 4; 6; 4; 7; 7; 5; 9; 3; 0; 9; 1; 0; 4; 6; 5; 8];
  value_cons #10 7 [7; 4; 6; 4; 7; 7; 5; 9; 3; 0; 9; 1; 0; 4; 6; 5; 8];
  value_cons #10 7 [4; 6; 4; 7; 7; 5; 9; 3; 0; 9; 1; 0; 4; 6; 5; 8];
  value_cons #10 4 [6; 4; 7; 7; 5; 9; 3; 0; 9; 1; 0; 4; 6; 5; 8];
  value_cons #10 6 [4; 7; 7; 5; 9; 3; 0; 9; 1; 0; 4; 6; 5; 8];
  value_cons #10 4 [7; 7; 5; 9; 3; 0; 9; 1; 0; 4; 6; 5; 8];
  value_cons #10 7 [7; 5; 9; 3; 0; 9; 1; 0; 4; 6; 5; 8];
  value_cons #10 7 [5; 9; 3; 0; 9; 1; 0; 4; 6; 5; 8];
  value_cons #10 5 [9; 3; 0; 9; 1; 0; 4; 6; 5; 8];
  value_cons #10 9 [3; 0; 9; 1; 0; 4; 6; 5; 8];
  value_cons #10 3 [0; 9; 1; 0; 4; 6; 5; 8];
  value_cons #10 0 [9; 1; 0; 4; 6; 5; 8];
  value_cons #10 9 [1; 0; 4; 6; 5; 8];
  value_cons #10 1 [0; 4; 6; 5; 8];
  value_cons #10 0 [4; 6; 5; 8];
  value_cons #10 4 [6; 5; 8];
  value_cons #10 6 [5; 8];
  value_cons #10 5 [8];
  value_cons #10 8 [];
  ()

let value_next18_reversed () : Lemma (
    value next18_reversed == 85640190395774647758219004669) =
  value_cons #10 9 [6; 6; 4; 0; 0; 9; 1; 2; 8; 5; 7; 7; 4; 6; 4; 7; 7; 5; 9; 3; 0; 9; 1; 0; 4; 6; 5; 8];
  value_cons #10 6 [6; 4; 0; 0; 9; 1; 2; 8; 5; 7; 7; 4; 6; 4; 7; 7; 5; 9; 3; 0; 9; 1; 0; 4; 6; 5; 8];
  value_cons #10 6 [4; 0; 0; 9; 1; 2; 8; 5; 7; 7; 4; 6; 4; 7; 7; 5; 9; 3; 0; 9; 1; 0; 4; 6; 5; 8];
  value_cons #10 4 [0; 0; 9; 1; 2; 8; 5; 7; 7; 4; 6; 4; 7; 7; 5; 9; 3; 0; 9; 1; 0; 4; 6; 5; 8];
  value_cons #10 0 [0; 9; 1; 2; 8; 5; 7; 7; 4; 6; 4; 7; 7; 5; 9; 3; 0; 9; 1; 0; 4; 6; 5; 8];
  value_cons #10 0 [9; 1; 2; 8; 5; 7; 7; 4; 6; 4; 7; 7; 5; 9; 3; 0; 9; 1; 0; 4; 6; 5; 8];
  value_cons #10 9 [1; 2; 8; 5; 7; 7; 4; 6; 4; 7; 7; 5; 9; 3; 0; 9; 1; 0; 4; 6; 5; 8];
  value_cons #10 1 [2; 8; 5; 7; 7; 4; 6; 4; 7; 7; 5; 9; 3; 0; 9; 1; 0; 4; 6; 5; 8];
  value_cons #10 2 [8; 5; 7; 7; 4; 6; 4; 7; 7; 5; 9; 3; 0; 9; 1; 0; 4; 6; 5; 8];
  value_cons #10 8 [5; 7; 7; 4; 6; 4; 7; 7; 5; 9; 3; 0; 9; 1; 0; 4; 6; 5; 8];
  value_next18_reversed_tail_19 ();
  ()

let value_next18_target_tail_20 () : Lemma (
    value #10 [1; 5; 5; 9; 2; 9; 4; 5; 1; 8; 6; 1; 8; 2; 0; 8; 2; 2; 8; 1] == 18228028168154929551) =
  value_cons #10 1 [5; 5; 9; 2; 9; 4; 5; 1; 8; 6; 1; 8; 2; 0; 8; 2; 2; 8; 1];
  value_cons #10 5 [5; 9; 2; 9; 4; 5; 1; 8; 6; 1; 8; 2; 0; 8; 2; 2; 8; 1];
  value_cons #10 5 [9; 2; 9; 4; 5; 1; 8; 6; 1; 8; 2; 0; 8; 2; 2; 8; 1];
  value_cons #10 9 [2; 9; 4; 5; 1; 8; 6; 1; 8; 2; 0; 8; 2; 2; 8; 1];
  value_cons #10 2 [9; 4; 5; 1; 8; 6; 1; 8; 2; 0; 8; 2; 2; 8; 1];
  value_cons #10 9 [4; 5; 1; 8; 6; 1; 8; 2; 0; 8; 2; 2; 8; 1];
  value_cons #10 4 [5; 1; 8; 6; 1; 8; 2; 0; 8; 2; 2; 8; 1];
  value_cons #10 5 [1; 8; 6; 1; 8; 2; 0; 8; 2; 2; 8; 1];
  value_cons #10 1 [8; 6; 1; 8; 2; 0; 8; 2; 2; 8; 1];
  value_cons #10 8 [6; 1; 8; 2; 0; 8; 2; 2; 8; 1];
  value_cons #10 6 [1; 8; 2; 0; 8; 2; 2; 8; 1];
  value_cons #10 1 [8; 2; 0; 8; 2; 2; 8; 1];
  value_cons #10 8 [2; 0; 8; 2; 2; 8; 1];
  value_cons #10 2 [0; 8; 2; 2; 8; 1];
  value_cons #10 0 [8; 2; 2; 8; 1];
  value_cons #10 8 [2; 2; 8; 1];
  value_cons #10 2 [2; 8; 1];
  value_cons #10 2 [8; 1];
  value_cons #10 8 [1];
  value_cons #10 1 [];
  ()

let value_next18_target () : Lemma (
    value next18_target == 182280281681549295517528109327) =
  value_cons #10 7 [2; 3; 9; 0; 1; 8; 2; 5; 7; 1; 5; 5; 9; 2; 9; 4; 5; 1; 8; 6; 1; 8; 2; 0; 8; 2; 2; 8; 1];
  value_cons #10 2 [3; 9; 0; 1; 8; 2; 5; 7; 1; 5; 5; 9; 2; 9; 4; 5; 1; 8; 6; 1; 8; 2; 0; 8; 2; 2; 8; 1];
  value_cons #10 3 [9; 0; 1; 8; 2; 5; 7; 1; 5; 5; 9; 2; 9; 4; 5; 1; 8; 6; 1; 8; 2; 0; 8; 2; 2; 8; 1];
  value_cons #10 9 [0; 1; 8; 2; 5; 7; 1; 5; 5; 9; 2; 9; 4; 5; 1; 8; 6; 1; 8; 2; 0; 8; 2; 2; 8; 1];
  value_cons #10 0 [1; 8; 2; 5; 7; 1; 5; 5; 9; 2; 9; 4; 5; 1; 8; 6; 1; 8; 2; 0; 8; 2; 2; 8; 1];
  value_cons #10 1 [8; 2; 5; 7; 1; 5; 5; 9; 2; 9; 4; 5; 1; 8; 6; 1; 8; 2; 0; 8; 2; 2; 8; 1];
  value_cons #10 8 [2; 5; 7; 1; 5; 5; 9; 2; 9; 4; 5; 1; 8; 6; 1; 8; 2; 0; 8; 2; 2; 8; 1];
  value_cons #10 2 [5; 7; 1; 5; 5; 9; 2; 9; 4; 5; 1; 8; 6; 1; 8; 2; 0; 8; 2; 2; 8; 1];
  value_cons #10 5 [7; 1; 5; 5; 9; 2; 9; 4; 5; 1; 8; 6; 1; 8; 2; 0; 8; 2; 2; 8; 1];
  value_cons #10 7 [1; 5; 5; 9; 2; 9; 4; 5; 1; 8; 6; 1; 8; 2; 0; 8; 2; 2; 8; 1];
  value_next18_target_tail_20 ();
  ()

let canonical_next18_reversed () : Lemma (canonical #10 next18_reversed) =
  assert (canonical #10 [8]);
  canonical_cons #10 5 [8];
  canonical_cons #10 6 [5; 8];
  canonical_cons #10 4 [6; 5; 8];
  canonical_cons #10 0 [4; 6; 5; 8];
  canonical_cons #10 1 [0; 4; 6; 5; 8];
  canonical_cons #10 9 [1; 0; 4; 6; 5; 8];
  canonical_cons #10 0 [9; 1; 0; 4; 6; 5; 8];
  canonical_cons #10 3 [0; 9; 1; 0; 4; 6; 5; 8];
  canonical_cons #10 9 [3; 0; 9; 1; 0; 4; 6; 5; 8];
  canonical_cons #10 5 [9; 3; 0; 9; 1; 0; 4; 6; 5; 8];
  canonical_cons #10 7 [5; 9; 3; 0; 9; 1; 0; 4; 6; 5; 8];
  canonical_cons #10 7 [7; 5; 9; 3; 0; 9; 1; 0; 4; 6; 5; 8];
  canonical_cons #10 4 [7; 7; 5; 9; 3; 0; 9; 1; 0; 4; 6; 5; 8];
  canonical_cons #10 6 [4; 7; 7; 5; 9; 3; 0; 9; 1; 0; 4; 6; 5; 8];
  canonical_cons #10 4 [6; 4; 7; 7; 5; 9; 3; 0; 9; 1; 0; 4; 6; 5; 8];
  canonical_cons #10 7 [4; 6; 4; 7; 7; 5; 9; 3; 0; 9; 1; 0; 4; 6; 5; 8];
  canonical_cons #10 7 [7; 4; 6; 4; 7; 7; 5; 9; 3; 0; 9; 1; 0; 4; 6; 5; 8];
  canonical_cons #10 5 [7; 7; 4; 6; 4; 7; 7; 5; 9; 3; 0; 9; 1; 0; 4; 6; 5; 8];
  canonical_cons #10 8 [5; 7; 7; 4; 6; 4; 7; 7; 5; 9; 3; 0; 9; 1; 0; 4; 6; 5; 8];
  canonical_cons #10 2 [8; 5; 7; 7; 4; 6; 4; 7; 7; 5; 9; 3; 0; 9; 1; 0; 4; 6; 5; 8];
  canonical_cons #10 1 [2; 8; 5; 7; 7; 4; 6; 4; 7; 7; 5; 9; 3; 0; 9; 1; 0; 4; 6; 5; 8];
  canonical_cons #10 9 [1; 2; 8; 5; 7; 7; 4; 6; 4; 7; 7; 5; 9; 3; 0; 9; 1; 0; 4; 6; 5; 8];
  canonical_cons #10 0 [9; 1; 2; 8; 5; 7; 7; 4; 6; 4; 7; 7; 5; 9; 3; 0; 9; 1; 0; 4; 6; 5; 8];
  canonical_cons #10 0 [0; 9; 1; 2; 8; 5; 7; 7; 4; 6; 4; 7; 7; 5; 9; 3; 0; 9; 1; 0; 4; 6; 5; 8];
  canonical_cons #10 4 [0; 0; 9; 1; 2; 8; 5; 7; 7; 4; 6; 4; 7; 7; 5; 9; 3; 0; 9; 1; 0; 4; 6; 5; 8];
  canonical_cons #10 6 [4; 0; 0; 9; 1; 2; 8; 5; 7; 7; 4; 6; 4; 7; 7; 5; 9; 3; 0; 9; 1; 0; 4; 6; 5; 8];
  canonical_cons #10 6 [6; 4; 0; 0; 9; 1; 2; 8; 5; 7; 7; 4; 6; 4; 7; 7; 5; 9; 3; 0; 9; 1; 0; 4; 6; 5; 8];
  canonical_cons #10 9 [6; 6; 4; 0; 0; 9; 1; 2; 8; 5; 7; 7; 4; 6; 4; 7; 7; 5; 9; 3; 0; 9; 1; 0; 4; 6; 5; 8];
  ()

let canonical_next18_target () : Lemma (canonical #10 next18_target) =
  assert (canonical #10 [1]);
  canonical_cons #10 8 [1];
  canonical_cons #10 2 [8; 1];
  canonical_cons #10 2 [2; 8; 1];
  canonical_cons #10 8 [2; 2; 8; 1];
  canonical_cons #10 0 [8; 2; 2; 8; 1];
  canonical_cons #10 2 [0; 8; 2; 2; 8; 1];
  canonical_cons #10 8 [2; 0; 8; 2; 2; 8; 1];
  canonical_cons #10 1 [8; 2; 0; 8; 2; 2; 8; 1];
  canonical_cons #10 6 [1; 8; 2; 0; 8; 2; 2; 8; 1];
  canonical_cons #10 8 [6; 1; 8; 2; 0; 8; 2; 2; 8; 1];
  canonical_cons #10 1 [8; 6; 1; 8; 2; 0; 8; 2; 2; 8; 1];
  canonical_cons #10 5 [1; 8; 6; 1; 8; 2; 0; 8; 2; 2; 8; 1];
  canonical_cons #10 4 [5; 1; 8; 6; 1; 8; 2; 0; 8; 2; 2; 8; 1];
  canonical_cons #10 9 [4; 5; 1; 8; 6; 1; 8; 2; 0; 8; 2; 2; 8; 1];
  canonical_cons #10 2 [9; 4; 5; 1; 8; 6; 1; 8; 2; 0; 8; 2; 2; 8; 1];
  canonical_cons #10 9 [2; 9; 4; 5; 1; 8; 6; 1; 8; 2; 0; 8; 2; 2; 8; 1];
  canonical_cons #10 5 [9; 2; 9; 4; 5; 1; 8; 6; 1; 8; 2; 0; 8; 2; 2; 8; 1];
  canonical_cons #10 5 [5; 9; 2; 9; 4; 5; 1; 8; 6; 1; 8; 2; 0; 8; 2; 2; 8; 1];
  canonical_cons #10 1 [5; 5; 9; 2; 9; 4; 5; 1; 8; 6; 1; 8; 2; 0; 8; 2; 2; 8; 1];
  canonical_cons #10 7 [1; 5; 5; 9; 2; 9; 4; 5; 1; 8; 6; 1; 8; 2; 0; 8; 2; 2; 8; 1];
  canonical_cons #10 5 [7; 1; 5; 5; 9; 2; 9; 4; 5; 1; 8; 6; 1; 8; 2; 0; 8; 2; 2; 8; 1];
  canonical_cons #10 2 [5; 7; 1; 5; 5; 9; 2; 9; 4; 5; 1; 8; 6; 1; 8; 2; 0; 8; 2; 2; 8; 1];
  canonical_cons #10 8 [2; 5; 7; 1; 5; 5; 9; 2; 9; 4; 5; 1; 8; 6; 1; 8; 2; 0; 8; 2; 2; 8; 1];
  canonical_cons #10 1 [8; 2; 5; 7; 1; 5; 5; 9; 2; 9; 4; 5; 1; 8; 6; 1; 8; 2; 0; 8; 2; 2; 8; 1];
  canonical_cons #10 0 [1; 8; 2; 5; 7; 1; 5; 5; 9; 2; 9; 4; 5; 1; 8; 6; 1; 8; 2; 0; 8; 2; 2; 8; 1];
  canonical_cons #10 9 [0; 1; 8; 2; 5; 7; 1; 5; 5; 9; 2; 9; 4; 5; 1; 8; 6; 1; 8; 2; 0; 8; 2; 2; 8; 1];
  canonical_cons #10 3 [9; 0; 1; 8; 2; 5; 7; 1; 5; 5; 9; 2; 9; 4; 5; 1; 8; 6; 1; 8; 2; 0; 8; 2; 2; 8; 1];
  canonical_cons #10 2 [3; 9; 0; 1; 8; 2; 5; 7; 1; 5; 5; 9; 2; 9; 4; 5; 1; 8; 6; 1; 8; 2; 0; 8; 2; 2; 8; 1];
  canonical_cons #10 7 [2; 3; 9; 0; 1; 8; 2; 5; 7; 1; 5; 5; 9; 2; 9; 4; 5; 1; 8; 6; 1; 8; 2; 0; 8; 2; 2; 8; 1];
  ()

let reverse_digits_next18_source () : Lemma (
    reverse_digits #10 next18_source == next18_reversed) =
  ReverseAddNext.canonical_next17_target ();
  reverse_list_next18_source ();
  value_next18_reversed ();
  canonical_next18_reversed ();
  reverse_digits_canonical #10 next18_source;
  normalize_value #10 (rev next18_source);
  assert (value (reverse_digits #10 next18_source) ==
    85640190395774647758219004669);
  digits_of_nat_of_canonical #10 (reverse_digits #10 next18_source);
  digits_of_nat_of_canonical #10 next18_reversed;
  assert (reverse_digits #10 next18_source == next18_reversed);
  ()

let reverse_add_96640091285774647759309104658_to_182280281681549295517528109327 () : Lemma (
    reverse_add #10 next18_source == next18_target) =
  ReverseAddNext.canonical_next17_target ();
  reverse_add_value #10 next18_source;
  ReverseAddNext.value_next17_target ();
  reverse_digits_next18_source ();
  value_next18_reversed ();
  value_next18_target ();
  assert (value (reverse_add #10 next18_source) ==
    182280281681549295517528109327);
  reverse_add_canonical #10 next18_source;
  digits_of_nat_of_canonical #10 (reverse_add #10 next18_source);
  canonical_next18_target ();
  digits_of_nat_of_canonical #10 next18_target;
  assert (reverse_add #10 next18_source == next18_target);
  ()

let trace_digits_profile_96640091285774647759309104658 () : Lemma (
    trace_digits next18_source == next18_target) =
  reverse_add_96640091285774647759309104658_to_182280281681549295517528109327 ();
  trace_digits_equals_reverse_add next18_source;
  assert (trace_digits next18_source == next18_target);
  ()

let trace_carries_next18_source () : Lemma (trace_carries next18_source ==
    [0; 1; 1; 1; 0; 0; 0; 1; 0; 0; 1; 1; 1; 1; 0; 1; 0; 1; 1; 1; 1; 0; 0; 1; 0; 0; 0; 1; 1; 1]) =
  reverse_list_next18_source ();
  assert (trace_carries next18_source ==
    (add_trace #10 next18_source next18_reversed 0).carries);
  add_trace_carries_step #10 8 9
    [5; 6; 4; 0; 1; 9; 0; 3; 9; 5; 7; 7; 4; 6; 4; 7; 7; 5; 8; 2; 1; 9; 0; 0; 4; 6; 6; 9]
    [6; 6; 4; 0; 0; 9; 1; 2; 8; 5; 7; 7; 4; 6; 4; 7; 7; 5; 9; 3; 0; 9; 1; 0; 4; 6; 5; 8] 0;
  add_trace_carries_step #10 5 6
    [6; 4; 0; 1; 9; 0; 3; 9; 5; 7; 7; 4; 6; 4; 7; 7; 5; 8; 2; 1; 9; 0; 0; 4; 6; 6; 9]
    [6; 4; 0; 0; 9; 1; 2; 8; 5; 7; 7; 4; 6; 4; 7; 7; 5; 9; 3; 0; 9; 1; 0; 4; 6; 5; 8] 1;
  add_trace_carries_step #10 6 6
    [4; 0; 1; 9; 0; 3; 9; 5; 7; 7; 4; 6; 4; 7; 7; 5; 8; 2; 1; 9; 0; 0; 4; 6; 6; 9]
    [4; 0; 0; 9; 1; 2; 8; 5; 7; 7; 4; 6; 4; 7; 7; 5; 9; 3; 0; 9; 1; 0; 4; 6; 5; 8] 1;
  add_trace_carries_step #10 4 4
    [0; 1; 9; 0; 3; 9; 5; 7; 7; 4; 6; 4; 7; 7; 5; 8; 2; 1; 9; 0; 0; 4; 6; 6; 9]
    [0; 0; 9; 1; 2; 8; 5; 7; 7; 4; 6; 4; 7; 7; 5; 9; 3; 0; 9; 1; 0; 4; 6; 5; 8] 1;
  add_trace_carries_step #10 0 0
    [1; 9; 0; 3; 9; 5; 7; 7; 4; 6; 4; 7; 7; 5; 8; 2; 1; 9; 0; 0; 4; 6; 6; 9]
    [0; 9; 1; 2; 8; 5; 7; 7; 4; 6; 4; 7; 7; 5; 9; 3; 0; 9; 1; 0; 4; 6; 5; 8] 0;
  add_trace_carries_step #10 1 0
    [9; 0; 3; 9; 5; 7; 7; 4; 6; 4; 7; 7; 5; 8; 2; 1; 9; 0; 0; 4; 6; 6; 9]
    [9; 1; 2; 8; 5; 7; 7; 4; 6; 4; 7; 7; 5; 9; 3; 0; 9; 1; 0; 4; 6; 5; 8] 0;
  add_trace_carries_step #10 9 9
    [0; 3; 9; 5; 7; 7; 4; 6; 4; 7; 7; 5; 8; 2; 1; 9; 0; 0; 4; 6; 6; 9]
    [1; 2; 8; 5; 7; 7; 4; 6; 4; 7; 7; 5; 9; 3; 0; 9; 1; 0; 4; 6; 5; 8] 0;
  add_trace_carries_step #10 0 1
    [3; 9; 5; 7; 7; 4; 6; 4; 7; 7; 5; 8; 2; 1; 9; 0; 0; 4; 6; 6; 9]
    [2; 8; 5; 7; 7; 4; 6; 4; 7; 7; 5; 9; 3; 0; 9; 1; 0; 4; 6; 5; 8] 1;
  add_trace_carries_step #10 3 2
    [9; 5; 7; 7; 4; 6; 4; 7; 7; 5; 8; 2; 1; 9; 0; 0; 4; 6; 6; 9]
    [8; 5; 7; 7; 4; 6; 4; 7; 7; 5; 9; 3; 0; 9; 1; 0; 4; 6; 5; 8] 0;
  add_trace_carries_step #10 9 8
    [5; 7; 7; 4; 6; 4; 7; 7; 5; 8; 2; 1; 9; 0; 0; 4; 6; 6; 9]
    [5; 7; 7; 4; 6; 4; 7; 7; 5; 9; 3; 0; 9; 1; 0; 4; 6; 5; 8] 0;
  add_trace_carries_step #10 5 5
    [7; 7; 4; 6; 4; 7; 7; 5; 8; 2; 1; 9; 0; 0; 4; 6; 6; 9]
    [7; 7; 4; 6; 4; 7; 7; 5; 9; 3; 0; 9; 1; 0; 4; 6; 5; 8] 1;
  add_trace_carries_step #10 7 7
    [7; 4; 6; 4; 7; 7; 5; 8; 2; 1; 9; 0; 0; 4; 6; 6; 9]
    [7; 4; 6; 4; 7; 7; 5; 9; 3; 0; 9; 1; 0; 4; 6; 5; 8] 1;
  add_trace_carries_step #10 7 7
    [4; 6; 4; 7; 7; 5; 8; 2; 1; 9; 0; 0; 4; 6; 6; 9]
    [4; 6; 4; 7; 7; 5; 9; 3; 0; 9; 1; 0; 4; 6; 5; 8] 1;
  add_trace_carries_step #10 4 4
    [6; 4; 7; 7; 5; 8; 2; 1; 9; 0; 0; 4; 6; 6; 9]
    [6; 4; 7; 7; 5; 9; 3; 0; 9; 1; 0; 4; 6; 5; 8] 1;
  add_trace_carries_step #10 6 6
    [4; 7; 7; 5; 8; 2; 1; 9; 0; 0; 4; 6; 6; 9]
    [4; 7; 7; 5; 9; 3; 0; 9; 1; 0; 4; 6; 5; 8] 0;
  add_trace_carries_step #10 4 4
    [7; 7; 5; 8; 2; 1; 9; 0; 0; 4; 6; 6; 9]
    [7; 7; 5; 9; 3; 0; 9; 1; 0; 4; 6; 5; 8] 1;
  add_trace_carries_step #10 7 7
    [7; 5; 8; 2; 1; 9; 0; 0; 4; 6; 6; 9]
    [7; 5; 9; 3; 0; 9; 1; 0; 4; 6; 5; 8] 0;
  add_trace_carries_step #10 7 7
    [5; 8; 2; 1; 9; 0; 0; 4; 6; 6; 9]
    [5; 9; 3; 0; 9; 1; 0; 4; 6; 5; 8] 1;
  add_trace_carries_step #10 5 5
    [8; 2; 1; 9; 0; 0; 4; 6; 6; 9]
    [9; 3; 0; 9; 1; 0; 4; 6; 5; 8] 1;
  add_trace_carries_step #10 8 9
    [2; 1; 9; 0; 0; 4; 6; 6; 9]
    [3; 0; 9; 1; 0; 4; 6; 5; 8] 1;
  add_trace_carries_step #10 2 3
    [1; 9; 0; 0; 4; 6; 6; 9]
    [0; 9; 1; 0; 4; 6; 5; 8] 1;
  add_trace_carries_step #10 1 0
    [9; 0; 0; 4; 6; 6; 9]
    [9; 1; 0; 4; 6; 5; 8] 0;
  add_trace_carries_step #10 9 9
    [0; 0; 4; 6; 6; 9]
    [1; 0; 4; 6; 5; 8] 0;
  add_trace_carries_step #10 0 1
    [0; 4; 6; 6; 9]
    [0; 4; 6; 5; 8] 1;
  add_trace_carries_step #10 0 0
    [4; 6; 6; 9]
    [4; 6; 5; 8] 0;
  add_trace_carries_step #10 4 4
    [6; 6; 9]
    [6; 5; 8] 0;
  add_trace_carries_step #10 6 6
    [6; 9]
    [5; 8] 0;
  add_trace_carries_step #10 6 5
    [9]
    [8] 1;
  add_trace_carries_step #10 9 8
    []
    [] 1;
  assert ((add_trace #10 [] [] 1).carries == [1]);
  assert ((add_trace #10 next18_source next18_reversed 0).carries ==
    [0; 1; 1; 1; 0; 0; 0; 1; 0; 0; 1; 1; 1; 1; 0; 1; 0; 1; 1; 1; 1; 0; 0; 1; 0; 0; 0; 1; 1; 1]);
  ()

let trace_profile_shape_96640091285774647759309104658 () : Lemma (
    length (trace_digits next18_source) == length next18_source + 1) =
  trace_digits_profile_96640091285774647759309104658 ();
  length_of_eq #(digit 10) (trace_digits next18_source) next18_target;
  assert (length next18_target == length next18_source + 1);
  ()

let trace_profile_final_carry_96640091285774647759309104658 () : Lemma (
    nth (trace_carries next18_source) (length next18_source) == Some 1) =
  trace_profile_shape_96640091285774647759309104658 ();
  ReverseAddContinuation.final_carry_from_overflow_length next18_source;
  ()

let trace_profile_sums_96640091285774647759309104658 () : Lemma (
    trace_sum_at next18_source 0 == 17 /\
    trace_sum_at next18_source 1 == 11 /\
    trace_sum_at next18_source 28 == 17) =
  reverse_list_next18_source ();
  ()

let trace_profile_carry_facts_96640091285774647759309104658 () : Lemma (
    trace_carry_at next18_source 1 == 1 /\
    trace_carry_at next18_source 28 == 1 /\
    trace_carry_at next18_source 2 == 1 /\
    trace_carry_at next18_source 29 == 1) =
  trace_carries_next18_source ();
  assert (trace_carries next18_source ==
    [0; 1; 1; 1; 0; 0; 0; 1; 0; 0; 1; 1; 1; 1; 0; 1; 0; 1; 1; 1; 1; 0; 0; 1; 0; 0; 0; 1; 1; 1]);
  ()

let overflow_precondition_96640091285774647759309104658 () : Lemma (
    canonical #10 next18_source /\
    next18_source <> [] /\
    length (trace_digits next18_source) == length next18_source + 1 /\
    nth (trace_carries next18_source) (length next18_source) == Some 1 /\
    1 <= trace_sum_at next18_source 0 /\
    trace_sum_at next18_source 0 <= 18 /\
    trace_sum_at next18_source 0 <> 10 /\
    exists (i:nat). 0 < i /\ i < length next18_source /\
      trace_sum_at next18_source i +
          trace_sum_at next18_source (length next18_source - i) +
          trace_carry_at next18_source i +
          trace_carry_at next18_source (length next18_source - i) >=
        10 + 10 *
          (trace_carry_at next18_source (i + 1) +
           trace_carry_at next18_source (length next18_source - i + 1))) =
  ReverseAddNext.canonical_next17_target ();
  assert (next18_source <> []);
  trace_profile_shape_96640091285774647759309104658 ();
  trace_profile_final_carry_96640091285774647759309104658 ();
  trace_profile_sums_96640091285774647759309104658 ();
  trace_profile_carry_facts_96640091285774647759309104658 ();
  assert (length (trace_digits next18_source) == length next18_source + 1);
  assert (nth (trace_carries next18_source)
    (length next18_source) == Some 1);
  assert (trace_sum_at next18_source 0 == 17);
  assert (trace_sum_at next18_source 1 == 11);
  assert (trace_sum_at next18_source 28 == 17);
  assert (trace_carry_at next18_source 1 == 1);
  assert (trace_carry_at next18_source 28 == 1);
  assert (trace_carry_at next18_source 2 == 1);
  assert (trace_carry_at next18_source 29 == 1);
  assert (1 <= trace_sum_at next18_source 0 /\
    trace_sum_at next18_source 0 <= 18);
  assert (trace_sum_at next18_source 0 <> 10);
  let n : nat = length next18_source in
  assert (0 < 1 /\ 1 < n);
  assert (trace_sum_at next18_source 1 +
      trace_sum_at next18_source (n - 1) +
      trace_carry_at next18_source 1 +
      trace_carry_at next18_source (n - 1) >=
    10 + 10 *
      (trace_carry_at next18_source 2 +
       trace_carry_at next18_source (n - 1 + 1)));
  exists_intro
    (fun (i:nat) -> 0 < i /\ i < n /\
      trace_sum_at next18_source i +
          trace_sum_at next18_source (n - i) +
          trace_carry_at next18_source i +
          trace_carry_at next18_source (n - i) >=
        10 + 10 *
          (trace_carry_at next18_source (i + 1) +
           trace_carry_at next18_source (n - i + 1)))
    1;
  ()

let local_profile_witness_182280281681549295517528109327 () : Lemma (
    trace_local_profile_complement_witness next18_target) =
  overflow_precondition_96640091285774647759309104658 ();
  reverse_add_96640091285774647759309104658_to_182280281681549295517528109327 ();
  overflow_internal_cell_implies_next_witness next18_source;
  ()

let next19_source : numeral 10 = next18_target

let next19_reversed : numeral 10 =
  [1; 8; 2; 2; 8; 0; 2; 8; 1; 6; 8; 1; 5; 4; 9; 2; 9; 5; 5; 1; 7; 5; 2; 8; 1; 0; 9; 3; 2; 7]

let next19_target : numeral 10 =
  [8; 0; 6; 1; 9; 1; 0; 1; 7; 3; 0; 7; 0; 4; 2; 2; 4; 1; 7; 9; 3; 7; 0; 1; 2; 8; 1; 6; 0; 9]

let reverse_list_next19_source () : Lemma (rev next19_source == next19_reversed) =
  assert (rev [1] == [1]);
  rev_cons 8 [1];
  rev_cons 2 [8; 1];
  rev_cons 2 [2; 8; 1];
  rev_cons 8 [2; 2; 8; 1];
  rev_cons 0 [8; 2; 2; 8; 1];
  rev_cons 2 [0; 8; 2; 2; 8; 1];
  rev_cons 8 [2; 0; 8; 2; 2; 8; 1];
  rev_cons 1 [8; 2; 0; 8; 2; 2; 8; 1];
  rev_cons 6 [1; 8; 2; 0; 8; 2; 2; 8; 1];
  rev_cons 8 [6; 1; 8; 2; 0; 8; 2; 2; 8; 1];
  rev_cons 1 [8; 6; 1; 8; 2; 0; 8; 2; 2; 8; 1];
  rev_cons 5 [1; 8; 6; 1; 8; 2; 0; 8; 2; 2; 8; 1];
  rev_cons 4 [5; 1; 8; 6; 1; 8; 2; 0; 8; 2; 2; 8; 1];
  rev_cons 9 [4; 5; 1; 8; 6; 1; 8; 2; 0; 8; 2; 2; 8; 1];
  rev_cons 2 [9; 4; 5; 1; 8; 6; 1; 8; 2; 0; 8; 2; 2; 8; 1];
  rev_cons 9 [2; 9; 4; 5; 1; 8; 6; 1; 8; 2; 0; 8; 2; 2; 8; 1];
  rev_cons 5 [9; 2; 9; 4; 5; 1; 8; 6; 1; 8; 2; 0; 8; 2; 2; 8; 1];
  rev_cons 5 [5; 9; 2; 9; 4; 5; 1; 8; 6; 1; 8; 2; 0; 8; 2; 2; 8; 1];
  rev_cons 1 [5; 5; 9; 2; 9; 4; 5; 1; 8; 6; 1; 8; 2; 0; 8; 2; 2; 8; 1];
  rev_cons 7 [1; 5; 5; 9; 2; 9; 4; 5; 1; 8; 6; 1; 8; 2; 0; 8; 2; 2; 8; 1];
  rev_cons 5 [7; 1; 5; 5; 9; 2; 9; 4; 5; 1; 8; 6; 1; 8; 2; 0; 8; 2; 2; 8; 1];
  rev_cons 2 [5; 7; 1; 5; 5; 9; 2; 9; 4; 5; 1; 8; 6; 1; 8; 2; 0; 8; 2; 2; 8; 1];
  rev_cons 8 [2; 5; 7; 1; 5; 5; 9; 2; 9; 4; 5; 1; 8; 6; 1; 8; 2; 0; 8; 2; 2; 8; 1];
  rev_cons 1 [8; 2; 5; 7; 1; 5; 5; 9; 2; 9; 4; 5; 1; 8; 6; 1; 8; 2; 0; 8; 2; 2; 8; 1];
  rev_cons 0 [1; 8; 2; 5; 7; 1; 5; 5; 9; 2; 9; 4; 5; 1; 8; 6; 1; 8; 2; 0; 8; 2; 2; 8; 1];
  rev_cons 9 [0; 1; 8; 2; 5; 7; 1; 5; 5; 9; 2; 9; 4; 5; 1; 8; 6; 1; 8; 2; 0; 8; 2; 2; 8; 1];
  rev_cons 3 [9; 0; 1; 8; 2; 5; 7; 1; 5; 5; 9; 2; 9; 4; 5; 1; 8; 6; 1; 8; 2; 0; 8; 2; 2; 8; 1];
  rev_cons 2 [3; 9; 0; 1; 8; 2; 5; 7; 1; 5; 5; 9; 2; 9; 4; 5; 1; 8; 6; 1; 8; 2; 0; 8; 2; 2; 8; 1];
  rev_cons 7 [2; 3; 9; 0; 1; 8; 2; 5; 7; 1; 5; 5; 9; 2; 9; 4; 5; 1; 8; 6; 1; 8; 2; 0; 8; 2; 2; 8; 1];
  ()

let value_next19_reversed_tail_20 () : Lemma (
    value #10 [8; 1; 5; 4; 9; 2; 9; 5; 5; 1; 7; 5; 2; 8; 1; 0; 9; 3; 2; 7] == 72390182571559294518) =
  value_cons #10 8 [1; 5; 4; 9; 2; 9; 5; 5; 1; 7; 5; 2; 8; 1; 0; 9; 3; 2; 7];
  value_cons #10 1 [5; 4; 9; 2; 9; 5; 5; 1; 7; 5; 2; 8; 1; 0; 9; 3; 2; 7];
  value_cons #10 5 [4; 9; 2; 9; 5; 5; 1; 7; 5; 2; 8; 1; 0; 9; 3; 2; 7];
  value_cons #10 4 [9; 2; 9; 5; 5; 1; 7; 5; 2; 8; 1; 0; 9; 3; 2; 7];
  value_cons #10 9 [2; 9; 5; 5; 1; 7; 5; 2; 8; 1; 0; 9; 3; 2; 7];
  value_cons #10 2 [9; 5; 5; 1; 7; 5; 2; 8; 1; 0; 9; 3; 2; 7];
  value_cons #10 9 [5; 5; 1; 7; 5; 2; 8; 1; 0; 9; 3; 2; 7];
  value_cons #10 5 [5; 1; 7; 5; 2; 8; 1; 0; 9; 3; 2; 7];
  value_cons #10 5 [1; 7; 5; 2; 8; 1; 0; 9; 3; 2; 7];
  value_cons #10 1 [7; 5; 2; 8; 1; 0; 9; 3; 2; 7];
  value_cons #10 7 [5; 2; 8; 1; 0; 9; 3; 2; 7];
  value_cons #10 5 [2; 8; 1; 0; 9; 3; 2; 7];
  value_cons #10 2 [8; 1; 0; 9; 3; 2; 7];
  value_cons #10 8 [1; 0; 9; 3; 2; 7];
  value_cons #10 1 [0; 9; 3; 2; 7];
  value_cons #10 0 [9; 3; 2; 7];
  value_cons #10 9 [3; 2; 7];
  value_cons #10 3 [2; 7];
  value_cons #10 2 [7];
  value_cons #10 7 [];
  ()

let value_next19_reversed () : Lemma (
    value next19_reversed == 723901825715592945186182082281) =
  value_cons #10 1 [8; 2; 2; 8; 0; 2; 8; 1; 6; 8; 1; 5; 4; 9; 2; 9; 5; 5; 1; 7; 5; 2; 8; 1; 0; 9; 3; 2; 7];
  value_cons #10 8 [2; 2; 8; 0; 2; 8; 1; 6; 8; 1; 5; 4; 9; 2; 9; 5; 5; 1; 7; 5; 2; 8; 1; 0; 9; 3; 2; 7];
  value_cons #10 2 [2; 8; 0; 2; 8; 1; 6; 8; 1; 5; 4; 9; 2; 9; 5; 5; 1; 7; 5; 2; 8; 1; 0; 9; 3; 2; 7];
  value_cons #10 2 [8; 0; 2; 8; 1; 6; 8; 1; 5; 4; 9; 2; 9; 5; 5; 1; 7; 5; 2; 8; 1; 0; 9; 3; 2; 7];
  value_cons #10 8 [0; 2; 8; 1; 6; 8; 1; 5; 4; 9; 2; 9; 5; 5; 1; 7; 5; 2; 8; 1; 0; 9; 3; 2; 7];
  value_cons #10 0 [2; 8; 1; 6; 8; 1; 5; 4; 9; 2; 9; 5; 5; 1; 7; 5; 2; 8; 1; 0; 9; 3; 2; 7];
  value_cons #10 2 [8; 1; 6; 8; 1; 5; 4; 9; 2; 9; 5; 5; 1; 7; 5; 2; 8; 1; 0; 9; 3; 2; 7];
  value_cons #10 8 [1; 6; 8; 1; 5; 4; 9; 2; 9; 5; 5; 1; 7; 5; 2; 8; 1; 0; 9; 3; 2; 7];
  value_cons #10 1 [6; 8; 1; 5; 4; 9; 2; 9; 5; 5; 1; 7; 5; 2; 8; 1; 0; 9; 3; 2; 7];
  value_cons #10 6 [8; 1; 5; 4; 9; 2; 9; 5; 5; 1; 7; 5; 2; 8; 1; 0; 9; 3; 2; 7];
  value_next19_reversed_tail_20 ();
  ()

let value_next19_target_tail_20 () : Lemma (
    value #10 [0; 7; 0; 4; 2; 2; 4; 1; 7; 9; 3; 7; 0; 1; 2; 8; 1; 6; 0; 9] == 90618210739714224070) =
  value_cons #10 0 [7; 0; 4; 2; 2; 4; 1; 7; 9; 3; 7; 0; 1; 2; 8; 1; 6; 0; 9];
  value_cons #10 7 [0; 4; 2; 2; 4; 1; 7; 9; 3; 7; 0; 1; 2; 8; 1; 6; 0; 9];
  value_cons #10 0 [4; 2; 2; 4; 1; 7; 9; 3; 7; 0; 1; 2; 8; 1; 6; 0; 9];
  value_cons #10 4 [2; 2; 4; 1; 7; 9; 3; 7; 0; 1; 2; 8; 1; 6; 0; 9];
  value_cons #10 2 [2; 4; 1; 7; 9; 3; 7; 0; 1; 2; 8; 1; 6; 0; 9];
  value_cons #10 2 [4; 1; 7; 9; 3; 7; 0; 1; 2; 8; 1; 6; 0; 9];
  value_cons #10 4 [1; 7; 9; 3; 7; 0; 1; 2; 8; 1; 6; 0; 9];
  value_cons #10 1 [7; 9; 3; 7; 0; 1; 2; 8; 1; 6; 0; 9];
  value_cons #10 7 [9; 3; 7; 0; 1; 2; 8; 1; 6; 0; 9];
  value_cons #10 9 [3; 7; 0; 1; 2; 8; 1; 6; 0; 9];
  value_cons #10 3 [7; 0; 1; 2; 8; 1; 6; 0; 9];
  value_cons #10 7 [0; 1; 2; 8; 1; 6; 0; 9];
  value_cons #10 0 [1; 2; 8; 1; 6; 0; 9];
  value_cons #10 1 [2; 8; 1; 6; 0; 9];
  value_cons #10 2 [8; 1; 6; 0; 9];
  value_cons #10 8 [1; 6; 0; 9];
  value_cons #10 1 [6; 0; 9];
  value_cons #10 6 [0; 9];
  value_cons #10 0 [9];
  value_cons #10 9 [];
  ()

let value_next19_target () : Lemma (
    value next19_target == 906182107397142240703710191608) =
  value_cons #10 8 [0; 6; 1; 9; 1; 0; 1; 7; 3; 0; 7; 0; 4; 2; 2; 4; 1; 7; 9; 3; 7; 0; 1; 2; 8; 1; 6; 0; 9];
  value_cons #10 0 [6; 1; 9; 1; 0; 1; 7; 3; 0; 7; 0; 4; 2; 2; 4; 1; 7; 9; 3; 7; 0; 1; 2; 8; 1; 6; 0; 9];
  value_cons #10 6 [1; 9; 1; 0; 1; 7; 3; 0; 7; 0; 4; 2; 2; 4; 1; 7; 9; 3; 7; 0; 1; 2; 8; 1; 6; 0; 9];
  value_cons #10 1 [9; 1; 0; 1; 7; 3; 0; 7; 0; 4; 2; 2; 4; 1; 7; 9; 3; 7; 0; 1; 2; 8; 1; 6; 0; 9];
  value_cons #10 9 [1; 0; 1; 7; 3; 0; 7; 0; 4; 2; 2; 4; 1; 7; 9; 3; 7; 0; 1; 2; 8; 1; 6; 0; 9];
  value_cons #10 1 [0; 1; 7; 3; 0; 7; 0; 4; 2; 2; 4; 1; 7; 9; 3; 7; 0; 1; 2; 8; 1; 6; 0; 9];
  value_cons #10 0 [1; 7; 3; 0; 7; 0; 4; 2; 2; 4; 1; 7; 9; 3; 7; 0; 1; 2; 8; 1; 6; 0; 9];
  value_cons #10 1 [7; 3; 0; 7; 0; 4; 2; 2; 4; 1; 7; 9; 3; 7; 0; 1; 2; 8; 1; 6; 0; 9];
  value_cons #10 7 [3; 0; 7; 0; 4; 2; 2; 4; 1; 7; 9; 3; 7; 0; 1; 2; 8; 1; 6; 0; 9];
  value_cons #10 3 [0; 7; 0; 4; 2; 2; 4; 1; 7; 9; 3; 7; 0; 1; 2; 8; 1; 6; 0; 9];
  value_next19_target_tail_20 ();
  ()

let canonical_next19_reversed () : Lemma (canonical #10 next19_reversed) =
  assert (canonical #10 [7]);
  canonical_cons #10 2 [7];
  canonical_cons #10 3 [2; 7];
  canonical_cons #10 9 [3; 2; 7];
  canonical_cons #10 0 [9; 3; 2; 7];
  canonical_cons #10 1 [0; 9; 3; 2; 7];
  canonical_cons #10 8 [1; 0; 9; 3; 2; 7];
  canonical_cons #10 2 [8; 1; 0; 9; 3; 2; 7];
  canonical_cons #10 5 [2; 8; 1; 0; 9; 3; 2; 7];
  canonical_cons #10 7 [5; 2; 8; 1; 0; 9; 3; 2; 7];
  canonical_cons #10 1 [7; 5; 2; 8; 1; 0; 9; 3; 2; 7];
  canonical_cons #10 5 [1; 7; 5; 2; 8; 1; 0; 9; 3; 2; 7];
  canonical_cons #10 5 [5; 1; 7; 5; 2; 8; 1; 0; 9; 3; 2; 7];
  canonical_cons #10 9 [5; 5; 1; 7; 5; 2; 8; 1; 0; 9; 3; 2; 7];
  canonical_cons #10 2 [9; 5; 5; 1; 7; 5; 2; 8; 1; 0; 9; 3; 2; 7];
  canonical_cons #10 9 [2; 9; 5; 5; 1; 7; 5; 2; 8; 1; 0; 9; 3; 2; 7];
  canonical_cons #10 4 [9; 2; 9; 5; 5; 1; 7; 5; 2; 8; 1; 0; 9; 3; 2; 7];
  canonical_cons #10 5 [4; 9; 2; 9; 5; 5; 1; 7; 5; 2; 8; 1; 0; 9; 3; 2; 7];
  canonical_cons #10 1 [5; 4; 9; 2; 9; 5; 5; 1; 7; 5; 2; 8; 1; 0; 9; 3; 2; 7];
  canonical_cons #10 8 [1; 5; 4; 9; 2; 9; 5; 5; 1; 7; 5; 2; 8; 1; 0; 9; 3; 2; 7];
  canonical_cons #10 6 [8; 1; 5; 4; 9; 2; 9; 5; 5; 1; 7; 5; 2; 8; 1; 0; 9; 3; 2; 7];
  canonical_cons #10 1 [6; 8; 1; 5; 4; 9; 2; 9; 5; 5; 1; 7; 5; 2; 8; 1; 0; 9; 3; 2; 7];
  canonical_cons #10 8 [1; 6; 8; 1; 5; 4; 9; 2; 9; 5; 5; 1; 7; 5; 2; 8; 1; 0; 9; 3; 2; 7];
  canonical_cons #10 2 [8; 1; 6; 8; 1; 5; 4; 9; 2; 9; 5; 5; 1; 7; 5; 2; 8; 1; 0; 9; 3; 2; 7];
  canonical_cons #10 0 [2; 8; 1; 6; 8; 1; 5; 4; 9; 2; 9; 5; 5; 1; 7; 5; 2; 8; 1; 0; 9; 3; 2; 7];
  canonical_cons #10 8 [0; 2; 8; 1; 6; 8; 1; 5; 4; 9; 2; 9; 5; 5; 1; 7; 5; 2; 8; 1; 0; 9; 3; 2; 7];
  canonical_cons #10 2 [8; 0; 2; 8; 1; 6; 8; 1; 5; 4; 9; 2; 9; 5; 5; 1; 7; 5; 2; 8; 1; 0; 9; 3; 2; 7];
  canonical_cons #10 2 [2; 8; 0; 2; 8; 1; 6; 8; 1; 5; 4; 9; 2; 9; 5; 5; 1; 7; 5; 2; 8; 1; 0; 9; 3; 2; 7];
  canonical_cons #10 8 [2; 2; 8; 0; 2; 8; 1; 6; 8; 1; 5; 4; 9; 2; 9; 5; 5; 1; 7; 5; 2; 8; 1; 0; 9; 3; 2; 7];
  canonical_cons #10 1 [8; 2; 2; 8; 0; 2; 8; 1; 6; 8; 1; 5; 4; 9; 2; 9; 5; 5; 1; 7; 5; 2; 8; 1; 0; 9; 3; 2; 7];
  ()

let canonical_next19_target () : Lemma (canonical #10 next19_target) =
  assert (canonical #10 [9]);
  canonical_cons #10 0 [9];
  canonical_cons #10 6 [0; 9];
  canonical_cons #10 1 [6; 0; 9];
  canonical_cons #10 8 [1; 6; 0; 9];
  canonical_cons #10 2 [8; 1; 6; 0; 9];
  canonical_cons #10 1 [2; 8; 1; 6; 0; 9];
  canonical_cons #10 0 [1; 2; 8; 1; 6; 0; 9];
  canonical_cons #10 7 [0; 1; 2; 8; 1; 6; 0; 9];
  canonical_cons #10 3 [7; 0; 1; 2; 8; 1; 6; 0; 9];
  canonical_cons #10 9 [3; 7; 0; 1; 2; 8; 1; 6; 0; 9];
  canonical_cons #10 7 [9; 3; 7; 0; 1; 2; 8; 1; 6; 0; 9];
  canonical_cons #10 1 [7; 9; 3; 7; 0; 1; 2; 8; 1; 6; 0; 9];
  canonical_cons #10 4 [1; 7; 9; 3; 7; 0; 1; 2; 8; 1; 6; 0; 9];
  canonical_cons #10 2 [4; 1; 7; 9; 3; 7; 0; 1; 2; 8; 1; 6; 0; 9];
  canonical_cons #10 2 [2; 4; 1; 7; 9; 3; 7; 0; 1; 2; 8; 1; 6; 0; 9];
  canonical_cons #10 4 [2; 2; 4; 1; 7; 9; 3; 7; 0; 1; 2; 8; 1; 6; 0; 9];
  canonical_cons #10 0 [4; 2; 2; 4; 1; 7; 9; 3; 7; 0; 1; 2; 8; 1; 6; 0; 9];
  canonical_cons #10 7 [0; 4; 2; 2; 4; 1; 7; 9; 3; 7; 0; 1; 2; 8; 1; 6; 0; 9];
  canonical_cons #10 0 [7; 0; 4; 2; 2; 4; 1; 7; 9; 3; 7; 0; 1; 2; 8; 1; 6; 0; 9];
  canonical_cons #10 3 [0; 7; 0; 4; 2; 2; 4; 1; 7; 9; 3; 7; 0; 1; 2; 8; 1; 6; 0; 9];
  canonical_cons #10 7 [3; 0; 7; 0; 4; 2; 2; 4; 1; 7; 9; 3; 7; 0; 1; 2; 8; 1; 6; 0; 9];
  canonical_cons #10 1 [7; 3; 0; 7; 0; 4; 2; 2; 4; 1; 7; 9; 3; 7; 0; 1; 2; 8; 1; 6; 0; 9];
  canonical_cons #10 0 [1; 7; 3; 0; 7; 0; 4; 2; 2; 4; 1; 7; 9; 3; 7; 0; 1; 2; 8; 1; 6; 0; 9];
  canonical_cons #10 1 [0; 1; 7; 3; 0; 7; 0; 4; 2; 2; 4; 1; 7; 9; 3; 7; 0; 1; 2; 8; 1; 6; 0; 9];
  canonical_cons #10 9 [1; 0; 1; 7; 3; 0; 7; 0; 4; 2; 2; 4; 1; 7; 9; 3; 7; 0; 1; 2; 8; 1; 6; 0; 9];
  canonical_cons #10 1 [9; 1; 0; 1; 7; 3; 0; 7; 0; 4; 2; 2; 4; 1; 7; 9; 3; 7; 0; 1; 2; 8; 1; 6; 0; 9];
  canonical_cons #10 6 [1; 9; 1; 0; 1; 7; 3; 0; 7; 0; 4; 2; 2; 4; 1; 7; 9; 3; 7; 0; 1; 2; 8; 1; 6; 0; 9];
  canonical_cons #10 0 [6; 1; 9; 1; 0; 1; 7; 3; 0; 7; 0; 4; 2; 2; 4; 1; 7; 9; 3; 7; 0; 1; 2; 8; 1; 6; 0; 9];
  canonical_cons #10 8 [0; 6; 1; 9; 1; 0; 1; 7; 3; 0; 7; 0; 4; 2; 2; 4; 1; 7; 9; 3; 7; 0; 1; 2; 8; 1; 6; 0; 9];
  ()

let reverse_digits_next19_source () : Lemma (
    reverse_digits #10 next19_source == next19_reversed) =
  ReverseAddNext.canonical_next18_target ();
  reverse_list_next19_source ();
  value_next19_reversed ();
  canonical_next19_reversed ();
  reverse_digits_canonical #10 next19_source;
  normalize_value #10 (rev next19_source);
  assert (value (reverse_digits #10 next19_source) ==
    723901825715592945186182082281);
  digits_of_nat_of_canonical #10 (reverse_digits #10 next19_source);
  digits_of_nat_of_canonical #10 next19_reversed;
  assert (reverse_digits #10 next19_source == next19_reversed);
  ()

let reverse_add_182280281681549295517528109327_to_906182107397142240703710191608 () : Lemma (
    reverse_add #10 next19_source == next19_target) =
  ReverseAddNext.canonical_next18_target ();
  reverse_add_value #10 next19_source;
  ReverseAddNext.value_next18_target ();
  reverse_digits_next19_source ();
  value_next19_reversed ();
  value_next19_target ();
  assert (value (reverse_add #10 next19_source) ==
    906182107397142240703710191608);
  reverse_add_canonical #10 next19_source;
  digits_of_nat_of_canonical #10 (reverse_add #10 next19_source);
  canonical_next19_target ();
  digits_of_nat_of_canonical #10 next19_target;
  assert (reverse_add #10 next19_source == next19_target);
  ()

let trace_digits_profile_182280281681549295517528109327 () : Lemma (
    trace_digits next19_source == next19_target) =
  reverse_add_182280281681549295517528109327_to_906182107397142240703710191608 ();
  trace_digits_equals_reverse_add next19_source;
  assert (trace_digits next19_source == next19_target);
  ()

let trace_profile_shape_182280281681549295517528109327 () : Lemma (
    length (trace_digits next19_source) == length next19_source) =
  trace_digits_profile_182280281681549295517528109327 ();
  length_of_eq #(digit 10) (trace_digits next19_source) next19_target;
  assert (length next19_target == length next19_source);
  ()

let trace_profile_final_carry_182280281681549295517528109327 () : Lemma (
    nth (trace_carries next19_source) (length next19_source) == Some 0) =
  trace_profile_shape_182280281681549295517528109327 ();
  final_carry_from_length next19_source;
  ()

let local_profile_witness_906182107397142240703710191608 () : Lemma (
    trace_local_profile_complement_witness next19_target) =
  ReverseAddNext.canonical_next18_target ();
  assert (next19_source <> []);
  trace_profile_shape_182280281681549295517528109327 ();
  trace_profile_final_carry_182280281681549295517528109327 ();
  assert (trace_sum_at next19_source 0 == 8);
  reverse_add_182280281681549295517528109327_to_906182107397142240703710191608 ();
  no_overflow_outer_sum_6_to_9_implies_next_witness next19_source;
  ()

let next20_source : numeral 10 = next19_target

let next20_reversed : numeral 10 =
  [9; 0; 6; 1; 8; 2; 1; 0; 7; 3; 9; 7; 1; 4; 2; 2; 4; 0; 7; 0; 3; 7; 1; 0; 1; 9; 1; 6; 0; 8]

let next20_target : numeral 10 =
  [7; 1; 2; 3; 7; 4; 1; 1; 4; 7; 9; 4; 2; 8; 4; 4; 8; 1; 4; 0; 7; 4; 2; 1; 3; 7; 3; 2; 1; 7; 1]

let reverse_list_next20_source () : Lemma (rev next20_source == next20_reversed) =
  assert (rev [9] == [9]);
  rev_cons 0 [9];
  rev_cons 6 [0; 9];
  rev_cons 1 [6; 0; 9];
  rev_cons 8 [1; 6; 0; 9];
  rev_cons 2 [8; 1; 6; 0; 9];
  rev_cons 1 [2; 8; 1; 6; 0; 9];
  rev_cons 0 [1; 2; 8; 1; 6; 0; 9];
  rev_cons 7 [0; 1; 2; 8; 1; 6; 0; 9];
  rev_cons 3 [7; 0; 1; 2; 8; 1; 6; 0; 9];
  rev_cons 9 [3; 7; 0; 1; 2; 8; 1; 6; 0; 9];
  rev_cons 7 [9; 3; 7; 0; 1; 2; 8; 1; 6; 0; 9];
  rev_cons 1 [7; 9; 3; 7; 0; 1; 2; 8; 1; 6; 0; 9];
  rev_cons 4 [1; 7; 9; 3; 7; 0; 1; 2; 8; 1; 6; 0; 9];
  rev_cons 2 [4; 1; 7; 9; 3; 7; 0; 1; 2; 8; 1; 6; 0; 9];
  rev_cons 2 [2; 4; 1; 7; 9; 3; 7; 0; 1; 2; 8; 1; 6; 0; 9];
  rev_cons 4 [2; 2; 4; 1; 7; 9; 3; 7; 0; 1; 2; 8; 1; 6; 0; 9];
  rev_cons 0 [4; 2; 2; 4; 1; 7; 9; 3; 7; 0; 1; 2; 8; 1; 6; 0; 9];
  rev_cons 7 [0; 4; 2; 2; 4; 1; 7; 9; 3; 7; 0; 1; 2; 8; 1; 6; 0; 9];
  rev_cons 0 [7; 0; 4; 2; 2; 4; 1; 7; 9; 3; 7; 0; 1; 2; 8; 1; 6; 0; 9];
  rev_cons 3 [0; 7; 0; 4; 2; 2; 4; 1; 7; 9; 3; 7; 0; 1; 2; 8; 1; 6; 0; 9];
  rev_cons 7 [3; 0; 7; 0; 4; 2; 2; 4; 1; 7; 9; 3; 7; 0; 1; 2; 8; 1; 6; 0; 9];
  rev_cons 1 [7; 3; 0; 7; 0; 4; 2; 2; 4; 1; 7; 9; 3; 7; 0; 1; 2; 8; 1; 6; 0; 9];
  rev_cons 0 [1; 7; 3; 0; 7; 0; 4; 2; 2; 4; 1; 7; 9; 3; 7; 0; 1; 2; 8; 1; 6; 0; 9];
  rev_cons 1 [0; 1; 7; 3; 0; 7; 0; 4; 2; 2; 4; 1; 7; 9; 3; 7; 0; 1; 2; 8; 1; 6; 0; 9];
  rev_cons 9 [1; 0; 1; 7; 3; 0; 7; 0; 4; 2; 2; 4; 1; 7; 9; 3; 7; 0; 1; 2; 8; 1; 6; 0; 9];
  rev_cons 1 [9; 1; 0; 1; 7; 3; 0; 7; 0; 4; 2; 2; 4; 1; 7; 9; 3; 7; 0; 1; 2; 8; 1; 6; 0; 9];
  rev_cons 6 [1; 9; 1; 0; 1; 7; 3; 0; 7; 0; 4; 2; 2; 4; 1; 7; 9; 3; 7; 0; 1; 2; 8; 1; 6; 0; 9];
  rev_cons 0 [6; 1; 9; 1; 0; 1; 7; 3; 0; 7; 0; 4; 2; 2; 4; 1; 7; 9; 3; 7; 0; 1; 2; 8; 1; 6; 0; 9];
  rev_cons 8 [0; 6; 1; 9; 1; 0; 1; 7; 3; 0; 7; 0; 4; 2; 2; 4; 1; 7; 9; 3; 7; 0; 1; 2; 8; 1; 6; 0; 9];
  ()

let value_next20_reversed_tail_20 () : Lemma (
    value #10 [9; 7; 1; 4; 2; 2; 4; 0; 7; 0; 3; 7; 1; 0; 1; 9; 1; 6; 0; 8] == 80619101730704224179) =
  value_cons #10 9 [7; 1; 4; 2; 2; 4; 0; 7; 0; 3; 7; 1; 0; 1; 9; 1; 6; 0; 8];
  value_cons #10 7 [1; 4; 2; 2; 4; 0; 7; 0; 3; 7; 1; 0; 1; 9; 1; 6; 0; 8];
  value_cons #10 1 [4; 2; 2; 4; 0; 7; 0; 3; 7; 1; 0; 1; 9; 1; 6; 0; 8];
  value_cons #10 4 [2; 2; 4; 0; 7; 0; 3; 7; 1; 0; 1; 9; 1; 6; 0; 8];
  value_cons #10 2 [2; 4; 0; 7; 0; 3; 7; 1; 0; 1; 9; 1; 6; 0; 8];
  value_cons #10 2 [4; 0; 7; 0; 3; 7; 1; 0; 1; 9; 1; 6; 0; 8];
  value_cons #10 4 [0; 7; 0; 3; 7; 1; 0; 1; 9; 1; 6; 0; 8];
  value_cons #10 0 [7; 0; 3; 7; 1; 0; 1; 9; 1; 6; 0; 8];
  value_cons #10 7 [0; 3; 7; 1; 0; 1; 9; 1; 6; 0; 8];
  value_cons #10 0 [3; 7; 1; 0; 1; 9; 1; 6; 0; 8];
  value_cons #10 3 [7; 1; 0; 1; 9; 1; 6; 0; 8];
  value_cons #10 7 [1; 0; 1; 9; 1; 6; 0; 8];
  value_cons #10 1 [0; 1; 9; 1; 6; 0; 8];
  value_cons #10 0 [1; 9; 1; 6; 0; 8];
  value_cons #10 1 [9; 1; 6; 0; 8];
  value_cons #10 9 [1; 6; 0; 8];
  value_cons #10 1 [6; 0; 8];
  value_cons #10 6 [0; 8];
  value_cons #10 0 [8];
  value_cons #10 8 [];
  ()

let value_next20_reversed () : Lemma (
    value next20_reversed == 806191017307042241793701281609) =
  value_cons #10 9 [0; 6; 1; 8; 2; 1; 0; 7; 3];
  value_cons #10 0 [6; 1; 8; 2; 1; 0; 7; 3];
  value_cons #10 6 [1; 8; 2; 1; 0; 7; 3];
  value_cons #10 1 [8; 2; 1; 0; 7; 3];
  value_cons #10 8 [2; 1; 0; 7; 3];
  value_cons #10 2 [1; 0; 7; 3];
  value_cons #10 1 [0; 7; 3];
  value_cons #10 0 [7; 3];
  value_cons #10 7 [3];
  value_cons #10 3 [];
  value_next20_reversed_tail_20 ();
  ()

let value_next20_target_tail_20 () : Lemma (
    value #10 [4; 2; 8; 4; 4; 8; 1; 4; 0; 7; 4; 2; 1; 3; 7; 3; 2; 1; 7; 1] == 17123731247041844824) =
  value_cons #10 4 [2; 8; 4; 4; 8; 1; 4; 0; 7; 4; 2; 1; 3; 7; 3; 2; 1; 7; 1];
  value_cons #10 2 [8; 4; 4; 8; 1; 4; 0; 7; 4; 2; 1; 3; 7; 3; 2; 1; 7; 1];
  value_cons #10 8 [4; 4; 8; 1; 4; 0; 7; 4; 2; 1; 3; 7; 3; 2; 1; 7; 1];
  value_cons #10 4 [4; 8; 1; 4; 0; 7; 4; 2; 1; 3; 7; 3; 2; 1; 7; 1];
  value_cons #10 4 [8; 1; 4; 0; 7; 4; 2; 1; 3; 7; 3; 2; 1; 7; 1];
  value_cons #10 8 [1; 4; 0; 7; 4; 2; 1; 3; 7; 3; 2; 1; 7; 1];
  value_cons #10 1 [4; 0; 7; 4; 2; 1; 3; 7; 3; 2; 1; 7; 1];
  value_cons #10 4 [0; 7; 4; 2; 1; 3; 7; 3; 2; 1; 7; 1];
  value_cons #10 0 [7; 4; 2; 1; 3; 7; 3; 2; 1; 7; 1];
  value_cons #10 7 [4; 2; 1; 3; 7; 3; 2; 1; 7; 1];
  value_cons #10 4 [2; 1; 3; 7; 3; 2; 1; 7; 1];
  value_cons #10 2 [1; 3; 7; 3; 2; 1; 7; 1];
  value_cons #10 1 [3; 7; 3; 2; 1; 7; 1];
  value_cons #10 3 [7; 3; 2; 1; 7; 1];
  value_cons #10 7 [3; 2; 1; 7; 1];
  value_cons #10 3 [2; 1; 7; 1];
  value_cons #10 2 [1; 7; 1];
  value_cons #10 1 [7; 1];
  value_cons #10 7 [1];
  value_cons #10 1 [];
  ()

let value_next20_target () : Lemma (
    value next20_target == 1712373124704184482497411473217) =
  value_cons #10 7 [1; 2; 3; 7; 4; 1; 1; 4; 7; 9];
  value_cons #10 1 [2; 3; 7; 4; 1; 1; 4; 7; 9];
  value_cons #10 2 [3; 7; 4; 1; 1; 4; 7; 9];
  value_cons #10 3 [7; 4; 1; 1; 4; 7; 9];
  value_cons #10 7 [4; 1; 1; 4; 7; 9];
  value_cons #10 4 [1; 1; 4; 7; 9];
  value_cons #10 1 [1; 4; 7; 9];
  value_cons #10 1 [4; 7; 9];
  value_cons #10 4 [7; 9];
  value_cons #10 7 [9];
  value_cons #10 9 [];
  value_next20_target_tail_20 ();
  ()

let canonical_next20_reversed () : Lemma (canonical #10 next20_reversed) =
  assert (canonical #10 [8]);
  canonical_cons #10 0 [8];
  canonical_cons #10 6 [0; 8];
  canonical_cons #10 1 [6; 0; 8];
  canonical_cons #10 9 [1; 6; 0; 8];
  canonical_cons #10 1 [9; 1; 6; 0; 8];
  canonical_cons #10 0 [1; 9; 1; 6; 0; 8];
  canonical_cons #10 1 [0; 1; 9; 1; 6; 0; 8];
  canonical_cons #10 7 [1; 0; 1; 9; 1; 6; 0; 8];
  canonical_cons #10 3 [7; 1; 0; 1; 9; 1; 6; 0; 8];
  canonical_cons #10 0 [3; 7; 1; 0; 1; 9; 1; 6; 0; 8];
  canonical_cons #10 7 [0; 3; 7; 1; 0; 1; 9; 1; 6; 0; 8];
  canonical_cons #10 0 [7; 0; 3; 7; 1; 0; 1; 9; 1; 6; 0; 8];
  canonical_cons #10 4 [0; 7; 0; 3; 7; 1; 0; 1; 9; 1; 6; 0; 8];
  canonical_cons #10 2 [4; 0; 7; 0; 3; 7; 1; 0; 1; 9; 1; 6; 0; 8];
  canonical_cons #10 2 [2; 4; 0; 7; 0; 3; 7; 1; 0; 1; 9; 1; 6; 0; 8];
  canonical_cons #10 4 [2; 2; 4; 0; 7; 0; 3; 7; 1; 0; 1; 9; 1; 6; 0; 8];
  canonical_cons #10 1 [4; 2; 2; 4; 0; 7; 0; 3; 7; 1; 0; 1; 9; 1; 6; 0; 8];
  canonical_cons #10 7 [1; 4; 2; 2; 4; 0; 7; 0; 3; 7; 1; 0; 1; 9; 1; 6; 0; 8];
  canonical_cons #10 9 [7; 1; 4; 2; 2; 4; 0; 7; 0; 3; 7; 1; 0; 1; 9; 1; 6; 0; 8];
  canonical_cons #10 3 [9; 7; 1; 4; 2; 2; 4; 0; 7; 0; 3; 7; 1; 0; 1; 9; 1; 6; 0; 8];
  canonical_cons #10 7 [3; 9; 7; 1; 4; 2; 2; 4; 0; 7; 0; 3; 7; 1; 0; 1; 9; 1; 6; 0; 8];
  canonical_cons #10 0 [7; 3; 9; 7; 1; 4; 2; 2; 4; 0; 7; 0; 3; 7; 1; 0; 1; 9; 1; 6; 0; 8];
  canonical_cons #10 1 [0; 7; 3; 9; 7; 1; 4; 2; 2; 4; 0; 7; 0; 3; 7; 1; 0; 1; 9; 1; 6; 0; 8];
  canonical_cons #10 2 [1; 0; 7; 3; 9; 7; 1; 4; 2; 2; 4; 0; 7; 0; 3; 7; 1; 0; 1; 9; 1; 6; 0; 8];
  canonical_cons #10 8 [2; 1; 0; 7; 3; 9; 7; 1; 4; 2; 2; 4; 0; 7; 0; 3; 7; 1; 0; 1; 9; 1; 6; 0; 8];
  canonical_cons #10 1 [8; 2; 1; 0; 7; 3; 9; 7; 1; 4; 2; 2; 4; 0; 7; 0; 3; 7; 1; 0; 1; 9; 1; 6; 0; 8];
  canonical_cons #10 6 [1; 8; 2; 1; 0; 7; 3; 9; 7; 1; 4; 2; 2; 4; 0; 7; 0; 3; 7; 1; 0; 1; 9; 1; 6; 0; 8];
  canonical_cons #10 0 [6; 1; 8; 2; 1; 0; 7; 3; 9; 7; 1; 4; 2; 2; 4; 0; 7; 0; 3; 7; 1; 0; 1; 9; 1; 6; 0; 8];
  canonical_cons #10 9 [0; 6; 1; 8; 2; 1; 0; 7; 3; 9; 7; 1; 4; 2; 2; 4; 0; 7; 0; 3; 7; 1; 0; 1; 9; 1; 6; 0; 8];
  ()

let canonical_next20_target () : Lemma (canonical #10 next20_target) =
  assert (canonical #10 [1]);
  canonical_cons #10 7 [1];
  canonical_cons #10 1 [7; 1];
  canonical_cons #10 2 [1; 7; 1];
  canonical_cons #10 3 [2; 1; 7; 1];
  canonical_cons #10 7 [3; 2; 1; 7; 1];
  canonical_cons #10 3 [7; 3; 2; 1; 7; 1];
  canonical_cons #10 1 [3; 7; 3; 2; 1; 7; 1];
  canonical_cons #10 2 [1; 3; 7; 3; 2; 1; 7; 1];
  canonical_cons #10 4 [2; 1; 3; 7; 3; 2; 1; 7; 1];
  canonical_cons #10 7 [4; 2; 1; 3; 7; 3; 2; 1; 7; 1];
  canonical_cons #10 0 [7; 4; 2; 1; 3; 7; 3; 2; 1; 7; 1];
  canonical_cons #10 4 [0; 7; 4; 2; 1; 3; 7; 3; 2; 1; 7; 1];
  canonical_cons #10 1 [4; 0; 7; 4; 2; 1; 3; 7; 3; 2; 1; 7; 1];
  canonical_cons #10 8 [1; 4; 0; 7; 4; 2; 1; 3; 7; 3; 2; 1; 7; 1];
  canonical_cons #10 4 [8; 1; 4; 0; 7; 4; 2; 1; 3; 7; 3; 2; 1; 7; 1];
  canonical_cons #10 4 [4; 8; 1; 4; 0; 7; 4; 2; 1; 3; 7; 3; 2; 1; 7; 1];
  canonical_cons #10 8 [4; 4; 8; 1; 4; 0; 7; 4; 2; 1; 3; 7; 3; 2; 1; 7; 1];
  canonical_cons #10 2 [8; 4; 4; 8; 1; 4; 0; 7; 4; 2; 1; 3; 7; 3; 2; 1; 7; 1];
  canonical_cons #10 4 [2; 8; 4; 4; 8; 1; 4; 0; 7; 4; 2; 1; 3; 7; 3; 2; 1; 7; 1];
  canonical_cons #10 9 [4; 2; 8; 4; 4; 8; 1; 4; 0; 7; 4; 2; 1; 3; 7; 3; 2; 1; 7; 1];
  canonical_cons #10 7 [9; 4; 2; 8; 4; 4; 8; 1; 4; 0; 7; 4; 2; 1; 3; 7; 3; 2; 1; 7; 1];
  canonical_cons #10 4 [7; 9; 4; 2; 8; 4; 4; 8; 1; 4; 0; 7; 4; 2; 1; 3; 7; 3; 2; 1; 7; 1];
  canonical_cons #10 1 [4; 7; 9; 4; 2; 8; 4; 4; 8; 1; 4; 0; 7; 4; 2; 1; 3; 7; 3; 2; 1; 7; 1];
  canonical_cons #10 1 [1; 4; 7; 9; 4; 2; 8; 4; 4; 8; 1; 4; 0; 7; 4; 2; 1; 3; 7; 3; 2; 1; 7; 1];
  canonical_cons #10 4 [1; 1; 4; 7; 9; 4; 2; 8; 4; 4; 8; 1; 4; 0; 7; 4; 2; 1; 3; 7; 3; 2; 1; 7; 1];
  canonical_cons #10 7 [4; 1; 1; 4; 7; 9; 4; 2; 8; 4; 4; 8; 1; 4; 0; 7; 4; 2; 1; 3; 7; 3; 2; 1; 7; 1];
  canonical_cons #10 3 [7; 4; 1; 1; 4; 7; 9; 4; 2; 8; 4; 4; 8; 1; 4; 0; 7; 4; 2; 1; 3; 7; 3; 2; 1; 7; 1];
  canonical_cons #10 2 [3; 7; 4; 1; 1; 4; 7; 9; 4; 2; 8; 4; 4; 8; 1; 4; 0; 7; 4; 2; 1; 3; 7; 3; 2; 1; 7; 1];
  canonical_cons #10 1 [2; 3; 7; 4; 1; 1; 4; 7; 9; 4; 2; 8; 4; 4; 8; 1; 4; 0; 7; 4; 2; 1; 3; 7; 3; 2; 1; 7; 1];
  canonical_cons #10 7 [1; 2; 3; 7; 4; 1; 1; 4; 7; 9; 4; 2; 8; 4; 4; 8; 1; 4; 0; 7; 4; 2; 1; 3; 7; 3; 2; 1; 7; 1];
  ()

let reverse_digits_next20_source () : Lemma (
    reverse_digits #10 next20_source == next20_reversed) =
  ReverseAddNext.canonical_next19_target ();
  reverse_list_next20_source ();
  value_next20_reversed ();
  canonical_next20_reversed ();
  reverse_digits_canonical #10 next20_source;
  normalize_value #10 (rev next20_source);
  assert (value (reverse_digits #10 next20_source) ==
    806191017307042241793701281609);
  digits_of_nat_of_canonical #10 (reverse_digits #10 next20_source);
  digits_of_nat_of_canonical #10 next20_reversed;
  assert (reverse_digits #10 next20_source == next20_reversed);
  ()

let reverse_add_906182107397142240703710191608_to_1712373124704184482497411473217 () : Lemma (
    reverse_add #10 next20_source == next20_target) =
  ReverseAddNext.canonical_next19_target ();
  reverse_add_value #10 next20_source;
  ReverseAddNext.value_next19_target ();
  reverse_digits_next20_source ();
  value_next20_reversed ();
  value_next20_target ();
  assert (value (reverse_add #10 next20_source) ==
    1712373124704184482497411473217);
  reverse_add_canonical #10 next20_source;
  digits_of_nat_of_canonical #10 (reverse_add #10 next20_source);
  canonical_next20_target ();
  digits_of_nat_of_canonical #10 next20_target;
  assert (reverse_add #10 next20_source == next20_target);
  ()

let trace_digits_profile_906182107397142240703710191608 () : Lemma (
    trace_digits next20_source == next20_target) =
  reverse_add_906182107397142240703710191608_to_1712373124704184482497411473217 ();
  trace_digits_equals_reverse_add next20_source;
  assert (trace_digits next20_source == next20_target);
  ()

let trace_carries_next20_source () : Lemma (trace_carries next20_source ==
    [0; 1; 0; 1; 0; 1; 0; 0; 0; 1; 0; 0; 1; 0; 0; 0; 0; 0; 0; 1; 1; 0; 1; 0; 0; 0; 1; 0; 1; 0; 1]) =
  reverse_list_next20_source ();
  assert (trace_carries next20_source ==
    (add_trace #10 next20_source next20_reversed 0).carries);
  add_trace_carries_step #10 8 9
    [0; 6; 1; 9; 1; 0; 1; 7; 3; 0; 7; 0; 4; 2; 2; 4; 1; 7; 9; 3; 7; 0; 1; 2; 8; 1; 6; 0; 9]
    [0; 6; 1; 8; 2; 1; 0; 7; 3; 9; 7; 1; 4; 2; 2; 4; 0; 7; 0; 3; 7; 1; 0; 1; 9; 1; 6; 0; 8] 0;
  add_trace_carries_step #10 0 0
    [6; 1; 9; 1; 0; 1; 7; 3; 0; 7; 0; 4; 2; 2; 4; 1; 7; 9; 3; 7; 0; 1; 2; 8; 1; 6; 0; 9]
    [6; 1; 8; 2; 1; 0; 7; 3; 9; 7; 1; 4; 2; 2; 4; 0; 7; 0; 3; 7; 1; 0; 1; 9; 1; 6; 0; 8] 1;
  add_trace_carries_step #10 6 6
    [1; 9; 1; 0; 1; 7; 3; 0; 7; 0; 4; 2; 2; 4; 1; 7; 9; 3; 7; 0; 1; 2; 8; 1; 6; 0; 9]
    [1; 8; 2; 1; 0; 7; 3; 9; 7; 1; 4; 2; 2; 4; 0; 7; 0; 3; 7; 1; 0; 1; 9; 1; 6; 0; 8] 0;
  add_trace_carries_step #10 1 1
    [9; 1; 0; 1; 7; 3; 0; 7; 0; 4; 2; 2; 4; 1; 7; 9; 3; 7; 0; 1; 2; 8; 1; 6; 0; 9]
    [8; 2; 1; 0; 7; 3; 9; 7; 1; 4; 2; 2; 4; 0; 7; 0; 3; 7; 1; 0; 1; 9; 1; 6; 0; 8] 1;
  add_trace_carries_step #10 9 8
    [1; 0; 1; 7; 3; 0; 7; 0; 4; 2; 2; 4; 1; 7; 9; 3; 7; 0; 1; 2; 8; 1; 6; 0; 9]
    [2; 1; 0; 7; 3; 9; 7; 1; 4; 2; 2; 4; 0; 7; 0; 3; 7; 1; 0; 1; 9; 1; 6; 0; 8] 0;
  add_trace_carries_step #10 1 2
    [0; 1; 7; 3; 0; 7; 0; 4; 2; 2; 4; 1; 7; 9; 3; 7; 0; 1; 2; 8; 1; 6; 0; 9]
    [1; 0; 7; 3; 9; 7; 1; 4; 2; 2; 4; 0; 7; 0; 3; 7; 1; 0; 1; 9; 1; 6; 0; 8] 1;
  add_trace_carries_step #10 0 1
    [1; 7; 3; 0; 7; 0; 4; 2; 2; 4; 1; 7; 9; 3; 7; 0; 1; 2; 8; 1; 6; 0; 9]
    [0; 7; 3; 9; 7; 1; 4; 2; 2; 4; 0; 7; 0; 3; 7; 1; 0; 1; 9; 1; 6; 0; 8] 0;
  add_trace_carries_step #10 1 0
    [7; 3; 0; 7; 0; 4; 2; 2; 4; 1; 7; 9; 3; 7; 0; 1; 2; 8; 1; 6; 0; 9]
    [7; 3; 9; 7; 1; 4; 2; 2; 4; 0; 7; 0; 3; 7; 1; 0; 1; 9; 1; 6; 0; 8] 0;
  add_trace_carries_step #10 7 7
    [3; 0; 7; 0; 4; 2; 2; 4; 1; 7; 9; 3; 7; 0; 1; 2; 8; 1; 6; 0; 9]
    [3; 9; 7; 1; 4; 2; 2; 4; 0; 7; 0; 3; 7; 1; 0; 1; 9; 1; 6; 0; 8] 0;
  add_trace_carries_step #10 3 3
    [0; 7; 0; 4; 2; 2; 4; 1; 7; 9; 3; 7; 0; 1; 2; 8; 1; 6; 0; 9]
    [9; 7; 1; 4; 2; 2; 4; 0; 7; 0; 3; 7; 1; 0; 1; 9; 1; 6; 0; 8] 1;
  add_trace_carries_step #10 0 9
    [7; 0; 4; 2; 2; 4; 1; 7; 9; 3; 7; 0; 1; 2; 8; 1; 6; 0; 9]
    [7; 1; 4; 2; 2; 4; 0; 7; 0; 3; 7; 1; 0; 1; 9; 1; 6; 0; 8] 0;
  add_trace_carries_step #10 7 7
    [0; 4; 2; 2; 4; 1; 7; 9; 3; 7; 0; 1; 2; 8; 1; 6; 0; 9]
    [1; 4; 2; 2; 4; 0; 7; 0; 3; 7; 1; 0; 1; 9; 1; 6; 0; 8] 0;
  add_trace_carries_step #10 0 1
    [4; 2; 2; 4; 1; 7; 9; 3; 7; 0; 1; 2; 8; 1; 6; 0; 9]
    [4; 2; 2; 4; 0; 7; 0; 3; 7; 1; 0; 1; 9; 1; 6; 0; 8] 1;
  add_trace_carries_step #10 4 4
    [2; 2; 4; 1; 7; 9; 3; 7; 0; 1; 2; 8; 1; 6; 0; 9]
    [2; 2; 4; 0; 7; 0; 3; 7; 1; 0; 1; 9; 1; 6; 0; 8] 0;
  add_trace_carries_step #10 2 2
    [2; 4; 1; 7; 9; 3; 7; 0; 1; 2; 8; 1; 6; 0; 9]
    [2; 4; 0; 7; 0; 3; 7; 1; 0; 1; 9; 1; 6; 0; 8] 0;
  add_trace_carries_step #10 2 2
    [4; 1; 7; 9; 3; 7; 0; 1; 2; 8; 1; 6; 0; 9]
    [4; 0; 7; 0; 3; 7; 1; 0; 1; 9; 1; 6; 0; 8] 0;
  add_trace_carries_step #10 4 4
    [1; 7; 9; 3; 7; 0; 1; 2; 8; 1; 6; 0; 9]
    [0; 7; 0; 3; 7; 1; 0; 1; 9; 1; 6; 0; 8] 0;
  add_trace_carries_step #10 1 0
    [7; 9; 3; 7; 0; 1; 2; 8; 1; 6; 0; 9]
    [7; 0; 3; 7; 1; 0; 1; 9; 1; 6; 0; 8] 0;
  add_trace_carries_step #10 7 7
    [9; 3; 7; 0; 1; 2; 8; 1; 6; 0; 9]
    [0; 3; 7; 1; 0; 1; 9; 1; 6; 0; 8] 0;
  add_trace_carries_step #10 9 0
    [3; 7; 0; 1; 2; 8; 1; 6; 0; 9]
    [3; 7; 1; 0; 1; 9; 1; 6; 0; 8] 1;
  add_trace_carries_step #10 3 3
    [7; 0; 1; 2; 8; 1; 6; 0; 9]
    [7; 1; 0; 1; 9; 1; 6; 0; 8] 1;
  add_trace_carries_step #10 7 7
    [0; 1; 2; 8; 1; 6; 0; 9]
    [1; 0; 1; 9; 1; 6; 0; 8] 0;
  add_trace_carries_step #10 0 1
    [1; 2; 8; 1; 6; 0; 9]
    [0; 1; 9; 1; 6; 0; 8] 1;
  add_trace_carries_step #10 1 0
    [2; 8; 1; 6; 0; 9]
    [1; 9; 1; 6; 0; 8] 0;
  add_trace_carries_step #10 2 1
    [8; 1; 6; 0; 9]
    [9; 1; 6; 0; 8] 0;
  add_trace_carries_step #10 8 9
    [1; 6; 0; 9]
    [1; 6; 0; 8] 0;
  add_trace_carries_step #10 1 1
    [6; 0; 9]
    [6; 0; 8] 1;
  add_trace_carries_step #10 6 6
    [0; 9]
    [0; 8] 0;
  add_trace_carries_step #10 0 0
    [9]
    [8] 1;
  add_trace_carries_step #10 9 8
    []
    [] 0;
  assert ((add_trace #10 [] [] 1).carries == [1]);
  assert ((add_trace #10 next20_source next20_reversed 0).carries ==
    [0; 1; 0; 1; 0; 1; 0; 0; 0; 1; 0; 0; 1; 0; 0; 0; 0; 0; 0; 1; 1; 0; 1; 0; 0; 0; 1; 0; 1; 0; 1]);
  ()

let trace_profile_shape_906182107397142240703710191608 () : Lemma (
    length (trace_digits next20_source) == length next20_source + 1) =
  trace_digits_profile_906182107397142240703710191608 ();
  length_of_eq #(digit 10) (trace_digits next20_source) next20_target;
  assert (length next20_target == length next20_source + 1);
  ()

let trace_profile_final_carry_906182107397142240703710191608 () : Lemma (
    nth (trace_carries next20_source) (length next20_source) == Some 1) =
  trace_profile_shape_906182107397142240703710191608 ();
  ReverseAddContinuation.final_carry_from_overflow_length next20_source;
  ()

let trace_profile_sums_906182107397142240703710191608 () : Lemma (
    trace_sum_at next20_source 0 == 17 /\
    trace_sum_at next20_source 1 == 0 /\
    trace_sum_at next20_source 4 == 17 /\
    trace_sum_at next20_source 26 == 2 /\
    trace_sum_at next20_source 29 == 17) =
  reverse_list_next20_source ();
  ()

let trace_profile_carry_facts_906182107397142240703710191608 () : Lemma (
    trace_carry_at next20_source 1 == 1 /\
    trace_carry_at next20_source 29 == 0 /\
    trace_carry_at next20_source 2 == 0 /\
    trace_carry_at next20_source 30 == 1 /\
    trace_carry_at next20_source 4 == 0 /\
    trace_carry_at next20_source 26 == 1 /\
    trace_carry_at next20_source 5 == 1 /\
    trace_carry_at next20_source 27 == 0) =
  trace_carries_next20_source ();
  assert (trace_carry_at next20_source 1 == 1);
  assert (trace_carry_at next20_source 29 == 0);
  assert (trace_carry_at next20_source 2 == 0);
  assert (trace_carry_at next20_source 30 == 1);
  assert (trace_carry_at next20_source 4 == 0);
  assert (trace_carry_at next20_source 26 == 1);
  assert (trace_carry_at next20_source 5 == 1);
  assert (trace_carry_at next20_source 27 == 0);
  assert (trace_carries next20_source ==
    [0; 1; 0; 1; 0; 1; 0; 0; 0; 1; 0; 0; 1; 0; 0; 0; 0; 0; 0; 1; 1; 0; 1; 0; 0; 0; 1; 0; 1; 0; 1]);
  ()

let overflow_precondition_906182107397142240703710191608 () : Lemma (
    canonical #10 next20_source /\
    next20_source <> [] /\
    length (trace_digits next20_source) == length next20_source + 1 /\
    nth (trace_carries next20_source) (length next20_source) == Some 1 /\
    1 <= trace_sum_at next20_source 0 /\
    trace_sum_at next20_source 0 <= 18 /\
    trace_sum_at next20_source 0 <> 10 /\
    exists (i:nat). 0 < i /\ i < length next20_source /\
      trace_sum_at next20_source i +
          trace_sum_at next20_source (length next20_source - i) +
          trace_carry_at next20_source i +
          trace_carry_at next20_source (length next20_source - i) >=
        10 + 10 *
          (trace_carry_at next20_source (i + 1) +
           trace_carry_at next20_source (length next20_source - i + 1))) =
  ReverseAddNext.canonical_next19_target ();
  assert (next20_source <> []);
  trace_profile_shape_906182107397142240703710191608 ();
  trace_profile_final_carry_906182107397142240703710191608 ();
  trace_profile_sums_906182107397142240703710191608 ();
  trace_profile_carry_facts_906182107397142240703710191608 ();
  assert (length (trace_digits next20_source) == length next20_source + 1);
  assert (nth (trace_carries next20_source)
    (length next20_source) == Some 1);
  assert (trace_sum_at next20_source 0 == 17);
  assert (trace_sum_at next20_source 1 == 0);
  assert (trace_sum_at next20_source 4 == 17);
  assert (trace_sum_at next20_source 26 == 2);
  assert (trace_sum_at next20_source 29 == 17);
  assert (trace_carry_at next20_source 1 == 1);
  assert (trace_carry_at next20_source 29 == 0);
  assert (trace_carry_at next20_source 2 == 0);
  assert (trace_carry_at next20_source 30 == 1);
  assert (trace_carry_at next20_source 4 == 0);
  assert (trace_carry_at next20_source 26 == 1);
  assert (trace_carry_at next20_source 5 == 1);
  assert (trace_carry_at next20_source 27 == 0);
  assert (1 <= trace_sum_at next20_source 0 /\
    trace_sum_at next20_source 0 <= 18);
  assert (trace_sum_at next20_source 0 <> 10);
  let n : nat = length next20_source in
  assert (0 < 4 /\ 4 < n);
  assert (trace_sum_at next20_source 4 +
      trace_sum_at next20_source (n - 4) +
      trace_carry_at next20_source 4 +
      trace_carry_at next20_source (n - 4) >=
    10 + 10 *
      (trace_carry_at next20_source (4 + 1) +
       trace_carry_at next20_source (n - 4 + 1)));
  exists_intro
    (fun (i:nat) -> 0 < i /\ i < n /\
      trace_sum_at next20_source i +
          trace_sum_at next20_source (n - i) +
          trace_carry_at next20_source i +
          trace_carry_at next20_source (n - i) >=
        10 + 10 *
          (trace_carry_at next20_source (i + 1) +
           trace_carry_at next20_source (n - i + 1)))
    4;
  ()

let local_profile_witness_1712373124704184482497411473217 () : Lemma (
    trace_local_profile_complement_witness next20_target) =
  overflow_precondition_906182107397142240703710191608 ();
  reverse_add_906182107397142240703710191608_to_1712373124704184482497411473217 ();
  overflow_internal_cell_implies_next_witness next20_source;
  ()

let next21_source : numeral 10 = next20_target

let next21_reversed : numeral 10 =
  [1; 7; 1; 2; 3; 7; 3; 1; 2; 4; 7; 0; 4; 1; 8; 4; 4; 8; 2; 4; 9; 7; 4; 1; 1; 4; 7; 3; 2; 1; 7]

let next21_target : numeral 10 =
  [8; 8; 3; 5; 0; 2; 5; 2; 6; 1; 7; 5; 6; 9; 2; 9; 2; 0; 7; 4; 6; 2; 7; 2; 4; 1; 1; 6; 3; 8; 8]

let reverse_list_next21_source () : Lemma (rev next21_source == next21_reversed) =
  assert (rev [1] == [1]);
  rev_cons 7 [1];
  rev_cons 1 [7; 1];
  rev_cons 2 [1; 7; 1];
  rev_cons 3 [2; 1; 7; 1];
  rev_cons 7 [3; 2; 1; 7; 1];
  rev_cons 3 [7; 3; 2; 1; 7; 1];
  rev_cons 1 [3; 7; 3; 2; 1; 7; 1];
  rev_cons 2 [1; 3; 7; 3; 2; 1; 7; 1];
  rev_cons 4 [2; 1; 3; 7; 3; 2; 1; 7; 1];
  rev_cons 7 [4; 2; 1; 3; 7; 3; 2; 1; 7; 1];
  rev_cons 0 [7; 4; 2; 1; 3; 7; 3; 2; 1; 7; 1];
  rev_cons 4 [0; 7; 4; 2; 1; 3; 7; 3; 2; 1; 7; 1];
  rev_cons 1 [4; 0; 7; 4; 2; 1; 3; 7; 3; 2; 1; 7; 1];
  rev_cons 8 [1; 4; 0; 7; 4; 2; 1; 3; 7; 3; 2; 1; 7; 1];
  rev_cons 4 [8; 1; 4; 0; 7; 4; 2; 1; 3; 7; 3; 2; 1; 7; 1];
  rev_cons 4 [4; 8; 1; 4; 0; 7; 4; 2; 1; 3; 7; 3; 2; 1; 7; 1];
  rev_cons 8 [4; 4; 8; 1; 4; 0; 7; 4; 2; 1; 3; 7; 3; 2; 1; 7; 1];
  rev_cons 2 [8; 4; 4; 8; 1; 4; 0; 7; 4; 2; 1; 3; 7; 3; 2; 1; 7; 1];
  rev_cons 4 [2; 8; 4; 4; 8; 1; 4; 0; 7; 4; 2; 1; 3; 7; 3; 2; 1; 7; 1];
  rev_cons 9 [4; 2; 8; 4; 4; 8; 1; 4; 0; 7; 4; 2; 1; 3; 7; 3; 2; 1; 7; 1];
  rev_cons 7 [9; 4; 2; 8; 4; 4; 8; 1; 4; 0; 7; 4; 2; 1; 3; 7; 3; 2; 1; 7; 1];
  rev_cons 4 [7; 9; 4; 2; 8; 4; 4; 8; 1; 4; 0; 7; 4; 2; 1; 3; 7; 3; 2; 1; 7; 1];
  rev_cons 1 [4; 7; 9; 4; 2; 8; 4; 4; 8; 1; 4; 0; 7; 4; 2; 1; 3; 7; 3; 2; 1; 7; 1];
  rev_cons 1 [1; 4; 7; 9; 4; 2; 8; 4; 4; 8; 1; 4; 0; 7; 4; 2; 1; 3; 7; 3; 2; 1; 7; 1];
  rev_cons 4 [1; 1; 4; 7; 9; 4; 2; 8; 4; 4; 8; 1; 4; 0; 7; 4; 2; 1; 3; 7; 3; 2; 1; 7; 1];
  rev_cons 7 [4; 1; 1; 4; 7; 9; 4; 2; 8; 4; 4; 8; 1; 4; 0; 7; 4; 2; 1; 3; 7; 3; 2; 1; 7; 1];
  rev_cons 3 [7; 4; 1; 1; 4; 7; 9; 4; 2; 8; 4; 4; 8; 1; 4; 0; 7; 4; 2; 1; 3; 7; 3; 2; 1; 7; 1];
  rev_cons 2 [3; 7; 4; 1; 1; 4; 7; 9; 4; 2; 8; 4; 4; 8; 1; 4; 0; 7; 4; 2; 1; 3; 7; 3; 2; 1; 7; 1];
  rev_cons 1 [2; 3; 7; 4; 1; 1; 4; 7; 9; 4; 2; 8; 4; 4; 8; 1; 4; 0; 7; 4; 2; 1; 3; 7; 3; 2; 1; 7; 1];
  rev_cons 7 [1; 2; 3; 7; 4; 1; 1; 4; 7; 9; 4; 2; 8; 4; 4; 8; 1; 4; 0; 7; 4; 2; 1; 3; 7; 3; 2; 1; 7; 1];
  ()

let value_next21_reversed_tail_20 () : Lemma (
    value #10 [0; 4; 1; 8; 4; 4; 8; 2; 4; 9; 7; 4; 1; 1; 4; 7; 3; 2; 1; 7] == 71237411479428448140) =
  value_cons #10 0 [4; 1; 8; 4; 4; 8; 2; 4; 9; 7; 4; 1; 1; 4; 7; 3; 2; 1; 7];
  value_cons #10 4 [1; 8; 4; 4; 8; 2; 4; 9; 7; 4; 1; 1; 4; 7; 3; 2; 1; 7];
  value_cons #10 1 [8; 4; 4; 8; 2; 4; 9; 7; 4; 1; 1; 4; 7; 3; 2; 1; 7];
  value_cons #10 8 [4; 4; 8; 2; 4; 9; 7; 4; 1; 1; 4; 7; 3; 2; 1; 7];
  value_cons #10 4 [4; 8; 2; 4; 9; 7; 4; 1; 1; 4; 7; 3; 2; 1; 7];
  value_cons #10 4 [8; 2; 4; 9; 7; 4; 1; 1; 4; 7; 3; 2; 1; 7];
  value_cons #10 8 [2; 4; 9; 7; 4; 1; 1; 4; 7; 3; 2; 1; 7];
  value_cons #10 2 [4; 9; 7; 4; 1; 1; 4; 7; 3; 2; 1; 7];
  value_cons #10 4 [9; 7; 4; 1; 1; 4; 7; 3; 2; 1; 7];
  value_cons #10 9 [7; 4; 1; 1; 4; 7; 3; 2; 1; 7];
  value_cons #10 7 [4; 1; 1; 4; 7; 3; 2; 1; 7];
  value_cons #10 4 [1; 1; 4; 7; 3; 2; 1; 7];
  value_cons #10 1 [1; 4; 7; 3; 2; 1; 7];
  value_cons #10 1 [4; 7; 3; 2; 1; 7];
  value_cons #10 4 [7; 3; 2; 1; 7];
  value_cons #10 7 [3; 2; 1; 7];
  value_cons #10 3 [2; 1; 7];
  value_cons #10 2 [1; 7];
  value_cons #10 1 [7];
  value_cons #10 7 [];
  ()

let value_next21_reversed () : Lemma (
    value next21_reversed == 7123741147942844814074213732171) =
  value_cons #10 1 [7; 1; 2; 3; 7; 3; 1; 2; 4; 7];
  value_cons #10 7 [1; 2; 3; 7; 3; 1; 2; 4; 7];
  value_cons #10 1 [2; 3; 7; 3; 1; 2; 4; 7];
  value_cons #10 2 [3; 7; 3; 1; 2; 4; 7];
  value_cons #10 3 [7; 3; 1; 2; 4; 7];
  value_cons #10 7 [3; 1; 2; 4; 7];
  value_cons #10 3 [1; 2; 4; 7];
  value_cons #10 1 [2; 4; 7];
  value_cons #10 2 [4; 7];
  value_cons #10 4 [7];
  value_cons #10 7 [];
  value_next21_reversed_tail_20 ();
  ()

let value_next21_target_tail_20 () : Lemma (
    value #10 [5; 6; 9; 2; 9; 2; 0; 7; 4; 6; 2; 7; 2; 4; 1; 1; 6; 3; 8; 8] == 88361142726470292965) =
  value_cons #10 5 [6; 9; 2; 9; 2; 0; 7; 4; 6; 2; 7; 2; 4; 1; 1; 6; 3; 8; 8];
  value_cons #10 6 [9; 2; 9; 2; 0; 7; 4; 6; 2; 7; 2; 4; 1; 1; 6; 3; 8; 8];
  value_cons #10 9 [2; 9; 2; 0; 7; 4; 6; 2; 7; 2; 4; 1; 1; 6; 3; 8; 8];
  value_cons #10 2 [9; 2; 0; 7; 4; 6; 2; 7; 2; 4; 1; 1; 6; 3; 8; 8];
  value_cons #10 9 [2; 0; 7; 4; 6; 2; 7; 2; 4; 1; 1; 6; 3; 8; 8];
  value_cons #10 2 [0; 7; 4; 6; 2; 7; 2; 4; 1; 1; 6; 3; 8; 8];
  value_cons #10 0 [7; 4; 6; 2; 7; 2; 4; 1; 1; 6; 3; 8; 8];
  value_cons #10 7 [4; 6; 2; 7; 2; 4; 1; 1; 6; 3; 8; 8];
  value_cons #10 4 [6; 2; 7; 2; 4; 1; 1; 6; 3; 8; 8];
  value_cons #10 6 [2; 7; 2; 4; 1; 1; 6; 3; 8; 8];
  value_cons #10 2 [7; 2; 4; 1; 1; 6; 3; 8; 8];
  value_cons #10 7 [2; 4; 1; 1; 6; 3; 8; 8];
  value_cons #10 2 [4; 1; 1; 6; 3; 8; 8];
  value_cons #10 4 [1; 1; 6; 3; 8; 8];
  value_cons #10 1 [1; 6; 3; 8; 8];
  value_cons #10 1 [6; 3; 8; 8];
  value_cons #10 6 [3; 8; 8];
  value_cons #10 3 [8; 8];
  value_cons #10 8 [8];
  value_cons #10 8 [];
  ()

let value_next21_target () : Lemma (
    value next21_target == 8836114272647029296571625205388) =
  value_cons #10 8 [8; 3; 5; 0; 2; 5; 2; 6; 1; 7];
  value_cons #10 8 [3; 5; 0; 2; 5; 2; 6; 1; 7];
  value_cons #10 3 [5; 0; 2; 5; 2; 6; 1; 7];
  value_cons #10 5 [0; 2; 5; 2; 6; 1; 7];
  value_cons #10 0 [2; 5; 2; 6; 1; 7];
  value_cons #10 2 [5; 2; 6; 1; 7];
  value_cons #10 5 [2; 6; 1; 7];
  value_cons #10 2 [6; 1; 7];
  value_cons #10 6 [1; 7];
  value_cons #10 1 [7];
  value_cons #10 7 [];
  value_next21_target_tail_20 ();
  ()

let canonical_next21_reversed () : Lemma (canonical #10 next21_reversed) =
  assert (canonical #10 [7]);
  canonical_cons #10 1 [7];
  canonical_cons #10 2 [1; 7];
  canonical_cons #10 3 [2; 1; 7];
  canonical_cons #10 7 [3; 2; 1; 7];
  canonical_cons #10 4 [7; 3; 2; 1; 7];
  canonical_cons #10 1 [4; 7; 3; 2; 1; 7];
  canonical_cons #10 1 [1; 4; 7; 3; 2; 1; 7];
  canonical_cons #10 4 [1; 1; 4; 7; 3; 2; 1; 7];
  canonical_cons #10 7 [4; 1; 1; 4; 7; 3; 2; 1; 7];
  canonical_cons #10 9 [7; 4; 1; 1; 4; 7; 3; 2; 1; 7];
  canonical_cons #10 4 [9; 7; 4; 1; 1; 4; 7; 3; 2; 1; 7];
  canonical_cons #10 2 [4; 9; 7; 4; 1; 1; 4; 7; 3; 2; 1; 7];
  canonical_cons #10 8 [2; 4; 9; 7; 4; 1; 1; 4; 7; 3; 2; 1; 7];
  canonical_cons #10 4 [8; 2; 4; 9; 7; 4; 1; 1; 4; 7; 3; 2; 1; 7];
  canonical_cons #10 4 [4; 8; 2; 4; 9; 7; 4; 1; 1; 4; 7; 3; 2; 1; 7];
  canonical_cons #10 8 [4; 4; 8; 2; 4; 9; 7; 4; 1; 1; 4; 7; 3; 2; 1; 7];
  canonical_cons #10 1 [8; 4; 4; 8; 2; 4; 9; 7; 4; 1; 1; 4; 7; 3; 2; 1; 7];
  canonical_cons #10 4 [1; 8; 4; 4; 8; 2; 4; 9; 7; 4; 1; 1; 4; 7; 3; 2; 1; 7];
  canonical_cons #10 0 [4; 1; 8; 4; 4; 8; 2; 4; 9; 7; 4; 1; 1; 4; 7; 3; 2; 1; 7];
  canonical_cons #10 7 [0; 4; 1; 8; 4; 4; 8; 2; 4; 9; 7; 4; 1; 1; 4; 7; 3; 2; 1; 7];
  canonical_cons #10 4 [7; 0; 4; 1; 8; 4; 4; 8; 2; 4; 9; 7; 4; 1; 1; 4; 7; 3; 2; 1; 7];
  canonical_cons #10 2 [4; 7; 0; 4; 1; 8; 4; 4; 8; 2; 4; 9; 7; 4; 1; 1; 4; 7; 3; 2; 1; 7];
  canonical_cons #10 1 [2; 4; 7; 0; 4; 1; 8; 4; 4; 8; 2; 4; 9; 7; 4; 1; 1; 4; 7; 3; 2; 1; 7];
  canonical_cons #10 3 [1; 2; 4; 7; 0; 4; 1; 8; 4; 4; 8; 2; 4; 9; 7; 4; 1; 1; 4; 7; 3; 2; 1; 7];
  canonical_cons #10 7 [3; 1; 2; 4; 7; 0; 4; 1; 8; 4; 4; 8; 2; 4; 9; 7; 4; 1; 1; 4; 7; 3; 2; 1; 7];
  canonical_cons #10 3 [7; 3; 1; 2; 4; 7; 0; 4; 1; 8; 4; 4; 8; 2; 4; 9; 7; 4; 1; 1; 4; 7; 3; 2; 1; 7];
  canonical_cons #10 2 [3; 7; 3; 1; 2; 4; 7; 0; 4; 1; 8; 4; 4; 8; 2; 4; 9; 7; 4; 1; 1; 4; 7; 3; 2; 1; 7];
  canonical_cons #10 1 [2; 3; 7; 3; 1; 2; 4; 7; 0; 4; 1; 8; 4; 4; 8; 2; 4; 9; 7; 4; 1; 1; 4; 7; 3; 2; 1; 7];
  canonical_cons #10 7 [1; 2; 3; 7; 3; 1; 2; 4; 7; 0; 4; 1; 8; 4; 4; 8; 2; 4; 9; 7; 4; 1; 1; 4; 7; 3; 2; 1; 7];
  canonical_cons #10 1 [7; 1; 2; 3; 7; 3; 1; 2; 4; 7; 0; 4; 1; 8; 4; 4; 8; 2; 4; 9; 7; 4; 1; 1; 4; 7; 3; 2; 1; 7];
  ()

let canonical_next21_target () : Lemma (canonical #10 next21_target) =
  assert (canonical #10 [8]);
  canonical_cons #10 8 [8];
  canonical_cons #10 3 [8; 8];
  canonical_cons #10 6 [3; 8; 8];
  canonical_cons #10 1 [6; 3; 8; 8];
  canonical_cons #10 1 [1; 6; 3; 8; 8];
  canonical_cons #10 4 [1; 1; 6; 3; 8; 8];
  canonical_cons #10 2 [4; 1; 1; 6; 3; 8; 8];
  canonical_cons #10 7 [2; 4; 1; 1; 6; 3; 8; 8];
  canonical_cons #10 2 [7; 2; 4; 1; 1; 6; 3; 8; 8];
  canonical_cons #10 6 [2; 7; 2; 4; 1; 1; 6; 3; 8; 8];
  canonical_cons #10 4 [6; 2; 7; 2; 4; 1; 1; 6; 3; 8; 8];
  canonical_cons #10 7 [4; 6; 2; 7; 2; 4; 1; 1; 6; 3; 8; 8];
  canonical_cons #10 0 [7; 4; 6; 2; 7; 2; 4; 1; 1; 6; 3; 8; 8];
  canonical_cons #10 2 [0; 7; 4; 6; 2; 7; 2; 4; 1; 1; 6; 3; 8; 8];
  canonical_cons #10 9 [2; 0; 7; 4; 6; 2; 7; 2; 4; 1; 1; 6; 3; 8; 8];
  canonical_cons #10 2 [9; 2; 0; 7; 4; 6; 2; 7; 2; 4; 1; 1; 6; 3; 8; 8];
  canonical_cons #10 9 [2; 9; 2; 0; 7; 4; 6; 2; 7; 2; 4; 1; 1; 6; 3; 8; 8];
  canonical_cons #10 6 [9; 2; 9; 2; 0; 7; 4; 6; 2; 7; 2; 4; 1; 1; 6; 3; 8; 8];
  canonical_cons #10 5 [6; 9; 2; 9; 2; 0; 7; 4; 6; 2; 7; 2; 4; 1; 1; 6; 3; 8; 8];
  canonical_cons #10 7 [5; 6; 9; 2; 9; 2; 0; 7; 4; 6; 2; 7; 2; 4; 1; 1; 6; 3; 8; 8];
  canonical_cons #10 1 [7; 5; 6; 9; 2; 9; 2; 0; 7; 4; 6; 2; 7; 2; 4; 1; 1; 6; 3; 8; 8];
  canonical_cons #10 6 [1; 7; 5; 6; 9; 2; 9; 2; 0; 7; 4; 6; 2; 7; 2; 4; 1; 1; 6; 3; 8; 8];
  canonical_cons #10 2 [6; 1; 7; 5; 6; 9; 2; 9; 2; 0; 7; 4; 6; 2; 7; 2; 4; 1; 1; 6; 3; 8; 8];
  canonical_cons #10 5 [2; 6; 1; 7; 5; 6; 9; 2; 9; 2; 0; 7; 4; 6; 2; 7; 2; 4; 1; 1; 6; 3; 8; 8];
  canonical_cons #10 2 [5; 2; 6; 1; 7; 5; 6; 9; 2; 9; 2; 0; 7; 4; 6; 2; 7; 2; 4; 1; 1; 6; 3; 8; 8];
  canonical_cons #10 0 [2; 5; 2; 6; 1; 7; 5; 6; 9; 2; 9; 2; 0; 7; 4; 6; 2; 7; 2; 4; 1; 1; 6; 3; 8; 8];
  canonical_cons #10 5 [0; 2; 5; 2; 6; 1; 7; 5; 6; 9; 2; 9; 2; 0; 7; 4; 6; 2; 7; 2; 4; 1; 1; 6; 3; 8; 8];
  canonical_cons #10 3 [5; 0; 2; 5; 2; 6; 1; 7; 5; 6; 9; 2; 9; 2; 0; 7; 4; 6; 2; 7; 2; 4; 1; 1; 6; 3; 8; 8];
  canonical_cons #10 8 [3; 5; 0; 2; 5; 2; 6; 1; 7; 5; 6; 9; 2; 9; 2; 0; 7; 4; 6; 2; 7; 2; 4; 1; 1; 6; 3; 8; 8];
  canonical_cons #10 8 [8; 3; 5; 0; 2; 5; 2; 6; 1; 7; 5; 6; 9; 2; 9; 2; 0; 7; 4; 6; 2; 7; 2; 4; 1; 1; 6; 3; 8; 8];
  ()

let reverse_digits_next21_source () : Lemma (
    reverse_digits #10 next21_source == next21_reversed) =
  ReverseAddNext.canonical_next20_target ();
  reverse_list_next21_source ();
  value_next21_reversed ();
  canonical_next21_reversed ();
  reverse_digits_canonical #10 next21_source;
  normalize_value #10 (rev next21_source);
  assert (value (reverse_digits #10 next21_source) ==
    7123741147942844814074213732171);
  digits_of_nat_of_canonical #10 (reverse_digits #10 next21_source);
  digits_of_nat_of_canonical #10 next21_reversed;
  assert (reverse_digits #10 next21_source == next21_reversed);
  ()

let reverse_add_1712373124704184482497411473217_to_8836114272647029296571625205388 () : Lemma (
    reverse_add #10 next21_source == next21_target) =
  ReverseAddNext.canonical_next20_target ();
  reverse_add_value #10 next21_source;
  ReverseAddNext.value_next20_target ();
  reverse_digits_next21_source ();
  value_next21_reversed ();
  value_next21_target ();
  assert (value (reverse_add #10 next21_source) ==
    8836114272647029296571625205388);
  reverse_add_canonical #10 next21_source;
  digits_of_nat_of_canonical #10 (reverse_add #10 next21_source);
  canonical_next21_target ();
  digits_of_nat_of_canonical #10 next21_target;
  assert (reverse_add #10 next21_source == next21_target);
  ()

let trace_digits_profile_1712373124704184482497411473217 () : Lemma (
    trace_digits next21_source == next21_target) =
  reverse_add_1712373124704184482497411473217_to_8836114272647029296571625205388 ();
  trace_digits_equals_reverse_add next21_source;
  assert (trace_digits next21_source == next21_target);
  ()

let trace_profile_shape_1712373124704184482497411473217 () : Lemma (
    length (trace_digits next21_source) == length next21_source) =
  trace_digits_profile_1712373124704184482497411473217 ();
  length_of_eq #(digit 10) (trace_digits next21_source) next21_target;
  assert (length next21_target == length next21_source);
  ()

let trace_profile_final_carry_1712373124704184482497411473217 () : Lemma (
    nth (trace_carries next21_source) (length next21_source) == Some 0) =
  trace_profile_shape_1712373124704184482497411473217 ();
  final_carry_from_length next21_source;
  ()

let local_profile_witness_8836114272647029296571625205388 () : Lemma (
    trace_local_profile_complement_witness next21_target) =
  ReverseAddNext.canonical_next20_target ();
  assert (next21_source <> []);
  trace_profile_shape_1712373124704184482497411473217 ();
  trace_profile_final_carry_1712373124704184482497411473217 ();
  assert (trace_sum_at next21_source 0 == 8);
  reverse_add_1712373124704184482497411473217_to_8836114272647029296571625205388 ();
  no_overflow_outer_sum_6_to_9_implies_next_witness next21_source;
  ()

let next22_source : numeral 10 = next21_target

let next22_reversed : numeral 10 =
  [8; 8; 3; 6; 1; 1; 4; 2; 7; 2; 6; 4; 7; 0; 2; 9; 2; 9; 6; 5; 7; 1; 6; 2; 5; 2; 0; 5; 3; 8; 8]

let next22_target : numeral 10 =
  [6; 7; 7; 1; 2; 3; 9; 4; 3; 4; 3; 0; 4; 0; 5; 8; 5; 9; 3; 0; 4; 4; 3; 5; 9; 3; 1; 1; 7; 6; 7; 1]

let reverse_list_next22_source () : Lemma (rev next22_source == next22_reversed) =
  assert (rev [8] == [8]);
  rev_cons 8 [8];
  rev_cons 3 [8; 8];
  rev_cons 6 [3; 8; 8];
  rev_cons 1 [6; 3; 8; 8];
  rev_cons 1 [1; 6; 3; 8; 8];
  rev_cons 4 [1; 1; 6; 3; 8; 8];
  rev_cons 2 [4; 1; 1; 6; 3; 8; 8];
  rev_cons 7 [2; 4; 1; 1; 6; 3; 8; 8];
  rev_cons 2 [7; 2; 4; 1; 1; 6; 3; 8; 8];
  rev_cons 6 [2; 7; 2; 4; 1; 1; 6; 3; 8; 8];
  rev_cons 4 [6; 2; 7; 2; 4; 1; 1; 6; 3; 8; 8];
  rev_cons 7 [4; 6; 2; 7; 2; 4; 1; 1; 6; 3; 8; 8];
  rev_cons 0 [7; 4; 6; 2; 7; 2; 4; 1; 1; 6; 3; 8; 8];
  rev_cons 2 [0; 7; 4; 6; 2; 7; 2; 4; 1; 1; 6; 3; 8; 8];
  rev_cons 9 [2; 0; 7; 4; 6; 2; 7; 2; 4; 1; 1; 6; 3; 8; 8];
  rev_cons 2 [9; 2; 0; 7; 4; 6; 2; 7; 2; 4; 1; 1; 6; 3; 8; 8];
  rev_cons 9 [2; 9; 2; 0; 7; 4; 6; 2; 7; 2; 4; 1; 1; 6; 3; 8; 8];
  rev_cons 6 [9; 2; 9; 2; 0; 7; 4; 6; 2; 7; 2; 4; 1; 1; 6; 3; 8; 8];
  rev_cons 5 [6; 9; 2; 9; 2; 0; 7; 4; 6; 2; 7; 2; 4; 1; 1; 6; 3; 8; 8];
  rev_cons 7 [5; 6; 9; 2; 9; 2; 0; 7; 4; 6; 2; 7; 2; 4; 1; 1; 6; 3; 8; 8];
  rev_cons 1 [7; 5; 6; 9; 2; 9; 2; 0; 7; 4; 6; 2; 7; 2; 4; 1; 1; 6; 3; 8; 8];
  rev_cons 6 [1; 7; 5; 6; 9; 2; 9; 2; 0; 7; 4; 6; 2; 7; 2; 4; 1; 1; 6; 3; 8; 8];
  rev_cons 2 [6; 1; 7; 5; 6; 9; 2; 9; 2; 0; 7; 4; 6; 2; 7; 2; 4; 1; 1; 6; 3; 8; 8];
  rev_cons 5 [2; 6; 1; 7; 5; 6; 9; 2; 9; 2; 0; 7; 4; 6; 2; 7; 2; 4; 1; 1; 6; 3; 8; 8];
  rev_cons 2 [5; 2; 6; 1; 7; 5; 6; 9; 2; 9; 2; 0; 7; 4; 6; 2; 7; 2; 4; 1; 1; 6; 3; 8; 8];
  rev_cons 0 [2; 5; 2; 6; 1; 7; 5; 6; 9; 2; 9; 2; 0; 7; 4; 6; 2; 7; 2; 4; 1; 1; 6; 3; 8; 8];
  rev_cons 5 [0; 2; 5; 2; 6; 1; 7; 5; 6; 9; 2; 9; 2; 0; 7; 4; 6; 2; 7; 2; 4; 1; 1; 6; 3; 8; 8];
  rev_cons 3 [5; 0; 2; 5; 2; 6; 1; 7; 5; 6; 9; 2; 9; 2; 0; 7; 4; 6; 2; 7; 2; 4; 1; 1; 6; 3; 8; 8];
  rev_cons 8 [3; 5; 0; 2; 5; 2; 6; 1; 7; 5; 6; 9; 2; 9; 2; 0; 7; 4; 6; 2; 7; 2; 4; 1; 1; 6; 3; 8; 8];
  rev_cons 8 [8; 3; 5; 0; 2; 5; 2; 6; 1; 7; 5; 6; 9; 2; 9; 2; 0; 7; 4; 6; 2; 7; 2; 4; 1; 1; 6; 3; 8; 8];
  ()

let value_next22_reversed_tail_20 () : Lemma (
    value #10 [4; 7; 0; 2; 9; 2; 9; 6; 5; 7; 1; 6; 2; 5; 2; 0; 5; 3; 8; 8] == 88350252617569292074) =
  value_cons #10 4 [7; 0; 2; 9; 2; 9; 6; 5; 7; 1; 6; 2; 5; 2; 0; 5; 3; 8; 8];
  value_cons #10 7 [0; 2; 9; 2; 9; 6; 5; 7; 1; 6; 2; 5; 2; 0; 5; 3; 8; 8];
  value_cons #10 0 [2; 9; 2; 9; 6; 5; 7; 1; 6; 2; 5; 2; 0; 5; 3; 8; 8];
  value_cons #10 2 [9; 2; 9; 6; 5; 7; 1; 6; 2; 5; 2; 0; 5; 3; 8; 8];
  value_cons #10 9 [2; 9; 6; 5; 7; 1; 6; 2; 5; 2; 0; 5; 3; 8; 8];
  value_cons #10 2 [9; 6; 5; 7; 1; 6; 2; 5; 2; 0; 5; 3; 8; 8];
  value_cons #10 9 [6; 5; 7; 1; 6; 2; 5; 2; 0; 5; 3; 8; 8];
  value_cons #10 6 [5; 7; 1; 6; 2; 5; 2; 0; 5; 3; 8; 8];
  value_cons #10 5 [7; 1; 6; 2; 5; 2; 0; 5; 3; 8; 8];
  value_cons #10 7 [1; 6; 2; 5; 2; 0; 5; 3; 8; 8];
  value_cons #10 1 [6; 2; 5; 2; 0; 5; 3; 8; 8];
  value_cons #10 6 [2; 5; 2; 0; 5; 3; 8; 8];
  value_cons #10 2 [5; 2; 0; 5; 3; 8; 8];
  value_cons #10 5 [2; 0; 5; 3; 8; 8];
  value_cons #10 2 [0; 5; 3; 8; 8];
  value_cons #10 0 [5; 3; 8; 8];
  value_cons #10 5 [3; 8; 8];
  value_cons #10 3 [8; 8];
  value_cons #10 8 [8];
  value_cons #10 8 [];
  ()

let value_next22_reversed () : Lemma (
    value next22_reversed == 8835025261756929207462724116388) =
  value_cons #10 8 [8; 3; 6; 1; 1; 4; 2; 7; 2; 6];
  value_cons #10 8 [3; 6; 1; 1; 4; 2; 7; 2; 6];
  value_cons #10 3 [6; 1; 1; 4; 2; 7; 2; 6];
  value_cons #10 6 [1; 1; 4; 2; 7; 2; 6];
  value_cons #10 1 [1; 4; 2; 7; 2; 6];
  value_cons #10 1 [4; 2; 7; 2; 6];
  value_cons #10 4 [2; 7; 2; 6];
  value_cons #10 2 [7; 2; 6];
  value_cons #10 7 [2; 6];
  value_cons #10 2 [6];
  value_cons #10 6 [];
  value_next22_reversed_tail_20 ();
  ()

let value_next22_target_tail_20 () : Lemma (
    value #10 [4; 0; 5; 8; 5; 9; 3; 0; 4; 4; 3; 5; 9; 3; 1; 1; 7; 6; 7; 1] == 17671139534403958504) =
  value_cons #10 4 [0; 5; 8; 5; 9; 3; 0; 4; 4; 3; 5; 9; 3; 1; 1; 7; 6; 7; 1];
  value_cons #10 0 [5; 8; 5; 9; 3; 0; 4; 4; 3; 5; 9; 3; 1; 1; 7; 6; 7; 1];
  value_cons #10 5 [8; 5; 9; 3; 0; 4; 4; 3; 5; 9; 3; 1; 1; 7; 6; 7; 1];
  value_cons #10 8 [5; 9; 3; 0; 4; 4; 3; 5; 9; 3; 1; 1; 7; 6; 7; 1];
  value_cons #10 5 [9; 3; 0; 4; 4; 3; 5; 9; 3; 1; 1; 7; 6; 7; 1];
  value_cons #10 9 [3; 0; 4; 4; 3; 5; 9; 3; 1; 1; 7; 6; 7; 1];
  value_cons #10 3 [0; 4; 4; 3; 5; 9; 3; 1; 1; 7; 6; 7; 1];
  value_cons #10 0 [4; 4; 3; 5; 9; 3; 1; 1; 7; 6; 7; 1];
  value_cons #10 4 [4; 3; 5; 9; 3; 1; 1; 7; 6; 7; 1];
  value_cons #10 4 [3; 5; 9; 3; 1; 1; 7; 6; 7; 1];
  value_cons #10 3 [5; 9; 3; 1; 1; 7; 6; 7; 1];
  value_cons #10 5 [9; 3; 1; 1; 7; 6; 7; 1];
  value_cons #10 9 [3; 1; 1; 7; 6; 7; 1];
  value_cons #10 3 [1; 1; 7; 6; 7; 1];
  value_cons #10 1 [1; 7; 6; 7; 1];
  value_cons #10 1 [7; 6; 7; 1];
  value_cons #10 7 [6; 7; 1];
  value_cons #10 6 [7; 1];
  value_cons #10 7 [1];
  value_cons #10 1 [];
  ()

let value_next22_target () : Lemma (
    value next22_target == 17671139534403958504034349321776) =
  value_cons #10 6 [7; 7; 1; 2; 3; 9; 4; 3; 4; 3; 0];
  value_cons #10 7 [7; 1; 2; 3; 9; 4; 3; 4; 3; 0];
  value_cons #10 7 [1; 2; 3; 9; 4; 3; 4; 3; 0];
  value_cons #10 1 [2; 3; 9; 4; 3; 4; 3; 0];
  value_cons #10 2 [3; 9; 4; 3; 4; 3; 0];
  value_cons #10 3 [9; 4; 3; 4; 3; 0];
  value_cons #10 9 [4; 3; 4; 3; 0];
  value_cons #10 4 [3; 4; 3; 0];
  value_cons #10 3 [4; 3; 0];
  value_cons #10 4 [3; 0];
  value_cons #10 3 [0];
  value_cons #10 0 [];
  value_next22_target_tail_20 ();
  ()

let canonical_next22_reversed () : Lemma (canonical #10 next22_reversed) =
  assert (canonical #10 [8]);
  canonical_cons #10 8 [8];
  canonical_cons #10 3 [8; 8];
  canonical_cons #10 5 [3; 8; 8];
  canonical_cons #10 0 [5; 3; 8; 8];
  canonical_cons #10 2 [0; 5; 3; 8; 8];
  canonical_cons #10 5 [2; 0; 5; 3; 8; 8];
  canonical_cons #10 2 [5; 2; 0; 5; 3; 8; 8];
  canonical_cons #10 6 [2; 5; 2; 0; 5; 3; 8; 8];
  canonical_cons #10 1 [6; 2; 5; 2; 0; 5; 3; 8; 8];
  canonical_cons #10 7 [1; 6; 2; 5; 2; 0; 5; 3; 8; 8];
  canonical_cons #10 5 [7; 1; 6; 2; 5; 2; 0; 5; 3; 8; 8];
  canonical_cons #10 6 [5; 7; 1; 6; 2; 5; 2; 0; 5; 3; 8; 8];
  canonical_cons #10 9 [6; 5; 7; 1; 6; 2; 5; 2; 0; 5; 3; 8; 8];
  canonical_cons #10 2 [9; 6; 5; 7; 1; 6; 2; 5; 2; 0; 5; 3; 8; 8];
  canonical_cons #10 9 [2; 9; 6; 5; 7; 1; 6; 2; 5; 2; 0; 5; 3; 8; 8];
  canonical_cons #10 2 [9; 2; 9; 6; 5; 7; 1; 6; 2; 5; 2; 0; 5; 3; 8; 8];
  canonical_cons #10 0 [2; 9; 2; 9; 6; 5; 7; 1; 6; 2; 5; 2; 0; 5; 3; 8; 8];
  canonical_cons #10 7 [0; 2; 9; 2; 9; 6; 5; 7; 1; 6; 2; 5; 2; 0; 5; 3; 8; 8];
  canonical_cons #10 4 [7; 0; 2; 9; 2; 9; 6; 5; 7; 1; 6; 2; 5; 2; 0; 5; 3; 8; 8];
  canonical_cons #10 6 [4; 7; 0; 2; 9; 2; 9; 6; 5; 7; 1; 6; 2; 5; 2; 0; 5; 3; 8; 8];
  canonical_cons #10 2 [6; 4; 7; 0; 2; 9; 2; 9; 6; 5; 7; 1; 6; 2; 5; 2; 0; 5; 3; 8; 8];
  canonical_cons #10 7 [2; 6; 4; 7; 0; 2; 9; 2; 9; 6; 5; 7; 1; 6; 2; 5; 2; 0; 5; 3; 8; 8];
  canonical_cons #10 2 [7; 2; 6; 4; 7; 0; 2; 9; 2; 9; 6; 5; 7; 1; 6; 2; 5; 2; 0; 5; 3; 8; 8];
  canonical_cons #10 4 [2; 7; 2; 6; 4; 7; 0; 2; 9; 2; 9; 6; 5; 7; 1; 6; 2; 5; 2; 0; 5; 3; 8; 8];
  canonical_cons #10 1 [4; 2; 7; 2; 6; 4; 7; 0; 2; 9; 2; 9; 6; 5; 7; 1; 6; 2; 5; 2; 0; 5; 3; 8; 8];
  canonical_cons #10 1 [1; 4; 2; 7; 2; 6; 4; 7; 0; 2; 9; 2; 9; 6; 5; 7; 1; 6; 2; 5; 2; 0; 5; 3; 8; 8];
  canonical_cons #10 6 [1; 1; 4; 2; 7; 2; 6; 4; 7; 0; 2; 9; 2; 9; 6; 5; 7; 1; 6; 2; 5; 2; 0; 5; 3; 8; 8];
  canonical_cons #10 3 [6; 1; 1; 4; 2; 7; 2; 6; 4; 7; 0; 2; 9; 2; 9; 6; 5; 7; 1; 6; 2; 5; 2; 0; 5; 3; 8; 8];
  canonical_cons #10 8 [3; 6; 1; 1; 4; 2; 7; 2; 6; 4; 7; 0; 2; 9; 2; 9; 6; 5; 7; 1; 6; 2; 5; 2; 0; 5; 3; 8; 8];
  canonical_cons #10 8 [8; 3; 6; 1; 1; 4; 2; 7; 2; 6; 4; 7; 0; 2; 9; 2; 9; 6; 5; 7; 1; 6; 2; 5; 2; 0; 5; 3; 8; 8];
  ()

let canonical_next22_target () : Lemma (canonical #10 next22_target) =
  assert (canonical #10 [1]);
  canonical_cons #10 7 [1];
  canonical_cons #10 6 [7; 1];
  canonical_cons #10 7 [6; 7; 1];
  canonical_cons #10 1 [7; 6; 7; 1];
  canonical_cons #10 1 [1; 7; 6; 7; 1];
  canonical_cons #10 3 [1; 1; 7; 6; 7; 1];
  canonical_cons #10 9 [3; 1; 1; 7; 6; 7; 1];
  canonical_cons #10 5 [9; 3; 1; 1; 7; 6; 7; 1];
  canonical_cons #10 3 [5; 9; 3; 1; 1; 7; 6; 7; 1];
  canonical_cons #10 4 [3; 5; 9; 3; 1; 1; 7; 6; 7; 1];
  canonical_cons #10 4 [4; 3; 5; 9; 3; 1; 1; 7; 6; 7; 1];
  canonical_cons #10 0 [4; 4; 3; 5; 9; 3; 1; 1; 7; 6; 7; 1];
  canonical_cons #10 3 [0; 4; 4; 3; 5; 9; 3; 1; 1; 7; 6; 7; 1];
  canonical_cons #10 9 [3; 0; 4; 4; 3; 5; 9; 3; 1; 1; 7; 6; 7; 1];
  canonical_cons #10 5 [9; 3; 0; 4; 4; 3; 5; 9; 3; 1; 1; 7; 6; 7; 1];
  canonical_cons #10 8 [5; 9; 3; 0; 4; 4; 3; 5; 9; 3; 1; 1; 7; 6; 7; 1];
  canonical_cons #10 5 [8; 5; 9; 3; 0; 4; 4; 3; 5; 9; 3; 1; 1; 7; 6; 7; 1];
  canonical_cons #10 0 [5; 8; 5; 9; 3; 0; 4; 4; 3; 5; 9; 3; 1; 1; 7; 6; 7; 1];
  canonical_cons #10 4 [0; 5; 8; 5; 9; 3; 0; 4; 4; 3; 5; 9; 3; 1; 1; 7; 6; 7; 1];
  canonical_cons #10 0 [4; 0; 5; 8; 5; 9; 3; 0; 4; 4; 3; 5; 9; 3; 1; 1; 7; 6; 7; 1];
  canonical_cons #10 3 [0; 4; 0; 5; 8; 5; 9; 3; 0; 4; 4; 3; 5; 9; 3; 1; 1; 7; 6; 7; 1];
  canonical_cons #10 4 [3; 0; 4; 0; 5; 8; 5; 9; 3; 0; 4; 4; 3; 5; 9; 3; 1; 1; 7; 6; 7; 1];
  canonical_cons #10 3 [4; 3; 0; 4; 0; 5; 8; 5; 9; 3; 0; 4; 4; 3; 5; 9; 3; 1; 1; 7; 6; 7; 1];
  canonical_cons #10 4 [3; 4; 3; 0; 4; 0; 5; 8; 5; 9; 3; 0; 4; 4; 3; 5; 9; 3; 1; 1; 7; 6; 7; 1];
  canonical_cons #10 9 [4; 3; 4; 3; 0; 4; 0; 5; 8; 5; 9; 3; 0; 4; 4; 3; 5; 9; 3; 1; 1; 7; 6; 7; 1];
  canonical_cons #10 3 [9; 4; 3; 4; 3; 0; 4; 0; 5; 8; 5; 9; 3; 0; 4; 4; 3; 5; 9; 3; 1; 1; 7; 6; 7; 1];
  canonical_cons #10 2 [3; 9; 4; 3; 4; 3; 0; 4; 0; 5; 8; 5; 9; 3; 0; 4; 4; 3; 5; 9; 3; 1; 1; 7; 6; 7; 1];
  canonical_cons #10 1 [2; 3; 9; 4; 3; 4; 3; 0; 4; 0; 5; 8; 5; 9; 3; 0; 4; 4; 3; 5; 9; 3; 1; 1; 7; 6; 7; 1];
  canonical_cons #10 7 [1; 2; 3; 9; 4; 3; 4; 3; 0; 4; 0; 5; 8; 5; 9; 3; 0; 4; 4; 3; 5; 9; 3; 1; 1; 7; 6; 7; 1];
  canonical_cons #10 7 [7; 1; 2; 3; 9; 4; 3; 4; 3; 0; 4; 0; 5; 8; 5; 9; 3; 0; 4; 4; 3; 5; 9; 3; 1; 1; 7; 6; 7; 1];
  canonical_cons #10 6 [7; 7; 1; 2; 3; 9; 4; 3; 4; 3; 0; 4; 0; 5; 8; 5; 9; 3; 0; 4; 4; 3; 5; 9; 3; 1; 1; 7; 6; 7; 1];
  ()

let reverse_digits_next22_source () : Lemma (
    reverse_digits #10 next22_source == next22_reversed) =
  ReverseAddNext.canonical_next21_target ();
  reverse_list_next22_source ();
  value_next22_reversed ();
  canonical_next22_reversed ();
  reverse_digits_canonical #10 next22_source;
  normalize_value #10 (rev next22_source);
  assert (value (reverse_digits #10 next22_source) ==
    8835025261756929207462724116388);
  digits_of_nat_of_canonical #10 (reverse_digits #10 next22_source);
  digits_of_nat_of_canonical #10 next22_reversed;
  assert (reverse_digits #10 next22_source == next22_reversed);
  ()

let reverse_add_8836114272647029296571625205388_to_17671139534403958504034349321776 () : Lemma (
    reverse_add #10 next22_source == next22_target) =
  ReverseAddNext.canonical_next21_target ();
  reverse_add_value #10 next22_source;
  ReverseAddNext.value_next21_target ();
  reverse_digits_next22_source ();
  value_next22_reversed ();
  value_next22_target ();
  assert (value (reverse_add #10 next22_source) ==
    17671139534403958504034349321776);
  reverse_add_canonical #10 next22_source;
  digits_of_nat_of_canonical #10 (reverse_add #10 next22_source);
  canonical_next22_target ();
  digits_of_nat_of_canonical #10 next22_target;
  assert (reverse_add #10 next22_source == next22_target);
  ()

let trace_digits_profile_8836114272647029296571625205388 () : Lemma (
    trace_digits next22_source == next22_target) =
  reverse_add_8836114272647029296571625205388_to_17671139534403958504034349321776 ();
  trace_digits_equals_reverse_add next22_source;
  assert (trace_digits next22_source == next22_target);
  ()

let trace_carries_next22_source () : Lemma (trace_carries next22_source ==
    [0; 1; 1; 0; 1; 0; 0; 0; 0; 1; 0; 1; 1; 1; 1; 0; 1; 0; 0; 1; 1; 1; 0; 1; 0; 0; 0; 0; 1; 0; 1; 1]) =
  reverse_list_next22_source ();
  assert (trace_carries next22_source ==
    (add_trace #10 next22_source next22_reversed 0).carries);
  add_trace_carries_step #10 8 8
    [8; 3; 5; 0; 2; 5; 2; 6; 1; 7; 5; 6; 9; 2; 9; 2; 0; 7; 4; 6; 2; 7; 2; 4; 1; 1; 6; 3; 8; 8]
    [8; 3; 6; 1; 1; 4; 2; 7; 2; 6; 4; 7; 0; 2; 9; 2; 9; 6; 5; 7; 1; 6; 2; 5; 2; 0; 5; 3; 8; 8] 0;
  add_trace_carries_step #10 8 8
    [3; 5; 0; 2; 5; 2; 6; 1; 7; 5; 6; 9; 2; 9; 2; 0; 7; 4; 6; 2; 7; 2; 4; 1; 1; 6; 3; 8; 8]
    [3; 6; 1; 1; 4; 2; 7; 2; 6; 4; 7; 0; 2; 9; 2; 9; 6; 5; 7; 1; 6; 2; 5; 2; 0; 5; 3; 8; 8] 1;
  add_trace_carries_step #10 3 3
    [5; 0; 2; 5; 2; 6; 1; 7; 5; 6; 9; 2; 9; 2; 0; 7; 4; 6; 2; 7; 2; 4; 1; 1; 6; 3; 8; 8]
    [6; 1; 1; 4; 2; 7; 2; 6; 4; 7; 0; 2; 9; 2; 9; 6; 5; 7; 1; 6; 2; 5; 2; 0; 5; 3; 8; 8] 1;
  add_trace_carries_step #10 5 6
    [0; 2; 5; 2; 6; 1; 7; 5; 6; 9; 2; 9; 2; 0; 7; 4; 6; 2; 7; 2; 4; 1; 1; 6; 3; 8; 8]
    [1; 1; 4; 2; 7; 2; 6; 4; 7; 0; 2; 9; 2; 9; 6; 5; 7; 1; 6; 2; 5; 2; 0; 5; 3; 8; 8] 0;
  add_trace_carries_step #10 0 1
    [2; 5; 2; 6; 1; 7; 5; 6; 9; 2; 9; 2; 0; 7; 4; 6; 2; 7; 2; 4; 1; 1; 6; 3; 8; 8]
    [1; 4; 2; 7; 2; 6; 4; 7; 0; 2; 9; 2; 9; 6; 5; 7; 1; 6; 2; 5; 2; 0; 5; 3; 8; 8] 1;
  add_trace_carries_step #10 2 1
    [5; 2; 6; 1; 7; 5; 6; 9; 2; 9; 2; 0; 7; 4; 6; 2; 7; 2; 4; 1; 1; 6; 3; 8; 8]
    [4; 2; 7; 2; 6; 4; 7; 0; 2; 9; 2; 9; 6; 5; 7; 1; 6; 2; 5; 2; 0; 5; 3; 8; 8] 0;
  add_trace_carries_step #10 5 4
    [2; 6; 1; 7; 5; 6; 9; 2; 9; 2; 0; 7; 4; 6; 2; 7; 2; 4; 1; 1; 6; 3; 8; 8]
    [2; 7; 2; 6; 4; 7; 0; 2; 9; 2; 9; 6; 5; 7; 1; 6; 2; 5; 2; 0; 5; 3; 8; 8] 0;
  add_trace_carries_step #10 2 2
    [6; 1; 7; 5; 6; 9; 2; 9; 2; 0; 7; 4; 6; 2; 7; 2; 4; 1; 1; 6; 3; 8; 8]
    [7; 2; 6; 4; 7; 0; 2; 9; 2; 9; 6; 5; 7; 1; 6; 2; 5; 2; 0; 5; 3; 8; 8] 0;
  add_trace_carries_step #10 6 7
    [1; 7; 5; 6; 9; 2; 9; 2; 0; 7; 4; 6; 2; 7; 2; 4; 1; 1; 6; 3; 8; 8]
    [2; 6; 4; 7; 0; 2; 9; 2; 9; 6; 5; 7; 1; 6; 2; 5; 2; 0; 5; 3; 8; 8] 0;
  add_trace_carries_step #10 1 2
    [7; 5; 6; 9; 2; 9; 2; 0; 7; 4; 6; 2; 7; 2; 4; 1; 1; 6; 3; 8; 8]
    [6; 4; 7; 0; 2; 9; 2; 9; 6; 5; 7; 1; 6; 2; 5; 2; 0; 5; 3; 8; 8] 1;
  add_trace_carries_step #10 7 6
    [5; 6; 9; 2; 9; 2; 0; 7; 4; 6; 2; 7; 2; 4; 1; 1; 6; 3; 8; 8]
    [4; 7; 0; 2; 9; 2; 9; 6; 5; 7; 1; 6; 2; 5; 2; 0; 5; 3; 8; 8] 0;
  add_trace_carries_step #10 5 4
    [6; 9; 2; 9; 2; 0; 7; 4; 6; 2; 7; 2; 4; 1; 1; 6; 3; 8; 8]
    [7; 0; 2; 9; 2; 9; 6; 5; 7; 1; 6; 2; 5; 2; 0; 5; 3; 8; 8] 1;
  add_trace_carries_step #10 6 7
    [9; 2; 9; 2; 0; 7; 4; 6; 2; 7; 2; 4; 1; 1; 6; 3; 8; 8]
    [0; 2; 9; 2; 9; 6; 5; 7; 1; 6; 2; 5; 2; 0; 5; 3; 8; 8] 1;
  add_trace_carries_step #10 9 0
    [2; 9; 2; 0; 7; 4; 6; 2; 7; 2; 4; 1; 1; 6; 3; 8; 8]
    [2; 9; 2; 9; 6; 5; 7; 1; 6; 2; 5; 2; 0; 5; 3; 8; 8] 1;
  add_trace_carries_step #10 2 2
    [9; 2; 0; 7; 4; 6; 2; 7; 2; 4; 1; 1; 6; 3; 8; 8]
    [9; 2; 9; 6; 5; 7; 1; 6; 2; 5; 2; 0; 5; 3; 8; 8] 1;
  add_trace_carries_step #10 9 9
    [2; 0; 7; 4; 6; 2; 7; 2; 4; 1; 1; 6; 3; 8; 8]
    [2; 9; 6; 5; 7; 1; 6; 2; 5; 2; 0; 5; 3; 8; 8] 0;
  add_trace_carries_step #10 2 2
    [0; 7; 4; 6; 2; 7; 2; 4; 1; 1; 6; 3; 8; 8]
    [9; 6; 5; 7; 1; 6; 2; 5; 2; 0; 5; 3; 8; 8] 1;
  add_trace_carries_step #10 0 9
    [7; 4; 6; 2; 7; 2; 4; 1; 1; 6; 3; 8; 8]
    [6; 5; 7; 1; 6; 2; 5; 2; 0; 5; 3; 8; 8] 0;
  add_trace_carries_step #10 7 6
    [4; 6; 2; 7; 2; 4; 1; 1; 6; 3; 8; 8]
    [5; 7; 1; 6; 2; 5; 2; 0; 5; 3; 8; 8] 0;
  add_trace_carries_step #10 4 5
    [6; 2; 7; 2; 4; 1; 1; 6; 3; 8; 8]
    [7; 1; 6; 2; 5; 2; 0; 5; 3; 8; 8] 1;
  add_trace_carries_step #10 6 7
    [2; 7; 2; 4; 1; 1; 6; 3; 8; 8]
    [1; 6; 2; 5; 2; 0; 5; 3; 8; 8] 1;
  add_trace_carries_step #10 2 1
    [7; 2; 4; 1; 1; 6; 3; 8; 8]
    [6; 2; 5; 2; 0; 5; 3; 8; 8] 1;
  add_trace_carries_step #10 7 6
    [2; 4; 1; 1; 6; 3; 8; 8]
    [2; 5; 2; 0; 5; 3; 8; 8] 0;
  add_trace_carries_step #10 2 2
    [4; 1; 1; 6; 3; 8; 8]
    [5; 2; 0; 5; 3; 8; 8] 1;
  add_trace_carries_step #10 4 5
    [1; 1; 6; 3; 8; 8]
    [2; 0; 5; 3; 8; 8] 0;
  add_trace_carries_step #10 1 2
    [1; 6; 3; 8; 8]
    [0; 5; 3; 8; 8] 0;
  add_trace_carries_step #10 1 0
    [6; 3; 8; 8]
    [5; 3; 8; 8] 0;
  add_trace_carries_step #10 6 5
    [3; 8; 8]
    [3; 8; 8] 0;
  add_trace_carries_step #10 3 3
    [8; 8]
    [8; 8] 1;
  add_trace_carries_step #10 8 8
    [8]
    [8] 0;
  add_trace_carries_step #10 8 8
    []
    [] 1;
  assert ((add_trace #10 [] [] 1).carries == [1]);
  assert ((add_trace #10 next22_source next22_reversed 0).carries ==
    [0; 1; 1; 0; 1; 0; 0; 0; 0; 1; 0; 1; 1; 1; 1; 0; 1; 0; 0; 1; 1; 1; 0; 1; 0; 0; 0; 0; 1; 0; 1; 1]);
  ()

let trace_profile_shape_8836114272647029296571625205388 () : Lemma (
    length (trace_digits next22_source) == length next22_source + 1) =
  trace_digits_profile_8836114272647029296571625205388 ();
  length_of_eq #(digit 10) (trace_digits next22_source) next22_target;
  assert (length next22_target == length next22_source + 1);
  ()

let trace_profile_final_carry_8836114272647029296571625205388 () : Lemma (
    nth (trace_carries next22_source) (length next22_source) == Some 1) =
  trace_profile_shape_8836114272647029296571625205388 ();
  ReverseAddContinuation.final_carry_from_overflow_length next22_source;
  ()

let trace_profile_sums_8836114272647029296571625205388 () : Lemma (
    trace_sum_at next22_source 0 == 16 /\
    trace_sum_at next22_source 1 == 16 /\
    trace_sum_at next22_source 30 == 16) =
  reverse_list_next22_source ();
  ()

let trace_profile_carry_facts_8836114272647029296571625205388 () : Lemma (
    trace_carry_at next22_source 1 == 1 /\
    trace_carry_at next22_source 30 == 1 /\
    trace_carry_at next22_source 2 == 1 /\
    trace_carry_at next22_source 31 == 1) =
  trace_carries_next22_source ();
  assert (trace_carry_at next22_source 1 == 1);
  assert (trace_carry_at next22_source 30 == 1);
  assert (trace_carry_at next22_source 2 == 1);
  assert (trace_carry_at next22_source 31 == 1);
  assert (trace_carries next22_source ==
    [0; 1; 1; 0; 1; 0; 0; 0; 0; 1; 0; 1; 1; 1; 1; 0; 1; 0; 0; 1; 1; 1; 0; 1; 0; 0; 0; 0; 1; 0; 1; 1]);
  ()

let overflow_precondition_8836114272647029296571625205388 () : Lemma (
    canonical #10 next22_source /\
    next22_source <> [] /\
    length (trace_digits next22_source) == length next22_source + 1 /\
    nth (trace_carries next22_source) (length next22_source) == Some 1 /\
    1 <= trace_sum_at next22_source 0 /\
    trace_sum_at next22_source 0 <= 18 /\
    trace_sum_at next22_source 0 <> 10 /\
    exists (i:nat). 0 < i /\ i < length next22_source /\
      trace_sum_at next22_source i +
          trace_sum_at next22_source (length next22_source - i) +
          trace_carry_at next22_source i +
          trace_carry_at next22_source (length next22_source - i) >=
        10 + 10 *
          (trace_carry_at next22_source (i + 1) +
           trace_carry_at next22_source (length next22_source - i + 1))) =
  ReverseAddNext.canonical_next21_target ();
  assert (next22_source <> []);
  trace_profile_shape_8836114272647029296571625205388 ();
  trace_profile_final_carry_8836114272647029296571625205388 ();
  trace_profile_sums_8836114272647029296571625205388 ();
  trace_profile_carry_facts_8836114272647029296571625205388 ();
  assert (length (trace_digits next22_source) == length next22_source + 1);
  assert (nth (trace_carries next22_source)
    (length next22_source) == Some 1);
  assert (trace_sum_at next22_source 0 == 16);
  assert (trace_sum_at next22_source 1 == 16);
  assert (trace_sum_at next22_source 30 == 16);
  assert (trace_carry_at next22_source 1 == 1);
  assert (trace_carry_at next22_source 30 == 1);
  assert (trace_carry_at next22_source 2 == 1);
  assert (trace_carry_at next22_source 31 == 1);
  assert (1 <= trace_sum_at next22_source 0 /\
    trace_sum_at next22_source 0 <= 18);
  assert (trace_sum_at next22_source 0 <> 10);
  let n : nat = length next22_source in
  assert (0 < 1 /\ 1 < n);
  assert (trace_sum_at next22_source 1 +
      trace_sum_at next22_source (n - 1) +
      trace_carry_at next22_source 1 +
      trace_carry_at next22_source (n - 1) >=
    10 + 10 *
      (trace_carry_at next22_source (1 + 1) +
       trace_carry_at next22_source (n - 1 + 1)));
  exists_intro
    (fun (i:nat) -> 0 < i /\ i < n /\
      trace_sum_at next22_source i +
          trace_sum_at next22_source (n - i) +
          trace_carry_at next22_source i +
          trace_carry_at next22_source (n - i) >=
        10 + 10 *
          (trace_carry_at next22_source (i + 1) +
           trace_carry_at next22_source (n - i + 1)))
    1;
  ()

let local_profile_witness_17671139534403958504034349321776 () : Lemma (
    trace_local_profile_complement_witness next22_target) =
  overflow_precondition_8836114272647029296571625205388 ();
  reverse_add_8836114272647029296571625205388_to_17671139534403958504034349321776 ();
  overflow_internal_cell_implies_next_witness next22_source;
  ()

let next23_source : numeral 10 = next22_target

let next23_reversed : numeral 10 =
  [1; 7; 6; 7; 1; 1; 3; 9; 5; 3; 4; 4; 0; 3; 9; 5; 8; 5; 0; 4; 0; 3; 4; 3; 4; 9; 3; 2; 1; 7; 7; 6]

let next23_target : numeral 10 =
  [7; 4; 4; 9; 3; 4; 2; 4; 9; 7; 7; 4; 4; 3; 4; 4; 4; 5; 4; 4; 4; 7; 7; 8; 3; 3; 5; 3; 8; 3; 5; 8]

let reverse_list_next23_source () : Lemma (rev next23_source == next23_reversed) =
  assert (rev [1] == [1]);
  rev_cons 7 [1];
  rev_cons 6 [7; 1];
  rev_cons 7 [6; 7; 1];
  rev_cons 1 [7; 6; 7; 1];
  rev_cons 1 [1; 7; 6; 7; 1];
  rev_cons 3 [1; 1; 7; 6; 7; 1];
  rev_cons 9 [3; 1; 1; 7; 6; 7; 1];
  rev_cons 5 [9; 3; 1; 1; 7; 6; 7; 1];
  rev_cons 3 [5; 9; 3; 1; 1; 7; 6; 7; 1];
  rev_cons 4 [3; 5; 9; 3; 1; 1; 7; 6; 7; 1];
  rev_cons 4 [4; 3; 5; 9; 3; 1; 1; 7; 6; 7; 1];
  rev_cons 0 [4; 4; 3; 5; 9; 3; 1; 1; 7; 6; 7; 1];
  rev_cons 3 [0; 4; 4; 3; 5; 9; 3; 1; 1; 7; 6; 7; 1];
  rev_cons 9 [3; 0; 4; 4; 3; 5; 9; 3; 1; 1; 7; 6; 7; 1];
  rev_cons 5 [9; 3; 0; 4; 4; 3; 5; 9; 3; 1; 1; 7; 6; 7; 1];
  rev_cons 8 [5; 9; 3; 0; 4; 4; 3; 5; 9; 3; 1; 1; 7; 6; 7; 1];
  rev_cons 5 [8; 5; 9; 3; 0; 4; 4; 3; 5; 9; 3; 1; 1; 7; 6; 7; 1];
  rev_cons 0 [5; 8; 5; 9; 3; 0; 4; 4; 3; 5; 9; 3; 1; 1; 7; 6; 7; 1];
  rev_cons 4 [0; 5; 8; 5; 9; 3; 0; 4; 4; 3; 5; 9; 3; 1; 1; 7; 6; 7; 1];
  rev_cons 0 [4; 0; 5; 8; 5; 9; 3; 0; 4; 4; 3; 5; 9; 3; 1; 1; 7; 6; 7; 1];
  rev_cons 3 [0; 4; 0; 5; 8; 5; 9; 3; 0; 4; 4; 3; 5; 9; 3; 1; 1; 7; 6; 7; 1];
  rev_cons 4 [3; 0; 4; 0; 5; 8; 5; 9; 3; 0; 4; 4; 3; 5; 9; 3; 1; 1; 7; 6; 7; 1];
  rev_cons 3 [4; 3; 0; 4; 0; 5; 8; 5; 9; 3; 0; 4; 4; 3; 5; 9; 3; 1; 1; 7; 6; 7; 1];
  rev_cons 4 [3; 4; 3; 0; 4; 0; 5; 8; 5; 9; 3; 0; 4; 4; 3; 5; 9; 3; 1; 1; 7; 6; 7; 1];
  rev_cons 9 [4; 3; 4; 3; 0; 4; 0; 5; 8; 5; 9; 3; 0; 4; 4; 3; 5; 9; 3; 1; 1; 7; 6; 7; 1];
  rev_cons 3 [9; 4; 3; 4; 3; 0; 4; 0; 5; 8; 5; 9; 3; 0; 4; 4; 3; 5; 9; 3; 1; 1; 7; 6; 7; 1];
  rev_cons 2 [3; 9; 4; 3; 4; 3; 0; 4; 0; 5; 8; 5; 9; 3; 0; 4; 4; 3; 5; 9; 3; 1; 1; 7; 6; 7; 1];
  rev_cons 1 [2; 3; 9; 4; 3; 4; 3; 0; 4; 0; 5; 8; 5; 9; 3; 0; 4; 4; 3; 5; 9; 3; 1; 1; 7; 6; 7; 1];
  rev_cons 7 [1; 2; 3; 9; 4; 3; 4; 3; 0; 4; 0; 5; 8; 5; 9; 3; 0; 4; 4; 3; 5; 9; 3; 1; 1; 7; 6; 7; 1];
  rev_cons 7 [7; 1; 2; 3; 9; 4; 3; 4; 3; 0; 4; 0; 5; 8; 5; 9; 3; 0; 4; 4; 3; 5; 9; 3; 1; 1; 7; 6; 7; 1];
  rev_cons 6 [7; 7; 1; 2; 3; 9; 4; 3; 4; 3; 0; 4; 0; 5; 8; 5; 9; 3; 0; 4; 4; 3; 5; 9; 3; 1; 1; 7; 6; 7; 1];
  ()

let value_next23_reversed_tail_20 () : Lemma (
    value #10 [0; 3; 9; 5; 8; 5; 0; 4; 0; 3; 4; 3; 4; 9; 3; 2; 1; 7; 7; 6] == 67712394343040585930) =
  value_cons #10 0 [3; 9; 5; 8; 5; 0; 4; 0; 3; 4; 3; 4; 9; 3; 2; 1; 7; 7; 6];
  value_cons #10 3 [9; 5; 8; 5; 0; 4; 0; 3; 4; 3; 4; 9; 3; 2; 1; 7; 7; 6];
  value_cons #10 9 [5; 8; 5; 0; 4; 0; 3; 4; 3; 4; 9; 3; 2; 1; 7; 7; 6];
  value_cons #10 5 [8; 5; 0; 4; 0; 3; 4; 3; 4; 9; 3; 2; 1; 7; 7; 6];
  value_cons #10 8 [5; 0; 4; 0; 3; 4; 3; 4; 9; 3; 2; 1; 7; 7; 6];
  value_cons #10 5 [0; 4; 0; 3; 4; 3; 4; 9; 3; 2; 1; 7; 7; 6];
  value_cons #10 0 [4; 0; 3; 4; 3; 4; 9; 3; 2; 1; 7; 7; 6];
  value_cons #10 4 [0; 3; 4; 3; 4; 9; 3; 2; 1; 7; 7; 6];
  value_cons #10 0 [3; 4; 3; 4; 9; 3; 2; 1; 7; 7; 6];
  value_cons #10 3 [4; 3; 4; 9; 3; 2; 1; 7; 7; 6];
  value_cons #10 4 [3; 4; 9; 3; 2; 1; 7; 7; 6];
  value_cons #10 3 [4; 9; 3; 2; 1; 7; 7; 6];
  value_cons #10 4 [9; 3; 2; 1; 7; 7; 6];
  value_cons #10 9 [3; 2; 1; 7; 7; 6];
  value_cons #10 3 [2; 1; 7; 7; 6];
  value_cons #10 2 [1; 7; 7; 6];
  value_cons #10 1 [7; 7; 6];
  value_cons #10 7 [7; 6];
  value_cons #10 7 [6];
  value_cons #10 6 [];
  ()

let value_next23_reversed () : Lemma (
    value next23_reversed == 67712394343040585930443593117671) =
  value_cons #10 1 [7; 6; 7; 1; 1; 3; 9; 5; 3; 4; 4];
  value_cons #10 7 [6; 7; 1; 1; 3; 9; 5; 3; 4; 4];
  value_cons #10 6 [7; 1; 1; 3; 9; 5; 3; 4; 4];
  value_cons #10 7 [1; 1; 3; 9; 5; 3; 4; 4];
  value_cons #10 1 [1; 3; 9; 5; 3; 4; 4];
  value_cons #10 1 [3; 9; 5; 3; 4; 4];
  value_cons #10 3 [9; 5; 3; 4; 4];
  value_cons #10 9 [5; 3; 4; 4];
  value_cons #10 5 [3; 4; 4];
  value_cons #10 3 [4; 4];
  value_cons #10 4 [4];
  value_cons #10 4 [];
  value_next23_reversed_tail_20 ();
  ()

let value_next23_target_tail_20 () : Lemma (
    value #10 [4; 3; 4; 4; 4; 5; 4; 4; 4; 7; 7; 8; 3; 3; 5; 3; 8; 3; 5; 8] == 85383533877444544434) =
  value_cons #10 4 [3; 4; 4; 4; 5; 4; 4; 4; 7; 7; 8; 3; 3; 5; 3; 8; 3; 5; 8];
  value_cons #10 3 [4; 4; 4; 5; 4; 4; 4; 7; 7; 8; 3; 3; 5; 3; 8; 3; 5; 8];
  value_cons #10 4 [4; 4; 5; 4; 4; 4; 7; 7; 8; 3; 3; 5; 3; 8; 3; 5; 8];
  value_cons #10 4 [4; 5; 4; 4; 4; 7; 7; 8; 3; 3; 5; 3; 8; 3; 5; 8];
  value_cons #10 4 [5; 4; 4; 4; 7; 7; 8; 3; 3; 5; 3; 8; 3; 5; 8];
  value_cons #10 5 [4; 4; 4; 7; 7; 8; 3; 3; 5; 3; 8; 3; 5; 8];
  value_cons #10 4 [4; 4; 7; 7; 8; 3; 3; 5; 3; 8; 3; 5; 8];
  value_cons #10 4 [4; 7; 7; 8; 3; 3; 5; 3; 8; 3; 5; 8];
  value_cons #10 4 [7; 7; 8; 3; 3; 5; 3; 8; 3; 5; 8];
  value_cons #10 7 [7; 8; 3; 3; 5; 3; 8; 3; 5; 8];
  value_cons #10 7 [8; 3; 3; 5; 3; 8; 3; 5; 8];
  value_cons #10 8 [3; 3; 5; 3; 8; 3; 5; 8];
  value_cons #10 3 [3; 5; 3; 8; 3; 5; 8];
  value_cons #10 3 [5; 3; 8; 3; 5; 8];
  value_cons #10 5 [3; 8; 3; 5; 8];
  value_cons #10 3 [8; 3; 5; 8];
  value_cons #10 8 [3; 5; 8];
  value_cons #10 3 [5; 8];
  value_cons #10 5 [8];
  value_cons #10 8 [];
  ()

let value_next23_target () : Lemma (
    value next23_target == 85383533877444544434477942439447) =
  value_cons #10 7 [4; 4; 9; 3; 4; 2; 4; 9; 7; 7; 4];
  value_cons #10 4 [4; 9; 3; 4; 2; 4; 9; 7; 7; 4];
  value_cons #10 4 [9; 3; 4; 2; 4; 9; 7; 7; 4];
  value_cons #10 9 [3; 4; 2; 4; 9; 7; 7; 4];
  value_cons #10 3 [4; 2; 4; 9; 7; 7; 4];
  value_cons #10 4 [2; 4; 9; 7; 7; 4];
  value_cons #10 2 [4; 9; 7; 7; 4];
  value_cons #10 4 [9; 7; 7; 4];
  value_cons #10 9 [7; 7; 4];
  value_cons #10 7 [7; 4];
  value_cons #10 7 [4];
  value_cons #10 4 [];
  value_next23_target_tail_20 ();
  ()

let canonical_next23_reversed () : Lemma (canonical #10 next23_reversed) =
  assert (canonical #10 [6]);
  canonical_cons #10 7 [6];
  canonical_cons #10 7 [7; 6];
  canonical_cons #10 1 [7; 7; 6];
  canonical_cons #10 2 [1; 7; 7; 6];
  canonical_cons #10 3 [2; 1; 7; 7; 6];
  canonical_cons #10 9 [3; 2; 1; 7; 7; 6];
  canonical_cons #10 4 [9; 3; 2; 1; 7; 7; 6];
  canonical_cons #10 3 [4; 9; 3; 2; 1; 7; 7; 6];
  canonical_cons #10 4 [3; 4; 9; 3; 2; 1; 7; 7; 6];
  canonical_cons #10 3 [4; 3; 4; 9; 3; 2; 1; 7; 7; 6];
  canonical_cons #10 0 [3; 4; 3; 4; 9; 3; 2; 1; 7; 7; 6];
  canonical_cons #10 4 [0; 3; 4; 3; 4; 9; 3; 2; 1; 7; 7; 6];
  canonical_cons #10 0 [4; 0; 3; 4; 3; 4; 9; 3; 2; 1; 7; 7; 6];
  canonical_cons #10 5 [0; 4; 0; 3; 4; 3; 4; 9; 3; 2; 1; 7; 7; 6];
  canonical_cons #10 8 [5; 0; 4; 0; 3; 4; 3; 4; 9; 3; 2; 1; 7; 7; 6];
  canonical_cons #10 5 [8; 5; 0; 4; 0; 3; 4; 3; 4; 9; 3; 2; 1; 7; 7; 6];
  canonical_cons #10 9 [5; 8; 5; 0; 4; 0; 3; 4; 3; 4; 9; 3; 2; 1; 7; 7; 6];
  canonical_cons #10 3 [9; 5; 8; 5; 0; 4; 0; 3; 4; 3; 4; 9; 3; 2; 1; 7; 7; 6];
  canonical_cons #10 0 [3; 9; 5; 8; 5; 0; 4; 0; 3; 4; 3; 4; 9; 3; 2; 1; 7; 7; 6];
  canonical_cons #10 4 [0; 3; 9; 5; 8; 5; 0; 4; 0; 3; 4; 3; 4; 9; 3; 2; 1; 7; 7; 6];
  canonical_cons #10 4 [4; 0; 3; 9; 5; 8; 5; 0; 4; 0; 3; 4; 3; 4; 9; 3; 2; 1; 7; 7; 6];
  canonical_cons #10 3 [4; 4; 0; 3; 9; 5; 8; 5; 0; 4; 0; 3; 4; 3; 4; 9; 3; 2; 1; 7; 7; 6];
  canonical_cons #10 5 [3; 4; 4; 0; 3; 9; 5; 8; 5; 0; 4; 0; 3; 4; 3; 4; 9; 3; 2; 1; 7; 7; 6];
  canonical_cons #10 9 [5; 3; 4; 4; 0; 3; 9; 5; 8; 5; 0; 4; 0; 3; 4; 3; 4; 9; 3; 2; 1; 7; 7; 6];
  canonical_cons #10 3 [9; 5; 3; 4; 4; 0; 3; 9; 5; 8; 5; 0; 4; 0; 3; 4; 3; 4; 9; 3; 2; 1; 7; 7; 6];
  canonical_cons #10 1 [3; 9; 5; 3; 4; 4; 0; 3; 9; 5; 8; 5; 0; 4; 0; 3; 4; 3; 4; 9; 3; 2; 1; 7; 7; 6];
  canonical_cons #10 1 [1; 3; 9; 5; 3; 4; 4; 0; 3; 9; 5; 8; 5; 0; 4; 0; 3; 4; 3; 4; 9; 3; 2; 1; 7; 7; 6];
  canonical_cons #10 7 [1; 1; 3; 9; 5; 3; 4; 4; 0; 3; 9; 5; 8; 5; 0; 4; 0; 3; 4; 3; 4; 9; 3; 2; 1; 7; 7; 6];
  canonical_cons #10 6 [7; 1; 1; 3; 9; 5; 3; 4; 4; 0; 3; 9; 5; 8; 5; 0; 4; 0; 3; 4; 3; 4; 9; 3; 2; 1; 7; 7; 6];
  canonical_cons #10 7 [6; 7; 1; 1; 3; 9; 5; 3; 4; 4; 0; 3; 9; 5; 8; 5; 0; 4; 0; 3; 4; 3; 4; 9; 3; 2; 1; 7; 7; 6];
  canonical_cons #10 1 [7; 6; 7; 1; 1; 3; 9; 5; 3; 4; 4; 0; 3; 9; 5; 8; 5; 0; 4; 0; 3; 4; 3; 4; 9; 3; 2; 1; 7; 7; 6];
  ()

let canonical_next23_target () : Lemma (canonical #10 next23_target) =
  assert (canonical #10 [8]);
  canonical_cons #10 5 [8];
  canonical_cons #10 3 [5; 8];
  canonical_cons #10 8 [3; 5; 8];
  canonical_cons #10 3 [8; 3; 5; 8];
  canonical_cons #10 5 [3; 8; 3; 5; 8];
  canonical_cons #10 3 [5; 3; 8; 3; 5; 8];
  canonical_cons #10 3 [3; 5; 3; 8; 3; 5; 8];
  canonical_cons #10 8 [3; 3; 5; 3; 8; 3; 5; 8];
  canonical_cons #10 7 [8; 3; 3; 5; 3; 8; 3; 5; 8];
  canonical_cons #10 7 [7; 8; 3; 3; 5; 3; 8; 3; 5; 8];
  canonical_cons #10 4 [7; 7; 8; 3; 3; 5; 3; 8; 3; 5; 8];
  canonical_cons #10 4 [4; 7; 7; 8; 3; 3; 5; 3; 8; 3; 5; 8];
  canonical_cons #10 4 [4; 4; 7; 7; 8; 3; 3; 5; 3; 8; 3; 5; 8];
  canonical_cons #10 5 [4; 4; 4; 7; 7; 8; 3; 3; 5; 3; 8; 3; 5; 8];
  canonical_cons #10 4 [5; 4; 4; 4; 7; 7; 8; 3; 3; 5; 3; 8; 3; 5; 8];
  canonical_cons #10 4 [4; 5; 4; 4; 4; 7; 7; 8; 3; 3; 5; 3; 8; 3; 5; 8];
  canonical_cons #10 4 [4; 4; 5; 4; 4; 4; 7; 7; 8; 3; 3; 5; 3; 8; 3; 5; 8];
  canonical_cons #10 3 [4; 4; 4; 5; 4; 4; 4; 7; 7; 8; 3; 3; 5; 3; 8; 3; 5; 8];
  canonical_cons #10 4 [3; 4; 4; 4; 5; 4; 4; 4; 7; 7; 8; 3; 3; 5; 3; 8; 3; 5; 8];
  canonical_cons #10 4 [4; 3; 4; 4; 4; 5; 4; 4; 4; 7; 7; 8; 3; 3; 5; 3; 8; 3; 5; 8];
  canonical_cons #10 7 [4; 4; 3; 4; 4; 4; 5; 4; 4; 4; 7; 7; 8; 3; 3; 5; 3; 8; 3; 5; 8];
  canonical_cons #10 7 [7; 4; 4; 3; 4; 4; 4; 5; 4; 4; 4; 7; 7; 8; 3; 3; 5; 3; 8; 3; 5; 8];
  canonical_cons #10 9 [7; 7; 4; 4; 3; 4; 4; 4; 5; 4; 4; 4; 7; 7; 8; 3; 3; 5; 3; 8; 3; 5; 8];
  canonical_cons #10 4 [9; 7; 7; 4; 4; 3; 4; 4; 4; 5; 4; 4; 4; 7; 7; 8; 3; 3; 5; 3; 8; 3; 5; 8];
  canonical_cons #10 2 [4; 9; 7; 7; 4; 4; 3; 4; 4; 4; 5; 4; 4; 4; 7; 7; 8; 3; 3; 5; 3; 8; 3; 5; 8];
  canonical_cons #10 4 [2; 4; 9; 7; 7; 4; 4; 3; 4; 4; 4; 5; 4; 4; 4; 7; 7; 8; 3; 3; 5; 3; 8; 3; 5; 8];
  canonical_cons #10 3 [4; 2; 4; 9; 7; 7; 4; 4; 3; 4; 4; 4; 5; 4; 4; 4; 7; 7; 8; 3; 3; 5; 3; 8; 3; 5; 8];
  canonical_cons #10 9 [3; 4; 2; 4; 9; 7; 7; 4; 4; 3; 4; 4; 4; 5; 4; 4; 4; 7; 7; 8; 3; 3; 5; 3; 8; 3; 5; 8];
  canonical_cons #10 4 [9; 3; 4; 2; 4; 9; 7; 7; 4; 4; 3; 4; 4; 4; 5; 4; 4; 4; 7; 7; 8; 3; 3; 5; 3; 8; 3; 5; 8];
  canonical_cons #10 4 [4; 9; 3; 4; 2; 4; 9; 7; 7; 4; 4; 3; 4; 4; 4; 5; 4; 4; 4; 7; 7; 8; 3; 3; 5; 3; 8; 3; 5; 8];
  canonical_cons #10 7 [4; 4; 9; 3; 4; 2; 4; 9; 7; 7; 4; 4; 3; 4; 4; 4; 5; 4; 4; 4; 7; 7; 8; 3; 3; 5; 3; 8; 3; 5; 8];
  ()

let reverse_digits_next23_source () : Lemma (
    reverse_digits #10 next23_source == next23_reversed) =
  ReverseAddNext.canonical_next22_target ();
  reverse_list_next23_source ();
  value_next23_reversed ();
  canonical_next23_reversed ();
  reverse_digits_canonical #10 next23_source;
  normalize_value #10 (rev next23_source);
  assert (value (reverse_digits #10 next23_source) ==
    67712394343040585930443593117671);
  digits_of_nat_of_canonical #10 (reverse_digits #10 next23_source);
  digits_of_nat_of_canonical #10 next23_reversed;
  assert (reverse_digits #10 next23_source == next23_reversed);
  ()

let reverse_add_17671139534403958504034349321776_to_85383533877444544434477942439447 () : Lemma (
    reverse_add #10 next23_source == next23_target) =
  ReverseAddNext.canonical_next22_target ();
  reverse_add_value #10 next23_source;
  ReverseAddNext.value_next22_target ();
  reverse_digits_next23_source ();
  value_next23_reversed ();
  value_next23_target ();
  assert (value (reverse_add #10 next23_source) ==
    85383533877444544434477942439447);
  reverse_add_canonical #10 next23_source;
  digits_of_nat_of_canonical #10 (reverse_add #10 next23_source);
  canonical_next23_target ();
  digits_of_nat_of_canonical #10 next23_target;
  assert (reverse_add #10 next23_source == next23_target);
  ()

let trace_digits_profile_17671139534403958504034349321776 () : Lemma (
    trace_digits next23_source == next23_target) =
  reverse_add_17671139534403958504034349321776_to_85383533877444544434477942439447 ();
  trace_digits_equals_reverse_add next23_source;
  assert (trace_digits next23_source == next23_target);
  ()

let trace_profile_shape_17671139534403958504034349321776 () : Lemma (
    length (trace_digits next23_source) == length next23_source) =
  trace_digits_profile_17671139534403958504034349321776 ();
  length_of_eq #(digit 10) (trace_digits next23_source) next23_target;
  assert (length next23_target == length next23_source);
  ()

let trace_profile_final_carry_17671139534403958504034349321776 () : Lemma (
    nth (trace_carries next23_source) (length next23_source) == Some 0) =
  trace_profile_shape_17671139534403958504034349321776 ();
  final_carry_from_length next23_source;
  ()

let local_profile_witness_85383533877444544434477942439447 () : Lemma (
    trace_local_profile_complement_witness next23_target) =
  ReverseAddNext.canonical_next22_target ();
  assert (next23_source <> []);
  trace_profile_shape_17671139534403958504034349321776 ();
  trace_profile_final_carry_17671139534403958504034349321776 ();
  assert (trace_sum_at next23_source 0 == 7);
  reverse_add_17671139534403958504034349321776_to_85383533877444544434477942439447 ();
  no_overflow_outer_sum_6_to_9_implies_next_witness next23_source;
  ()

let next24_source : numeral 10 = next23_target

let next24_reversed : numeral 10 =
  [8; 5; 3; 8; 3; 5; 3; 3; 8; 7; 7; 4; 4; 4; 5; 4; 4; 4; 3; 4; 4; 7; 7; 9; 4; 2; 4; 3; 9; 4; 4; 7]

let next24_target : numeral 10 =
  [5; 0; 8; 7; 7; 9; 5; 7; 7; 5; 5; 9; 8; 7; 9; 8; 8; 9; 7; 8; 8; 4; 5; 8; 8; 5; 9; 6; 7; 8; 9; 5; 1]

let reverse_list_next24_source () : Lemma (rev next24_source == next24_reversed) =
  assert (rev [8] == [8]);
  rev_cons 5 [8];
  rev_cons 3 [5; 8];
  rev_cons 8 [3; 5; 8];
  rev_cons 3 [8; 3; 5; 8];
  rev_cons 5 [3; 8; 3; 5; 8];
  rev_cons 3 [5; 3; 8; 3; 5; 8];
  rev_cons 3 [3; 5; 3; 8; 3; 5; 8];
  rev_cons 8 [3; 3; 5; 3; 8; 3; 5; 8];
  rev_cons 7 [8; 3; 3; 5; 3; 8; 3; 5; 8];
  rev_cons 7 [7; 8; 3; 3; 5; 3; 8; 3; 5; 8];
  rev_cons 4 [7; 7; 8; 3; 3; 5; 3; 8; 3; 5; 8];
  rev_cons 4 [4; 7; 7; 8; 3; 3; 5; 3; 8; 3; 5; 8];
  rev_cons 4 [4; 4; 7; 7; 8; 3; 3; 5; 3; 8; 3; 5; 8];
  rev_cons 5 [4; 4; 4; 7; 7; 8; 3; 3; 5; 3; 8; 3; 5; 8];
  rev_cons 4 [5; 4; 4; 4; 7; 7; 8; 3; 3; 5; 3; 8; 3; 5; 8];
  rev_cons 4 [4; 5; 4; 4; 4; 7; 7; 8; 3; 3; 5; 3; 8; 3; 5; 8];
  rev_cons 4 [4; 4; 5; 4; 4; 4; 7; 7; 8; 3; 3; 5; 3; 8; 3; 5; 8];
  rev_cons 3 [4; 4; 4; 5; 4; 4; 4; 7; 7; 8; 3; 3; 5; 3; 8; 3; 5; 8];
  rev_cons 4 [3; 4; 4; 4; 5; 4; 4; 4; 7; 7; 8; 3; 3; 5; 3; 8; 3; 5; 8];
  rev_cons 4 [4; 3; 4; 4; 4; 5; 4; 4; 4; 7; 7; 8; 3; 3; 5; 3; 8; 3; 5; 8];
  rev_cons 7 [4; 4; 3; 4; 4; 4; 5; 4; 4; 4; 7; 7; 8; 3; 3; 5; 3; 8; 3; 5; 8];
  rev_cons 7 [7; 4; 4; 3; 4; 4; 4; 5; 4; 4; 4; 7; 7; 8; 3; 3; 5; 3; 8; 3; 5; 8];
  rev_cons 9 [7; 7; 4; 4; 3; 4; 4; 4; 5; 4; 4; 4; 7; 7; 8; 3; 3; 5; 3; 8; 3; 5; 8];
  rev_cons 4 [9; 7; 7; 4; 4; 3; 4; 4; 4; 5; 4; 4; 4; 7; 7; 8; 3; 3; 5; 3; 8; 3; 5; 8];
  rev_cons 2 [4; 9; 7; 7; 4; 4; 3; 4; 4; 4; 5; 4; 4; 4; 7; 7; 8; 3; 3; 5; 3; 8; 3; 5; 8];
  rev_cons 4 [2; 4; 9; 7; 7; 4; 4; 3; 4; 4; 4; 5; 4; 4; 4; 7; 7; 8; 3; 3; 5; 3; 8; 3; 5; 8];
  rev_cons 3 [4; 2; 4; 9; 7; 7; 4; 4; 3; 4; 4; 4; 5; 4; 4; 4; 7; 7; 8; 3; 3; 5; 3; 8; 3; 5; 8];
  rev_cons 9 [3; 4; 2; 4; 9; 7; 7; 4; 4; 3; 4; 4; 4; 5; 4; 4; 4; 7; 7; 8; 3; 3; 5; 3; 8; 3; 5; 8];
  rev_cons 4 [9; 3; 4; 2; 4; 9; 7; 7; 4; 4; 3; 4; 4; 4; 5; 4; 4; 4; 7; 7; 8; 3; 3; 5; 3; 8; 3; 5; 8];
  rev_cons 4 [4; 9; 3; 4; 2; 4; 9; 7; 7; 4; 4; 3; 4; 4; 4; 5; 4; 4; 4; 7; 7; 8; 3; 3; 5; 3; 8; 3; 5; 8];
  rev_cons 7 [4; 4; 9; 3; 4; 2; 4; 9; 7; 7; 4; 4; 3; 4; 4; 4; 5; 4; 4; 4; 7; 7; 8; 3; 3; 5; 3; 8; 3; 5; 8];
  ()

let value_next24_reversed_tail_20 () : Lemma (
    value #10 [4; 4; 5; 4; 4; 4; 3; 4; 4; 7; 7; 9; 4; 2; 4; 3; 9; 4; 4; 7] == 74493424977443444544) =
  value_cons #10 4 [4; 5; 4; 4; 4; 3; 4; 4; 7; 7; 9; 4; 2; 4; 3; 9; 4; 4; 7];
  value_cons #10 4 [5; 4; 4; 4; 3; 4; 4; 7; 7; 9; 4; 2; 4; 3; 9; 4; 4; 7];
  value_cons #10 5 [4; 4; 4; 3; 4; 4; 7; 7; 9; 4; 2; 4; 3; 9; 4; 4; 7];
  value_cons #10 4 [4; 4; 3; 4; 4; 7; 7; 9; 4; 2; 4; 3; 9; 4; 4; 7];
  value_cons #10 4 [4; 3; 4; 4; 7; 7; 9; 4; 2; 4; 3; 9; 4; 4; 7];
  value_cons #10 4 [3; 4; 4; 7; 7; 9; 4; 2; 4; 3; 9; 4; 4; 7];
  value_cons #10 3 [4; 4; 7; 7; 9; 4; 2; 4; 3; 9; 4; 4; 7];
  value_cons #10 4 [4; 7; 7; 9; 4; 2; 4; 3; 9; 4; 4; 7];
  value_cons #10 4 [7; 7; 9; 4; 2; 4; 3; 9; 4; 4; 7];
  value_cons #10 7 [7; 9; 4; 2; 4; 3; 9; 4; 4; 7];
  value_cons #10 7 [9; 4; 2; 4; 3; 9; 4; 4; 7];
  value_cons #10 9 [4; 2; 4; 3; 9; 4; 4; 7];
  value_cons #10 4 [2; 4; 3; 9; 4; 4; 7];
  value_cons #10 2 [4; 3; 9; 4; 4; 7];
  value_cons #10 4 [3; 9; 4; 4; 7];
  value_cons #10 3 [9; 4; 4; 7];
  value_cons #10 9 [4; 4; 7];
  value_cons #10 4 [4; 7];
  value_cons #10 4 [7];
  value_cons #10 7 [];
  ()

let value_next24_reversed () : Lemma (
    value next24_reversed == 74493424977443444544477833538358) =
  value_cons #10 8 [5; 3; 8; 3; 5; 3; 3; 8; 7; 7; 4];
  value_cons #10 5 [3; 8; 3; 5; 3; 3; 8; 7; 7; 4];
  value_cons #10 3 [8; 3; 5; 3; 3; 8; 7; 7; 4];
  value_cons #10 8 [3; 5; 3; 3; 8; 7; 7; 4];
  value_cons #10 3 [5; 3; 3; 8; 7; 7; 4];
  value_cons #10 5 [3; 3; 8; 7; 7; 4];
  value_cons #10 3 [3; 8; 7; 7; 4];
  value_cons #10 3 [8; 7; 7; 4];
  value_cons #10 8 [7; 7; 4];
  value_cons #10 7 [7; 4];
  value_cons #10 7 [4];
  value_cons #10 4 [];
  value_next24_reversed_tail_20 ();
  ()

let value_next24_target_tail_20 () : Lemma (
    value #10 [7; 9; 8; 8; 9; 7; 8; 8; 4; 5; 8; 8; 5; 9; 6; 7; 8; 9; 5; 1] == 15987695885488798897) =
  value_cons #10 7 [9; 8; 8; 9; 7; 8; 8; 4; 5; 8; 8; 5; 9; 6; 7; 8; 9; 5; 1];
  value_cons #10 9 [8; 8; 9; 7; 8; 8; 4; 5; 8; 8; 5; 9; 6; 7; 8; 9; 5; 1];
  value_cons #10 8 [8; 9; 7; 8; 8; 4; 5; 8; 8; 5; 9; 6; 7; 8; 9; 5; 1];
  value_cons #10 8 [9; 7; 8; 8; 4; 5; 8; 8; 5; 9; 6; 7; 8; 9; 5; 1];
  value_cons #10 9 [7; 8; 8; 4; 5; 8; 8; 5; 9; 6; 7; 8; 9; 5; 1];
  value_cons #10 7 [8; 8; 4; 5; 8; 8; 5; 9; 6; 7; 8; 9; 5; 1];
  value_cons #10 8 [8; 4; 5; 8; 8; 5; 9; 6; 7; 8; 9; 5; 1];
  value_cons #10 8 [4; 5; 8; 8; 5; 9; 6; 7; 8; 9; 5; 1];
  value_cons #10 4 [5; 8; 8; 5; 9; 6; 7; 8; 9; 5; 1];
  value_cons #10 5 [8; 8; 5; 9; 6; 7; 8; 9; 5; 1];
  value_cons #10 8 [8; 5; 9; 6; 7; 8; 9; 5; 1];
  value_cons #10 8 [5; 9; 6; 7; 8; 9; 5; 1];
  value_cons #10 5 [9; 6; 7; 8; 9; 5; 1];
  value_cons #10 9 [6; 7; 8; 9; 5; 1];
  value_cons #10 6 [7; 8; 9; 5; 1];
  value_cons #10 7 [8; 9; 5; 1];
  value_cons #10 8 [9; 5; 1];
  value_cons #10 9 [5; 1];
  value_cons #10 5 [1];
  value_cons #10 1 [];
  ()

let value_next24_target () : Lemma (
    value next24_target == 159876958854887988978955775977805) =
  value_cons #10 5 [0; 8; 7; 7; 9; 5; 7; 7; 5; 5; 9; 8];
  value_cons #10 0 [8; 7; 7; 9; 5; 7; 7; 5; 5; 9; 8];
  value_cons #10 8 [7; 7; 9; 5; 7; 7; 5; 5; 9; 8];
  value_cons #10 7 [7; 9; 5; 7; 7; 5; 5; 9; 8];
  value_cons #10 7 [9; 5; 7; 7; 5; 5; 9; 8];
  value_cons #10 9 [5; 7; 7; 5; 5; 9; 8];
  value_cons #10 5 [7; 7; 5; 5; 9; 8];
  value_cons #10 7 [7; 5; 5; 9; 8];
  value_cons #10 7 [5; 5; 9; 8];
  value_cons #10 5 [5; 9; 8];
  value_cons #10 5 [9; 8];
  value_cons #10 9 [8];
  value_cons #10 8 [];
  value_next24_target_tail_20 ();
  ()

let canonical_next24_reversed () : Lemma (canonical #10 next24_reversed) =
  assert (canonical #10 [7]);
  canonical_cons #10 4 [7];
  canonical_cons #10 4 [4; 7];
  canonical_cons #10 9 [4; 4; 7];
  canonical_cons #10 3 [9; 4; 4; 7];
  canonical_cons #10 4 [3; 9; 4; 4; 7];
  canonical_cons #10 2 [4; 3; 9; 4; 4; 7];
  canonical_cons #10 4 [2; 4; 3; 9; 4; 4; 7];
  canonical_cons #10 9 [4; 2; 4; 3; 9; 4; 4; 7];
  canonical_cons #10 7 [9; 4; 2; 4; 3; 9; 4; 4; 7];
  canonical_cons #10 7 [7; 9; 4; 2; 4; 3; 9; 4; 4; 7];
  canonical_cons #10 4 [7; 7; 9; 4; 2; 4; 3; 9; 4; 4; 7];
  canonical_cons #10 4 [4; 7; 7; 9; 4; 2; 4; 3; 9; 4; 4; 7];
  canonical_cons #10 3 [4; 4; 7; 7; 9; 4; 2; 4; 3; 9; 4; 4; 7];
  canonical_cons #10 4 [3; 4; 4; 7; 7; 9; 4; 2; 4; 3; 9; 4; 4; 7];
  canonical_cons #10 4 [4; 3; 4; 4; 7; 7; 9; 4; 2; 4; 3; 9; 4; 4; 7];
  canonical_cons #10 4 [4; 4; 3; 4; 4; 7; 7; 9; 4; 2; 4; 3; 9; 4; 4; 7];
  canonical_cons #10 5 [4; 4; 4; 3; 4; 4; 7; 7; 9; 4; 2; 4; 3; 9; 4; 4; 7];
  canonical_cons #10 4 [5; 4; 4; 4; 3; 4; 4; 7; 7; 9; 4; 2; 4; 3; 9; 4; 4; 7];
  canonical_cons #10 4 [4; 5; 4; 4; 4; 3; 4; 4; 7; 7; 9; 4; 2; 4; 3; 9; 4; 4; 7];
  canonical_cons #10 4 [4; 4; 5; 4; 4; 4; 3; 4; 4; 7; 7; 9; 4; 2; 4; 3; 9; 4; 4; 7];
  canonical_cons #10 7 [4; 4; 4; 5; 4; 4; 4; 3; 4; 4; 7; 7; 9; 4; 2; 4; 3; 9; 4; 4; 7];
  canonical_cons #10 7 [7; 4; 4; 4; 5; 4; 4; 4; 3; 4; 4; 7; 7; 9; 4; 2; 4; 3; 9; 4; 4; 7];
  canonical_cons #10 8 [7; 7; 4; 4; 4; 5; 4; 4; 4; 3; 4; 4; 7; 7; 9; 4; 2; 4; 3; 9; 4; 4; 7];
  canonical_cons #10 3 [8; 7; 7; 4; 4; 4; 5; 4; 4; 4; 3; 4; 4; 7; 7; 9; 4; 2; 4; 3; 9; 4; 4; 7];
  canonical_cons #10 3 [3; 8; 7; 7; 4; 4; 4; 5; 4; 4; 4; 3; 4; 4; 7; 7; 9; 4; 2; 4; 3; 9; 4; 4; 7];
  canonical_cons #10 5 [3; 3; 8; 7; 7; 4; 4; 4; 5; 4; 4; 4; 3; 4; 4; 7; 7; 9; 4; 2; 4; 3; 9; 4; 4; 7];
  canonical_cons #10 3 [5; 3; 3; 8; 7; 7; 4; 4; 4; 5; 4; 4; 4; 3; 4; 4; 7; 7; 9; 4; 2; 4; 3; 9; 4; 4; 7];
  canonical_cons #10 8 [3; 5; 3; 3; 8; 7; 7; 4; 4; 4; 5; 4; 4; 4; 3; 4; 4; 7; 7; 9; 4; 2; 4; 3; 9; 4; 4; 7];
  canonical_cons #10 3 [8; 3; 5; 3; 3; 8; 7; 7; 4; 4; 4; 5; 4; 4; 4; 3; 4; 4; 7; 7; 9; 4; 2; 4; 3; 9; 4; 4; 7];
  canonical_cons #10 5 [3; 8; 3; 5; 3; 3; 8; 7; 7; 4; 4; 4; 5; 4; 4; 4; 3; 4; 4; 7; 7; 9; 4; 2; 4; 3; 9; 4; 4; 7];
  canonical_cons #10 8 [5; 3; 8; 3; 5; 3; 3; 8; 7; 7; 4; 4; 4; 5; 4; 4; 4; 3; 4; 4; 7; 7; 9; 4; 2; 4; 3; 9; 4; 4; 7];
  ()

let canonical_next24_target () : Lemma (canonical #10 next24_target) =
  assert (canonical #10 [1]);
  canonical_cons #10 5 [1];
  canonical_cons #10 9 [5; 1];
  canonical_cons #10 8 [9; 5; 1];
  canonical_cons #10 7 [8; 9; 5; 1];
  canonical_cons #10 6 [7; 8; 9; 5; 1];
  canonical_cons #10 9 [6; 7; 8; 9; 5; 1];
  canonical_cons #10 5 [9; 6; 7; 8; 9; 5; 1];
  canonical_cons #10 8 [5; 9; 6; 7; 8; 9; 5; 1];
  canonical_cons #10 8 [8; 5; 9; 6; 7; 8; 9; 5; 1];
  canonical_cons #10 5 [8; 8; 5; 9; 6; 7; 8; 9; 5; 1];
  canonical_cons #10 4 [5; 8; 8; 5; 9; 6; 7; 8; 9; 5; 1];
  canonical_cons #10 8 [4; 5; 8; 8; 5; 9; 6; 7; 8; 9; 5; 1];
  canonical_cons #10 8 [8; 4; 5; 8; 8; 5; 9; 6; 7; 8; 9; 5; 1];
  canonical_cons #10 7 [8; 8; 4; 5; 8; 8; 5; 9; 6; 7; 8; 9; 5; 1];
  canonical_cons #10 9 [7; 8; 8; 4; 5; 8; 8; 5; 9; 6; 7; 8; 9; 5; 1];
  canonical_cons #10 8 [9; 7; 8; 8; 4; 5; 8; 8; 5; 9; 6; 7; 8; 9; 5; 1];
  canonical_cons #10 8 [8; 9; 7; 8; 8; 4; 5; 8; 8; 5; 9; 6; 7; 8; 9; 5; 1];
  canonical_cons #10 9 [8; 8; 9; 7; 8; 8; 4; 5; 8; 8; 5; 9; 6; 7; 8; 9; 5; 1];
  canonical_cons #10 7 [9; 8; 8; 9; 7; 8; 8; 4; 5; 8; 8; 5; 9; 6; 7; 8; 9; 5; 1];
  canonical_cons #10 8 [7; 9; 8; 8; 9; 7; 8; 8; 4; 5; 8; 8; 5; 9; 6; 7; 8; 9; 5; 1];
  canonical_cons #10 9 [8; 7; 9; 8; 8; 9; 7; 8; 8; 4; 5; 8; 8; 5; 9; 6; 7; 8; 9; 5; 1];
  canonical_cons #10 5 [9; 8; 7; 9; 8; 8; 9; 7; 8; 8; 4; 5; 8; 8; 5; 9; 6; 7; 8; 9; 5; 1];
  canonical_cons #10 5 [5; 9; 8; 7; 9; 8; 8; 9; 7; 8; 8; 4; 5; 8; 8; 5; 9; 6; 7; 8; 9; 5; 1];
  canonical_cons #10 7 [5; 5; 9; 8; 7; 9; 8; 8; 9; 7; 8; 8; 4; 5; 8; 8; 5; 9; 6; 7; 8; 9; 5; 1];
  canonical_cons #10 7 [7; 5; 5; 9; 8; 7; 9; 8; 8; 9; 7; 8; 8; 4; 5; 8; 8; 5; 9; 6; 7; 8; 9; 5; 1];
  canonical_cons #10 5 [7; 7; 5; 5; 9; 8; 7; 9; 8; 8; 9; 7; 8; 8; 4; 5; 8; 8; 5; 9; 6; 7; 8; 9; 5; 1];
  canonical_cons #10 9 [5; 7; 7; 5; 5; 9; 8; 7; 9; 8; 8; 9; 7; 8; 8; 4; 5; 8; 8; 5; 9; 6; 7; 8; 9; 5; 1];
  canonical_cons #10 7 [9; 5; 7; 7; 5; 5; 9; 8; 7; 9; 8; 8; 9; 7; 8; 8; 4; 5; 8; 8; 5; 9; 6; 7; 8; 9; 5; 1];
  canonical_cons #10 7 [7; 9; 5; 7; 7; 5; 5; 9; 8; 7; 9; 8; 8; 9; 7; 8; 8; 4; 5; 8; 8; 5; 9; 6; 7; 8; 9; 5; 1];
  canonical_cons #10 8 [7; 7; 9; 5; 7; 7; 5; 5; 9; 8; 7; 9; 8; 8; 9; 7; 8; 8; 4; 5; 8; 8; 5; 9; 6; 7; 8; 9; 5; 1];
  canonical_cons #10 0 [8; 7; 7; 9; 5; 7; 7; 5; 5; 9; 8; 7; 9; 8; 8; 9; 7; 8; 8; 4; 5; 8; 8; 5; 9; 6; 7; 8; 9; 5; 1];
  canonical_cons #10 5 [0; 8; 7; 7; 9; 5; 7; 7; 5; 5; 9; 8; 7; 9; 8; 8; 9; 7; 8; 8; 4; 5; 8; 8; 5; 9; 6; 7; 8; 9; 5; 1];
  ()

let reverse_digits_next24_source () : Lemma (
    reverse_digits #10 next24_source == next24_reversed) =
  ReverseAddNext.canonical_next23_target ();
  reverse_list_next24_source ();
  value_next24_reversed ();
  canonical_next24_reversed ();
  reverse_digits_canonical #10 next24_source;
  normalize_value #10 (rev next24_source);
  assert (value (reverse_digits #10 next24_source) ==
    74493424977443444544477833538358);
  digits_of_nat_of_canonical #10 (reverse_digits #10 next24_source);
  digits_of_nat_of_canonical #10 next24_reversed;
  assert (reverse_digits #10 next24_source == next24_reversed);
  ()

let reverse_add_85383533877444544434477942439447_to_159876958854887988978955775977805 () : Lemma (
    reverse_add #10 next24_source == next24_target) =
  ReverseAddNext.canonical_next23_target ();
  reverse_add_value #10 next24_source;
  ReverseAddNext.value_next23_target ();
  reverse_digits_next24_source ();
  value_next24_reversed ();
  value_next24_target ();
  assert (value (reverse_add #10 next24_source) ==
    159876958854887988978955775977805);
  reverse_add_canonical #10 next24_source;
  digits_of_nat_of_canonical #10 (reverse_add #10 next24_source);
  canonical_next24_target ();
  digits_of_nat_of_canonical #10 next24_target;
  assert (reverse_add #10 next24_source == next24_target);
  ()

let trace_digits_profile_85383533877444544434477942439447 () : Lemma (
    trace_digits next24_source == next24_target) =
  reverse_add_85383533877444544434477942439447_to_159876958854887988978955775977805 ();
  trace_digits_equals_reverse_add next24_source;
  assert (trace_digits next24_source == next24_target);
  ()

let trace_carries_next24_source () : Lemma (trace_carries next24_source ==
    [0; 1; 1; 0; 1; 0; 0; 0; 0; 1; 1; 1; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 1; 1; 1; 0; 0; 0; 0; 1; 0; 0; 1]) =
  reverse_list_next24_source ();
  assert (trace_carries next24_source ==
    (add_trace #10 next24_source next24_reversed 0).carries);
  add_trace_carries_step #10 7 8
    [4; 4; 9; 3; 4; 2; 4; 9; 7; 7; 4; 4; 3; 4; 4; 4; 5; 4; 4; 4; 7; 7; 8; 3; 3; 5; 3; 8; 3; 5; 8]
    [5; 3; 8; 3; 5; 3; 3; 8; 7; 7; 4; 4; 4; 5; 4; 4; 4; 3; 4; 4; 7; 7; 9; 4; 2; 4; 3; 9; 4; 4; 7] 0;
  add_trace_carries_step #10 4 5
    [4; 9; 3; 4; 2; 4; 9; 7; 7; 4; 4; 3; 4; 4; 4; 5; 4; 4; 4; 7; 7; 8; 3; 3; 5; 3; 8; 3; 5; 8]
    [3; 8; 3; 5; 3; 3; 8; 7; 7; 4; 4; 4; 5; 4; 4; 4; 3; 4; 4; 7; 7; 9; 4; 2; 4; 3; 9; 4; 4; 7] 1;
  add_trace_carries_step #10 4 3
    [9; 3; 4; 2; 4; 9; 7; 7; 4; 4; 3; 4; 4; 4; 5; 4; 4; 4; 7; 7; 8; 3; 3; 5; 3; 8; 3; 5; 8]
    [8; 3; 5; 3; 3; 8; 7; 7; 4; 4; 4; 5; 4; 4; 4; 3; 4; 4; 7; 7; 9; 4; 2; 4; 3; 9; 4; 4; 7] 1;
  add_trace_carries_step #10 9 8
    [3; 4; 2; 4; 9; 7; 7; 4; 4; 3; 4; 4; 4; 5; 4; 4; 4; 7; 7; 8; 3; 3; 5; 3; 8; 3; 5; 8]
    [3; 5; 3; 3; 8; 7; 7; 4; 4; 4; 5; 4; 4; 4; 3; 4; 4; 7; 7; 9; 4; 2; 4; 3; 9; 4; 4; 7] 0;
  add_trace_carries_step #10 3 3
    [4; 2; 4; 9; 7; 7; 4; 4; 3; 4; 4; 4; 5; 4; 4; 4; 7; 7; 8; 3; 3; 5; 3; 8; 3; 5; 8]
    [5; 3; 3; 8; 7; 7; 4; 4; 4; 5; 4; 4; 4; 3; 4; 4; 7; 7; 9; 4; 2; 4; 3; 9; 4; 4; 7] 1;
  add_trace_carries_step #10 4 5
    [2; 4; 9; 7; 7; 4; 4; 3; 4; 4; 4; 5; 4; 4; 4; 7; 7; 8; 3; 3; 5; 3; 8; 3; 5; 8]
    [3; 3; 8; 7; 7; 4; 4; 4; 5; 4; 4; 4; 3; 4; 4; 7; 7; 9; 4; 2; 4; 3; 9; 4; 4; 7] 0;
  add_trace_carries_step #10 2 3
    [4; 9; 7; 7; 4; 4; 3; 4; 4; 4; 5; 4; 4; 4; 7; 7; 8; 3; 3; 5; 3; 8; 3; 5; 8]
    [3; 8; 7; 7; 4; 4; 4; 5; 4; 4; 4; 3; 4; 4; 7; 7; 9; 4; 2; 4; 3; 9; 4; 4; 7] 0;
  add_trace_carries_step #10 4 3
    [9; 7; 7; 4; 4; 3; 4; 4; 4; 5; 4; 4; 4; 7; 7; 8; 3; 3; 5; 3; 8; 3; 5; 8]
    [8; 7; 7; 4; 4; 4; 5; 4; 4; 4; 3; 4; 4; 7; 7; 9; 4; 2; 4; 3; 9; 4; 4; 7] 0;
  add_trace_carries_step #10 9 8
    [7; 7; 4; 4; 3; 4; 4; 4; 5; 4; 4; 4; 7; 7; 8; 3; 3; 5; 3; 8; 3; 5; 8]
    [7; 7; 4; 4; 4; 5; 4; 4; 4; 3; 4; 4; 7; 7; 9; 4; 2; 4; 3; 9; 4; 4; 7] 0;
  add_trace_carries_step #10 7 7
    [7; 4; 4; 3; 4; 4; 4; 5; 4; 4; 4; 7; 7; 8; 3; 3; 5; 3; 8; 3; 5; 8]
    [7; 4; 4; 4; 5; 4; 4; 4; 3; 4; 4; 7; 7; 9; 4; 2; 4; 3; 9; 4; 4; 7] 1;
  add_trace_carries_step #10 7 7
    [4; 4; 3; 4; 4; 4; 5; 4; 4; 4; 7; 7; 8; 3; 3; 5; 3; 8; 3; 5; 8]
    [4; 4; 4; 5; 4; 4; 4; 3; 4; 4; 7; 7; 9; 4; 2; 4; 3; 9; 4; 4; 7] 1;
  add_trace_carries_step #10 4 4
    [4; 3; 4; 4; 4; 5; 4; 4; 4; 7; 7; 8; 3; 3; 5; 3; 8; 3; 5; 8]
    [4; 4; 5; 4; 4; 4; 3; 4; 4; 7; 7; 9; 4; 2; 4; 3; 9; 4; 4; 7] 1;
  add_trace_carries_step #10 4 4
    [3; 4; 4; 4; 5; 4; 4; 4; 7; 7; 8; 3; 3; 5; 3; 8; 3; 5; 8]
    [4; 5; 4; 4; 4; 3; 4; 4; 7; 7; 9; 4; 2; 4; 3; 9; 4; 4; 7] 0;
  add_trace_carries_step #10 3 4
    [4; 4; 4; 5; 4; 4; 4; 7; 7; 8; 3; 3; 5; 3; 8; 3; 5; 8]
    [5; 4; 4; 4; 3; 4; 4; 7; 7; 9; 4; 2; 4; 3; 9; 4; 4; 7] 0;
  add_trace_carries_step #10 4 5
    [4; 4; 5; 4; 4; 4; 7; 7; 8; 3; 3; 5; 3; 8; 3; 5; 8]
    [4; 4; 4; 3; 4; 4; 7; 7; 9; 4; 2; 4; 3; 9; 4; 4; 7] 0;
  add_trace_carries_step #10 4 4
    [4; 5; 4; 4; 4; 7; 7; 8; 3; 3; 5; 3; 8; 3; 5; 8]
    [4; 4; 3; 4; 4; 7; 7; 9; 4; 2; 4; 3; 9; 4; 4; 7] 0;
  add_trace_carries_step #10 4 4
    [5; 4; 4; 4; 7; 7; 8; 3; 3; 5; 3; 8; 3; 5; 8]
    [4; 3; 4; 4; 7; 7; 9; 4; 2; 4; 3; 9; 4; 4; 7] 0;
  add_trace_carries_step #10 5 4
    [4; 4; 4; 7; 7; 8; 3; 3; 5; 3; 8; 3; 5; 8]
    [3; 4; 4; 7; 7; 9; 4; 2; 4; 3; 9; 4; 4; 7] 0;
  add_trace_carries_step #10 4 3
    [4; 4; 7; 7; 8; 3; 3; 5; 3; 8; 3; 5; 8]
    [4; 4; 7; 7; 9; 4; 2; 4; 3; 9; 4; 4; 7] 0;
  add_trace_carries_step #10 4 4
    [4; 7; 7; 8; 3; 3; 5; 3; 8; 3; 5; 8]
    [4; 7; 7; 9; 4; 2; 4; 3; 9; 4; 4; 7] 0;
  add_trace_carries_step #10 4 4
    [7; 7; 8; 3; 3; 5; 3; 8; 3; 5; 8]
    [7; 7; 9; 4; 2; 4; 3; 9; 4; 4; 7] 0;
  add_trace_carries_step #10 7 7
    [7; 8; 3; 3; 5; 3; 8; 3; 5; 8]
    [7; 9; 4; 2; 4; 3; 9; 4; 4; 7] 0;
  add_trace_carries_step #10 7 7
    [8; 3; 3; 5; 3; 8; 3; 5; 8]
    [9; 4; 2; 4; 3; 9; 4; 4; 7] 1;
  add_trace_carries_step #10 8 9
    [3; 3; 5; 3; 8; 3; 5; 8]
    [4; 2; 4; 3; 9; 4; 4; 7] 1;
  add_trace_carries_step #10 3 4
    [3; 5; 3; 8; 3; 5; 8]
    [2; 4; 3; 9; 4; 4; 7] 1;
  add_trace_carries_step #10 3 2
    [5; 3; 8; 3; 5; 8]
    [4; 3; 9; 4; 4; 7] 0;
  add_trace_carries_step #10 5 4
    [3; 8; 3; 5; 8]
    [3; 9; 4; 4; 7] 0;
  add_trace_carries_step #10 3 3
    [8; 3; 5; 8]
    [9; 4; 4; 7] 0;
  add_trace_carries_step #10 8 9
    [3; 5; 8]
    [4; 4; 7] 0;
  add_trace_carries_step #10 3 4
    [5; 8]
    [4; 7] 1;
  add_trace_carries_step #10 5 4
    [8]
    [7] 0;
  add_trace_carries_step #10 8 7
    []
    [] 0;
  assert ((add_trace #10 [] [] 1).carries == [1]);
  assert ((add_trace #10 next24_source next24_reversed 0).carries ==
    [0; 1; 1; 0; 1; 0; 0; 0; 0; 1; 1; 1; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 1; 1; 1; 0; 0; 0; 0; 1; 0; 0; 1]);
  ()

let trace_profile_shape_85383533877444544434477942439447 () : Lemma (
    length (trace_digits next24_source) == length next24_source + 1) =
  trace_digits_profile_85383533877444544434477942439447 ();
  length_of_eq #(digit 10) (trace_digits next24_source) next24_target;
  assert (length next24_target == length next24_source + 1);
  ()

let trace_profile_final_carry_85383533877444544434477942439447 () : Lemma (
    nth (trace_carries next24_source) (length next24_source) == Some 1) =
  trace_profile_shape_85383533877444544434477942439447 ();
  ReverseAddContinuation.final_carry_from_overflow_length next24_source;
  ()

let trace_profile_sums_85383533877444544434477942439447 () : Lemma (
    trace_sum_at next24_source 0 == 15 /\
    trace_sum_at next24_source 2 == 7 /\
    trace_sum_at next24_source 30 == 9) =
  reverse_list_next24_source ();
  ()

let trace_profile_carry_facts_85383533877444544434477942439447 () : Lemma (
    trace_carry_at next24_source 1 == 1 /\
    trace_carry_at next24_source 31 == 0 /\
    trace_carry_at next24_source 2 == 1 /\
    trace_carry_at next24_source 32 == 1 /\
    trace_carry_at next24_source 3 == 0 /\
    trace_carry_at next24_source 30 == 0) =
  trace_carries_next24_source ();
  assert (trace_carry_at next24_source 1 == 1);
  assert (trace_carry_at next24_source 31 == 0);
  assert (trace_carry_at next24_source 2 == 1);
  assert (trace_carry_at next24_source 32 == 1);
  assert (trace_carry_at next24_source 3 == 0);
  assert (trace_carry_at next24_source 30 == 0);
  assert (trace_carries next24_source ==
    [0; 1; 1; 0; 1; 0; 0; 0; 0; 1; 1; 1; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 1; 1; 1; 0; 0; 0; 0; 1; 0; 0; 1]);
  ()

let overflow_precondition_85383533877444544434477942439447 () : Lemma (
    canonical #10 next24_source /\
    next24_source <> [] /\
    length (trace_digits next24_source) == length next24_source + 1 /\
    nth (trace_carries next24_source) (length next24_source) == Some 1 /\
    1 <= trace_sum_at next24_source 0 /\
    trace_sum_at next24_source 0 <= 18 /\
    trace_sum_at next24_source 0 <> 10 /\
    exists (i:nat). 0 < i /\ i < length next24_source /\
      trace_sum_at next24_source i +
          trace_sum_at next24_source (length next24_source - i) +
          trace_carry_at next24_source i +
          trace_carry_at next24_source (length next24_source - i) >=
        10 + 10 *
          (trace_carry_at next24_source (i + 1) +
           trace_carry_at next24_source (length next24_source - i + 1))) =
  ReverseAddNext.canonical_next23_target ();
  assert (next24_source <> []);
  trace_profile_shape_85383533877444544434477942439447 ();
  trace_profile_final_carry_85383533877444544434477942439447 ();
  trace_profile_sums_85383533877444544434477942439447 ();
  trace_profile_carry_facts_85383533877444544434477942439447 ();
  assert (length (trace_digits next24_source) == length next24_source + 1);
  assert (nth (trace_carries next24_source)
    (length next24_source) == Some 1);
  assert (trace_sum_at next24_source 0 == 15);
  assert (trace_sum_at next24_source 2 == 7);
  assert (trace_sum_at next24_source 30 == 9);
  assert (trace_carry_at next24_source 1 == 1);
  assert (trace_carry_at next24_source 31 == 0);
  assert (trace_carry_at next24_source 2 == 1);
  assert (trace_carry_at next24_source 32 == 1);
  assert (trace_carry_at next24_source 3 == 0);
  assert (trace_carry_at next24_source 30 == 0);
  assert (1 <= trace_sum_at next24_source 0 /\
    trace_sum_at next24_source 0 <= 18);
  assert (trace_sum_at next24_source 0 <> 10);
  let n : nat = length next24_source in
  assert (0 < 2 /\ 2 < n);
  assert (trace_sum_at next24_source 2 +
      trace_sum_at next24_source (n - 2) +
      trace_carry_at next24_source 2 +
      trace_carry_at next24_source (n - 2) >=
    10 + 10 *
      (trace_carry_at next24_source (2 + 1) +
       trace_carry_at next24_source (n - 2 + 1)));
  exists_intro
    (fun (i:nat) -> 0 < i /\ i < n /\
      trace_sum_at next24_source i +
          trace_sum_at next24_source (n - i) +
          trace_carry_at next24_source i +
          trace_carry_at next24_source (n - i) >=
        10 + 10 *
          (trace_carry_at next24_source (i + 1) +
           trace_carry_at next24_source (n - i + 1)))
    2;
  ()

let local_profile_witness_159876958854887988978955775977805 () : Lemma (
    trace_local_profile_complement_witness next24_target) =
  overflow_precondition_85383533877444544434477942439447 ();
  reverse_add_85383533877444544434477942439447_to_159876958854887988978955775977805 ();
  overflow_internal_cell_implies_next_witness next24_source;
  ()

let next25_source : numeral 10 = next24_target

let next25_reversed : numeral 10 =
  [1; 5; 9; 8; 7; 6; 9; 5; 8; 8; 5; 4; 8; 8; 7; 9; 8; 8; 9; 7; 8; 9; 5; 5; 7; 7; 5; 9; 7; 7; 8; 0; 5]

let next25_target : numeral 10 =
  [6; 5; 7; 6; 5; 6; 5; 3; 6; 4; 1; 4; 7; 6; 7; 8; 7; 8; 7; 6; 7; 4; 1; 4; 6; 3; 5; 6; 5; 6; 8; 6; 6]

let reverse_list_next25_source () : Lemma (rev next25_source == next25_reversed) =
  assert (rev [1] == [1]);
  rev_cons 5 [1];
  rev_cons 9 [5; 1];
  rev_cons 8 [9; 5; 1];
  rev_cons 7 [8; 9; 5; 1];
  rev_cons 6 [7; 8; 9; 5; 1];
  rev_cons 9 [6; 7; 8; 9; 5; 1];
  rev_cons 5 [9; 6; 7; 8; 9; 5; 1];
  rev_cons 8 [5; 9; 6; 7; 8; 9; 5; 1];
  rev_cons 8 [8; 5; 9; 6; 7; 8; 9; 5; 1];
  rev_cons 5 [8; 8; 5; 9; 6; 7; 8; 9; 5; 1];
  rev_cons 4 [5; 8; 8; 5; 9; 6; 7; 8; 9; 5; 1];
  rev_cons 8 [4; 5; 8; 8; 5; 9; 6; 7; 8; 9; 5; 1];
  rev_cons 8 [8; 4; 5; 8; 8; 5; 9; 6; 7; 8; 9; 5; 1];
  rev_cons 7 [8; 8; 4; 5; 8; 8; 5; 9; 6; 7; 8; 9; 5; 1];
  rev_cons 9 [7; 8; 8; 4; 5; 8; 8; 5; 9; 6; 7; 8; 9; 5; 1];
  rev_cons 8 [9; 7; 8; 8; 4; 5; 8; 8; 5; 9; 6; 7; 8; 9; 5; 1];
  rev_cons 8 [8; 9; 7; 8; 8; 4; 5; 8; 8; 5; 9; 6; 7; 8; 9; 5; 1];
  rev_cons 9 [8; 8; 9; 7; 8; 8; 4; 5; 8; 8; 5; 9; 6; 7; 8; 9; 5; 1];
  rev_cons 7 [9; 8; 8; 9; 7; 8; 8; 4; 5; 8; 8; 5; 9; 6; 7; 8; 9; 5; 1];
  rev_cons 8 [7; 9; 8; 8; 9; 7; 8; 8; 4; 5; 8; 8; 5; 9; 6; 7; 8; 9; 5; 1];
  rev_cons 9 [8; 7; 9; 8; 8; 9; 7; 8; 8; 4; 5; 8; 8; 5; 9; 6; 7; 8; 9; 5; 1];
  rev_cons 5 [9; 8; 7; 9; 8; 8; 9; 7; 8; 8; 4; 5; 8; 8; 5; 9; 6; 7; 8; 9; 5; 1];
  rev_cons 5 [5; 9; 8; 7; 9; 8; 8; 9; 7; 8; 8; 4; 5; 8; 8; 5; 9; 6; 7; 8; 9; 5; 1];
  rev_cons 7 [5; 5; 9; 8; 7; 9; 8; 8; 9; 7; 8; 8; 4; 5; 8; 8; 5; 9; 6; 7; 8; 9; 5; 1];
  rev_cons 7 [7; 5; 5; 9; 8; 7; 9; 8; 8; 9; 7; 8; 8; 4; 5; 8; 8; 5; 9; 6; 7; 8; 9; 5; 1];
  rev_cons 5 [7; 7; 5; 5; 9; 8; 7; 9; 8; 8; 9; 7; 8; 8; 4; 5; 8; 8; 5; 9; 6; 7; 8; 9; 5; 1];
  rev_cons 9 [5; 7; 7; 5; 5; 9; 8; 7; 9; 8; 8; 9; 7; 8; 8; 4; 5; 8; 8; 5; 9; 6; 7; 8; 9; 5; 1];
  rev_cons 7 [9; 5; 7; 7; 5; 5; 9; 8; 7; 9; 8; 8; 9; 7; 8; 8; 4; 5; 8; 8; 5; 9; 6; 7; 8; 9; 5; 1];
  rev_cons 7 [7; 9; 5; 7; 7; 5; 5; 9; 8; 7; 9; 8; 8; 9; 7; 8; 8; 4; 5; 8; 8; 5; 9; 6; 7; 8; 9; 5; 1];
  rev_cons 8 [7; 7; 9; 5; 7; 7; 5; 5; 9; 8; 7; 9; 8; 8; 9; 7; 8; 8; 4; 5; 8; 8; 5; 9; 6; 7; 8; 9; 5; 1];
  rev_cons 0 [8; 7; 7; 9; 5; 7; 7; 5; 5; 9; 8; 7; 9; 8; 8; 9; 7; 8; 8; 4; 5; 8; 8; 5; 9; 6; 7; 8; 9; 5; 1];
  rev_cons 5 [0; 8; 7; 7; 9; 5; 7; 7; 5; 5; 9; 8; 7; 9; 8; 8; 9; 7; 8; 8; 4; 5; 8; 8; 5; 9; 6; 7; 8; 9; 5; 1];
  ()

let value_next25_reversed_tail_20 () : Lemma (
    value #10 [8; 7; 9; 8; 8; 9; 7; 8; 9; 5; 5; 7; 7; 5; 9; 7; 7; 8; 0; 5] == 50877957755987988978) =
  value_cons #10 8 [7; 9; 8; 8; 9; 7; 8; 9; 5; 5; 7; 7; 5; 9; 7; 7; 8; 0; 5];
  value_cons #10 7 [9; 8; 8; 9; 7; 8; 9; 5; 5; 7; 7; 5; 9; 7; 7; 8; 0; 5];
  value_cons #10 9 [8; 8; 9; 7; 8; 9; 5; 5; 7; 7; 5; 9; 7; 7; 8; 0; 5];
  value_cons #10 8 [8; 9; 7; 8; 9; 5; 5; 7; 7; 5; 9; 7; 7; 8; 0; 5];
  value_cons #10 8 [9; 7; 8; 9; 5; 5; 7; 7; 5; 9; 7; 7; 8; 0; 5];
  value_cons #10 9 [7; 8; 9; 5; 5; 7; 7; 5; 9; 7; 7; 8; 0; 5];
  value_cons #10 7 [8; 9; 5; 5; 7; 7; 5; 9; 7; 7; 8; 0; 5];
  value_cons #10 8 [9; 5; 5; 7; 7; 5; 9; 7; 7; 8; 0; 5];
  value_cons #10 9 [5; 5; 7; 7; 5; 9; 7; 7; 8; 0; 5];
  value_cons #10 5 [5; 7; 7; 5; 9; 7; 7; 8; 0; 5];
  value_cons #10 5 [7; 7; 5; 9; 7; 7; 8; 0; 5];
  value_cons #10 7 [7; 5; 9; 7; 7; 8; 0; 5];
  value_cons #10 7 [5; 9; 7; 7; 8; 0; 5];
  value_cons #10 5 [9; 7; 7; 8; 0; 5];
  value_cons #10 9 [7; 7; 8; 0; 5];
  value_cons #10 7 [7; 8; 0; 5];
  value_cons #10 7 [8; 0; 5];
  value_cons #10 8 [0; 5];
  value_cons #10 0 [5];
  value_cons #10 5 [];
  ()

let value_next25_reversed () : Lemma (
    value next25_reversed == 508779577559879889788458859678951) =
  value_cons #10 1 [5; 9; 8; 7; 6; 9; 5; 8; 8; 5; 4; 8];
  value_cons #10 5 [9; 8; 7; 6; 9; 5; 8; 8; 5; 4; 8];
  value_cons #10 9 [8; 7; 6; 9; 5; 8; 8; 5; 4; 8];
  value_cons #10 8 [7; 6; 9; 5; 8; 8; 5; 4; 8];
  value_cons #10 7 [6; 9; 5; 8; 8; 5; 4; 8];
  value_cons #10 6 [9; 5; 8; 8; 5; 4; 8];
  value_cons #10 9 [5; 8; 8; 5; 4; 8];
  value_cons #10 5 [8; 8; 5; 4; 8];
  value_cons #10 8 [8; 5; 4; 8];
  value_cons #10 8 [5; 4; 8];
  value_cons #10 5 [4; 8];
  value_cons #10 4 [8];
  value_cons #10 8 [];
  value_next25_reversed_tail_20 ();
  ()

let value_next25_target_tail_20 () : Lemma (
    value #10 [6; 7; 8; 7; 8; 7; 6; 7; 4; 1; 4; 6; 3; 5; 6; 5; 6; 8; 6; 6] == 66865653641476787876) =
  value_cons #10 6 [7; 8; 7; 8; 7; 6; 7; 4; 1; 4; 6; 3; 5; 6; 5; 6; 8; 6; 6];
  value_cons #10 7 [8; 7; 8; 7; 6; 7; 4; 1; 4; 6; 3; 5; 6; 5; 6; 8; 6; 6];
  value_cons #10 8 [7; 8; 7; 6; 7; 4; 1; 4; 6; 3; 5; 6; 5; 6; 8; 6; 6];
  value_cons #10 7 [8; 7; 6; 7; 4; 1; 4; 6; 3; 5; 6; 5; 6; 8; 6; 6];
  value_cons #10 8 [7; 6; 7; 4; 1; 4; 6; 3; 5; 6; 5; 6; 8; 6; 6];
  value_cons #10 7 [6; 7; 4; 1; 4; 6; 3; 5; 6; 5; 6; 8; 6; 6];
  value_cons #10 6 [7; 4; 1; 4; 6; 3; 5; 6; 5; 6; 8; 6; 6];
  value_cons #10 7 [4; 1; 4; 6; 3; 5; 6; 5; 6; 8; 6; 6];
  value_cons #10 4 [1; 4; 6; 3; 5; 6; 5; 6; 8; 6; 6];
  value_cons #10 1 [4; 6; 3; 5; 6; 5; 6; 8; 6; 6];
  value_cons #10 4 [6; 3; 5; 6; 5; 6; 8; 6; 6];
  value_cons #10 6 [3; 5; 6; 5; 6; 8; 6; 6];
  value_cons #10 3 [5; 6; 5; 6; 8; 6; 6];
  value_cons #10 5 [6; 5; 6; 8; 6; 6];
  value_cons #10 6 [5; 6; 8; 6; 6];
  value_cons #10 5 [6; 8; 6; 6];
  value_cons #10 6 [8; 6; 6];
  value_cons #10 8 [6; 6];
  value_cons #10 6 [6];
  value_cons #10 6 [];
  ()

let value_next25_target () : Lemma (
    value next25_target == 668656536414767878767414635656756) =
  value_cons #10 6 [5; 7; 6; 5; 6; 5; 3; 6; 4; 1; 4; 7];
  value_cons #10 5 [7; 6; 5; 6; 5; 3; 6; 4; 1; 4; 7];
  value_cons #10 7 [6; 5; 6; 5; 3; 6; 4; 1; 4; 7];
  value_cons #10 6 [5; 6; 5; 3; 6; 4; 1; 4; 7];
  value_cons #10 5 [6; 5; 3; 6; 4; 1; 4; 7];
  value_cons #10 6 [5; 3; 6; 4; 1; 4; 7];
  value_cons #10 5 [3; 6; 4; 1; 4; 7];
  value_cons #10 3 [6; 4; 1; 4; 7];
  value_cons #10 6 [4; 1; 4; 7];
  value_cons #10 4 [1; 4; 7];
  value_cons #10 1 [4; 7];
  value_cons #10 4 [7];
  value_cons #10 7 [];
  value_next25_target_tail_20 ();
  ()

let canonical_next25_reversed () : Lemma (canonical #10 next25_reversed) =
  assert (canonical #10 [5]);
  canonical_cons #10 0 [5];
  canonical_cons #10 8 [0; 5];
  canonical_cons #10 7 [8; 0; 5];
  canonical_cons #10 7 [7; 8; 0; 5];
  canonical_cons #10 9 [7; 7; 8; 0; 5];
  canonical_cons #10 5 [9; 7; 7; 8; 0; 5];
  canonical_cons #10 7 [5; 9; 7; 7; 8; 0; 5];
  canonical_cons #10 7 [7; 5; 9; 7; 7; 8; 0; 5];
  canonical_cons #10 5 [7; 7; 5; 9; 7; 7; 8; 0; 5];
  canonical_cons #10 5 [5; 7; 7; 5; 9; 7; 7; 8; 0; 5];
  canonical_cons #10 9 [5; 5; 7; 7; 5; 9; 7; 7; 8; 0; 5];
  canonical_cons #10 8 [9; 5; 5; 7; 7; 5; 9; 7; 7; 8; 0; 5];
  canonical_cons #10 7 [8; 9; 5; 5; 7; 7; 5; 9; 7; 7; 8; 0; 5];
  canonical_cons #10 9 [7; 8; 9; 5; 5; 7; 7; 5; 9; 7; 7; 8; 0; 5];
  canonical_cons #10 8 [9; 7; 8; 9; 5; 5; 7; 7; 5; 9; 7; 7; 8; 0; 5];
  canonical_cons #10 8 [8; 9; 7; 8; 9; 5; 5; 7; 7; 5; 9; 7; 7; 8; 0; 5];
  canonical_cons #10 9 [8; 8; 9; 7; 8; 9; 5; 5; 7; 7; 5; 9; 7; 7; 8; 0; 5];
  canonical_cons #10 7 [9; 8; 8; 9; 7; 8; 9; 5; 5; 7; 7; 5; 9; 7; 7; 8; 0; 5];
  canonical_cons #10 8 [7; 9; 8; 8; 9; 7; 8; 9; 5; 5; 7; 7; 5; 9; 7; 7; 8; 0; 5];
  canonical_cons #10 8 [8; 7; 9; 8; 8; 9; 7; 8; 9; 5; 5; 7; 7; 5; 9; 7; 7; 8; 0; 5];
  canonical_cons #10 4 [8; 8; 7; 9; 8; 8; 9; 7; 8; 9; 5; 5; 7; 7; 5; 9; 7; 7; 8; 0; 5];
  canonical_cons #10 5 [4; 8; 8; 7; 9; 8; 8; 9; 7; 8; 9; 5; 5; 7; 7; 5; 9; 7; 7; 8; 0; 5];
  canonical_cons #10 8 [5; 4; 8; 8; 7; 9; 8; 8; 9; 7; 8; 9; 5; 5; 7; 7; 5; 9; 7; 7; 8; 0; 5];
  canonical_cons #10 8 [8; 5; 4; 8; 8; 7; 9; 8; 8; 9; 7; 8; 9; 5; 5; 7; 7; 5; 9; 7; 7; 8; 0; 5];
  canonical_cons #10 5 [8; 8; 5; 4; 8; 8; 7; 9; 8; 8; 9; 7; 8; 9; 5; 5; 7; 7; 5; 9; 7; 7; 8; 0; 5];
  canonical_cons #10 9 [5; 8; 8; 5; 4; 8; 8; 7; 9; 8; 8; 9; 7; 8; 9; 5; 5; 7; 7; 5; 9; 7; 7; 8; 0; 5];
  canonical_cons #10 6 [9; 5; 8; 8; 5; 4; 8; 8; 7; 9; 8; 8; 9; 7; 8; 9; 5; 5; 7; 7; 5; 9; 7; 7; 8; 0; 5];
  canonical_cons #10 7 [6; 9; 5; 8; 8; 5; 4; 8; 8; 7; 9; 8; 8; 9; 7; 8; 9; 5; 5; 7; 7; 5; 9; 7; 7; 8; 0; 5];
  canonical_cons #10 8 [7; 6; 9; 5; 8; 8; 5; 4; 8; 8; 7; 9; 8; 8; 9; 7; 8; 9; 5; 5; 7; 7; 5; 9; 7; 7; 8; 0; 5];
  canonical_cons #10 9 [8; 7; 6; 9; 5; 8; 8; 5; 4; 8; 8; 7; 9; 8; 8; 9; 7; 8; 9; 5; 5; 7; 7; 5; 9; 7; 7; 8; 0; 5];
  canonical_cons #10 5 [9; 8; 7; 6; 9; 5; 8; 8; 5; 4; 8; 8; 7; 9; 8; 8; 9; 7; 8; 9; 5; 5; 7; 7; 5; 9; 7; 7; 8; 0; 5];
  canonical_cons #10 1 [5; 9; 8; 7; 6; 9; 5; 8; 8; 5; 4; 8; 8; 7; 9; 8; 8; 9; 7; 8; 9; 5; 5; 7; 7; 5; 9; 7; 7; 8; 0; 5];
  ()

let canonical_next25_target () : Lemma (canonical #10 next25_target) =
  assert (canonical #10 [6]);
  canonical_cons #10 6 [6];
  canonical_cons #10 8 [6; 6];
  canonical_cons #10 6 [8; 6; 6];
  canonical_cons #10 5 [6; 8; 6; 6];
  canonical_cons #10 6 [5; 6; 8; 6; 6];
  canonical_cons #10 5 [6; 5; 6; 8; 6; 6];
  canonical_cons #10 3 [5; 6; 5; 6; 8; 6; 6];
  canonical_cons #10 6 [3; 5; 6; 5; 6; 8; 6; 6];
  canonical_cons #10 4 [6; 3; 5; 6; 5; 6; 8; 6; 6];
  canonical_cons #10 1 [4; 6; 3; 5; 6; 5; 6; 8; 6; 6];
  canonical_cons #10 4 [1; 4; 6; 3; 5; 6; 5; 6; 8; 6; 6];
  canonical_cons #10 7 [4; 1; 4; 6; 3; 5; 6; 5; 6; 8; 6; 6];
  canonical_cons #10 6 [7; 4; 1; 4; 6; 3; 5; 6; 5; 6; 8; 6; 6];
  canonical_cons #10 7 [6; 7; 4; 1; 4; 6; 3; 5; 6; 5; 6; 8; 6; 6];
  canonical_cons #10 8 [7; 6; 7; 4; 1; 4; 6; 3; 5; 6; 5; 6; 8; 6; 6];
  canonical_cons #10 7 [8; 7; 6; 7; 4; 1; 4; 6; 3; 5; 6; 5; 6; 8; 6; 6];
  canonical_cons #10 8 [7; 8; 7; 6; 7; 4; 1; 4; 6; 3; 5; 6; 5; 6; 8; 6; 6];
  canonical_cons #10 7 [8; 7; 8; 7; 6; 7; 4; 1; 4; 6; 3; 5; 6; 5; 6; 8; 6; 6];
  canonical_cons #10 6 [7; 8; 7; 8; 7; 6; 7; 4; 1; 4; 6; 3; 5; 6; 5; 6; 8; 6; 6];
  canonical_cons #10 7 [6; 7; 8; 7; 8; 7; 6; 7; 4; 1; 4; 6; 3; 5; 6; 5; 6; 8; 6; 6];
  canonical_cons #10 4 [7; 6; 7; 8; 7; 8; 7; 6; 7; 4; 1; 4; 6; 3; 5; 6; 5; 6; 8; 6; 6];
  canonical_cons #10 1 [4; 7; 6; 7; 8; 7; 8; 7; 6; 7; 4; 1; 4; 6; 3; 5; 6; 5; 6; 8; 6; 6];
  canonical_cons #10 4 [1; 4; 7; 6; 7; 8; 7; 8; 7; 6; 7; 4; 1; 4; 6; 3; 5; 6; 5; 6; 8; 6; 6];
  canonical_cons #10 6 [4; 1; 4; 7; 6; 7; 8; 7; 8; 7; 6; 7; 4; 1; 4; 6; 3; 5; 6; 5; 6; 8; 6; 6];
  canonical_cons #10 3 [6; 4; 1; 4; 7; 6; 7; 8; 7; 8; 7; 6; 7; 4; 1; 4; 6; 3; 5; 6; 5; 6; 8; 6; 6];
  canonical_cons #10 5 [3; 6; 4; 1; 4; 7; 6; 7; 8; 7; 8; 7; 6; 7; 4; 1; 4; 6; 3; 5; 6; 5; 6; 8; 6; 6];
  canonical_cons #10 6 [5; 3; 6; 4; 1; 4; 7; 6; 7; 8; 7; 8; 7; 6; 7; 4; 1; 4; 6; 3; 5; 6; 5; 6; 8; 6; 6];
  canonical_cons #10 5 [6; 5; 3; 6; 4; 1; 4; 7; 6; 7; 8; 7; 8; 7; 6; 7; 4; 1; 4; 6; 3; 5; 6; 5; 6; 8; 6; 6];
  canonical_cons #10 6 [5; 6; 5; 3; 6; 4; 1; 4; 7; 6; 7; 8; 7; 8; 7; 6; 7; 4; 1; 4; 6; 3; 5; 6; 5; 6; 8; 6; 6];
  canonical_cons #10 7 [6; 5; 6; 5; 3; 6; 4; 1; 4; 7; 6; 7; 8; 7; 8; 7; 6; 7; 4; 1; 4; 6; 3; 5; 6; 5; 6; 8; 6; 6];
  canonical_cons #10 5 [7; 6; 5; 6; 5; 3; 6; 4; 1; 4; 7; 6; 7; 8; 7; 8; 7; 6; 7; 4; 1; 4; 6; 3; 5; 6; 5; 6; 8; 6; 6];
  canonical_cons #10 6 [5; 7; 6; 5; 6; 5; 3; 6; 4; 1; 4; 7; 6; 7; 8; 7; 8; 7; 6; 7; 4; 1; 4; 6; 3; 5; 6; 5; 6; 8; 6; 6];
  ()

let reverse_digits_next25_source () : Lemma (
    reverse_digits #10 next25_source == next25_reversed) =
  ReverseAddNext.canonical_next24_target ();
  reverse_list_next25_source ();
  value_next25_reversed ();
  canonical_next25_reversed ();
  reverse_digits_canonical #10 next25_source;
  normalize_value #10 (rev next25_source);
  assert (value (reverse_digits #10 next25_source) ==
    508779577559879889788458859678951);
  digits_of_nat_of_canonical #10 (reverse_digits #10 next25_source);
  digits_of_nat_of_canonical #10 next25_reversed;
  assert (reverse_digits #10 next25_source == next25_reversed);
  ()

let reverse_add_159876958854887988978955775977805_to_668656536414767878767414635656756 () : Lemma (
    reverse_add #10 next25_source == next25_target) =
  ReverseAddNext.canonical_next24_target ();
  reverse_add_value #10 next25_source;
  ReverseAddNext.value_next24_target ();
  reverse_digits_next25_source ();
  value_next25_reversed ();
  value_next25_target ();
  assert (value (reverse_add #10 next25_source) ==
    668656536414767878767414635656756);
  reverse_add_canonical #10 next25_source;
  digits_of_nat_of_canonical #10 (reverse_add #10 next25_source);
  canonical_next25_target ();
  digits_of_nat_of_canonical #10 next25_target;
  assert (reverse_add #10 next25_source == next25_target);
  ()

let trace_digits_profile_159876958854887988978955775977805 () : Lemma (
    trace_digits next25_source == next25_target) =
  reverse_add_159876958854887988978955775977805_to_668656536414767878767414635656756 ();
  trace_digits_equals_reverse_add next25_source;
  assert (trace_digits next25_source == next25_target);
  ()

let trace_profile_shape_159876958854887988978955775977805 () : Lemma (
    length (trace_digits next25_source) == length next25_source) =
  trace_digits_profile_159876958854887988978955775977805 ();
  length_of_eq #(digit 10) (trace_digits next25_source) next25_target;
  assert (length next25_target == length next25_source);
  ()

let trace_profile_final_carry_159876958854887988978955775977805 () : Lemma (
    nth (trace_carries next25_source) (length next25_source) == Some 0) =
  trace_profile_shape_159876958854887988978955775977805 ();
  final_carry_from_length next25_source;
  ()

let local_profile_witness_668656536414767878767414635656756 () : Lemma (
    trace_local_profile_complement_witness next25_target) =
  ReverseAddNext.canonical_next24_target ();
  assert (next25_source <> []);
  trace_profile_shape_159876958854887988978955775977805 ();
  trace_profile_final_carry_159876958854887988978955775977805 ();
  assert (trace_sum_at next25_source 0 == 6);
  reverse_add_159876958854887988978955775977805_to_668656536414767878767414635656756 ();
  no_overflow_outer_sum_6_to_9_implies_next_witness next25_source;
  ()

let next26_source : numeral 10 = next25_target

let next26_reversed : numeral 10 =
  [6; 6; 8; 6; 5; 6; 5; 3; 6; 4; 1; 4; 7; 6; 7; 8; 7; 8; 7; 6; 7; 4; 1; 4; 6; 3; 5; 6; 5; 6; 7; 5; 6]

let next26_target : numeral 10 =
  [2; 2; 6; 3; 1; 3; 1; 7; 2; 9; 2; 8; 4; 3; 5; 7; 5; 7; 5; 3; 5; 9; 2; 8; 2; 7; 0; 3; 1; 3; 6; 2; 3; 1]

let reverse_list_next26_source () : Lemma (rev next26_source == next26_reversed) =
  assert (rev [6] == [6]);
  rev_cons 6 [6];
  rev_cons 8 [6; 6];
  rev_cons 6 [8; 6; 6];
  rev_cons 5 [6; 8; 6; 6];
  rev_cons 6 [5; 6; 8; 6; 6];
  rev_cons 5 [6; 5; 6; 8; 6; 6];
  rev_cons 3 [5; 6; 5; 6; 8; 6; 6];
  rev_cons 6 [3; 5; 6; 5; 6; 8; 6; 6];
  rev_cons 4 [6; 3; 5; 6; 5; 6; 8; 6; 6];
  rev_cons 1 [4; 6; 3; 5; 6; 5; 6; 8; 6; 6];
  rev_cons 4 [1; 4; 6; 3; 5; 6; 5; 6; 8; 6; 6];
  rev_cons 7 [4; 1; 4; 6; 3; 5; 6; 5; 6; 8; 6; 6];
  rev_cons 6 [7; 4; 1; 4; 6; 3; 5; 6; 5; 6; 8; 6; 6];
  rev_cons 7 [6; 7; 4; 1; 4; 6; 3; 5; 6; 5; 6; 8; 6; 6];
  rev_cons 8 [7; 6; 7; 4; 1; 4; 6; 3; 5; 6; 5; 6; 8; 6; 6];
  rev_cons 7 [8; 7; 6; 7; 4; 1; 4; 6; 3; 5; 6; 5; 6; 8; 6; 6];
  rev_cons 8 [7; 8; 7; 6; 7; 4; 1; 4; 6; 3; 5; 6; 5; 6; 8; 6; 6];
  rev_cons 7 [8; 7; 8; 7; 6; 7; 4; 1; 4; 6; 3; 5; 6; 5; 6; 8; 6; 6];
  rev_cons 6 [7; 8; 7; 8; 7; 6; 7; 4; 1; 4; 6; 3; 5; 6; 5; 6; 8; 6; 6];
  rev_cons 7 [6; 7; 8; 7; 8; 7; 6; 7; 4; 1; 4; 6; 3; 5; 6; 5; 6; 8; 6; 6];
  rev_cons 4 [7; 6; 7; 8; 7; 8; 7; 6; 7; 4; 1; 4; 6; 3; 5; 6; 5; 6; 8; 6; 6];
  rev_cons 1 [4; 7; 6; 7; 8; 7; 8; 7; 6; 7; 4; 1; 4; 6; 3; 5; 6; 5; 6; 8; 6; 6];
  rev_cons 4 [1; 4; 7; 6; 7; 8; 7; 8; 7; 6; 7; 4; 1; 4; 6; 3; 5; 6; 5; 6; 8; 6; 6];
  rev_cons 6 [4; 1; 4; 7; 6; 7; 8; 7; 8; 7; 6; 7; 4; 1; 4; 6; 3; 5; 6; 5; 6; 8; 6; 6];
  rev_cons 3 [6; 4; 1; 4; 7; 6; 7; 8; 7; 8; 7; 6; 7; 4; 1; 4; 6; 3; 5; 6; 5; 6; 8; 6; 6];
  rev_cons 5 [3; 6; 4; 1; 4; 7; 6; 7; 8; 7; 8; 7; 6; 7; 4; 1; 4; 6; 3; 5; 6; 5; 6; 8; 6; 6];
  rev_cons 6 [5; 3; 6; 4; 1; 4; 7; 6; 7; 8; 7; 8; 7; 6; 7; 4; 1; 4; 6; 3; 5; 6; 5; 6; 8; 6; 6];
  rev_cons 5 [6; 5; 3; 6; 4; 1; 4; 7; 6; 7; 8; 7; 8; 7; 6; 7; 4; 1; 4; 6; 3; 5; 6; 5; 6; 8; 6; 6];
  rev_cons 6 [5; 6; 5; 3; 6; 4; 1; 4; 7; 6; 7; 8; 7; 8; 7; 6; 7; 4; 1; 4; 6; 3; 5; 6; 5; 6; 8; 6; 6];
  rev_cons 7 [6; 5; 6; 5; 3; 6; 4; 1; 4; 7; 6; 7; 8; 7; 8; 7; 6; 7; 4; 1; 4; 6; 3; 5; 6; 5; 6; 8; 6; 6];
  rev_cons 5 [7; 6; 5; 6; 5; 3; 6; 4; 1; 4; 7; 6; 7; 8; 7; 8; 7; 6; 7; 4; 1; 4; 6; 3; 5; 6; 5; 6; 8; 6; 6];
  rev_cons 6 [5; 7; 6; 5; 6; 5; 3; 6; 4; 1; 4; 7; 6; 7; 8; 7; 8; 7; 6; 7; 4; 1; 4; 6; 3; 5; 6; 5; 6; 8; 6; 6];
  ()

let value_next26_reversed_tail_20 () : Lemma (
    value #10 [6; 7; 8; 7; 8; 7; 6; 7; 4; 1; 4; 6; 3; 5; 6; 5; 6; 7; 5; 6] == 65765653641476787876) =
  value_cons #10 6 [7; 8; 7; 8; 7; 6; 7; 4; 1; 4; 6; 3; 5; 6; 5; 6; 7; 5; 6];
  value_cons #10 7 [8; 7; 8; 7; 6; 7; 4; 1; 4; 6; 3; 5; 6; 5; 6; 7; 5; 6];
  value_cons #10 8 [7; 8; 7; 6; 7; 4; 1; 4; 6; 3; 5; 6; 5; 6; 7; 5; 6];
  value_cons #10 7 [8; 7; 6; 7; 4; 1; 4; 6; 3; 5; 6; 5; 6; 7; 5; 6];
  value_cons #10 8 [7; 6; 7; 4; 1; 4; 6; 3; 5; 6; 5; 6; 7; 5; 6];
  value_cons #10 7 [6; 7; 4; 1; 4; 6; 3; 5; 6; 5; 6; 7; 5; 6];
  value_cons #10 6 [7; 4; 1; 4; 6; 3; 5; 6; 5; 6; 7; 5; 6];
  value_cons #10 7 [4; 1; 4; 6; 3; 5; 6; 5; 6; 7; 5; 6];
  value_cons #10 4 [1; 4; 6; 3; 5; 6; 5; 6; 7; 5; 6];
  value_cons #10 1 [4; 6; 3; 5; 6; 5; 6; 7; 5; 6];
  value_cons #10 4 [6; 3; 5; 6; 5; 6; 7; 5; 6];
  value_cons #10 6 [3; 5; 6; 5; 6; 7; 5; 6];
  value_cons #10 3 [5; 6; 5; 6; 7; 5; 6];
  value_cons #10 5 [6; 5; 6; 7; 5; 6];
  value_cons #10 6 [5; 6; 7; 5; 6];
  value_cons #10 5 [6; 7; 5; 6];
  value_cons #10 6 [7; 5; 6];
  value_cons #10 7 [5; 6];
  value_cons #10 5 [6];
  value_cons #10 6 [];
  ()

let value_next26_reversed () : Lemma (
    value next26_reversed == 657656536414767878767414635656866) =
  value_cons #10 6 [6; 8; 6; 5; 6; 5; 3; 6; 4; 1; 4; 7];
  value_cons #10 6 [8; 6; 5; 6; 5; 3; 6; 4; 1; 4; 7];
  value_cons #10 8 [6; 5; 6; 5; 3; 6; 4; 1; 4; 7];
  value_cons #10 6 [5; 6; 5; 3; 6; 4; 1; 4; 7];
  value_cons #10 5 [6; 5; 3; 6; 4; 1; 4; 7];
  value_cons #10 6 [5; 3; 6; 4; 1; 4; 7];
  value_cons #10 5 [3; 6; 4; 1; 4; 7];
  value_cons #10 3 [6; 4; 1; 4; 7];
  value_cons #10 6 [4; 1; 4; 7];
  value_cons #10 4 [1; 4; 7];
  value_cons #10 1 [4; 7];
  value_cons #10 4 [7];
  value_cons #10 7 [];
  value_next26_reversed_tail_20 ();
  ()

let value_next26_target_tail_20 () : Lemma (
    value #10 [5; 7; 5; 7; 5; 3; 5; 9; 2; 8; 2; 7; 0; 3; 1; 3; 6; 2; 3; 1] == 13263130728295357575) =
  value_cons #10 5 [7; 5; 7; 5; 3; 5; 9; 2; 8; 2; 7; 0; 3; 1; 3; 6; 2; 3; 1];
  value_cons #10 7 [5; 7; 5; 3; 5; 9; 2; 8; 2; 7; 0; 3; 1; 3; 6; 2; 3; 1];
  value_cons #10 5 [7; 5; 3; 5; 9; 2; 8; 2; 7; 0; 3; 1; 3; 6; 2; 3; 1];
  value_cons #10 7 [5; 3; 5; 9; 2; 8; 2; 7; 0; 3; 1; 3; 6; 2; 3; 1];
  value_cons #10 5 [3; 5; 9; 2; 8; 2; 7; 0; 3; 1; 3; 6; 2; 3; 1];
  value_cons #10 3 [5; 9; 2; 8; 2; 7; 0; 3; 1; 3; 6; 2; 3; 1];
  value_cons #10 5 [9; 2; 8; 2; 7; 0; 3; 1; 3; 6; 2; 3; 1];
  value_cons #10 9 [2; 8; 2; 7; 0; 3; 1; 3; 6; 2; 3; 1];
  value_cons #10 2 [8; 2; 7; 0; 3; 1; 3; 6; 2; 3; 1];
  value_cons #10 8 [2; 7; 0; 3; 1; 3; 6; 2; 3; 1];
  value_cons #10 2 [7; 0; 3; 1; 3; 6; 2; 3; 1];
  value_cons #10 7 [0; 3; 1; 3; 6; 2; 3; 1];
  value_cons #10 0 [3; 1; 3; 6; 2; 3; 1];
  value_cons #10 3 [1; 3; 6; 2; 3; 1];
  value_cons #10 1 [3; 6; 2; 3; 1];
  value_cons #10 3 [6; 2; 3; 1];
  value_cons #10 6 [2; 3; 1];
  value_cons #10 2 [3; 1];
  value_cons #10 3 [1];
  value_cons #10 1 [];
  ()

let value_next26_target () : Lemma (
    value next26_target == 1326313072829535757534829271313622) =
  value_cons #10 2 [2; 6; 3; 1; 3; 1; 7; 2; 9; 2; 8; 4; 3];
  value_cons #10 2 [6; 3; 1; 3; 1; 7; 2; 9; 2; 8; 4; 3];
  value_cons #10 6 [3; 1; 3; 1; 7; 2; 9; 2; 8; 4; 3];
  value_cons #10 3 [1; 3; 1; 7; 2; 9; 2; 8; 4; 3];
  value_cons #10 1 [3; 1; 7; 2; 9; 2; 8; 4; 3];
  value_cons #10 3 [1; 7; 2; 9; 2; 8; 4; 3];
  value_cons #10 1 [7; 2; 9; 2; 8; 4; 3];
  value_cons #10 7 [2; 9; 2; 8; 4; 3];
  value_cons #10 2 [9; 2; 8; 4; 3];
  value_cons #10 9 [2; 8; 4; 3];
  value_cons #10 2 [8; 4; 3];
  value_cons #10 8 [4; 3];
  value_cons #10 4 [3];
  value_cons #10 3 [];
  value_next26_target_tail_20 ();
  ()

let canonical_next26_reversed () : Lemma (canonical #10 next26_reversed) =
  assert (canonical #10 [6]);
  canonical_cons #10 5 [6];
  canonical_cons #10 7 [5; 6];
  canonical_cons #10 6 [7; 5; 6];
  canonical_cons #10 5 [6; 7; 5; 6];
  canonical_cons #10 6 [5; 6; 7; 5; 6];
  canonical_cons #10 5 [6; 5; 6; 7; 5; 6];
  canonical_cons #10 3 [5; 6; 5; 6; 7; 5; 6];
  canonical_cons #10 6 [3; 5; 6; 5; 6; 7; 5; 6];
  canonical_cons #10 4 [6; 3; 5; 6; 5; 6; 7; 5; 6];
  canonical_cons #10 1 [4; 6; 3; 5; 6; 5; 6; 7; 5; 6];
  canonical_cons #10 4 [1; 4; 6; 3; 5; 6; 5; 6; 7; 5; 6];
  canonical_cons #10 7 [4; 1; 4; 6; 3; 5; 6; 5; 6; 7; 5; 6];
  canonical_cons #10 6 [7; 4; 1; 4; 6; 3; 5; 6; 5; 6; 7; 5; 6];
  canonical_cons #10 7 [6; 7; 4; 1; 4; 6; 3; 5; 6; 5; 6; 7; 5; 6];
  canonical_cons #10 8 [7; 6; 7; 4; 1; 4; 6; 3; 5; 6; 5; 6; 7; 5; 6];
  canonical_cons #10 7 [8; 7; 6; 7; 4; 1; 4; 6; 3; 5; 6; 5; 6; 7; 5; 6];
  canonical_cons #10 8 [7; 8; 7; 6; 7; 4; 1; 4; 6; 3; 5; 6; 5; 6; 7; 5; 6];
  canonical_cons #10 7 [8; 7; 8; 7; 6; 7; 4; 1; 4; 6; 3; 5; 6; 5; 6; 7; 5; 6];
  canonical_cons #10 6 [7; 8; 7; 8; 7; 6; 7; 4; 1; 4; 6; 3; 5; 6; 5; 6; 7; 5; 6];
  canonical_cons #10 7 [6; 7; 8; 7; 8; 7; 6; 7; 4; 1; 4; 6; 3; 5; 6; 5; 6; 7; 5; 6];
  canonical_cons #10 4 [7; 6; 7; 8; 7; 8; 7; 6; 7; 4; 1; 4; 6; 3; 5; 6; 5; 6; 7; 5; 6];
  canonical_cons #10 1 [4; 7; 6; 7; 8; 7; 8; 7; 6; 7; 4; 1; 4; 6; 3; 5; 6; 5; 6; 7; 5; 6];
  canonical_cons #10 4 [1; 4; 7; 6; 7; 8; 7; 8; 7; 6; 7; 4; 1; 4; 6; 3; 5; 6; 5; 6; 7; 5; 6];
  canonical_cons #10 6 [4; 1; 4; 7; 6; 7; 8; 7; 8; 7; 6; 7; 4; 1; 4; 6; 3; 5; 6; 5; 6; 7; 5; 6];
  canonical_cons #10 3 [6; 4; 1; 4; 7; 6; 7; 8; 7; 8; 7; 6; 7; 4; 1; 4; 6; 3; 5; 6; 5; 6; 7; 5; 6];
  canonical_cons #10 5 [3; 6; 4; 1; 4; 7; 6; 7; 8; 7; 8; 7; 6; 7; 4; 1; 4; 6; 3; 5; 6; 5; 6; 7; 5; 6];
  canonical_cons #10 6 [5; 3; 6; 4; 1; 4; 7; 6; 7; 8; 7; 8; 7; 6; 7; 4; 1; 4; 6; 3; 5; 6; 5; 6; 7; 5; 6];
  canonical_cons #10 5 [6; 5; 3; 6; 4; 1; 4; 7; 6; 7; 8; 7; 8; 7; 6; 7; 4; 1; 4; 6; 3; 5; 6; 5; 6; 7; 5; 6];
  canonical_cons #10 6 [5; 6; 5; 3; 6; 4; 1; 4; 7; 6; 7; 8; 7; 8; 7; 6; 7; 4; 1; 4; 6; 3; 5; 6; 5; 6; 7; 5; 6];
  canonical_cons #10 8 [6; 5; 6; 5; 3; 6; 4; 1; 4; 7; 6; 7; 8; 7; 8; 7; 6; 7; 4; 1; 4; 6; 3; 5; 6; 5; 6; 7; 5; 6];
  canonical_cons #10 6 [8; 6; 5; 6; 5; 3; 6; 4; 1; 4; 7; 6; 7; 8; 7; 8; 7; 6; 7; 4; 1; 4; 6; 3; 5; 6; 5; 6; 7; 5; 6];
  canonical_cons #10 6 [6; 8; 6; 5; 6; 5; 3; 6; 4; 1; 4; 7; 6; 7; 8; 7; 8; 7; 6; 7; 4; 1; 4; 6; 3; 5; 6; 5; 6; 7; 5; 6];
  ()

let canonical_next26_target () : Lemma (canonical #10 next26_target) =
  assert (canonical #10 [1]);
  canonical_cons #10 3 [1];
  canonical_cons #10 2 [3; 1];
  canonical_cons #10 6 [2; 3; 1];
  canonical_cons #10 3 [6; 2; 3; 1];
  canonical_cons #10 1 [3; 6; 2; 3; 1];
  canonical_cons #10 3 [1; 3; 6; 2; 3; 1];
  canonical_cons #10 0 [3; 1; 3; 6; 2; 3; 1];
  canonical_cons #10 7 [0; 3; 1; 3; 6; 2; 3; 1];
  canonical_cons #10 2 [7; 0; 3; 1; 3; 6; 2; 3; 1];
  canonical_cons #10 8 [2; 7; 0; 3; 1; 3; 6; 2; 3; 1];
  canonical_cons #10 2 [8; 2; 7; 0; 3; 1; 3; 6; 2; 3; 1];
  canonical_cons #10 9 [2; 8; 2; 7; 0; 3; 1; 3; 6; 2; 3; 1];
  canonical_cons #10 5 [9; 2; 8; 2; 7; 0; 3; 1; 3; 6; 2; 3; 1];
  canonical_cons #10 3 [5; 9; 2; 8; 2; 7; 0; 3; 1; 3; 6; 2; 3; 1];
  canonical_cons #10 5 [3; 5; 9; 2; 8; 2; 7; 0; 3; 1; 3; 6; 2; 3; 1];
  canonical_cons #10 7 [5; 3; 5; 9; 2; 8; 2; 7; 0; 3; 1; 3; 6; 2; 3; 1];
  canonical_cons #10 5 [7; 5; 3; 5; 9; 2; 8; 2; 7; 0; 3; 1; 3; 6; 2; 3; 1];
  canonical_cons #10 7 [5; 7; 5; 3; 5; 9; 2; 8; 2; 7; 0; 3; 1; 3; 6; 2; 3; 1];
  canonical_cons #10 5 [7; 5; 7; 5; 3; 5; 9; 2; 8; 2; 7; 0; 3; 1; 3; 6; 2; 3; 1];
  canonical_cons #10 3 [5; 7; 5; 7; 5; 3; 5; 9; 2; 8; 2; 7; 0; 3; 1; 3; 6; 2; 3; 1];
  canonical_cons #10 4 [3; 5; 7; 5; 7; 5; 3; 5; 9; 2; 8; 2; 7; 0; 3; 1; 3; 6; 2; 3; 1];
  canonical_cons #10 8 [4; 3; 5; 7; 5; 7; 5; 3; 5; 9; 2; 8; 2; 7; 0; 3; 1; 3; 6; 2; 3; 1];
  canonical_cons #10 2 [8; 4; 3; 5; 7; 5; 7; 5; 3; 5; 9; 2; 8; 2; 7; 0; 3; 1; 3; 6; 2; 3; 1];
  canonical_cons #10 9 [2; 8; 4; 3; 5; 7; 5; 7; 5; 3; 5; 9; 2; 8; 2; 7; 0; 3; 1; 3; 6; 2; 3; 1];
  canonical_cons #10 2 [9; 2; 8; 4; 3; 5; 7; 5; 7; 5; 3; 5; 9; 2; 8; 2; 7; 0; 3; 1; 3; 6; 2; 3; 1];
  canonical_cons #10 7 [2; 9; 2; 8; 4; 3; 5; 7; 5; 7; 5; 3; 5; 9; 2; 8; 2; 7; 0; 3; 1; 3; 6; 2; 3; 1];
  canonical_cons #10 1 [7; 2; 9; 2; 8; 4; 3; 5; 7; 5; 7; 5; 3; 5; 9; 2; 8; 2; 7; 0; 3; 1; 3; 6; 2; 3; 1];
  canonical_cons #10 3 [1; 7; 2; 9; 2; 8; 4; 3; 5; 7; 5; 7; 5; 3; 5; 9; 2; 8; 2; 7; 0; 3; 1; 3; 6; 2; 3; 1];
  canonical_cons #10 1 [3; 1; 7; 2; 9; 2; 8; 4; 3; 5; 7; 5; 7; 5; 3; 5; 9; 2; 8; 2; 7; 0; 3; 1; 3; 6; 2; 3; 1];
  canonical_cons #10 3 [1; 3; 1; 7; 2; 9; 2; 8; 4; 3; 5; 7; 5; 7; 5; 3; 5; 9; 2; 8; 2; 7; 0; 3; 1; 3; 6; 2; 3; 1];
  canonical_cons #10 6 [3; 1; 3; 1; 7; 2; 9; 2; 8; 4; 3; 5; 7; 5; 7; 5; 3; 5; 9; 2; 8; 2; 7; 0; 3; 1; 3; 6; 2; 3; 1];
  canonical_cons #10 2 [6; 3; 1; 3; 1; 7; 2; 9; 2; 8; 4; 3; 5; 7; 5; 7; 5; 3; 5; 9; 2; 8; 2; 7; 0; 3; 1; 3; 6; 2; 3; 1];
  canonical_cons #10 2 [2; 6; 3; 1; 3; 1; 7; 2; 9; 2; 8; 4; 3; 5; 7; 5; 7; 5; 3; 5; 9; 2; 8; 2; 7; 0; 3; 1; 3; 6; 2; 3; 1];
  ()

let reverse_digits_next26_source () : Lemma (
    reverse_digits #10 next26_source == next26_reversed) =
  ReverseAddNext.canonical_next25_target ();
  reverse_list_next26_source ();
  value_next26_reversed ();
  canonical_next26_reversed ();
  reverse_digits_canonical #10 next26_source;
  normalize_value #10 (rev next26_source);
  assert (value (reverse_digits #10 next26_source) ==
    657656536414767878767414635656866);
  digits_of_nat_of_canonical #10 (reverse_digits #10 next26_source);
  digits_of_nat_of_canonical #10 next26_reversed;
  assert (reverse_digits #10 next26_source == next26_reversed);
  ()

let reverse_add_668656536414767878767414635656756_to_1326313072829535757534829271313622 () : Lemma (
    reverse_add #10 next26_source == next26_target) =
  ReverseAddNext.canonical_next25_target ();
  reverse_add_value #10 next26_source;
  ReverseAddNext.value_next25_target ();
  reverse_digits_next26_source ();
  value_next26_reversed ();
  value_next26_target ();
  assert (value (reverse_add #10 next26_source) ==
    1326313072829535757534829271313622);
  reverse_add_canonical #10 next26_source;
  digits_of_nat_of_canonical #10 (reverse_add #10 next26_source);
  canonical_next26_target ();
  digits_of_nat_of_canonical #10 next26_target;
  assert (reverse_add #10 next26_source == next26_target);
  ()

let trace_digits_profile_668656536414767878767414635656756 () : Lemma (
    trace_digits next26_source == next26_target) =
  reverse_add_668656536414767878767414635656756_to_1326313072829535757534829271313622 ();
  trace_digits_equals_reverse_add next26_source;
  assert (trace_digits next26_source == next26_target);
  ()

let trace_carries_next26_source () : Lemma (trace_carries next26_source ==
    [0; 1; 1; 1; 1; 1; 1; 1; 0; 1; 0; 0; 0; 1; 1; 1; 1; 1; 1; 1; 1; 1; 0; 0; 0; 1; 0; 1; 1; 1; 1; 1; 1; 1]) =
  reverse_list_next26_source ();
  assert (trace_carries next26_source ==
    (add_trace #10 next26_source next26_reversed 0).carries);
  add_trace_carries_step #10 6 6
    [5; 7; 6; 5; 6; 5; 3; 6; 4; 1; 4; 7; 6; 7; 8; 7; 8; 7; 6; 7; 4; 1; 4; 6; 3; 5; 6; 5; 6; 8; 6; 6]
    [6; 8; 6; 5; 6; 5; 3; 6; 4; 1; 4; 7; 6; 7; 8; 7; 8; 7; 6; 7; 4; 1; 4; 6; 3; 5; 6; 5; 6; 7; 5; 6] 0;
  add_trace_carries_step #10 5 6
    [7; 6; 5; 6; 5; 3; 6; 4; 1; 4; 7; 6; 7; 8; 7; 8; 7; 6; 7; 4; 1; 4; 6; 3; 5; 6; 5; 6; 8; 6; 6]
    [8; 6; 5; 6; 5; 3; 6; 4; 1; 4; 7; 6; 7; 8; 7; 8; 7; 6; 7; 4; 1; 4; 6; 3; 5; 6; 5; 6; 7; 5; 6] 1;
  add_trace_carries_step #10 7 8
    [6; 5; 6; 5; 3; 6; 4; 1; 4; 7; 6; 7; 8; 7; 8; 7; 6; 7; 4; 1; 4; 6; 3; 5; 6; 5; 6; 8; 6; 6]
    [6; 5; 6; 5; 3; 6; 4; 1; 4; 7; 6; 7; 8; 7; 8; 7; 6; 7; 4; 1; 4; 6; 3; 5; 6; 5; 6; 7; 5; 6] 1;
  add_trace_carries_step #10 6 6
    [5; 6; 5; 3; 6; 4; 1; 4; 7; 6; 7; 8; 7; 8; 7; 6; 7; 4; 1; 4; 6; 3; 5; 6; 5; 6; 8; 6; 6]
    [5; 6; 5; 3; 6; 4; 1; 4; 7; 6; 7; 8; 7; 8; 7; 6; 7; 4; 1; 4; 6; 3; 5; 6; 5; 6; 7; 5; 6] 1;
  add_trace_carries_step #10 5 5
    [6; 5; 3; 6; 4; 1; 4; 7; 6; 7; 8; 7; 8; 7; 6; 7; 4; 1; 4; 6; 3; 5; 6; 5; 6; 8; 6; 6]
    [6; 5; 3; 6; 4; 1; 4; 7; 6; 7; 8; 7; 8; 7; 6; 7; 4; 1; 4; 6; 3; 5; 6; 5; 6; 7; 5; 6] 1;
  add_trace_carries_step #10 6 6
    [5; 3; 6; 4; 1; 4; 7; 6; 7; 8; 7; 8; 7; 6; 7; 4; 1; 4; 6; 3; 5; 6; 5; 6; 8; 6; 6]
    [5; 3; 6; 4; 1; 4; 7; 6; 7; 8; 7; 8; 7; 6; 7; 4; 1; 4; 6; 3; 5; 6; 5; 6; 7; 5; 6] 1;
  add_trace_carries_step #10 5 5
    [3; 6; 4; 1; 4; 7; 6; 7; 8; 7; 8; 7; 6; 7; 4; 1; 4; 6; 3; 5; 6; 5; 6; 8; 6; 6]
    [3; 6; 4; 1; 4; 7; 6; 7; 8; 7; 8; 7; 6; 7; 4; 1; 4; 6; 3; 5; 6; 5; 6; 7; 5; 6] 1;
  add_trace_carries_step #10 3 3
    [6; 4; 1; 4; 7; 6; 7; 8; 7; 8; 7; 6; 7; 4; 1; 4; 6; 3; 5; 6; 5; 6; 8; 6; 6]
    [6; 4; 1; 4; 7; 6; 7; 8; 7; 8; 7; 6; 7; 4; 1; 4; 6; 3; 5; 6; 5; 6; 7; 5; 6] 1;
  add_trace_carries_step #10 6 6
    [4; 1; 4; 7; 6; 7; 8; 7; 8; 7; 6; 7; 4; 1; 4; 6; 3; 5; 6; 5; 6; 8; 6; 6]
    [4; 1; 4; 7; 6; 7; 8; 7; 8; 7; 6; 7; 4; 1; 4; 6; 3; 5; 6; 5; 6; 7; 5; 6] 0;
  add_trace_carries_step #10 4 4
    [1; 4; 7; 6; 7; 8; 7; 8; 7; 6; 7; 4; 1; 4; 6; 3; 5; 6; 5; 6; 8; 6; 6]
    [1; 4; 7; 6; 7; 8; 7; 8; 7; 6; 7; 4; 1; 4; 6; 3; 5; 6; 5; 6; 7; 5; 6] 1;
  add_trace_carries_step #10 1 1
    [4; 7; 6; 7; 8; 7; 8; 7; 6; 7; 4; 1; 4; 6; 3; 5; 6; 5; 6; 8; 6; 6]
    [4; 7; 6; 7; 8; 7; 8; 7; 6; 7; 4; 1; 4; 6; 3; 5; 6; 5; 6; 7; 5; 6] 0;
  add_trace_carries_step #10 4 4
    [7; 6; 7; 8; 7; 8; 7; 6; 7; 4; 1; 4; 6; 3; 5; 6; 5; 6; 8; 6; 6]
    [7; 6; 7; 8; 7; 8; 7; 6; 7; 4; 1; 4; 6; 3; 5; 6; 5; 6; 7; 5; 6] 0;
  add_trace_carries_step #10 7 7
    [6; 7; 8; 7; 8; 7; 6; 7; 4; 1; 4; 6; 3; 5; 6; 5; 6; 8; 6; 6]
    [6; 7; 8; 7; 8; 7; 6; 7; 4; 1; 4; 6; 3; 5; 6; 5; 6; 7; 5; 6] 0;
  add_trace_carries_step #10 6 6
    [7; 8; 7; 8; 7; 6; 7; 4; 1; 4; 6; 3; 5; 6; 5; 6; 8; 6; 6]
    [7; 8; 7; 8; 7; 6; 7; 4; 1; 4; 6; 3; 5; 6; 5; 6; 7; 5; 6] 1;
  add_trace_carries_step #10 7 7
    [8; 7; 8; 7; 6; 7; 4; 1; 4; 6; 3; 5; 6; 5; 6; 8; 6; 6]
    [8; 7; 8; 7; 6; 7; 4; 1; 4; 6; 3; 5; 6; 5; 6; 7; 5; 6] 1;
  add_trace_carries_step #10 8 8
    [7; 8; 7; 6; 7; 4; 1; 4; 6; 3; 5; 6; 5; 6; 8; 6; 6]
    [7; 8; 7; 6; 7; 4; 1; 4; 6; 3; 5; 6; 5; 6; 7; 5; 6] 1;
  add_trace_carries_step #10 7 7
    [8; 7; 6; 7; 4; 1; 4; 6; 3; 5; 6; 5; 6; 8; 6; 6]
    [8; 7; 6; 7; 4; 1; 4; 6; 3; 5; 6; 5; 6; 7; 5; 6] 1;
  add_trace_carries_step #10 8 8
    [7; 6; 7; 4; 1; 4; 6; 3; 5; 6; 5; 6; 8; 6; 6]
    [7; 6; 7; 4; 1; 4; 6; 3; 5; 6; 5; 6; 7; 5; 6] 1;
  add_trace_carries_step #10 7 7
    [6; 7; 4; 1; 4; 6; 3; 5; 6; 5; 6; 8; 6; 6]
    [6; 7; 4; 1; 4; 6; 3; 5; 6; 5; 6; 7; 5; 6] 1;
  add_trace_carries_step #10 6 6
    [7; 4; 1; 4; 6; 3; 5; 6; 5; 6; 8; 6; 6]
    [7; 4; 1; 4; 6; 3; 5; 6; 5; 6; 7; 5; 6] 1;
  add_trace_carries_step #10 7 7
    [4; 1; 4; 6; 3; 5; 6; 5; 6; 8; 6; 6]
    [4; 1; 4; 6; 3; 5; 6; 5; 6; 7; 5; 6] 1;
  add_trace_carries_step #10 4 4
    [1; 4; 6; 3; 5; 6; 5; 6; 8; 6; 6]
    [1; 4; 6; 3; 5; 6; 5; 6; 7; 5; 6] 1;
  add_trace_carries_step #10 1 1
    [4; 6; 3; 5; 6; 5; 6; 8; 6; 6]
    [4; 6; 3; 5; 6; 5; 6; 7; 5; 6] 0;
  add_trace_carries_step #10 4 4
    [6; 3; 5; 6; 5; 6; 8; 6; 6]
    [6; 3; 5; 6; 5; 6; 7; 5; 6] 0;
  add_trace_carries_step #10 6 6
    [3; 5; 6; 5; 6; 8; 6; 6]
    [3; 5; 6; 5; 6; 7; 5; 6] 0;
  add_trace_carries_step #10 3 3
    [5; 6; 5; 6; 8; 6; 6]
    [5; 6; 5; 6; 7; 5; 6] 1;
  add_trace_carries_step #10 5 5
    [6; 5; 6; 8; 6; 6]
    [6; 5; 6; 7; 5; 6] 0;
  add_trace_carries_step #10 6 6
    [5; 6; 8; 6; 6]
    [5; 6; 7; 5; 6] 1;
  add_trace_carries_step #10 5 5
    [6; 8; 6; 6]
    [6; 7; 5; 6] 1;
  add_trace_carries_step #10 6 6
    [8; 6; 6]
    [7; 5; 6] 1;
  add_trace_carries_step #10 8 7
    [6; 6]
    [5; 6] 1;
  add_trace_carries_step #10 6 5
    [6]
    [6] 1;
  add_trace_carries_step #10 6 6
    []
    [] 1;
  assert ((add_trace #10 [] [] 1).carries == [1]);
  assert ((add_trace #10 next26_source next26_reversed 0).carries == [0; 1; 1; 1; 1; 1; 1; 1; 0; 1; 0; 0; 0; 1; 1; 1; 1; 1; 1; 1; 1; 1; 0; 0; 0; 1; 0; 1; 1; 1; 1; 1; 1; 1]);
  ()

let trace_profile_shape_668656536414767878767414635656756 () : Lemma (
    length (trace_digits next26_source) == length next26_source + 1) =
  trace_digits_profile_668656536414767878767414635656756 ();
  length_of_eq #(digit 10) (trace_digits next26_source) next26_target;
  assert (length next26_target == length next26_source + 1);
  ()

let trace_profile_final_carry_668656536414767878767414635656756 () : Lemma (
    nth (trace_carries next26_source) (length next26_source) == Some 1) =
  trace_profile_shape_668656536414767878767414635656756 ();
  ReverseAddContinuation.final_carry_from_overflow_length next26_source;
  ()

let trace_profile_sums_668656536414767878767414635656756 () : Lemma (
    trace_sum_at next26_source 0 == 12 /\
    trace_sum_at next26_source 9 == 8 /\
    trace_sum_at next26_source 24 == 12) =
  reverse_list_next26_source ();
  ()

let trace_profile_carry_facts_668656536414767878767414635656756 () : Lemma (
    trace_carry_at next26_source 1 == 1 /\
    trace_carry_at next26_source 32 == 1 /\
    trace_carry_at next26_source 9 == 1 /\
    trace_carry_at next26_source 33 == 1 /\
    trace_carry_at next26_source 10 == 0 /\
    trace_carry_at next26_source 24 == 0) =
  trace_carries_next26_source ();
  assert (trace_carry_at next26_source 1 == 1);
  assert (trace_carry_at next26_source 32 == 1);
  assert (trace_carry_at next26_source 9 == 1);
  assert (trace_carry_at next26_source 33 == 1);
  assert (trace_carry_at next26_source 10 == 0);
  assert (trace_carry_at next26_source 24 == 0);
  assert (trace_carries next26_source == [0; 1; 1; 1; 1; 1; 1; 1; 0; 1; 0; 0; 0; 1; 1; 1; 1; 1; 1; 1; 1; 1; 0; 0; 0; 1; 0; 1; 1; 1; 1; 1; 1; 1]);
  ()

let overflow_precondition_668656536414767878767414635656756 () : Lemma (
    canonical #10 next26_source /\
    next26_source <> [] /\
    length (trace_digits next26_source) == length next26_source + 1 /\
    nth (trace_carries next26_source) (length next26_source) == Some 1 /\
    1 <= trace_sum_at next26_source 0 /\
    trace_sum_at next26_source 0 <= 18 /\
    trace_sum_at next26_source 0 <> 10 /\
    exists (i:nat). 0 < i /\ i < length next26_source /\
      trace_sum_at next26_source i +
          trace_sum_at next26_source (length next26_source - i) +
          trace_carry_at next26_source i +
          trace_carry_at next26_source (length next26_source - i) >=
        10 + 10 *
          (trace_carry_at next26_source (i + 1) +
           trace_carry_at next26_source (length next26_source - i + 1))) =
  ReverseAddNext.canonical_next25_target ();
  assert (next26_source <> []);
  trace_profile_shape_668656536414767878767414635656756 ();
  trace_profile_final_carry_668656536414767878767414635656756 ();
  trace_profile_sums_668656536414767878767414635656756 ();
  trace_profile_carry_facts_668656536414767878767414635656756 ();
  assert (length (trace_digits next26_source) == length next26_source + 1);
  assert (nth (trace_carries next26_source)
    (length next26_source) == Some 1);
  assert (trace_sum_at next26_source 0 == 12);
  assert (trace_sum_at next26_source 9 == 8);
  assert (trace_sum_at next26_source 24 == 12);
  assert (trace_carry_at next26_source 1 == 1);
  assert (trace_carry_at next26_source 32 == 1);
  assert (trace_carry_at next26_source 9 == 1);
  assert (trace_carry_at next26_source 33 == 1);
  assert (trace_carry_at next26_source 10 == 0);
  assert (trace_carry_at next26_source 24 == 0);
  assert (1 <= trace_sum_at next26_source 0 /\
    trace_sum_at next26_source 0 <= 18);
  assert (trace_sum_at next26_source 0 <> 10);
  let n : nat = length next26_source in
  assert (0 < 9 /\ 9 < n);
  assert (trace_sum_at next26_source 9 +
      trace_sum_at next26_source (n - 9) +
      trace_carry_at next26_source 9 +
      trace_carry_at next26_source (n - 9) >=
    10 + 10 *
      (trace_carry_at next26_source (9 + 1) +
       trace_carry_at next26_source (n - 9 + 1)));
  exists_intro
    (fun (i:nat) -> 0 < i /\ i < n /\
      trace_sum_at next26_source i +
          trace_sum_at next26_source (n - i) +
          trace_carry_at next26_source i +
          trace_carry_at next26_source (n - i) >=
        10 + 10 *
          (trace_carry_at next26_source (i + 1) +
           trace_carry_at next26_source (n - i + 1)))
    9;
  ()

let local_profile_witness_1326313072829535757534829271313622 () : Lemma (
    trace_local_profile_complement_witness next26_target) =
  overflow_precondition_668656536414767878767414635656756 ();
  reverse_add_668656536414767878767414635656756_to_1326313072829535757534829271313622 ();
  overflow_internal_cell_implies_next_witness next26_source;
  ()
