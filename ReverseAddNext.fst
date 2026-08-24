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
