module ReverseAddNext

#set-options "--fuel 100 --ifuel 100 --retry 10"

open ReverseAdd
open ReverseAddCarry
open ReverseAddWitness
open ReverseAddOverflowProfile
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
