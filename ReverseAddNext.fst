module ReverseAddNext

#set-options "--fuel 100 --ifuel 100 --retry 10"

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
