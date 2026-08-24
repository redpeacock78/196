module ReverseAddTail

#set-options "--fuel 100 --ifuel 100 --retry 10"

open ReverseAdd
open ReverseAddCarry
open ReverseAddWitness
open ReverseAddOverflowProfile
open FStar.Classical
open FStar.List.Tot

let tail_source : numeral 10 =
  [8; 3; 5; 9; 6; 9; 3; 3; 9; 7; 6; 8; 3; 3; 9; 7; 0; 5; 3; 9]

let tail_reversed : numeral 10 =
  [9; 3; 5; 0; 7; 9; 3; 3; 8; 6; 7; 9; 3; 3; 9; 6; 9; 5; 3; 8]

let tail_target : numeral 10 =
  [7; 7; 0; 0; 4; 9; 7; 6; 7; 4; 4; 8; 7; 6; 8; 4; 0; 1; 7; 7; 1]

let reverse_list_tail_source () : Lemma (rev tail_source == tail_reversed) =
  assert (rev [9] == [9]);
  rev_cons 3 [9];
  rev_cons 5 [3; 9];
  rev_cons 0 [5; 3; 9];
  rev_cons 7 [0; 5; 3; 9];
  rev_cons 9 [7; 0; 5; 3; 9];
  rev_cons 3 [9; 7; 0; 5; 3; 9];
  rev_cons 3 [3; 9; 7; 0; 5; 3; 9];
  rev_cons 8 [3; 3; 9; 7; 0; 5; 3; 9];
  rev_cons 6 [8; 3; 3; 9; 7; 0; 5; 3; 9];
  rev_cons 7 [6; 8; 3; 3; 9; 7; 0; 5; 3; 9];
  rev_cons 9 [7; 6; 8; 3; 3; 9; 7; 0; 5; 3; 9];
  rev_cons 3 [9; 7; 6; 8; 3; 3; 9; 7; 0; 5; 3; 9];
  rev_cons 3 [3; 9; 7; 6; 8; 3; 3; 9; 7; 0; 5; 3; 9];
  rev_cons 9 [3; 3; 9; 7; 6; 8; 3; 3; 9; 7; 0; 5; 3; 9];
  rev_cons 6 [9; 3; 3; 9; 7; 6; 8; 3; 3; 9; 7; 0; 5; 3; 9];
  rev_cons 9 [6; 9; 3; 3; 9; 7; 6; 8; 3; 3; 9; 7; 0; 5; 3; 9];
  rev_cons 5 [9; 6; 9; 3; 3; 9; 7; 6; 8; 3; 3; 9; 7; 0; 5; 3; 9];
  rev_cons 3 [5; 9; 6; 9; 3; 3; 9; 7; 6; 8; 3; 3; 9; 7; 0; 5; 3; 9];
  rev_cons 8 [3; 5; 9; 6; 9; 3; 3; 9; 7; 6; 8; 3; 3; 9; 7; 0; 5; 3; 9];
  ()

let value_tail_source () : Lemma (value tail_source == 93507933867933969538) =
  value_cons #10 8 [3; 5; 9; 6; 9; 3; 3; 9; 7; 6; 8; 3; 3; 9; 7; 0; 5; 3; 9];
  value_cons #10 3 [5; 9; 6; 9; 3; 3; 9; 7; 6; 8; 3; 3; 9; 7; 0; 5; 3; 9];
  value_cons #10 5 [9; 6; 9; 3; 3; 9; 7; 6; 8; 3; 3; 9; 7; 0; 5; 3; 9];
  value_cons #10 9 [6; 9; 3; 3; 9; 7; 6; 8; 3; 3; 9; 7; 0; 5; 3; 9];
  value_cons #10 6 [9; 3; 3; 9; 7; 6; 8; 3; 3; 9; 7; 0; 5; 3; 9];
  value_cons #10 9 [3; 3; 9; 7; 6; 8; 3; 3; 9; 7; 0; 5; 3; 9];
  value_cons #10 3 [3; 9; 7; 6; 8; 3; 3; 9; 7; 0; 5; 3; 9];
  value_cons #10 3 [9; 7; 6; 8; 3; 3; 9; 7; 0; 5; 3; 9];
  value_cons #10 9 [7; 6; 8; 3; 3; 9; 7; 0; 5; 3; 9];
  value_cons #10 7 [6; 8; 3; 3; 9; 7; 0; 5; 3; 9];
  value_cons #10 6 [8; 3; 3; 9; 7; 0; 5; 3; 9];
  value_cons #10 8 [3; 3; 9; 7; 0; 5; 3; 9];
  value_cons #10 3 [3; 9; 7; 0; 5; 3; 9];
  value_cons #10 3 [9; 7; 0; 5; 3; 9];
  value_cons #10 9 [7; 0; 5; 3; 9];
  value_cons #10 7 [0; 5; 3; 9];
  value_cons #10 0 [5; 3; 9];
  value_cons #10 5 [3; 9];
  value_cons #10 3 [9];
  value_cons #10 9 [];
  ()

let value_tail_reversed () : Lemma (value tail_reversed == 83596933976833970539) =
  value_cons #10 9 [3; 5; 0; 7; 9; 3; 3; 8; 6; 7; 9; 3; 3; 9; 6; 9; 5; 3; 8];
  value_cons #10 3 [5; 0; 7; 9; 3; 3; 8; 6; 7; 9; 3; 3; 9; 6; 9; 5; 3; 8];
  value_cons #10 5 [0; 7; 9; 3; 3; 8; 6; 7; 9; 3; 3; 9; 6; 9; 5; 3; 8];
  value_cons #10 0 [7; 9; 3; 3; 8; 6; 7; 9; 3; 3; 9; 6; 9; 5; 3; 8];
  value_cons #10 7 [9; 3; 3; 8; 6; 7; 9; 3; 3; 9; 6; 9; 5; 3; 8];
  value_cons #10 9 [3; 3; 8; 6; 7; 9; 3; 3; 9; 6; 9; 5; 3; 8];
  value_cons #10 3 [3; 8; 6; 7; 9; 3; 3; 9; 6; 9; 5; 3; 8];
  value_cons #10 3 [8; 6; 7; 9; 3; 3; 9; 6; 9; 5; 3; 8];
  value_cons #10 8 [6; 7; 9; 3; 3; 9; 6; 9; 5; 3; 8];
  value_cons #10 6 [7; 9; 3; 3; 9; 6; 9; 5; 3; 8];
  value_cons #10 7 [9; 3; 3; 9; 6; 9; 5; 3; 8];
  value_cons #10 9 [3; 3; 9; 6; 9; 5; 3; 8];
  value_cons #10 3 [3; 9; 6; 9; 5; 3; 8];
  value_cons #10 3 [9; 6; 9; 5; 3; 8];
  value_cons #10 9 [6; 9; 5; 3; 8];
  value_cons #10 6 [9; 5; 3; 8];
  value_cons #10 9 [5; 3; 8];
  value_cons #10 5 [3; 8];
  value_cons #10 3 [8];
  value_cons #10 8 [];
  ()

let value_tail_target () : Lemma (value tail_target == 177104867844767940077) =
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

let canonical_tail_source () : Lemma (canonical #10 tail_source /\ tail_source <> []) =
  assert (canonical #10 [9]);
  canonical_cons #10 3 [9];
  canonical_cons #10 5 [3; 9];
  canonical_cons #10 0 [5; 3; 9];
  canonical_cons #10 7 [0; 5; 3; 9];
  canonical_cons #10 9 [7; 0; 5; 3; 9];
  canonical_cons #10 3 [9; 7; 0; 5; 3; 9];
  canonical_cons #10 3 [3; 9; 7; 0; 5; 3; 9];
  canonical_cons #10 8 [3; 3; 9; 7; 0; 5; 3; 9];
  canonical_cons #10 6 [8; 3; 3; 9; 7; 0; 5; 3; 9];
  canonical_cons #10 7 [6; 8; 3; 3; 9; 7; 0; 5; 3; 9];
  canonical_cons #10 9 [7; 6; 8; 3; 3; 9; 7; 0; 5; 3; 9];
  canonical_cons #10 3 [9; 7; 6; 8; 3; 3; 9; 7; 0; 5; 3; 9];
  canonical_cons #10 3 [3; 9; 7; 6; 8; 3; 3; 9; 7; 0; 5; 3; 9];
  canonical_cons #10 9 [3; 3; 9; 7; 6; 8; 3; 3; 9; 7; 0; 5; 3; 9];
  canonical_cons #10 6 [9; 3; 3; 9; 7; 6; 8; 3; 3; 9; 7; 0; 5; 3; 9];
  canonical_cons #10 9 [6; 9; 3; 3; 9; 7; 6; 8; 3; 3; 9; 7; 0; 5; 3; 9];
  canonical_cons #10 5 [9; 6; 9; 3; 3; 9; 7; 6; 8; 3; 3; 9; 7; 0; 5; 3; 9];
  canonical_cons #10 3 [5; 9; 6; 9; 3; 3; 9; 7; 6; 8; 3; 3; 9; 7; 0; 5; 3; 9];
  canonical_cons #10 8 [3; 5; 9; 6; 9; 3; 3; 9; 7; 6; 8; 3; 3; 9; 7; 0; 5; 3; 9];
  ()

let canonical_tail_reversed () : Lemma (canonical #10 tail_reversed) =
  assert (canonical #10 [8]);
  canonical_cons #10 3 [8];
  canonical_cons #10 5 [3; 8];
  canonical_cons #10 9 [5; 3; 8];
  canonical_cons #10 6 [9; 5; 3; 8];
  canonical_cons #10 9 [6; 9; 5; 3; 8];
  canonical_cons #10 3 [9; 6; 9; 5; 3; 8];
  canonical_cons #10 3 [3; 9; 6; 9; 5; 3; 8];
  canonical_cons #10 9 [3; 3; 9; 6; 9; 5; 3; 8];
  canonical_cons #10 7 [9; 3; 3; 9; 6; 9; 5; 3; 8];
  canonical_cons #10 6 [7; 9; 3; 3; 9; 6; 9; 5; 3; 8];
  canonical_cons #10 8 [6; 7; 9; 3; 3; 9; 6; 9; 5; 3; 8];
  canonical_cons #10 3 [8; 6; 7; 9; 3; 3; 9; 6; 9; 5; 3; 8];
  canonical_cons #10 3 [3; 8; 6; 7; 9; 3; 3; 9; 6; 9; 5; 3; 8];
  canonical_cons #10 9 [3; 3; 8; 6; 7; 9; 3; 3; 9; 6; 9; 5; 3; 8];
  canonical_cons #10 7 [9; 3; 3; 8; 6; 7; 9; 3; 3; 9; 6; 9; 5; 3; 8];
  canonical_cons #10 0 [7; 9; 3; 3; 8; 6; 7; 9; 3; 3; 9; 6; 9; 5; 3; 8];
  canonical_cons #10 5 [0; 7; 9; 3; 3; 8; 6; 7; 9; 3; 3; 9; 6; 9; 5; 3; 8];
  canonical_cons #10 3 [5; 0; 7; 9; 3; 3; 8; 6; 7; 9; 3; 3; 9; 6; 9; 5; 3; 8];
  canonical_cons #10 9 [3; 5; 0; 7; 9; 3; 3; 8; 6; 7; 9; 3; 3; 9; 6; 9; 5; 3; 8];
  ()

let canonical_tail_target () : Lemma (canonical #10 tail_target) =
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

let reverse_digits_tail_source () : Lemma (reverse_digits #10 tail_source == tail_reversed) =
  canonical_tail_source ();
  reverse_list_tail_source ();
  value_tail_reversed ();
  canonical_tail_reversed ();
  reverse_digits_canonical #10 tail_source;
  normalize_value #10 (rev tail_source);
  assert (value (reverse_digits #10 tail_source) == 83596933976833970539);
  digits_of_nat_of_canonical #10 (reverse_digits #10 tail_source);
  digits_of_nat_of_canonical #10 tail_reversed;
  assert (reverse_digits #10 tail_source == tail_reversed);
  ()

let reverse_add_tail_source () : Lemma (reverse_add #10 tail_source == tail_target) =
  canonical_tail_source ();
  reverse_add_value #10 tail_source;
  value_tail_source ();
  reverse_digits_tail_source ();
  value_tail_reversed ();
  value_tail_target ();
  assert (value (reverse_add #10 tail_source) == 177104867844767940077);
  reverse_add_canonical #10 tail_source;
  digits_of_nat_of_canonical #10 (reverse_add #10 tail_source);
  canonical_tail_target ();
  digits_of_nat_of_canonical #10 tail_target;
  assert (reverse_add #10 tail_source == tail_target);
  ()

let reverse_add_93507933867933969538_to_177104867844767940077 () : Lemma (
    reverse_add #10 tail_source == tail_target) =
  reverse_add_tail_source ();
  ()

let trace_digits_profile_93507933867933969538 () : Lemma (
    trace_digits tail_source == tail_target) =
  reverse_add_tail_source ();
  trace_digits_equals_reverse_add tail_source;
  assert (trace_digits tail_source == reverse_add #10 tail_source);
  assert (reverse_add #10 tail_source == tail_target);
  assert (trace_digits tail_source == tail_target);
  ()

let trace_carries_tail_source () : Lemma (trace_carries tail_source ==
    [0; 1; 0; 1; 1; 1; 1; 0; 0; 1; 1; 1; 1; 0; 0; 1; 1; 1; 1; 0; 1]) =
  reverse_list_tail_source ();
  assert (trace_carries tail_source == (add_trace #10 tail_source tail_reversed 0).carries);
  add_trace_carries_step #10 8 9
    [3; 5; 9; 6; 9; 3; 3; 9; 7; 6; 8; 3; 3; 9; 7; 0; 5; 3; 9]
    [3; 5; 0; 7; 9; 3; 3; 8; 6; 7; 9; 3; 3; 9; 6; 9; 5; 3; 8] 0;
  add_trace_carries_step #10 3 3
    [5; 9; 6; 9; 3; 3; 9; 7; 6; 8; 3; 3; 9; 7; 0; 5; 3; 9]
    [5; 0; 7; 9; 3; 3; 8; 6; 7; 9; 3; 3; 9; 6; 9; 5; 3; 8] 1;
  add_trace_carries_step #10 5 5
    [9; 6; 9; 3; 3; 9; 7; 6; 8; 3; 3; 9; 7; 0; 5; 3; 9]
    [0; 7; 9; 3; 3; 8; 6; 7; 9; 3; 3; 9; 6; 9; 5; 3; 8] 0;
  add_trace_carries_step #10 9 0
    [6; 9; 3; 3; 9; 7; 6; 8; 3; 3; 9; 7; 0; 5; 3; 9]
    [7; 9; 3; 3; 8; 6; 7; 9; 3; 3; 9; 6; 9; 5; 3; 8] 1;
  add_trace_carries_step #10 6 7
    [9; 3; 3; 9; 7; 6; 8; 3; 3; 9; 7; 0; 5; 3; 9]
    [9; 3; 3; 8; 6; 7; 9; 3; 3; 9; 6; 9; 5; 3; 8] 1;
  add_trace_carries_step #10 9 9
    [3; 3; 9; 7; 6; 8; 3; 3; 9; 7; 0; 5; 3; 9]
    [3; 3; 8; 6; 7; 9; 3; 3; 9; 6; 9; 5; 3; 8] 1;
  add_trace_carries_step #10 3 3
    [3; 9; 7; 6; 8; 3; 3; 9; 7; 0; 5; 3; 9]
    [3; 8; 6; 7; 9; 3; 3; 9; 6; 9; 5; 3; 8] 1;
  add_trace_carries_step #10 3 3
    [9; 7; 6; 8; 3; 3; 9; 7; 0; 5; 3; 9]
    [8; 6; 7; 9; 3; 3; 9; 6; 9; 5; 3; 8] 0;
  add_trace_carries_step #10 9 8
    [7; 6; 8; 3; 3; 9; 7; 0; 5; 3; 9]
    [6; 7; 9; 3; 3; 9; 6; 9; 5; 3; 8] 0;
  add_trace_carries_step #10 7 6
    [6; 8; 3; 3; 9; 7; 0; 5; 3; 9]
    [7; 9; 3; 3; 9; 6; 9; 5; 3; 8] 1;
  add_trace_carries_step #10 6 7
    [8; 3; 3; 9; 7; 0; 5; 3; 9]
    [9; 3; 3; 9; 6; 9; 5; 3; 8] 1;
  add_trace_carries_step #10 8 9
    [3; 3; 9; 7; 0; 5; 3; 9]
    [3; 3; 9; 6; 9; 5; 3; 8] 1;
  add_trace_carries_step #10 3 3
    [3; 9; 7; 0; 5; 3; 9]
    [3; 9; 6; 9; 5; 3; 8] 1;
  add_trace_carries_step #10 3 3
    [9; 7; 0; 5; 3; 9]
    [9; 6; 9; 5; 3; 8] 0;
  add_trace_carries_step #10 9 9 [7; 0; 5; 3; 9] [6; 9; 5; 3; 8] 0;
  add_trace_carries_step #10 7 6 [0; 5; 3; 9] [9; 5; 3; 8] 1;
  add_trace_carries_step #10 0 9 [5; 3; 9] [5; 3; 8] 1;
  add_trace_carries_step #10 5 5 [3; 9] [3; 8] 1;
  add_trace_carries_step #10 3 3 [9] [8] 1;
  add_trace_carries_step #10 9 8 [] [] 0;
  assert ((add_trace #10 tail_source tail_reversed 0).carries ==
    [0; 1; 0; 1; 1; 1; 1; 0; 0; 1; 1; 1; 1; 0; 0; 1; 1; 1; 1; 0; 1]);
  ()

let trace_profile_shape_93507933867933969538 () : Lemma (
    length (trace_digits tail_source) == length tail_source + 1) =
  trace_digits_profile_93507933867933969538 ();
  length_of_eq #(digit 10) (trace_digits tail_source) tail_target;
  assert (length tail_target == length tail_source + 1);
  ()

let trace_profile_final_carry_93507933867933969538 () : Lemma (
    nth (trace_carries tail_source) (length tail_source) == Some 1) =
  trace_carries_tail_source ();
  ()

let trace_profile_sums_93507933867933969538 () : Lemma (
    trace_sum_at tail_source 0 == 17 /\
    trace_sum_at tail_source 1 == 6 /\
    trace_sum_at tail_source 19 == 17) =
  reverse_list_tail_source ();
  ()

let trace_profile_facts_93507933867933969538 () : Lemma (
    trace_digits tail_source == tail_target /\
    trace_carries tail_source ==
      [0; 1; 0; 1; 1; 1; 1; 0; 0; 1; 1; 1; 1; 0; 0; 1; 1; 1; 1; 0; 1] /\
    length (trace_digits tail_source) == length tail_source + 1 /\
    nth (trace_carries tail_source) (length tail_source) == Some 1 /\
    trace_sum_at tail_source 0 == 17 /\
    trace_sum_at tail_source 1 == 6 /\
    trace_sum_at tail_source 19 == 17) =
  trace_digits_profile_93507933867933969538 ();
  trace_carries_tail_source ();
  trace_profile_shape_93507933867933969538 ();
  trace_profile_final_carry_93507933867933969538 ();
  trace_profile_sums_93507933867933969538 ();
  ()

let overflow_precondition_177104867844767940077 () : Lemma (
    canonical #10 tail_source /\
    tail_source <> [] /\
    length (trace_digits tail_source) == length tail_source + 1 /\
    nth (trace_carries tail_source) (length tail_source) == Some 1 /\
    1 <= trace_sum_at tail_source 0 /\
    trace_sum_at tail_source 0 <= 18 /\
    trace_sum_at tail_source 0 <> 10 /\
    exists (i:nat). 0 < i /\ i < length tail_source /\
      trace_sum_at tail_source i +
          trace_sum_at tail_source (length tail_source - i) +
          trace_carry_at tail_source i +
          trace_carry_at tail_source (length tail_source - i) >=
        10 + 10 *
          (trace_carry_at tail_source (i + 1) +
           trace_carry_at tail_source (length tail_source - i + 1))) =
  trace_profile_facts_93507933867933969538 ();
  assert (canonical #10 tail_source);
  assert (tail_source <> []);
  assert (length (trace_digits tail_source) == length tail_source + 1);
  assert (nth (trace_carries tail_source) (length tail_source) == Some 1);
  assert (trace_sum_at tail_source 0 == 17);
  assert (trace_sum_at tail_source 1 == 6);
  assert (trace_sum_at tail_source 19 == 17);
  assert (trace_carry_at tail_source 1 == 1);
  assert (trace_carry_at tail_source 19 == 0);
  assert (trace_carry_at tail_source 2 == 0);
  assert (trace_carry_at tail_source 20 == 1);
  assert (1 <= trace_sum_at tail_source 0 /\
    trace_sum_at tail_source 0 <= 18);
  assert (trace_sum_at tail_source 0 <> 10);
  let n : nat = length tail_source in
  exists_intro
    (fun (i:nat) -> 0 < i /\ i < n /\
      trace_sum_at tail_source i + trace_sum_at tail_source (n - i) +
          trace_carry_at tail_source i + trace_carry_at tail_source (n - i) >=
        10 + 10 *
          (trace_carry_at tail_source (i + 1) +
           trace_carry_at tail_source (n - i + 1)))
    1;
  ()

let local_profile_witness_177104867844767940077 () : Lemma (
    trace_local_profile_complement_witness tail_target) =
  overflow_precondition_177104867844767940077 ();
  reverse_add_tail_source ();
  overflow_internal_cell_implies_next_witness tail_source;
  ()
