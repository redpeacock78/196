module ReverseAddBoundary

#set-options "--fuel 10 --ifuel 10 --retry 10"

open ReverseAdd
open ReverseAddCarry
open ReverseAddWitness
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
