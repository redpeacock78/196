module ReverseAdd196

open ReverseAdd
open AbstractReachability
open ReverseAddBlockCarry
open ReverseAddFixed3
open ReverseAddRefinedProduct
open FStar.ReflexiveTransitiveClosure

let block_initial_196 : state (block_count #2) =
  block_alpha #10 #2 digits_196

let block_actual_887 : state (block_count #2) =
  block_alpha #10 #2 digits_887

// The coarse block abstraction can choose a bad successor that is not the
// concrete successor; this is the first CEGAR counterexample to refine.
let block_spurious_bad : state (block_count #2) = 7

let block_196_counterexample () : Lemma (
    block_initial_196 == 2 /\
    block_actual_887 == 4 /\
    block_bad #2 block_spurious_bad /\
    block_edge #2 block_initial_196 block_spurious_bad /\
    ~ (block_bad #2 block_actual_887)) =
  example_196 ();
  ()

let block_196_abstract_path () : Lemma (
    closure (edge_relation (block_edge #2))
      block_initial_196 block_spurious_bad /\
    block_bad #2 block_spurious_bad) =
  block_196_counterexample ();
  FStar.ReflexiveTransitiveClosure.closure_step
    (edge_relation (block_edge #2))
    block_initial_196 block_spurious_bad;
  ()

let fixed3_196_alpha () : Lemma (
    fixed3_alpha digits_196 == 196) =
  assert (fixed3_alpha digits_196 == 196);
  ()

let fixed3_196_next_alpha () : Lemma (
    fixed3_alpha (reverse_add #10 (digits_of_nat #10 196)) == 887) =
  assert (digits_of_nat #10 196 == digits_196);
  example_196 ();
  assert (reverse_add #10 (digits_of_nat #10 196) == digits_887);
  assert (fixed3_alpha digits_887 == 887);
  ()

let fixed3_887 : state fixed3_count = 887

let fixed3_887_not_bad () : Lemma (
    ~ (fixed3_bad fixed3_887)) =
  ()

let fixed3_196_no_bad_one_step (s:state fixed3_count)
  : Lemma (requires (fixed3_edge (fixed3_alpha digits_196) s))
    (ensures (~ (fixed3_bad s))) =
  fixed3_196_alpha ();
  fixed3_196_next_alpha ();
  assert (s == 887);
  fixed3_887_not_bad ();
  ()

let block_196_verdict : verdict (block_count #2) =
  check_bad (block_edge #2) (block_bad #2) block_initial_196

let block_196_one_step_verdict : verdict (block_count #2) =
  check_bad_fuel (block_edge #2) (block_bad #2) 0 block_initial_196

let fixed3_196_verdict () : verdict fixed3_count =
  check_bad fixed3_edge fixed3_bad (fixed3_alpha digits_196)

let fixed3_196_one_step_verdict : verdict fixed3_count =
  check_bad_fuel fixed3_edge fixed3_bad 0 (fixed3_alpha digits_196)

let refined_initial_196 : state (refined_count #2) =
  refined_alpha #2 digits_196

let refined_actual_887 : state (refined_count #2) =
  refined_alpha #2 digits_887

let refined_196_no_bad_one_step (s:state (refined_count #2))
  : Lemma (requires (refined_edge #2 refined_initial_196 s))
    (ensures (~ (refined_bad #2 s))) =
  refined_fixed3_alpha #2 digits_196;
  assert (refined_fixed3 #2 refined_initial_196 ==
    fixed3_alpha digits_196);
  assert (fixed3_edge
    (refined_fixed3 #2 refined_initial_196)
    (refined_fixed3 #2 s));
  fixed3_196_no_bad_one_step (refined_fixed3 #2 s);
  ()

let refined_196_actual_not_bad () : Lemma (
    ~ (refined_bad #2 refined_actual_887)) =
  example_196 ();
  refined_simulates_step digits_196 digits_887;
  refined_196_no_bad_one_step refined_actual_887;
  ()

let refined_196_verdict () : verdict (refined_count #2) =
  check_bad (refined_edge #2) (refined_bad #2) refined_initial_196

let refined_196_one_step_verdict : verdict (refined_count #2) =
  check_bad_fuel (refined_edge #2) (refined_bad #2) 0 refined_initial_196
