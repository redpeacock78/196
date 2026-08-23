module ReverseAddRefinedProduct

open ReverseAdd
open ReverseAddBlockCarry
open ReverseAddFixed3
open AbstractReachability
open FStar.Math.Lemmas
open FStar.ReflexiveTransitiveClosure

// Product refinement: retain the block-carry state and add exact 3-digit
// information.  The block projection is therefore preserved by construction.
let refined_count (#m:state_count) : state_count =
  fixed3_count * block_count #m

let refined_alpha (#m:state_count) (xs:numeral 10)
  : state (refined_count #m) =
  fixed3_alpha xs * block_count #m + block_alpha #10 #m xs

let refined_fixed3 (#m:state_count)
  (s:state (refined_count #m)) : state fixed3_count =
  s / block_count #m

let refined_block (#m:state_count)
  (s:state (refined_count #m)) : state (block_count #m) =
  s % block_count #m

let refined_fixed3_alpha (#m:state_count) (xs:numeral 10)
  : Lemma (refined_fixed3 #m (refined_alpha #m xs) ==
      fixed3_alpha xs) =
  let f = fixed3_alpha xs in
  let b = block_alpha #10 #m xs in
  lemma_div_mod_plus b f (block_count #m);
  small_div b (block_count #m);
  assert (b + f * block_count #m ==
    f * block_count #m + b);
  ()

let refined_block_alpha (#m:state_count) (xs:numeral 10)
  : Lemma (refined_block #m (refined_alpha #m xs) ==
      block_alpha #10 #m xs) =
  let f = fixed3_alpha xs in
  let b = block_alpha #10 #m xs in
  modulo_addition_lemma b (block_count #m) f;
  small_mod b (block_count #m);
  assert (f * block_count #m + b ==
    b + f * block_count #m);
  ()

let refined_edge (#m:state_count)
  (x y:state (refined_count #m)) : Tot bool =
  fixed3_edge
    (refined_fixed3 #m x) (refined_fixed3 #m y) &&
  block_edge
    (refined_block #m x) (refined_block #m y)

let refined_bad (#m:state_count)
  (s:state (refined_count #m)) : Tot bool =
  fixed3_bad (refined_fixed3 #m s) &&
  block_bad #m (refined_block #m s)

let refined_edge_projects_block (#m:state_count)
  (x y:state (refined_count #m))
  : Lemma (requires (refined_edge #m x y))
    (ensures (block_edge #m
      (refined_block #m x) (refined_block #m y))) =
  ()

let refined_bad_projects_block (#m:state_count)
  (s:state (refined_count #m))
  : Lemma (requires (refined_bad #m s))
    (ensures (block_bad #m (refined_block #m s))) =
  ()

let refined_path_projects_block (#m:state_count)
  (x y:state (refined_count #m))
  : Lemma (requires (closure (edge_relation (refined_edge #m)) x y))
    (ensures (closure (edge_relation (block_edge #m))
      (refined_block #m x) (refined_block #m y))) =
  introduce forall (u v:state (refined_count #m)).
    edge_relation (refined_edge #m) u v ==>
      edge_relation (block_edge #m)
        (refined_block #m u) (refined_block #m v)
  with (
    introduce _ ==> _
    with (refined_edge_projects_block #m u v)
  );
  simulation_closure
    (edge_relation (refined_edge #m))
    (refined_block #m)
    (block_edge #m)
    x y;
  ()

let refined_simulates_step (x y:numeral 10)
  : Lemma (requires (step #10 x y))
    (ensures (refined_edge #2
      (refined_alpha #2 x) (refined_alpha #2 y))) =
  refined_fixed3_alpha #2 x;
  refined_fixed3_alpha #2 y;
  refined_block_alpha #2 x;
  refined_block_alpha #2 y;
  fixed3_simulates_step x y;
  block_simulates_step #10 #2 x y;
  ()

let refined_palindrome_sound (xs:numeral 10)
  : Lemma (requires (palindrome #10 xs))
    (ensures (refined_bad #2 (refined_alpha #2 xs))) =
  refined_fixed3_alpha #2 xs;
  refined_block_alpha #2 xs;
  fixed3_palindrome_sound xs;
  block_palindrome_sound #10 #2 xs;
  ()

let refined_unreachable_sound
  (x y:numeral 10)
  (states:list (state (refined_count #2)))
  : Lemma (requires (
      check_bad (refined_edge #2) (refined_bad #2)
          (refined_alpha #2 x) == Unreachable states /\
      closure (step #10) x y /\
      palindrome #10 y))
    (ensures False) =
  introduce forall (u v:numeral 10).
    step #10 u v ==> refined_edge #2
      (refined_alpha #2 u) (refined_alpha #2 v)
  with (
    introduce _ ==> _
    with (refined_simulates_step u v)
  );
  introduce forall (u:numeral 10).
    palindrome #10 u ==> refined_bad #2 (refined_alpha #2 u)
  with (
    introduce _ ==> _
    with (refined_palindrome_sound u)
  );
  check_bad_sound
    (step #10)
    (refined_alpha #2)
    (refined_edge #2)
    (palindrome #10)
    (refined_bad #2)
    x y states;
  ()
