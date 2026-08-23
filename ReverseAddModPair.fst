module ReverseAddModPair

open ReverseAdd
open AbstractReachability
open ReverseAddResidue
open FStar.List.Tot
open FStar.Math.Lemmas
open FStar.ReflexiveTransitiveClosure

let pair_count (#m:state_count) : state_count =
  m * m

let pair_alpha (#b:base) (#m:state_count)
  (xs:numeral b) : state (pair_count #m) =
  let n = value xs % m in
  let r = value (reverse_digits #b xs) % m in
  n * m + r

let pair_left (#m:state_count)
  (s:state (pair_count #m)) : nat =
  s / m

let pair_right (#m:state_count)
  (s:state (pair_count #m)) : nat =
  s % m

let pair_edge (#m:state_count)
  (x y:state (pair_count #m)) : Tot bool =
  pair_left #m y =
    (pair_left #m x + pair_right #m x) % m

let pair_bad (#m:state_count)
  (s:state (pair_count #m)) : Tot bool =
  pair_left #m s = pair_right #m s

// The pair domain refines the one-coordinate residue domain.
let pair_project (#m:state_count)
  (s:state (pair_count #m)) : state m =
  pair_left #m s

let pair_edge_refines_residue (#m:state_count)
  (x y:state (pair_count #m))
  : Lemma (requires (pair_edge #m x y))
    (ensures (residue_edge #m
      (pair_project #m x) (pair_project #m y))) =
  ()

let pair_bad_refines_residue (#m:state_count)
  (s:state (pair_count #m))
  : Lemma (requires (pair_bad #m s))
    (ensures (residue_bad #m (pair_project #m s))) =
  ()

let pair_path_projects (#m:state_count)
  (x y:state (pair_count #m))
  : Lemma (requires (closure (edge_relation (pair_edge #m)) x y))
    (ensures (closure (edge_relation (residue_edge #m))
      (pair_project #m x) (pair_project #m y))) =
  introduce forall (u v:state (pair_count #m)).
    edge_relation (pair_edge #m) u v ==>
      edge_relation (residue_edge #m)
        (pair_project #m u) (pair_project #m v)
  with (
    introduce _ ==> _
    with (pair_edge_refines_residue #m u v)
  );
  simulation_closure
    (edge_relation (pair_edge #m))
    (pair_project #m)
    (residue_edge #m)
    x y;
  ()

let pair_alpha_left (#b:base) (#m:state_count)
  (xs:numeral b)
  : Lemma (pair_left #m (pair_alpha #b #m xs) == value xs % m) =
  ()

let pair_project_alpha (#b:base) (#m:state_count)
  (xs:numeral b)
  : Lemma (pair_project #m (pair_alpha #b #m xs) ==
      residue_alpha #b #m xs) =
  pair_alpha_left #b #m xs;
  ()

let pair_alpha_right (#b:base) (#m:state_count)
  (xs:numeral b)
  : Lemma (pair_right #m (pair_alpha #b #m xs) ==
      value (reverse_digits #b xs) % m) =
  let n = value xs % m in
  let r = value (reverse_digits #b xs) % m in
  modulo_addition_lemma r m n;
  small_mod r m;
  assert (n * m + r == r + n * m);
  ()

let reverse_add_mod (#b:base) (#m:state_count)
  (x y:numeral b)
  : Lemma (requires (step x y))
    (ensures (value y % m ==
      (value x % m + value (reverse_digits #b x) % m) % m)) =
  reverse_add_value #b x;
  assert (value y == value (reverse_add #b x));
  modulo_distributivity (value x) (value (reverse_digits #b x)) m;
  ()

let pair_simulates_step (#b:base) (#m:state_count)
  (x y:numeral b)
  : Lemma (requires (step x y))
    (ensures (pair_edge #m
      (pair_alpha #b #m x)
      (pair_alpha #b #m y))) =
  pair_alpha_left #b #m x;
  pair_alpha_right #b #m x;
  pair_alpha_left #b #m y;
  reverse_add_mod #b #m x y;
  ()

let pair_palindrome_sound (#b:base) (#m:state_count)
  (xs:numeral b)
  : Lemma (requires (palindrome xs))
    (ensures (pair_bad #m (pair_alpha #b #m xs))) =
  normalize_value (rev xs);
  assert (value xs == value (rev xs));
  pair_alpha_left #b #m xs;
  pair_alpha_right #b #m xs;
  ()

let pair_unreachable_sound (#b:base) (#m:state_count)
  (x y:numeral b)
  (states:list (state (pair_count #m)))
  : Lemma (requires (
      check_bad (pair_edge #m) (pair_bad #m) (pair_alpha #b #m x) ==
        Unreachable states /\
      closure (step #b) x y /\
      palindrome y))
    (ensures False) =
  introduce forall (u v:numeral b).
    step u v ==> pair_edge #m
      (pair_alpha #b #m u) (pair_alpha #b #m v)
  with (
    introduce _ ==> _
    with (pair_simulates_step #b #m u v)
  );
  introduce forall (u:numeral b).
    palindrome u ==> pair_bad #m (pair_alpha #b #m u)
  with (
    introduce _ ==> _
    with (pair_palindrome_sound #b #m u)
  );
  check_bad_sound
    (step #b)
    (pair_alpha #b #m)
    (pair_edge #m)
    (palindrome #b)
    (pair_bad #m)
    x y states;
  ()
