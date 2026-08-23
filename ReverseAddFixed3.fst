module ReverseAddFixed3

open ReverseAdd
open AbstractReachability
open ReverseAddFixedWidth
open FStar.ReflexiveTransitiveClosure

let fixed3_width : nat = 3
let fixed3_count : state_count = fixed_count fixed3_width
let fixed3_fallback : state fixed3_count = fixed_fallback fixed3_width

let fixed3_alpha (xs:numeral 10) : state fixed3_count =
  fixed_alpha fixed3_width xs

let fixed3_edge (x y:state fixed3_count) : Tot bool =
  fixed_edge fixed3_width x y

let fixed3_bad (s:state fixed3_count) : Tot bool =
  fixed_bad fixed3_width s

let fixed3_alpha_value (#a:digit 10) (#b:digit 10) (#c:digit 10)
  : Lemma (requires (c > 0))
    (ensures (fixed3_alpha [a; b; c] ==
      a + 10 * b + 100 * c)) =
  assert (canonical_flag [a; b; c] == true);
  assert (value [a; b; c] < power10 fixed3_width);
  fixed_alpha_exact fixed3_width [a; b; c];
  ()

let fixed3_alpha_exact (#a:digit 10) (#b:digit 10) (#c:digit 10)
  : Lemma (requires (c > 0))
    (ensures (fixed3_alpha [a; b; c] ==
      value [a; b; c])) =
  fixed3_alpha_value #a #b #c;
  ()

let fixed3_simulates_step (x y:numeral 10)
  : Lemma (requires (step #10 x y))
    (ensures (fixed3_edge (fixed3_alpha x) (fixed3_alpha y))) =
  fixed_simulates_step fixed3_width x y;
  ()

let fixed3_palindrome_sound (xs:numeral 10)
  : Lemma (requires (palindrome #10 xs))
    (ensures (fixed3_bad (fixed3_alpha xs))) =
  fixed_palindrome_sound fixed3_width xs;
  ()

let fixed3_unreachable_sound
  (x y:numeral 10)
  (states:list (state fixed3_count))
  : Lemma (requires (
      check_bad fixed3_edge fixed3_bad (fixed3_alpha x) ==
        Unreachable states /\
      closure (step #10) x y /\
      palindrome #10 y))
    (ensures False) =
  introduce forall (u v:numeral 10).
    step #10 u v ==> fixed3_edge (fixed3_alpha u) (fixed3_alpha v)
  with (
    introduce _ ==> _
    with (fixed3_simulates_step u v)
  );
  introduce forall (u:numeral 10).
    palindrome #10 u ==> fixed3_bad (fixed3_alpha u)
  with (
    introduce _ ==> _
    with (fixed3_palindrome_sound u)
  );
  check_bad_sound
    (step #10)
    fixed3_alpha
    fixed3_edge
    (palindrome #10)
    fixed3_bad
    x y states;
  ()
