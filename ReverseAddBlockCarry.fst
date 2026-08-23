module ReverseAddBlockCarry

open ReverseAdd
open AbstractReachability
open ReverseAddModPair
open FStar.List.Tot
open FStar.Math.Lemmas
open FStar.ReflexiveTransitiveClosure

// A finite state stores two residues and the carry of their m-sized block sum.
let block_count (#m:state_count) : state_count =
  m * m * 2

let block_carry_of_residues (#m:state_count)
  (n:nat{n < m}) (r:nat{r < m}) : carry =
  if n + r < m then 0 else 1

let block_alpha (#b:base) (#m:state_count)
  (xs:numeral b) : state (block_count #m) =
  let n = value xs % m in
  let r = value (reverse_digits #b xs) % m in
  let c = if n + r < m then 0 else 1 in
  assert (n < m);
  assert (r < m);
  assert ((n * m + r) * 2 + c < m * m * 2);
  (n * m + r) * 2 + c

let block_pair_index (#m:state_count)
  (s:state (block_count #m)) : nat =
  s / 2

let block_left (#m:state_count)
  (s:state (block_count #m)) : nat =
  block_pair_index #m s / m

let block_right (#m:state_count)
  (s:state (block_count #m)) : nat =
  block_pair_index #m s % m

let block_carry (#m:state_count)
  (s:state (block_count #m)) : nat =
  s % 2

let block_valid (#m:state_count)
  (s:state (block_count #m)) : Tot bool =
  block_carry #m s =
    (if block_left #m s + block_right #m s < m then 0 else 1)

let block_edge (#m:state_count)
  (x y:state (block_count #m)) : Tot bool =
  block_valid #m x &&
  (block_left #m y =
    (block_left #m x + block_right #m x) % m) &&
  block_valid #m y

let block_bad (#m:state_count)
  (s:state (block_count #m)) : Tot bool =
  block_left #m s = block_right #m s

let block_pair_index_alpha (#b:base) (#m:state_count)
  (xs:numeral b)
  : Lemma (block_pair_index #m (block_alpha #b #m xs) ==
      (value xs % m) * m +
        value (reverse_digits #b xs) % m) =
  let n = value xs % m in
  let r = value (reverse_digits #b xs) % m in
  let c = if n + r < m then 0 else 1 in
  lemma_div_mod_plus c (n * m + r) 2;
  small_div c 2;
  assert (c + (n * m + r) * 2 ==
    (n * m + r) * 2 + c);
  ()

let block_alpha_left (#b:base) (#m:state_count)
  (xs:numeral b)
  : Lemma (block_left #m (block_alpha #b #m xs) == value xs % m) =
  block_pair_index_alpha #b #m xs;
  let n = value xs % m in
  let r = value (reverse_digits #b xs) % m in
  small_div r m;
  lemma_div_mod_plus r n m;
  assert (n * m + r == r + n * m);
  ()

let block_alpha_right (#b:base) (#m:state_count)
  (xs:numeral b)
  : Lemma (block_right #m (block_alpha #b #m xs) ==
      value (reverse_digits #b xs) % m) =
  block_pair_index_alpha #b #m xs;
  let n = value xs % m in
  let r = value (reverse_digits #b xs) % m in
  modulo_addition_lemma r m n;
  small_mod r m;
  assert (n * m + r == r + n * m);
  ()

let block_alpha_carry (#b:base) (#m:state_count)
  (xs:numeral b)
  : Lemma (block_carry #m (block_alpha #b #m xs) ==
      (if value xs % m + value (reverse_digits #b xs) % m < m
       then 0 else 1)) =
  let n = value xs % m in
  let r = value (reverse_digits #b xs) % m in
  let c = if n + r < m then 0 else 1 in
  modulo_addition_lemma c 2 (n * m + r);
  small_mod c 2;
  assert (c + (n * m + r) * 2 ==
    (n * m + r) * 2 + c);
  ()

let block_valid_alpha (#b:base) (#m:state_count)
  (xs:numeral b)
  : Lemma (block_valid #m (block_alpha #b #m xs)) =
  block_alpha_left #b #m xs;
  block_alpha_right #b #m xs;
  block_alpha_carry #b #m xs;
  ()

let block_simulates_step (#b:base) (#m:state_count)
  (x y:numeral b)
  : Lemma (requires (step x y))
    (ensures (block_edge #m
      (block_alpha #b #m x)
      (block_alpha #b #m y))) =
  block_valid_alpha #b #m x;
  block_valid_alpha #b #m y;
  block_alpha_left #b #m x;
  block_alpha_right #b #m x;
  block_alpha_left #b #m y;
  reverse_add_mod #b #m x y;
  ()

let block_palindrome_sound (#b:base) (#m:state_count)
  (xs:numeral b)
  : Lemma (requires (palindrome xs))
    (ensures (block_bad #m (block_alpha #b #m xs))) =
  normalize_value (rev xs);
  assert (value xs == value (rev xs));
  block_alpha_left #b #m xs;
  block_alpha_right #b #m xs;
  ()

let block_unreachable_sound (#b:base) (#m:state_count)
  (x y:numeral b)
  (states:list (state (block_count #m)))
  : Lemma (requires (
      check_bad (block_edge #m) (block_bad #m) (block_alpha #b #m x) ==
        Unreachable states /\
      closure (step #b) x y /\
      palindrome y))
    (ensures False) =
  introduce forall (u v:numeral b).
    step u v ==> block_edge #m
      (block_alpha #b #m u) (block_alpha #b #m v)
  with (
    introduce _ ==> _
    with (block_simulates_step #b #m u v)
  );
  introduce forall (u:numeral b).
    palindrome u ==> block_bad #m (block_alpha #b #m u)
  with (
    introduce _ ==> _
    with (block_palindrome_sound #b #m u)
  );
  check_bad_sound
    (step #b)
    (block_alpha #b #m)
    (block_edge #m)
    (palindrome #b)
    (block_bad #m)
    x y states;
  ()
