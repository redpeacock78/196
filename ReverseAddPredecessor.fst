module ReverseAddPredecessor

open ReverseAdd
open FStar.List.Tot
open FStar.List.Tot.Properties

let rec nat_range (n:nat) : Tot (list nat)
  (decreases n) =
  if n = 0 then [0]
  else n :: nat_range (n - 1)

let rec nat_range_mem (bound:nat) (n:nat)
  : Lemma (requires (n <= bound))
    (ensures (memP n (nat_range bound)))
    (decreases bound) =
  if bound = 0 then ()
  else if n = bound then ()
  else nat_range_mem (bound - 1) n

let is_predecessor (#b:base) (y:numeral b) (n:nat) : Tot bool =
  if reverse_add #b (digits_of_nat #b n) = y then true else false

let predecessors_bounded (#b:base) (y:numeral b) : Tot (list nat) =
  filter (is_predecessor #b y) (nat_range (value y))

let is_predecessor_iff (#b:base) (y:numeral b) (n:nat)
  : Lemma (is_predecessor #b y n = true <==>
      step #b (digits_of_nat #b n) y) =
  ()

let predecessor_candidate_sound (#b:base) (y:numeral b) (n:nat)
  : Lemma (requires (memP n (predecessors_bounded #b y)))
    (ensures (predecessor #b y (digits_of_nat #b n))) =
  mem_filter (is_predecessor #b y) (nat_range (value y)) n;
  is_predecessor_iff #b y n;
  ()

let reverse_add_ge (#b:base) (x y:numeral b)
  : Lemma (requires (step x y))
    (ensures (value x <= value y)) =
  reverse_add_value #b x;
  assert (value y == value (reverse_add #b x));
  ()

let predecessor_complete (#b:base) (y x:numeral b)
  : Lemma (requires (canonical x /\ predecessor #b y x))
    (ensures (memP (value x) (predecessors_bounded #b y))) =
  reverse_add_ge #b x y;
  nat_range_mem (value y) (value x);
  mem_filter (is_predecessor #b y) (nat_range (value y)) (value x);
  digits_of_nat_of_canonical #b x;
  ()
