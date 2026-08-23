module ReverseAddResidue

open ReverseAdd
open AbstractReachability

// A first finite abstraction: the numeric value modulo a positive modulus.
let residue_alpha (#b:base) (#count:state_count)
  (xs:numeral b) : state count =
  value xs % count

// ponytail: universal edge is maximally coarse; add digit/carry context before
// using this abstraction for an exclusion result.
let residue_edge (#count:state_count)
  (x y:state count) : Tot bool =
  true

let residue_bad (#count:state_count)
  (s:state count) : Tot bool =
  true

let residue_simulates_step (#b:base) (#count:state_count)
  (x y:numeral b)
  : Lemma (requires (step x y))
    (ensures (edge_relation (residue_edge #count)
      (residue_alpha #b #count x)
      (residue_alpha #b #count y))) =
  ()

let residue_palindrome_sound (#b:base) (#count:state_count)
  (xs:numeral b)
  : Lemma (requires (palindrome xs))
    (ensures (residue_bad #count
      (residue_alpha #b #count xs))) =
  ()
