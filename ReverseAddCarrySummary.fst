module ReverseAddCarrySummary

open ReverseAdd
open ReverseAddCarry
open FStar.List.Tot

// A summary is the effect of a whole sum-cell sequence on an incoming carry.
// It is independent of the sequence length and composes associatively.
type carry_summary = {
  from_zero: carry;
  from_one: carry
}

let carry_step (s:nat) (c:carry) : carry =
  if s + c < 10 then 0 else 1

let carry_summary_apply (f:carry_summary) (c:carry) : carry =
  if c = 0 then f.from_zero else f.from_one

let carry_summary_cell (s:nat) : carry_summary = {
  from_zero = carry_step s 0;
  from_one = carry_step s 1
}

let carry_summary_compose
  (first second:carry_summary) : carry_summary = {
  from_zero = carry_summary_apply second first.from_zero;
  from_one = carry_summary_apply second first.from_one
}

let carry_summary_identity : carry_summary = {
  from_zero = 0;
  from_one = 1
}

let carry_summary_compose_left_identity
  (f:carry_summary) : Lemma (
    carry_summary_compose carry_summary_identity f == f) = ()

let carry_summary_compose_right_identity
  (f:carry_summary) : Lemma (
    carry_summary_compose f carry_summary_identity == f) = ()

let carry_summary_compose_assoc
  (a b c:carry_summary) : Lemma (
    carry_summary_compose
      (carry_summary_compose a b) c ==
    carry_summary_compose
      a (carry_summary_compose b c)) = ()

let carry_summary_apply_zero (f:carry_summary) : Lemma (
    carry_summary_apply f 0 == f.from_zero) = ()

let carry_summary_apply_one (f:carry_summary) : Lemma (
    carry_summary_apply f 1 == f.from_one) =
  ()

let carry_summary_cell_sound (s:nat) (c:carry) : Lemma (
    carry_summary_apply (carry_summary_cell s) c ==
      carry_step s c) =
  if c = 0 then
    ()
  else
    assert (c == 1)

let carry_summary_compose_apply
  (first second:carry_summary) (c:carry) : Lemma (
    carry_summary_apply (carry_summary_compose first second) c ==
      carry_summary_apply second
        (carry_summary_apply first c)) =
  if c = 0 then
    ()
  else
    assert (c == 1)

let rec carry_summary_of_sums (sums:list nat) : carry_summary =
  match sums with
  | [] -> carry_summary_identity
  | s::tl ->
      carry_summary_compose
        (carry_summary_cell s)
        (carry_summary_of_sums tl)

let rec carry_scan (sums:list nat) (c:carry) : carry =
  match sums with
  | [] -> c
  | s::tl -> carry_scan tl (carry_step s c)

let rec carry_sum_cells
  (xs ys:numeral 10) : list nat =
  match xs, ys with
  | [], [] -> []
  | x::xt, y::yt -> (x + y) :: carry_sum_cells xt yt
  | x::xt, [] -> x :: carry_sum_cells xt []
  | [], y::yt -> y :: carry_sum_cells [] yt

let rec final_carry (cs:list carry) : carry =
  match cs with
  | [] -> 0
  | [c] -> c
  | _::tl -> final_carry tl

let rec add_trace_final_carry_summary
  (xs ys:numeral 10) (c:carry) : Lemma (
    ensures (final_carry (add_trace xs ys c).carries ==
      carry_scan (carry_sum_cells xs ys) c))
    (decreases (length xs + length ys)) =
  match xs, ys with
  | [], [] -> ()
  | x::xt, y::yt ->
      let cell = split_add_cell #10 x y c in
      add_trace_final_carry_summary xt yt cell.carry;
      assert (carry_step (x + y) c == cell.carry);
      ()
  | x::xt, [] ->
      let cell = split_add_cell #10 x 0 c in
      add_trace_final_carry_summary xt [] cell.carry;
      assert (carry_step x c == cell.carry);
      ()
  | [], y::yt ->
      let cell = split_add_cell #10 0 y c in
      add_trace_final_carry_summary [] yt cell.carry;
      assert (carry_step y c == cell.carry);
      ()

let trace_final_carry_summary (xs:numeral 10) : Lemma (
    final_carry (trace_carries xs) ==
      carry_scan (carry_sum_cells xs (rev xs)) 0) =
  add_trace_final_carry_summary xs (rev xs) 0;
  ()

let rec carry_scan_summary (sums:list nat) (c:carry) : Lemma (
    carry_scan sums c ==
      carry_summary_apply (carry_summary_of_sums sums) c) =
  match sums with
  | [] -> ()
  | s::tl ->
      carry_scan_summary tl (carry_step s c);
      carry_summary_cell_sound s c;
      carry_summary_compose_apply
        (carry_summary_cell s)
        (carry_summary_of_sums tl)
        c;
      ()
