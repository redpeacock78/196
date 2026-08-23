module ReverseAddCarry

open ReverseAdd
open FStar.List.Tot
open FStar.List.Tot.Properties

type add_trace_result (b:base) = {
  digits: numeral b;
  carries: list carry
}

// carries records the carry entering each processed cell, including the
// initial carry and the carry entering the final carry-only cell.
let rec add_trace (#b:base)
  (xs:numeral b) (ys:numeral b) (c:carry)
  : Tot (add_trace_result b)
    (decreases (length xs + length ys)) =
  match xs, ys with
  | [], [] ->
      { digits = if c = 0 then [] else [c]; carries = [c] }
  | x::xs', [] ->
      let cell = split_add_cell x 0 c in
      let rest = add_trace xs' [] cell.carry in
      { digits = cell.digit :: rest.digits;
        carries = c :: rest.carries }
  | [], y::ys' ->
      let cell = split_add_cell 0 y c in
      let rest = add_trace [] ys' cell.carry in
      { digits = cell.digit :: rest.digits;
        carries = c :: rest.carries }
  | x::xs', y::ys' ->
      let cell = split_add_cell x y c in
      let rest = add_trace xs' ys' cell.carry in
      { digits = cell.digit :: rest.digits;
        carries = c :: rest.carries }

let rec trace_digits_eq (#b:base) (xs ys:numeral b) (c:carry)
  : Lemma (ensures ((add_trace xs ys c).digits == add_digits xs ys c))
    (decreases (length xs + length ys)) =
  match xs, ys with
  | [], [] -> ()
  | x::xs', [] ->
      let cell = split_add_cell x 0 c in
      trace_digits_eq xs' [] cell.carry;
      ()
  | [], y::ys' ->
      let cell = split_add_cell 0 y c in
      trace_digits_eq [] ys' cell.carry;
      ()
  | x::xs', y::ys' ->
      let cell = split_add_cell x y c in
      trace_digits_eq xs' ys' cell.carry;
      ()

let rec trace_cell_equation (#b:base)
  (xs ys:numeral b) (c:carry) (i:nat)
  : Lemma (requires (i < length xs /\ i < length ys))
    (ensures (exists (di:digit b) (cin cout:carry).
      nth (add_trace xs ys c).digits i == Some di /\
      nth (add_trace xs ys c).carries i == Some cin /\
      nth (add_trace xs ys c).carries (i + 1) == Some cout /\
      di + b * cout ==
        (match nth xs i with | Some x -> x | None -> 0) +
        (match nth ys i with | Some y -> y | None -> 0) + cin))
    (decreases (length xs + length ys)) =
  match xs, ys with
  | [], _ -> ()
  | _, [] -> ()
  | x::xs', y::ys' ->
      let cell = split_add_cell x y c in
      if i = 0 then
        (split_add_cell_value x y c; ())
      else
        (trace_cell_equation xs' ys' cell.carry (i - 1); ())

let rec trace_output_length_case (#b:base)
  (xs ys:numeral b) (c:carry)
  : Lemma (requires (length xs == length ys))
    (ensures (
      length (add_trace xs ys c).digits == length xs \/
      length (add_trace xs ys c).digits == length xs + 1))
    (decreases (length xs + length ys)) =
  match xs, ys with
  | [], [] -> ()
  | x::xs', y::ys' ->
      let cell = split_add_cell x y c in
      trace_output_length_case xs' ys' cell.carry;
      ()
  | [], _ -> ()
  | _, [] -> ()

let rec trace_output_length_carry_link (#b:base)
  (xs ys:numeral b) (c:carry)
  : Lemma (requires (length xs == length ys))
    (ensures (
      (length (add_trace xs ys c).digits == length xs /\
       nth (add_trace xs ys c).carries (length xs) == Some 0) \/
      (length (add_trace xs ys c).digits == length xs + 1 /\
       nth (add_trace xs ys c).carries (length xs) == Some 1)))
    (decreases (length xs + length ys)) =
  match xs, ys with
  | [], [] ->
      if c = 0 then () else ()
  | x::xs', y::ys' ->
      let cell = split_add_cell x y c in
      trace_output_length_carry_link xs' ys' cell.carry;
      ()
  | [], _ -> ()
  | _, [] -> ()

let rec trace_final_digit_carry_link (#b:base)
  (xs ys:numeral b) (c:carry)
  : Lemma (requires (
      length xs == length ys /\
      nth (add_trace xs ys c).carries (length xs) == Some 1))
    (ensures (nth (add_trace xs ys c).digits (length xs) == Some 1))
    (decreases (length xs + length ys)) =
  match xs, ys with
  | [], [] -> ()
  | x::xs', y::ys' ->
      let cell = split_add_cell x y c in
      trace_final_digit_carry_link xs' ys' cell.carry;
      ()
  | [], _ -> ()
  | _, [] -> ()

let carry_profile (#b:base)
  (xs ys:numeral b) (c:carry) : list carry =
  (add_trace xs ys c).carries

let carry_profile_196 : list carry =
  carry_profile digits_196 (rev digits_196) 0

let carry_profile_196_is_0010 () : Lemma (
    carry_profile_196 == [0; 0; 1; 0]) = ()

let carry_profile_196_is_not_symmetric () : Lemma (
    ~ (carry_profile_196 == rev carry_profile_196)) =
  carry_profile_196_is_0010 ();
  ()

let equal_output_carry_cell
  (s:nat) (cin1 cin2:carry)
  (d1 d2:digit 10) (cout1 cout2:carry)
    : Lemma (requires (
      d1 == d2 /\
      d1 + 10 * cout1 == s + cin1 /\
      d2 + 10 * cout2 == s + cin2))
    (ensures (cin1 == cin2 /\ cout1 == cout2)) =
  ()

let mirrored_cells_force_carry_symmetry
  (n:nat)
  (s:nat -> nat)
  (d:nat -> digit 10)
  (c:nat -> carry)
  : Lemma (requires (
      n > 0 /\
      c 0 == 0 /\ c n == 0 /\
      (forall i. i < n ==> (
        d i + 10 * c (i + 1) == s i + c i)) /\
      (forall i. i < n ==> (
        d i == d (n - 1 - i) /\
        s i == s (n - 1 - i)))))
    (ensures (forall i. i < n ==> c i == c (n - 1 - i))) =
  introduce forall (i:nat). i < n ==> c i == c (n - 1 - i)
  with (
    introduce _ ==> _
    with (
      let j = n - 1 - i in
      assert (j < n);
      assert (n - 1 - j == i);
      assert (j + 1 == n - i);
      assert (d j == d i);
      assert (s j == s i);
      assert (d j + 10 * c (j + 1) == s j + c j);
      assert (d i + 10 * c (i + 1) == s i + c i);
      equal_output_carry_cell (s i) (c i) (c j)
        (d i) (d j) (c (i + 1)) (c (j + 1));
      ()))

let mirrored_overflow_cells_force_sum_carry_relation
  (n:nat)
  (s:nat -> nat)
  (d:nat -> digit 10)
  (c:nat -> carry)
  : Lemma (requires (
      (forall i. i <= n ==> (
        d i + 10 * c (i + 1) == s i + c i)) /\
      (forall i. i <= n ==> d i == d (n - i))))
    (ensures (forall i. i <= n ==>
      s i + c i + 10 * c (n - i + 1) ==
        s (n - i) + c (n - i) + 10 * c (i + 1))) =
  introduce forall (i:nat). i <= n ==>
    s i + c i + 10 * c (n - i + 1) ==
      s (n - i) + c (n - i) + 10 * c (i + 1)
  with (
    introduce _ ==> _
    with (
      let j = n - i in
      assert (j <= n);
      assert (d i == d j);
      assert (d i + 10 * c (i + 1) == s i + c i);
      assert (d j + 10 * c (j + 1) == s j + c j);
      assert (j + 1 == n - i + 1);
      ()))

let rec reverse_first_is_last (#a:eqtype) (xs:list a)
  : Lemma (requires (xs <> []))
    (ensures (nth (rev xs) 0 == Some (last xs)))
    (decreases xs) =
  match xs with
  | [] -> ()
  | [_] -> ()
  | d::tl ->
      rev_length xs;
      assert (length xs = 1 + length tl);
      assert (length (rev xs) > 0);
      reverse_first_is_last tl;
      rev_append [d] tl;
      ()

let rec nth_last (#a:eqtype) (xs:list a)
  : Lemma (requires (xs <> []))
    (ensures (nth xs (length xs - 1) == Some (last xs)))
    (decreases xs) =
  match xs with
  | [] -> ()
  | [_] -> ()
  | _::tl ->
      nth_last tl;
      ()

let rec nth_length_none (#a:eqtype) (xs:list a)
  : Lemma (ensures (nth xs (length xs) == None))
    (decreases xs) =
  match xs with
  | [] -> ()
  | _::tl -> nth_length_none tl

let rec nth_append_left (#a:eqtype) (l1 l2:list a) (i:nat)
  : Lemma (requires (i < length l1))
    (ensures (nth (l1 @ l2) i == nth l1 i))
    (decreases l1) =
  match l1 with
  | [] -> ()
  | x::tl ->
      if i = 0 then ()
      else nth_append_left tl l2 (i - 1)

let rec nth_append_last (#a:eqtype) (l:list a) (x:a)
  : Lemma (ensures (nth (l @ [x]) (length l) == Some x))
    (decreases l) =
  match l with
  | [] -> ()
  | _::tl ->
      nth_append_last tl x;
      ()

let rec nth_rev (#a:eqtype) (xs:list a) (i:nat)
  : Lemma (requires (i < length xs))
    (ensures (nth (rev xs) i ==
      nth xs (length xs - 1 - i)))
    (decreases xs) =
  match xs with
  | [] -> ()
  | x::tl ->
      if i = 0 then begin
        reverse_first_is_last xs;
        nth_last xs;
        ()
      end else if i < length tl then begin
        rev_append [x] tl;
        rev_length tl;
        nth_rev tl i;
        nth_append_left (rev tl) [x] i;
        ()
      end else begin
        rev_append [x] tl;
        nth_append_last (rev tl) x;
        rev_length tl;
        ()
      end

let palindrome_nth_symmetric (#a:eqtype) (xs:list a) (i:nat)
  : Lemma (requires (xs == rev xs /\ i < length xs))
    (ensures (nth xs i == nth xs (length xs - 1 - i))) =
  nth_rev xs i;
  ()

let digit_at (#b:base) (xs:numeral b) (i:nat) : digit b =
  match nth xs i with
  | Some d -> d
  | None -> 0

let carry_at (xs:list carry) (i:nat) : carry =
  match nth xs i with
  | Some c -> c
  | None -> 0

let trace_digits (xs:numeral 10) : numeral 10 =
  (add_trace xs (rev xs) 0).digits

let rec canonical_last_positive (#b:base) (xs:numeral b)
  : Lemma (requires (canonical xs /\ xs <> []))
    (ensures (last xs > 0))
    (decreases xs) =
  match xs with
  | [] -> ()
  | [_] -> ()
  | _::tl ->
      canonical_last_positive #b tl;
      ()

let add_trace_nonempty (#b:base)
  (xs:numeral b) (ys:numeral b) (c:carry)
  : Lemma (requires (xs <> [] \/ ys <> []))
    (ensures ((add_trace xs ys c).digits <> [])) =
  match xs, ys with
  | [], [] -> ()
  | _::_, [] -> ()
  | [], _::_ -> ()
  | _::_, _::_ -> ()

let rec add_trace_canonical_top_positive (#b:base)
  (xs:numeral b) (ys:numeral b) (c:carry)
  : Lemma (requires (
      length xs == length ys /\
      xs <> [] /\
      last xs > 0))
    (ensures (canonical ((add_trace xs ys c).digits)))
    (decreases (length xs + length ys)) =
  match xs, ys with
  | [], [] -> ()
  | x::xs', y::ys' ->
      let cell = split_add_cell x y c in
      if xs' == [] then begin
        assert (ys' == []);
        if cell.carry == 1 then
          ()
        else begin
          assert (cell.digit > 0);
          ()
        end
      end else begin
        assert (ys' <> []);
        add_trace_canonical_top_positive xs' ys' cell.carry;
        add_trace_nonempty xs' ys' cell.carry;
        ()
      end
  | [], _ -> ()
  | _, [] -> ()

let trace_digits_canonical (xs:numeral 10)
  : Lemma (requires (canonical xs /\ xs <> []))
    (ensures (canonical (trace_digits xs))) =
  canonical_last_positive #10 xs;
  rev_length xs;
  add_trace_canonical_top_positive #10 xs (rev xs) 0;
  ()

let trace_digits_equals_reverse_add (xs:numeral 10)
  : Lemma (requires (canonical xs /\ xs <> []))
    (ensures (trace_digits xs == reverse_add xs)) =
  trace_digits_canonical xs;
  reverse_add_canonical #10 xs;
  trace_digits_eq xs (rev xs) 0;
  add_digits_value xs (rev xs) 0;
  reverse_add_value #10 xs;
  normalize_value (rev xs);
  assert (value (trace_digits xs) == value (reverse_add xs));
  digits_of_nat_of_canonical #10 (trace_digits xs);
  digits_of_nat_of_canonical #10 (reverse_add xs);
  ()

let trace_carries (xs:numeral 10) : list carry =
  (add_trace xs (rev xs) 0).carries

let reverse_trace_output_length_case (xs:numeral 10)
  : Lemma (ensures (
      length (trace_digits xs) == length xs \/
      length (trace_digits xs) == length xs + 1)) =
  rev_length xs;
  trace_output_length_case xs (rev xs) 0;
  ()

let trace_digit_at (xs:numeral 10) (i:nat) : digit 10 =
  digit_at (trace_digits xs) i

let trace_carry_at (xs:numeral 10) (i:nat) : carry =
  carry_at (trace_carries xs) i

let carry_prefix_symmetric (xs:numeral 10) : prop =
  forall i. i < length xs ==>
    trace_carry_at xs i == trace_carry_at xs (length xs - 1 - i)

let trace_carry_obstruction (xs:numeral 10) : prop =
  ((length (trace_digits xs) == length xs /\
    nth (trace_carries xs) (length xs) == Some 0 /\
    ~(carry_prefix_symmetric xs)) \/
   (length (trace_digits xs) == length xs + 1 /\
    nth (trace_carries xs) (length xs) == Some 1 /\
    ~(trace_digit_at xs 0 == 1)))

let trace_case_obstruction_contradiction (xs:numeral 10)
  : Lemma (requires (
      ((length (trace_digits xs) == length xs /\
        nth (trace_carries xs) (length xs) == Some 0 /\
        ~(carry_prefix_symmetric xs)) \/
       (length (trace_digits xs) == length xs + 1 /\
        nth (trace_carries xs) (length xs) == Some 1 /\
        ~(trace_digit_at xs 0 == 1))) /\
      ((length (trace_digits xs) == length xs /\
        nth (trace_carries xs) (length xs) == Some 0 /\
        carry_prefix_symmetric xs) \/
       (length (trace_digits xs) == length xs + 1 /\
        nth (trace_carries xs) (length xs) == Some 1 /\
        trace_digit_at xs 0 == 1))))
    (ensures False) = ()

let trace_sum_at (xs:numeral 10) (i:nat) : nat =
  let ys = rev xs in
  (match nth xs i with | Some d -> d | None -> 0) +
  (match nth ys i with | Some d -> d | None -> 0)

let trace_overflow_outer_obstruction (xs:numeral 10) : prop =
  length (trace_digits xs) == length xs + 1 /\
  nth (trace_carries xs) (length xs) == Some 1 /\
  ~(trace_sum_at xs 0 == 1 + 10 * trace_carry_at xs 1)

let trace_equation_at (xs:numeral 10) (i:nat)
  : Lemma (requires (i < length xs))
    (ensures (trace_digit_at xs i +
        10 * trace_carry_at xs (i + 1) ==
        trace_sum_at xs i + trace_carry_at xs i)) =
  rev_length xs;
  trace_cell_equation xs (rev xs) 0 i;
  ()

let trace_equations_all (xs:numeral 10)
  : Lemma (ensures (forall i. i < length xs ==>
      trace_digit_at xs i +
        10 * trace_carry_at xs (i + 1) ==
        trace_sum_at xs i + trace_carry_at xs i)) =
  introduce forall (i:nat). i < length xs ==>
    trace_digit_at xs i +
      10 * trace_carry_at xs (i + 1) ==
      trace_sum_at xs i + trace_carry_at xs i
  with (
    introduce _ ==> _
    with (trace_equation_at xs i)
  );
  ()

let overflow_trace_carry_at (xs:numeral 10) (i:nat) : carry =
  if i = length xs + 1 then 0 else trace_carry_at xs i

let overflow_trace_equation_at (xs:numeral 10) (i:nat)
  : Lemma (requires (
      xs <> [] /\
      i <= length xs /\
      length (trace_digits xs) == length xs + 1 /\
      nth (trace_carries xs) (length xs) == Some 1))
    (ensures (trace_digit_at xs i +
        10 * overflow_trace_carry_at xs (i + 1) ==
        trace_sum_at xs i + overflow_trace_carry_at xs i)) =
  let n = length xs in
  if i < n then begin
    trace_equation_at xs i;
    ()
  end else begin
    assert (i == n);
    rev_length xs;
    trace_final_digit_carry_link xs (rev xs) 0;
    assert (trace_digit_at xs n == 1);
    assert (trace_carry_at xs n == 1);
    nth_length_none xs;
    nth_length_none (rev xs);
    assert (trace_sum_at xs n == 0);
    ()
  end

let overflow_trace_equations_all (xs:numeral 10)
  : Lemma (requires (
      xs <> [] /\
      length (trace_digits xs) == length xs + 1 /\
      nth (trace_carries xs) (length xs) == Some 1))
    (ensures (forall i. i <= length xs ==>
      trace_digit_at xs i +
        10 * overflow_trace_carry_at xs (i + 1) ==
        trace_sum_at xs i + overflow_trace_carry_at xs i)) =
  introduce forall (i:nat). i <= length xs ==>
    trace_digit_at xs i +
      10 * overflow_trace_carry_at xs (i + 1) ==
      trace_sum_at xs i + overflow_trace_carry_at xs i
  with (
    introduce _ ==> _
    with (overflow_trace_equation_at xs i)
  );
  ()

let overflow_trace_digit_symmetric_at (xs:numeral 10) (i:nat)
  : Lemma (requires (
      i <= length xs /\
      length (trace_digits xs) == length xs + 1 /\
      trace_digits xs == rev (trace_digits xs)))
    (ensures (trace_digit_at xs i ==
      trace_digit_at xs (length xs - i))) =
  let out = trace_digits xs in
  let n = length xs in
  let j = n - i in
  assert (i < length out);
  assert (j < length out);
  palindrome_nth_symmetric out i;
  ()

let overflow_trace_digits_symmetric_all (xs:numeral 10)
  : Lemma (requires (
      length (trace_digits xs) == length xs + 1 /\
      trace_digits xs == rev (trace_digits xs)))
    (ensures (forall i. i <= length xs ==>
      trace_digit_at xs i == trace_digit_at xs (length xs - i))) =
  introduce forall (i:nat). i <= length xs ==>
    trace_digit_at xs i == trace_digit_at xs (length xs - i)
  with (
    introduce _ ==> _
    with (overflow_trace_digit_symmetric_at xs i)
  );
  ()

let reverse_trace_overflow_sum_carry_relation (xs:numeral 10)
  : Lemma (requires (
      xs <> [] /\
      length (trace_digits xs) == length xs + 1 /\
      nth (trace_carries xs) (length xs) == Some 1 /\
      trace_digits xs == rev (trace_digits xs)))
    (ensures (forall i. i <= length xs ==>
      trace_sum_at xs i + overflow_trace_carry_at xs i +
          10 * overflow_trace_carry_at xs (length xs - i + 1) ==
        trace_sum_at xs (length xs - i) +
          overflow_trace_carry_at xs (length xs - i) +
          10 * overflow_trace_carry_at xs (i + 1))) =
  overflow_trace_equations_all xs;
  overflow_trace_digits_symmetric_all xs;
  mirrored_overflow_cells_force_sum_carry_relation
    (length xs)
    (trace_sum_at xs)
    (trace_digit_at xs)
    (overflow_trace_carry_at xs);
  ()

let overflow_sum_carry_relation_holds (xs:numeral 10) : prop =
  forall i. i <= length xs ==>
    trace_sum_at xs i + overflow_trace_carry_at xs i +
        10 * overflow_trace_carry_at xs (length xs - i + 1) ==
      trace_sum_at xs (length xs - i) +
        overflow_trace_carry_at xs (length xs - i) +
        10 * overflow_trace_carry_at xs (i + 1)

let trace_overflow_relation_obstruction (xs:numeral 10) : prop =
  length (trace_digits xs) == length xs + 1 /\
  nth (trace_carries xs) (length xs) == Some 1 /\
  ~(overflow_sum_carry_relation_holds xs)

let trace_overflow_relation_obstruction_excludes_palindrome
  (xs:numeral 10)
  : Lemma (requires (
      xs <> [] /\
      trace_overflow_relation_obstruction xs /\
      trace_digits xs == rev (trace_digits xs)))
    (ensures False) =
  reverse_trace_overflow_sum_carry_relation xs;
  ()

let trace_digit_symmetric_at (xs:numeral 10) (i:nat)
  : Lemma (requires (
      i < length xs /\
      length (trace_digits xs) == length xs /\
      trace_digits xs == rev (trace_digits xs)))
    (ensures (trace_digit_at xs i ==
      trace_digit_at xs (length xs - 1 - i))) =
  let out = trace_digits xs in
  let n = length xs in
  let j = n - 1 - i in
  assert (j < n);
  assert (i < length out);
  assert (j < length out);
  palindrome_nth_symmetric out i;
  ()

let trace_digits_symmetric_all (xs:numeral 10)
  : Lemma (requires (
      length (trace_digits xs) == length xs /\
      trace_digits xs == rev (trace_digits xs)))
    (ensures (forall i. i < length xs ==>
      trace_digit_at xs i == trace_digit_at xs (length xs - 1 - i))) =
  introduce forall (i:nat). i < length xs ==>
    trace_digit_at xs i == trace_digit_at xs (length xs - 1 - i)
  with (
    introduce _ ==> _
    with (trace_digit_symmetric_at xs i)
  );
  ()

let trace_sum_symmetric_at (xs:numeral 10) (i:nat)
  : Lemma (requires (i < length xs))
    (ensures (trace_sum_at xs i ==
      trace_sum_at xs (length xs - 1 - i))) =
  let n = length xs in
  let j = n - 1 - i in
  assert (j < n);
  rev_length xs;
  nth_rev xs i;
  nth_rev xs j;
  ()

let trace_sums_symmetric_all (xs:numeral 10)
  : Lemma (ensures (forall i. i < length xs ==>
      trace_sum_at xs i == trace_sum_at xs (length xs - 1 - i))) =
  introduce forall (i:nat). i < length xs ==>
    trace_sum_at xs i == trace_sum_at xs (length xs - 1 - i)
  with (
    introduce _ ==> _
    with (trace_sum_symmetric_at xs i)
  );
  ()

let reverse_trace_no_overflow_carry_symmetry (xs:numeral 10)
  : Lemma (requires (
      xs <> [] /\
      length (trace_digits xs) == length xs /\
      nth (trace_carries xs) (length xs) == Some 0 /\
      trace_digits xs == rev (trace_digits xs)))
    (ensures (forall i. i < length xs ==>
      trace_carry_at xs i ==
        trace_carry_at xs (length xs - 1 - i))) =
  let n = length xs in
  trace_equations_all xs;
  trace_digits_symmetric_all xs;
  trace_sums_symmetric_all xs;
  mirrored_cells_force_carry_symmetry
    n
    (trace_sum_at xs)
    (trace_digit_at xs)
    (trace_carry_at xs);
  ()

let reverse_trace_196_carry_exclusion ()
  : Lemma (requires (
      trace_digits digits_196 == rev (trace_digits digits_196)))
    (ensures False) =
  assert (length (trace_digits digits_196) == length digits_196);
  assert (nth (trace_carries digits_196) (length digits_196) == Some 0);
  reverse_trace_no_overflow_carry_symmetry digits_196;
  assert (trace_carry_at digits_196 0 ==
    trace_carry_at digits_196 2);
  assert (trace_carries digits_196 == [0; 0; 1; 0]);
  ()

let palindrome_first_is_last (#a:eqtype) (xs:list a)
  : Lemma (requires (xs <> [] /\ xs == rev xs))
    (ensures (nth xs 0 == Some (last xs))) =
  reverse_first_is_last xs;
  ()

let final_carry_palindrome_requires_low_one (ds:numeral 10)
  : Lemma (requires (ds <> [] /\
      (ds @ [1]) == rev (ds @ [1])))
    (ensures (nth ds 0 == Some 1)) =
  palindrome_first_is_last (ds @ [1]);
  lemma_append_last ds [1];
  assert (nth (ds @ [1]) 0 == nth ds 0);
  ()

let palindrome_last_one_requires_first_one (xs:numeral 10)
  : Lemma (requires (xs <> [] /\ xs == rev xs /\ last xs == 1))
    (ensures (nth xs 0 == Some 1)) =
  palindrome_first_is_last xs;
  ()

let reverse_trace_overflow_low_one (xs:numeral 10)
  : Lemma (requires (
      xs <> [] /\
      length (trace_digits xs) == length xs + 1 /\
      nth (trace_digits xs) (length xs) == Some 1 /\
      trace_digits xs == rev (trace_digits xs)))
    (ensures (trace_digit_at xs 0 == 1)) =
  let out = trace_digits xs in
  nth_last out;
  assert (last out == 1);
  palindrome_last_one_requires_first_one out;
  ()

let reverse_trace_overflow_outer_sum_condition (xs:numeral 10)
  : Lemma (requires (
      xs <> [] /\
      length (trace_digits xs) == length xs + 1 /\
      nth (trace_carries xs) (length xs) == Some 1 /\
      trace_digits xs == rev (trace_digits xs)))
    (ensures (trace_sum_at xs 0 ==
      1 + 10 * trace_carry_at xs 1)) =
  rev_length xs;
  trace_final_digit_carry_link xs (rev xs) 0;
  reverse_trace_overflow_low_one xs;
  trace_equation_at xs 0;
  assert (trace_carry_at xs 0 == 0);
  ()

let trace_overflow_outer_obstruction_excludes_palindrome
  (xs:numeral 10)
  : Lemma (requires (
      xs <> [] /\
      trace_overflow_outer_obstruction xs /\
      trace_digits xs == rev (trace_digits xs)))
    (ensures False) =
  reverse_trace_overflow_outer_sum_condition xs;
  ()

let reverse_trace_palindrome_cases (xs:numeral 10)
  : Lemma (requires (
      xs <> [] /\ trace_digits xs == rev (trace_digits xs)))
    (ensures (
      (length (trace_digits xs) == length xs /\
       nth (trace_carries xs) (length xs) == Some 0 /\
       (forall i. i < length xs ==>
         trace_carry_at xs i ==
           trace_carry_at xs (length xs - 1 - i))) \/
      (length (trace_digits xs) == length xs + 1 /\
       nth (trace_carries xs) (length xs) == Some 1 /\
       trace_digit_at xs 0 == 1))) =
  reverse_trace_output_length_case xs;
  rev_length xs;
  trace_output_length_carry_link xs (rev xs) 0;
  eliminate
    (length (trace_digits xs) == length xs /\
     nth (trace_carries xs) (length xs) == Some 0) \/
    (length (trace_digits xs) == length xs + 1 /\
     nth (trace_carries xs) (length xs) == Some 1)
  with (
    reverse_trace_no_overflow_carry_symmetry xs;
    ())
  and (
    rev_length xs;
    trace_final_digit_carry_link xs (rev xs) 0;
    reverse_trace_overflow_low_one xs;
    ())

let trace_carry_obstruction_excludes_palindrome (xs:numeral 10)
  : Lemma (requires (
      xs <> [] /\
      trace_carry_obstruction xs /\
      palindrome #10 (trace_digits xs)))
    (ensures False) =
  reverse_trace_palindrome_cases xs;
  trace_case_obstruction_contradiction xs

let reverse_add_carry_obstruction_excludes_palindrome (xs:numeral 10)
  : Lemma (requires (
      xs <> [] /\
      trace_digits xs == reverse_add xs /\
      trace_carry_obstruction xs /\
      palindrome #10 (reverse_add xs)))
    (ensures False) =
  assert (palindrome #10 (trace_digits xs));
  trace_carry_obstruction_excludes_palindrome xs

let trace_palindrome_obstruction (xs:numeral 10) : prop =
  trace_carry_obstruction xs \/
  trace_overflow_relation_obstruction xs

let trace_palindrome_obstruction_excludes_palindrome
  (xs:numeral 10)
  : Lemma (requires (
      xs <> [] /\
      trace_palindrome_obstruction xs /\
      trace_digits xs == rev (trace_digits xs)))
    (ensures False) =
  eliminate trace_carry_obstruction xs \/
    trace_overflow_relation_obstruction xs
  with (
    trace_carry_obstruction_excludes_palindrome xs;
    ())
  and (
    trace_overflow_relation_obstruction_excludes_palindrome xs;
    ())

let reverse_add_palindrome_obstruction_excludes_palindrome
  (xs:numeral 10)
  : Lemma (requires (
      xs <> [] /\
      trace_digits xs == reverse_add xs /\
      trace_palindrome_obstruction xs /\
      palindrome #10 (reverse_add xs)))
    (ensures False) =
  assert (palindrome #10 (trace_digits xs));
  trace_palindrome_obstruction_excludes_palindrome xs

let trace_carry_obstruction_196 () : Lemma (
    trace_carry_obstruction digits_196) =
  assert (length (trace_digits digits_196) == length digits_196);
  assert (nth (trace_carries digits_196) (length digits_196) == Some 0);
  assert (~ (trace_carry_at digits_196 0 ==
    trace_carry_at digits_196 2));
  ()

let trace_carry_obstruction_887 () : Lemma (
    trace_carry_obstruction [7; 8; 8]) =
  assert (length (trace_digits [7; 8; 8]) == length [7; 8; 8] + 1);
  assert (nth (trace_carries [7; 8; 8])
    (length [7; 8; 8]) == Some 1);
  assert (~ (trace_digit_at [7; 8; 8] 0 == 1));
  ()

let trace_carry_obstruction_1675 () : Lemma (
    trace_carry_obstruction [5; 7; 6; 1]) =
  assert (length (trace_digits [5; 7; 6; 1]) ==
    length [5; 7; 6; 1]);
  assert (nth (trace_carries [5; 7; 6; 1])
    (length [5; 7; 6; 1]) == Some 0);
  assert (~ (trace_carry_at [5; 7; 6; 1] 0 ==
    trace_carry_at [5; 7; 6; 1] 3));
  ()

let trace_carry_obstruction_7436 () : Lemma (
    trace_carry_obstruction [6; 3; 4; 7]) =
  assert (length (trace_digits [6; 3; 4; 7]) ==
    length [6; 3; 4; 7] + 1);
  assert (nth (trace_carries [6; 3; 4; 7])
    (length [6; 3; 4; 7]) == Some 1);
  assert (~ (trace_digit_at [6; 3; 4; 7] 0 == 1));
  ()

let trace_carry_obstruction_13783 () : Lemma (
    trace_carry_obstruction [3; 8; 7; 3; 1]) =
  assert (length (trace_digits [3; 8; 7; 3; 1]) ==
    length [3; 8; 7; 3; 1]);
  assert (nth (trace_carries [3; 8; 7; 3; 1])
    (length [3; 8; 7; 3; 1]) == Some 0);
  assert (~ (trace_carry_at [3; 8; 7; 3; 1] 0 ==
    trace_carry_at [3; 8; 7; 3; 1] 4));
  ()

let trace_carry_obstruction_52514 () : Lemma (
    trace_carry_obstruction [4; 1; 5; 2; 5]) =
  assert (length (trace_digits [4; 1; 5; 2; 5]) ==
    length [4; 1; 5; 2; 5]);
  assert (nth (trace_carries [4; 1; 5; 2; 5])
    (length [4; 1; 5; 2; 5]) == Some 0);
  assert (~ (trace_carry_at [4; 1; 5; 2; 5] 1 ==
    trace_carry_at [4; 1; 5; 2; 5] 3));
  ()

let trace_carry_obstruction_94039 () : Lemma (
    trace_carry_obstruction [9; 3; 0; 4; 9]) =
  assert (length (trace_digits [9; 3; 0; 4; 9]) ==
    length [9; 3; 0; 4; 9] + 1);
  assert (nth (trace_carries [9; 3; 0; 4; 9])
    (length [9; 3; 0; 4; 9]) == Some 1);
  assert (~ (trace_digit_at [9; 3; 0; 4; 9] 0 == 1));
  ()

let trace_palindrome_obstruction_not_inductive_19 () : Lemma (
    trace_palindrome_obstruction [9; 1] /\
    trace_digits [9; 1] == reverse_add #10 [9; 1] /\
    reverse_add #10 [9; 1] == [0; 1; 1] /\
    ~ (trace_palindrome_obstruction [0; 1; 1])) =
  assert (trace_digits [9; 1] == [0; 1; 1]);
  assert (reverse_add #10 [9; 1] == [0; 1; 1]);
  assert (trace_digits [0; 1; 1] == [1; 2; 1]);
  assert (~ (trace_carry_obstruction [0; 1; 1]));
  assert (~ (trace_overflow_relation_obstruction [0; 1; 1]));
  ()

let transition_7436_to_13783 () : Lemma (
    trace_digits [6; 3; 4; 7] == [3; 8; 7; 3; 1] /\
    trace_digits [6; 3; 4; 7] == reverse_add [6; 3; 4; 7]) =
  assert (trace_digits [6; 3; 4; 7] == [3; 8; 7; 3; 1]);
  assert (trace_digits [6; 3; 4; 7] == reverse_add [6; 3; 4; 7]);
  ()

let transition_13783_to_52514 () : Lemma (
    trace_digits [3; 8; 7; 3; 1] == [4; 1; 5; 2; 5] /\
    trace_digits [3; 8; 7; 3; 1] == reverse_add [3; 8; 7; 3; 1]) =
  assert (trace_digits [3; 8; 7; 3; 1] == [4; 1; 5; 2; 5]);
  assert (trace_digits [3; 8; 7; 3; 1] ==
    reverse_add [3; 8; 7; 3; 1]);
  ()

let transition_52514_to_94039 () : Lemma (
    trace_digits [4; 1; 5; 2; 5] == [9; 3; 0; 4; 9] /\
    trace_digits [4; 1; 5; 2; 5] == reverse_add [4; 1; 5; 2; 5]) =
  assert (trace_digits [4; 1; 5; 2; 5] == [9; 3; 0; 4; 9]);
  assert (trace_digits [4; 1; 5; 2; 5] ==
    reverse_add [4; 1; 5; 2; 5]);
  ()

let reverse_trace_887_overflow_carry_exclusion ()
  : Lemma (requires (
      trace_digits [7; 8; 8] == rev (trace_digits [7; 8; 8])))
    (ensures False) =
  assert (length (trace_digits [7; 8; 8]) == length [7; 8; 8] + 1);
  assert (nth (trace_digits [7; 8; 8]) (length [7; 8; 8]) == Some 1);
  reverse_trace_overflow_low_one [7; 8; 8];
  assert (trace_digit_at [7; 8; 8] 0 == 5);
  ()

let reverse_trace_1675_no_overflow_carry_exclusion ()
  : Lemma (requires (
      trace_digits [5; 7; 6; 1] ==
        rev (trace_digits [5; 7; 6; 1])))
    (ensures False) =
  assert (length (trace_digits [5; 7; 6; 1]) ==
    length [5; 7; 6; 1]);
  assert (nth (trace_carries [5; 7; 6; 1])
    (length [5; 7; 6; 1]) == Some 0);
  reverse_trace_no_overflow_carry_symmetry [5; 7; 6; 1];
  assert (trace_carry_at [5; 7; 6; 1] 0 ==
    trace_carry_at [5; 7; 6; 1] 3);
  assert (trace_carries [5; 7; 6; 1] == [0; 0; 1; 1; 0]);
  ()

let reverse_trace_887_output_not_palindrome ()
  : Lemma (ensures (~ (palindrome #10 (trace_digits [7; 8; 8])))) =
  introduce (palindrome #10 (trace_digits [7; 8; 8])) ==> False
  with (reverse_trace_887_overflow_carry_exclusion ());
  ()

let reverse_add_palindrome_implies_trace_palindrome (xs:numeral 10)
  : Lemma (requires (
      palindrome #10 (reverse_add xs) /\
      trace_digits xs == reverse_add xs))
    (ensures (palindrome #10 (trace_digits xs))) =
  ()

let reverse_add_887_output_not_palindrome ()
  : Lemma (ensures (~ (palindrome #10 (reverse_add [7; 8; 8])))) =
  introduce (palindrome #10 (reverse_add [7; 8; 8])) ==> False
  with (
    assert (trace_digits [7; 8; 8] == reverse_add [7; 8; 8]);
    trace_carry_obstruction_887 ();
    reverse_add_carry_obstruction_excludes_palindrome [7; 8; 8])

let reverse_add_1675_output_not_palindrome ()
  : Lemma (ensures (~ (palindrome #10 (reverse_add [5; 7; 6; 1])))) =
  introduce (palindrome #10 (reverse_add [5; 7; 6; 1])) ==> False
  with (
    assert (trace_digits [5; 7; 6; 1] ==
      reverse_add [5; 7; 6; 1]);
    trace_carry_obstruction_1675 ();
    reverse_add_carry_obstruction_excludes_palindrome [5; 7; 6; 1])

let reverse_trace_7436_overflow_carry_exclusion ()
  : Lemma (requires (
      trace_digits [6; 3; 4; 7] ==
        rev (trace_digits [6; 3; 4; 7])))
    (ensures False) =
  assert (length (trace_digits [6; 3; 4; 7]) ==
    length [6; 3; 4; 7] + 1);
  assert (nth (trace_digits [6; 3; 4; 7])
    (length [6; 3; 4; 7]) == Some 1);
  reverse_trace_overflow_low_one [6; 3; 4; 7];
  assert (trace_digit_at [6; 3; 4; 7] 0 == 3);
  ()

let reverse_add_7436_output_not_palindrome ()
  : Lemma (ensures (~ (palindrome #10 (reverse_add [6; 3; 4; 7])))) =
  introduce (palindrome #10 (reverse_add [6; 3; 4; 7])) ==> False
  with (
    assert (trace_digits [6; 3; 4; 7] ==
      reverse_add [6; 3; 4; 7]);
    trace_carry_obstruction_7436 ();
    reverse_add_carry_obstruction_excludes_palindrome [6; 3; 4; 7])

let reverse_add_13783_output_not_palindrome ()
  : Lemma (ensures (~ (palindrome #10 (reverse_add [3; 8; 7; 3; 1])))) =
  introduce (palindrome #10 (reverse_add [3; 8; 7; 3; 1])) ==> False
  with (
    assert (trace_digits [3; 8; 7; 3; 1] ==
      reverse_add [3; 8; 7; 3; 1]);
    trace_carry_obstruction_13783 ();
    reverse_add_carry_obstruction_excludes_palindrome [3; 8; 7; 3; 1])

let reverse_add_52514_output_not_palindrome ()
  : Lemma (ensures (~ (palindrome #10 (reverse_add [4; 1; 5; 2; 5])))) =
  introduce (palindrome #10 (reverse_add [4; 1; 5; 2; 5])) ==> False
  with (
    assert (trace_digits [4; 1; 5; 2; 5] ==
      reverse_add [4; 1; 5; 2; 5]);
    trace_carry_obstruction_52514 ();
    reverse_add_carry_obstruction_excludes_palindrome [4; 1; 5; 2; 5])

let reverse_add_94039_output_not_palindrome ()
  : Lemma (ensures (~ (palindrome #10 (reverse_add [9; 3; 0; 4; 9])))) =
  introduce (palindrome #10 (reverse_add [9; 3; 0; 4; 9])) ==> False
  with (
    assert (trace_digits [9; 3; 0; 4; 9] ==
      reverse_add [9; 3; 0; 4; 9]);
    trace_carry_obstruction_94039 ();
    reverse_add_carry_obstruction_excludes_palindrome [9; 3; 0; 4; 9])

let three_digit_carry_prefix (a b c:digit 10) : list carry =
  let cell0 = split_add_cell a c 0 in
  let cell1 = split_add_cell b b cell0.carry in
  [0; cell0.carry; cell1.carry]

let three_digit_palindrome_requires_symmetric_carries
  (a b c:digit 10)
  : Lemma (requires (
      let cell0 = split_add_cell a c 0 in
      let cell1 = split_add_cell b b cell0.carry in
      let cell2 = split_add_cell c a cell1.carry in
      cell2.carry == 0 /\
      palindrome #10 (add_digits [a; b; c] [c; b; a] 0)))
    (ensures (three_digit_carry_prefix a b c ==
      rev (three_digit_carry_prefix a b c))) =
  let cell0 = split_add_cell a c 0 in
  let cell1 = split_add_cell b b cell0.carry in
  let cell2 = split_add_cell c a cell1.carry in
  split_add_cell_value a c 0;
  split_add_cell_value b b cell0.carry;
  split_add_cell_value c a cell1.carry;
  assert (add_digits [a; b; c] [c; b; a] 0 ==
    [cell0.digit; cell1.digit; cell2.digit]);
  assert (cell0.digit == cell2.digit);
  equal_output_carry_cell (a + c) 0 cell1.carry
    cell0.digit cell2.digit cell0.carry cell2.carry;
  assert (cell0.carry == 0);
  assert (cell1.carry == 0);
  ()

let carry_prefix_196_is_not_symmetric () : Lemma (
    ~ (three_digit_carry_prefix 6 9 1 ==
      rev (three_digit_carry_prefix 6 9 1))) =
  ()

let three_digit_196_carry_exclusion ()
  : Lemma (requires (
      palindrome #10 (add_digits digits_196 (rev digits_196) 0)))
    (ensures False) =
  three_digit_palindrome_requires_symmetric_carries 6 9 1;
  carry_prefix_196_is_not_symmetric ();
  ()
