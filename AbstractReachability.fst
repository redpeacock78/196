module AbstractReachability

open FStar.List.Tot
open FStar.List.Tot.Properties
open FStar.ReflexiveTransitiveClosure

// State identifiers are finite naturals: 0 <= state < count.
type state_count = n:nat { n > 0 }
type state (count:state_count) = s:nat { s < count }

let rec enumerate (#count:state_count) (n:nat{n <= count})
  : Tot (list (state count))
    (decreases n) =
  if n = 0 then []
  else
    (n - 1) :: enumerate #count (n - 1)

let all_states (#count:state_count) : Tot (list (state count)) =
  enumerate #count count

let rec enumerate_mem (#count:state_count)
  (n:nat{n <= count}) (s:state count)
  : Lemma (requires (s < n))
    (ensures (memP s (enumerate #count n)))
    (decreases n) =
  if n = 0 then ()
  else if s = n - 1 then ()
  else enumerate_mem #count (n - 1) s

let all_states_mem (#count:state_count) (s:state count)
  : Lemma (memP s (all_states #count)) =
  enumerate_mem #count count s

let add_unique (#count:state_count)
  (x:state count) (xs:list (state count)) : Tot (list (state count)) =
  if mem x xs then xs else x::xs

let add_unique_mem (#count:state_count)
  (x y:state count) (xs:list (state count))
  : Lemma (memP y (add_unique x xs) <==>
      y == x \/ memP y xs) =
  mem_memP x xs;
  if mem x xs then () else ()

let rec union_unique (#count:state_count)
  (xs:list (state count)) (ys:list (state count))
  : Tot (list (state count))
    (decreases xs) =
  match xs with
  | [] -> ys
  | x::tl -> union_unique tl (add_unique x ys)

let rec union_unique_mem (#count:state_count)
  (xs ys:list (state count)) (y:state count)
  : Lemma (ensures (memP y (union_unique xs ys) <==>
      memP y xs \/ memP y ys))
    (decreases xs) =
  match xs with
  | [] -> ()
  | x::tl ->
      add_unique_mem x y ys;
      union_unique_mem tl (add_unique x ys) y;
      ()

type edge (count:state_count) = state count -> state count -> Tot bool

let reverse_edge (#count:state_count)
  (next:edge count) : edge count =
  fun x y -> next y x

let successors (#count:state_count)
  (next:edge count) (s:state count) : Tot (list (state count)) =
  filter (fun t -> next s t) (all_states #count)

let successors_mem (#count:state_count)
  (next:edge count) (s t:state count)
  : Lemma (requires (next s t))
    (ensures (memP t (successors next s))) =
  mem_filter (fun u -> next s u) (all_states #count) t;
  all_states_mem #count t;
  ()

let predecessors (#count:state_count)
  (next:edge count) (target:state count) : Tot (list (state count)) =
  successors (reverse_edge next) target

let predecessors_mem (#count:state_count)
  (next:edge count) (source target:state count)
  : Lemma (requires (next source target))
    (ensures (memP source (predecessors next target))) =
  successors_mem (reverse_edge next) target source;
  ()

let rec expand (#count:state_count)
  (next:edge count) (xs:list (state count))
  : Tot (list (state count))
    (decreases xs) =
  match xs with
  | [] -> []
  | x::tl -> union_unique (successors next x) (expand next tl)

let rec expand_mem (#count:state_count)
  (next:edge count) (xs:list (state count))
  (source target:state count)
  : Lemma (requires (memP source xs /\ next source target))
    (ensures (memP target (expand next xs)))
    (decreases xs) =
  match xs with
  | [] -> ()
  | x::tl ->
      if source = x then begin
        successors_mem next x target;
        union_unique_mem (successors next x) (expand next tl) target;
        ()
      end else begin
        expand_mem next tl source target;
        union_unique_mem (successors next x) (expand next tl) target;
        ()
      end

let close_once (#count:state_count)
  (next:edge count) (seen:list (state count))
  : Tot (list (state count)) =
  union_unique (expand next seen) seen

let closed (#count:state_count)
  (next:edge count) (seen:list (state count)) : prop =
  forall s t. memP s seen /\ next s t ==> memP t seen

let stable_closed (#count:state_count)
  (next:edge count) (seen:list (state count))
  : Lemma (requires (close_once next seen = seen))
    (ensures (closed next seen)) =
  introduce forall (s:state count) (t:state count).
    memP s seen /\ next s t ==> memP t seen
  with (
    introduce _ ==> _
    with (
      expand_mem next seen s t;
      union_unique_mem (expand next seen) seen t;
      ()
    )
  )

let edge_relation (#count:state_count) (next:edge count)
  : state count -> state count -> prop =
  fun x y -> next x y

let stable_path_member (#count:state_count)
  (next:edge count) (seen:list (state count))
  (start finish:state count)
  (hclosed:squash (closed next seen))
  : Lemma (requires (memP start seen /\
      closure (edge_relation next) start finish))
    (ensures (memP finish seen)) =
  FStar.ReflexiveTransitiveClosure.stable_on_closure
    (edge_relation next)
    (fun s -> memP s seen)
    hclosed;
  ()

let simulation_closure (#a:Type) (#count:state_count)
  (concrete_step:a -> a -> prop)
  (alpha:a -> state count)
  (next:edge count)
  (x y:a)
  : Lemma (requires (
      closure concrete_step x y /\
      (forall u v. concrete_step u v ==>
        edge_relation next (alpha u) (alpha v))))
    (ensures (closure (edge_relation next) (alpha x) (alpha y))) =
  FStar.ReflexiveTransitiveClosure.induct
    concrete_step
    (fun u v -> closure (edge_relation next) (alpha u) (alpha v))
    (fun u -> ())
    (fun u v ->
      FStar.ReflexiveTransitiveClosure.closure_step
        (edge_relation next) (alpha u) (alpha v))
    (fun u v w -> ())
  x y ();
  ()

let invariant_on_closure (#a:Type)
  (concrete_step:a -> a -> prop)
  (invariant:a -> prop)
  (x y:a)
  (hstable:squash (forall u v.
    invariant u /\ concrete_step u v ==> invariant v))
  : Lemma (requires (invariant x /\ closure concrete_step x y))
    (ensures (invariant y)) =
  FStar.ReflexiveTransitiveClosure.stable_on_closure
    concrete_step invariant hstable;
  ()

let invariant_excludes_bad (#a:Type)
  (concrete_step:a -> a -> prop)
  (invariant:a -> prop)
  (bad:a -> prop)
  (start finish:a)
  (hstart:invariant start)
  (hstable:squash (forall u v.
    invariant u /\ concrete_step u v ==> invariant v))
  (hno_bad:squash (forall u. invariant u ==> ~ (bad u)))
  : Lemma (requires (closure concrete_step start finish /\ bad finish))
    (ensures False) =
  invariant_on_closure concrete_step invariant start finish hstable;
  hno_bad;
  ()

let closure_reverse (#a:Type) (next:binrel a)
  (x y:a)
  : Lemma (requires (closure next x y))
    (ensures (closure (fun u v -> next v u) y x)) =
  FStar.ReflexiveTransitiveClosure.induct
    next
    (fun u v -> closure (fun p q -> next q p) v u)
    (fun u -> ())
    (fun u v ->
      FStar.ReflexiveTransitiveClosure.closure_step
        (fun p q -> next q p) v u)
    (fun u v w -> ())
    x y ();
  ()

type reach_result (count:state_count) =
  // Exhausted is deliberately separate: it cannot justify Unreachable.
  | Stable of list (state count)
  | Exhausted of list (state count)

type verdict (count:state_count) =
  | Unreachable of list (state count)
  | Reachable of list (state count)
  | Unknown of list (state count)

let verdict_states (#count:state_count)
  (result:verdict count) : Tot (list (state count)) =
  match result with
  | Unreachable states -> states
  | Reachable states -> states
  | Unknown states -> states

let rec explore (#count:state_count)
  (next:edge count)
  (fuel:nat)
  (seen:list (state count))
  : Tot (reach_result count)
    (decreases fuel) =
  let next_seen = close_once next seen in
  if next_seen = seen then Stable seen
  else if fuel = 0 then Exhausted next_seen
  else explore next (fuel - 1) next_seen

let rec explore_stable_closed (#count:state_count)
  (next:edge count) (fuel:nat)
  (seen final:list (state count))
  : Lemma (requires (explore next fuel seen == Stable final))
    (ensures (closed next final))
    (decreases fuel) =
  let next_seen = close_once next seen in
  if next_seen = seen then begin
    stable_closed next seen;
    ()
  end else if fuel = 0 then
    ()
  else
    explore_stable_closed next (fuel - 1) next_seen final

let rec explore_stable_contains (#count:state_count)
  (next:edge count) (fuel:nat)
  (seen final:list (state count)) (x:state count)
  : Lemma (requires (
      explore next fuel seen == Stable final /\
      memP x seen))
    (ensures (memP x final))
    (decreases fuel) =
  let next_seen = close_once next seen in
  if next_seen = seen then
    ()
  else if fuel = 0 then
    ()
  else begin
    union_unique_mem (expand next seen) seen x;
    explore_stable_contains next (fuel - 1) next_seen final x
  end

let stable_checker_sound (#a:Type) (#count:state_count)
  (concrete_step:a -> a -> prop)
  (alpha:a -> state count)
  (next:edge count)
  (bad:a -> prop)
  (abstract_bad:state count -> prop)
  (fuel:nat)
  (start finish:a)
  (states:list (state count))
  : Lemma (requires (
      explore next fuel [alpha start] == Stable states /\
      (forall (s:state count). memP s states ==> ~ (abstract_bad s)) /\
      (forall u v. concrete_step u v ==>
        edge_relation next (alpha u) (alpha v)) /\
      (forall u. bad u ==> abstract_bad (alpha u)) /\
      closure concrete_step start finish /\
      bad finish))
    (ensures False) =
  explore_stable_closed next fuel [alpha start] states;
  explore_stable_contains next fuel [alpha start] states (alpha start);
  simulation_closure concrete_step alpha next start finish;
  stable_path_member next states (alpha start) (alpha finish) ();
  ()

let rec any_bad (#count:state_count)
  (bad:state count -> Tot bool)
  (states:list (state count)) : Tot bool
  (decreases states) =
  match states with
  | [] -> false
  | s::tl -> if bad s then true else any_bad bad tl

let rec first_bad (#count:state_count)
  (bad:state count -> Tot bool)
  (states:list (state count)) : Tot (option (state count))
  (decreases states) =
  match states with
  | [] -> None
  | s::tl -> if bad s then Some s else first_bad bad tl

let rec first_bad_some (#count:state_count)
  (bad:state count -> Tot bool)
  (states:list (state count)) (s:state count)
  : Lemma (requires (first_bad bad states == Some s))
    (ensures (memP s states /\ bad s))
    (decreases states) =
  match states with
  | [] -> ()
  | h::tl ->
      if bad h then () else first_bad_some bad tl s

let rec first_bad_none (#count:state_count)
  (bad:state count -> Tot bool)
  (states:list (state count))
  : Lemma (requires (first_bad bad states == None))
    (ensures (any_bad bad states = false))
    (decreases states) =
  match states with
  | [] -> ()
  | h::tl ->
      if bad h then () else first_bad_none bad tl

let verdict_first_bad_sound (#count:state_count)
  (bad:state count -> Tot bool)
  (result:verdict count) (s:state count)
  : Lemma (requires (first_bad bad (verdict_states result) == Some s))
    (ensures (memP s (verdict_states result) /\ bad s)) =
  first_bad_some bad (verdict_states result) s;
  ()

let rec any_bad_member (#count:state_count)
  (bad:state count -> Tot bool)
  (states:list (state count)) (s:state count)
  : Lemma (requires (
      memP s states /\ any_bad bad states = false))
    (ensures (~ (bad s)))
    (decreases states) =
  match states with
  | [] -> ()
  | h::tl ->
      if bad h then ()
      else if s = h then ()
      else any_bad_member bad tl s

let no_bad_of_any_bad_false (#count:state_count)
  (bad:state count -> Tot bool)
  (states:list (state count))
  : Lemma (requires (any_bad bad states = false))
    (ensures (forall (s:state count).
      memP s states ==> ~ (bad s))) =
  introduce forall (s:state count). memP s states ==> ~ (bad s)
  with (
    introduce _ ==> _
    with (any_bad_member bad states s)
  )

let classify (#count:state_count)
  (bad:state count -> Tot bool)
  (result:reach_result count) : Tot (verdict count) =
  match result with
  | Exhausted states -> Unknown states
  | Stable states ->
      if any_bad bad states then Reachable states else Unreachable states

let classify_unreachable (#count:state_count)
  (bad:state count -> Tot bool)
  (states:list (state count))
  : Lemma (requires (classify bad (Stable states) ==
      Unreachable states))
    (ensures (forall (s:state count).
      memP s states ==> ~ (bad s))) =
  no_bad_of_any_bad_false bad states

let check_bad_fuel (#count:state_count)
  (next:edge count)
  (bad:state count -> Tot bool)
  (fuel:nat)
  (start:state count) : Tot (verdict count) =
  classify bad (explore next fuel [start])

let check (#count:state_count)
  (next:edge count) (start:state count)
  : Tot (reach_result count) =
  explore next count [start]

let check_bad (#count:state_count)
  (next:edge count)
  (bad:state count -> Tot bool)
  (start:state count) : Tot (verdict count) =
  check_bad_fuel next bad count start

let unreachable_checker_sound (#a:Type) (#count:state_count)
  (concrete_step:a -> a -> prop)
  (alpha:a -> state count)
  (next:edge count)
  (concrete_bad:a -> prop)
  (abstract_bad:state count -> Tot bool)
  (fuel:nat)
  (start finish:a)
  (states:list (state count))
  : Lemma (requires (
      classify abstract_bad (explore next fuel [alpha start]) ==
        Unreachable states /\
      (forall u v. concrete_step u v ==>
        edge_relation next (alpha u) (alpha v)) /\
      (forall u. concrete_bad u ==> abstract_bad (alpha u)) /\
      closure concrete_step start finish /\
      concrete_bad finish))
    (ensures False) =
  assert (explore next fuel [alpha start] == Stable states);
  classify_unreachable abstract_bad states;
  stable_checker_sound
    concrete_step alpha next concrete_bad
    (fun s -> abstract_bad s)
    fuel start finish states;
  ()

let check_bad_sound (#a:Type) (#count:state_count)
  (concrete_step:a -> a -> prop)
  (alpha:a -> state count)
  (next:edge count)
  (concrete_bad:a -> prop)
  (abstract_bad:state count -> Tot bool)
  (start finish:a)
  (states:list (state count))
  : Lemma (requires (
      check_bad next abstract_bad (alpha start) ==
        Unreachable states /\
      (forall u v. concrete_step u v ==>
        edge_relation next (alpha u) (alpha v)) /\
      (forall u. concrete_bad u ==> abstract_bad (alpha u)) /\
      closure concrete_step start finish /\
      concrete_bad finish))
    (ensures False) =
  unreachable_checker_sound
    concrete_step alpha next concrete_bad abstract_bad
    count start finish states

let backward_checker_sound (#count:state_count)
  (next:edge count)
  (start target:state count)
  (states:list (state count))
  : Lemma (requires (
      check_bad (reverse_edge next) (fun s -> s = start) target ==
        Unreachable states /\
      closure (edge_relation next) start target))
    (ensures False) =
  closure_reverse (edge_relation next) start target;
  check_bad_sound
    (fun u v -> edge_relation next v u)
    (fun s -> s)
    (reverse_edge next)
    (fun s -> s == start)
    (fun s -> s = start)
    target start states;
  ()
