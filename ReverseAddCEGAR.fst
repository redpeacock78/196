module ReverseAddCEGAR

#set-options "--fuel 20 --ifuel 20 --retry 10"

open ReverseAdd
open ReverseAddCarry
open ReverseAdd196
open ReverseAddBlockCarry
open ReverseAddFixedWidth
open ReverseAddRefinedProduct
open ReverseAddInvariant
open ReverseAddBoundary
open ReverseAddWitness
open AbstractReachability
open FStar.Classical
open FStar.List.Tot

type cegar_stage =
  | BlockCarry
  | ProductOneStep
  | FixedWidth of nat & nat

type stage_outcome =
  | StageUnreachable of cegar_stage
  | StageReachable of cegar_stage & nat
  | StageUnknown of cegar_stage

type cegar_result =
  | CegarUnreachable of cegar_stage
  | CegarReachable of cegar_stage & nat
  | CegarUnknown of cegar_stage
  | CegarRefined of cegar_stage & cegar_stage & nat & cegar_result

let stage_outcome_of_result (#count:state_count)
  (stage:cegar_stage)
  (bad:state count -> Tot bool)
  (result:verdict count) : Tot stage_outcome =
  match result with
  | Unreachable _ -> StageUnreachable stage
  | Reachable states ->
      begin match first_bad bad (verdict_states result) with
      | Some s -> StageReachable (stage, s)
      | None -> StageUnknown stage
      end
  | Unknown states ->
      begin match first_bad bad (verdict_states result) with
      | Some s -> StageReachable (stage, s)
      | None -> StageUnknown stage
      end

let stage_reachable_sound (#count:state_count)
  (stage:cegar_stage)
  (bad:state count -> Tot bool)
  (result:verdict count)
  (s:state count)
  : Lemma (requires (
      stage_outcome_of_result stage bad result ==
        StageReachable (stage, s)))
    (ensures (
      memP s (verdict_states result) /\ bad s)) =
  match result with
  | Unreachable _ -> ()
  | Reachable states ->
      assert (first_bad bad states == Some s);
      verdict_first_bad_sound bad (Reachable states) s
  | Unknown states ->
      assert (first_bad bad states == Some s);
      verdict_first_bad_sound bad (Unknown states) s

let stage_unknown_sound (#count:state_count)
  (stage:cegar_stage)
  (bad:state count -> Tot bool)
  (result:verdict count)
  : Lemma (requires (
      stage_outcome_of_result stage bad result == StageUnknown stage))
    (ensures (
      first_bad bad (verdict_states result) == None /\
      any_bad bad (verdict_states result) = false)) =
  match result with
  | Unreachable _ -> ()
  | Reachable states ->
      assert (first_bad bad states == None);
      first_bad_none bad states
  | Unknown states ->
      assert (first_bad bad states == None);
      first_bad_none bad states

let check_stage (stage:cegar_stage) : Tot stage_outcome =
  match stage with
  | BlockCarry ->
      stage_outcome_of_result
        BlockCarry (block_bad #2) block_196_one_step_verdict
  | ProductOneStep ->
      stage_outcome_of_result
        ProductOneStep refined_bad refined_196_one_step_verdict
  | FixedWidth (width, fuel) ->
      stage_outcome_of_result
        (FixedWidth (width, fuel))
        (fixed_bad width)
        (check_bad_fuel
          (fixed_edge width)
          (fixed_bad width)
          fuel
          (fixed_alpha width digits_196))

let rec run_cegar
  (stages:list cegar_stage)
  (fuel:nat) : Tot cegar_result
  (decreases fuel) =
  match stages with
  | [] -> CegarUnknown ProductOneStep
  | stage::tl ->
      if fuel = 0 then CegarUnknown stage
      else
        match check_stage stage with
        | StageUnreachable s -> CegarUnreachable s
        | StageUnknown s -> CegarUnknown s
        | StageReachable (s, counterexample) ->
            match tl with
            | [] -> CegarReachable (s, counterexample)
            | next::_ ->
                CegarRefined
                  (s, next, counterexample, run_cegar tl (fuel - 1))

let cegar_196_report : cegar_result =
  run_cegar [BlockCarry; ProductOneStep] 2

let block_counterexample_sound (s:state (block_count #2))
  : Lemma (requires (
      first_bad (block_bad #2) (verdict_states block_196_verdict) ==
        Some s))
    (ensures (
      memP s (verdict_states block_196_verdict) /\
      block_bad #2 s)) =
  first_bad_some (block_bad #2)
    (verdict_states block_196_verdict) s;
  ()

let block_one_step_counterexample_sound (s:state (block_count #2))
  : Lemma (requires (
      first_bad (block_bad #2)
        (verdict_states block_196_one_step_verdict) == Some s))
    (ensures (
      memP s (verdict_states block_196_one_step_verdict) /\
      block_bad #2 s)) =
  verdict_first_bad_sound
    (block_bad #2) block_196_one_step_verdict s;
  ()

let product_one_step_counterexample_sound
  (s:state (refined_count #2))
  : Lemma (requires (
      first_bad refined_bad
        (verdict_states refined_196_one_step_verdict) == Some s))
    (ensures (
      memP s (verdict_states refined_196_one_step_verdict) /\
      refined_bad s)) =
  verdict_first_bad_sound
    refined_bad refined_196_one_step_verdict s;
  ()

let trace_jump_witness_60744805 () : Lemma (
    exists (i:nat). 0 < i /\
      i <= length [5; 0; 8; 4; 4; 7; 0; 6] /\
      (trace_sum_at [5; 0; 8; 4; 4; 7; 0; 6] i >=
         trace_sum_at [5; 0; 8; 4; 4; 7; 0; 6] (i - 1) + 12 \/
       trace_sum_at [5; 0; 8; 4; 4; 7; 0; 6] (i - 1) >=
         trace_sum_at [5; 0; 8; 4; 4; 7; 0; 6] i + 12)) =
  trace_profile_60744805 ();
  assert (2 <= length [5; 0; 8; 4; 4; 7; 0; 6]);
  assert (trace_sum_at [5; 0; 8; 4; 4; 7; 0; 6] 2 == 15);
  assert (trace_sum_at [5; 0; 8; 4; 4; 7; 0; 6] 1 == 0);
  assert (15 >= 0 + 12);
  assert (trace_sum_at [5; 0; 8; 4; 4; 7; 0; 6] 2 >=
    trace_sum_at [5; 0; 8; 4; 4; 7; 0; 6] 1 + 12);
  assert (~ (forall (i:nat). 0 < i /\
    i <= length [5; 0; 8; 4; 4; 7; 0; 6] ==>
    ~(trace_sum_at [5; 0; 8; 4; 4; 7; 0; 6] i >=
       trace_sum_at [5; 0; 8; 4; 4; 7; 0; 6] (i - 1) + 12 \/
     trace_sum_at [5; 0; 8; 4; 4; 7; 0; 6] (i - 1) >=
       trace_sum_at [5; 0; 8; 4; 4; 7; 0; 6] i + 12)));
  assert (~ (forall (i:nat). ~(
    0 < i /\ i <= length [5; 0; 8; 4; 4; 7; 0; 6] /\
    (trace_sum_at [5; 0; 8; 4; 4; 7; 0; 6] i >=
       trace_sum_at [5; 0; 8; 4; 4; 7; 0; 6] (i - 1) + 12 \/
     trace_sum_at [5; 0; 8; 4; 4; 7; 0; 6] (i - 1) >=
       trace_sum_at [5; 0; 8; 4; 4; 7; 0; 6] i + 12))));
  not_forall_implies_exists #nat
    #(fun (i:nat) -> 0 < i /\
      i <= length [5; 0; 8; 4; 4; 7; 0; 6] /\
      (trace_sum_at [5; 0; 8; 4; 4; 7; 0; 6] i >=
         trace_sum_at [5; 0; 8; 4; 4; 7; 0; 6] (i - 1) + 12 \/
       trace_sum_at [5; 0; 8; 4; 4; 7; 0; 6] (i - 1) >=
         trace_sum_at [5; 0; 8; 4; 4; 7; 0; 6] i + 12))
    ();
  ()

let candidate_witness_60744805_boundary () : Lemma (
    trace_candidate_complement_witness
      [5; 0; 8; 4; 4; 7; 0; 6]) =
  trace_profile_60744805 ();
  assert (length (trace_digits [5; 0; 8; 4; 4; 7; 0; 6]) ==
    length [5; 0; 8; 4; 4; 7; 0; 6] + 1);
  assert (nth (trace_carries [5; 0; 8; 4; 4; 7; 0; 6])
    (length [5; 0; 8; 4; 4; 7; 0; 6]) == Some 1);
  assert (trace_sum_at [5; 0; 8; 4; 4; 7; 0; 6] 2 == 15);
  assert (trace_sum_at [5; 0; 8; 4; 4; 7; 0; 6] 1 == 0);
  assert (15 >= 0 + 12);
  assert (trace_sum_at [5; 0; 8; 4; 4; 7; 0; 6] 2 >=
    trace_sum_at [5; 0; 8; 4; 4; 7; 0; 6] 1 + 12);
  trace_jump_witness_60744805 ();
  eliminate exists (i:nat).
    0 < i /\ i <= length [5; 0; 8; 4; 4; 7; 0; 6] /\
    (trace_sum_at [5; 0; 8; 4; 4; 7; 0; 6] i >=
       trace_sum_at [5; 0; 8; 4; 4; 7; 0; 6] (i - 1) + 12 \/
     trace_sum_at [5; 0; 8; 4; 4; 7; 0; 6] (i - 1) >=
       trace_sum_at [5; 0; 8; 4; 4; 7; 0; 6] i + 12)
  with (
    assert (trace_candidate_complement_witness
      [5; 0; 8; 4; 4; 7; 0; 6]);
    ())

let candidate_boundary_sound_60744805 () : Lemma (
    ~ (trace_palindrome_candidate [5; 0; 8; 4; 4; 7; 0; 6]) /\
    trace_palindrome_obstruction_exists [5; 0; 8; 4; 4; 7; 0; 6]) =
  candidate_witness_60744805_boundary ();
  assert ([5; 0; 8; 4; 4; 7; 0; 6] <> []);
  trace_candidate_witness_implies_not_candidate
    [5; 0; 8; 4; 4; 7; 0; 6];
  trace_candidate_witness_implies_obstruction
    [5; 0; 8; 4; 4; 7; 0; 6];
  ()
