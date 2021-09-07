open Core
open Grammar
open Task
open Task_with_data

(* open Utils *)
open Program_with_data
module Heap = Pairing_heap
module Varmap = Map.Make (String)

type solution_ctx = {
  known_vars : task_val Varmap.t;
  unknown_vars : task_val Varmap.t;
  operations : program_block list;
}

let create_start_solution (td : task_def) : solution_ctx =
  {
    known_vars =
      Varmap.of_alist_exn
      @@ List.mapi
           ~f:(fun i tv -> ("$i" ^ string_of_int i, new task_val tv#get_ty tv#get_values 1.))
           td.train_inputs;
    unknown_vars =
      Varmap.of_alist_exn
      @@ [ ("$out", new task_val td.train_outputs#get_ty td.train_outputs#get_values 0.) ];
    operations = [];
  }

let enumeration_timeout = ref Float.max_value

let enumeration_timed_out () = Float.( > ) (Unix.time ()) !enumeration_timeout

let set_enumeration_timeout dt = enumeration_timeout := Unix.time () +. dt

let get_candidates_for_var (_sol_ctx : solution_ctx) (_key : string) (_value : task_val)
    (_g : contextual_grammar) =
  []

let enumerate_for_task (g : contextual_grammar) ?(_verbose = true)
    ~timeout td maximumFrontier : hit_result list * int =
  (* Returns, for each task, (program,logPrior) as well as the total number of enumerated programs *)
  set_enumeration_timeout timeout;

  let start_solution_ctx = create_start_solution td in

  (* Store the hits in a priority queue *)
  (* We will only ever maintain maximumFrontier best solutions *)
  let hits =
    Heap.create
      ~cmp:(fun h1 h2 ->
        Float.compare (h1.hit_likelihood +. h1.hit_prior) (h2.hit_likelihood +. h2.hit_prior))
      ()
  in

  (* let startTime = Time.now () in *)

  let total_number_of_enumerated_programs = ref 0 in

  let pq =
    Heap.create
      ~cmp:(fun s1 s2 ->
        let open Float in
        let c = fst s1 -. fst s2 in
        if c < 0. then -1 else if c > 0. then 1 else 0)
      ()
  in
  Varmap.iteri start_solution_ctx.known_vars ~f:(fun ~key ~data ->
      List.iter (get_candidates_for_var start_solution_ctx key data g) ~f:(fun (score, candidate) ->
          Heap.add pq (score, (start_solution_ctx, candidate))));
  Varmap.iteri start_solution_ctx.unknown_vars ~f:(fun ~key ~data ->
      List.iter (get_candidates_for_var start_solution_ctx key data g) ~f:(fun (score, candidate) ->
          Heap.add pq (score, (start_solution_ctx, candidate))));

  while not (enumeration_timed_out ()) && Heap.length pq > 0 && Heap.length hits < maximumFrontier do
    let (_score, (_s_ctx, _candidate)) = Heap.pop_exn pq in
    ()
  done;

  (Heap.to_list hits, !total_number_of_enumerated_programs)
