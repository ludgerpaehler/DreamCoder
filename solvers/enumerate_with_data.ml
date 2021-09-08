open Core
open Grammar
open Task
open Task_with_data
open Type
open Utils

(* open Utils *)
open Program
open Enumeration
open Program_with_data
module Heap = Pairing_heap

type solution_ctx = {
  known_vars : (string, task_val) Hashtbl.t;
  unknown_vars : (string, task_val) Hashtbl.t;
  operations : program_block list ref;
  created_vars : int ref;
}

type block_prototype = {
  state : best_first_state;
  input_vals : string list;
  output_vals : string list;
}

let initial_block_prototype request (g : grammar) inputs outputs =
  { state = initial_best_first_state request g; input_vals = inputs; output_vals = outputs }

let create_start_solution (td : task_def) : solution_ctx =
  {
    known_vars =
      Hashtbl.of_alist_exn (module String)
      @@ List.mapi
           ~f:(fun i tv -> ("$i" ^ string_of_int i, new task_val tv#get_ty tv#get_values 1.))
           td.train_inputs;
    unknown_vars =
      Hashtbl.of_alist_exn (module String)
      @@ [ ("$out", new task_val td.train_outputs#get_ty td.train_outputs#get_values 0.) ];
    operations = ref [];
    created_vars = ref 0;
  }

let enumeration_timeout = ref Float.max_value

let enumeration_timed_out () = Float.( > ) (Unix.time ()) !enumeration_timeout

let set_enumeration_timeout dt = enumeration_timeout := Unix.time () +. dt

let get_candidates_for_known_var (_sol_ctx : solution_ctx) (_key : string) (_value : task_val)
    (_g : contextual_grammar) =
  []

let get_candidates_for_unknown_var (_sol_ctx : solution_ctx) (key : string) (value : task_val)
    (g : contextual_grammar) : block_prototype list =
  let target = value#get_ty in
  [ initial_block_prototype target g.no_context [] [ key ] ]

let block_state_violates_symmetry (state : best_first_state) =
  match state.skeleton with
  | Primitive (_, "FREE_VAR", _) -> true
  | _ -> state_violates_symmetry state

let block_state_successors ~maxFreeParameters cg state =
  let request, g =
    match follow_path state.skeleton state.path with
    | Primitive (t, "??", g) -> (t, !(g |> magical))
    | _ -> assert false
  in
  (* Printf.printf "request: %s\n" (string_of_type request); *)
  let context = state.context in
  let context, request = applyContext context request in

  match request with
  | TCon ("->", [ argument_type; return_type ], _) ->
      [
        {
          skeleton =
            modify_skeleton state.skeleton
              (Abstraction (primitive_unknown return_type g))
              state.path;
          path = state.path @ [ A argument_type ];
          free_parameters = state.free_parameters;
          context;
          cost = state.cost;
        };
      ]
  | _ ->
      let environment = path_environment state.path in
      let candidates =
        unifying_expressions g environment request context
        @ [
            ( Primitive (request, "FREE_VAR", ref (List.length environment |> magical)),
              [],
              context,
              g.logVariable );
          ]
      in
      candidates
      |> List.map ~f:(fun (candidate, argument_types, context, ll) ->
             let new_free_parameters = number_of_free_parameters candidate in
             let argument_requests =
               match candidate with
               | Index _ -> argument_types |> List.map ~f:(fun at -> (at, cg.variable_context))
               | Primitive (_, "FREE_VAR", _) -> []
               | _ ->
                   List.Assoc.find_exn cg.contextual_library candidate ~equal:program_equal
                   |> List.zip_exn argument_types
             in

             match argument_types with
             | [] ->
                 (* terminal - unwind the recursion *)
                 {
                   context;
                   cost = state.cost -. ll;
                   free_parameters = state.free_parameters + new_free_parameters;
                   path = unwind_path state.path;
                   skeleton = modify_skeleton state.skeleton candidate state.path;
                 }
             | _first_argument :: later_arguments ->
                 (* nonterminal *)
                 let application_template =
                   List.fold_left argument_requests ~init:candidate ~f:(fun e (a, at) ->
                       Apply (e, primitive_unknown a at))
                 in
                 {
                   skeleton = modify_skeleton state.skeleton application_template state.path;
                   cost = state.cost -. ll;
                   free_parameters = state.free_parameters + new_free_parameters;
                   context;
                   path = state.path @ List.map ~f:(fun _ -> L) later_arguments @ [ R ];
                 })
      |> List.filter ~f:(fun new_state ->
             (not (block_state_violates_symmetry new_state))
             && new_state.free_parameters <= maxFreeParameters)

let capture_free_vars p =
  let rec r p c ts =
    match p with
    | Apply (f, x) ->
        let f', c', ts' = r f c ts in
        let x', c'', ts'' = r x c' ts' in
        (Apply (f', x'), c'', ts'')
    | Abstraction b ->
        let b', c', ts' = r b c ts in
        (Abstraction b', c', ts')
    | Primitive (t, "FREE_VAR", depth) -> (Index ((!depth |> magical) + c), c + 1, t :: ts)
    | Primitive (_, _, _) | Index _ | Invented (_, _) -> (p, c, ts)
  in
  let rec wrap p c = match c with 0 -> p | _ -> wrap (Abstraction p) (c - 1) in
  let p, free_c, ts = r p 0 [] in
  (wrap p free_c, ts)

let enumerate_for_task (g : contextual_grammar) ?(_verbose = true) ~timeout td maximumFrontier :
    hit_result list * int =
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
  let maxFreeParameters = 2 in

  let pq =
    Heap.create
      ~cmp:(fun s1 s2 ->
        let open Float in
        let c = (snd s1).state.cost -. (snd s2).state.cost in
        if c < 0. then -1 else if c > 0. then 1 else 0)
      ()
  in
  Hashtbl.iteri start_solution_ctx.known_vars ~f:(fun ~key ~data ->
      List.iter (get_candidates_for_known_var start_solution_ctx key data g) ~f:(fun candidate ->
          Heap.add pq (start_solution_ctx, candidate)));
  Hashtbl.iteri start_solution_ctx.unknown_vars ~f:(fun ~key ~data ->
      List.iter (get_candidates_for_unknown_var start_solution_ctx key data g) ~f:(fun candidate ->
          Heap.add pq (start_solution_ctx, candidate)));

  while
    (not (enumeration_timed_out ())) && Heap.length pq > 0 && Heap.length hits < maximumFrontier
  do
    let s_ctx, bp = Heap.pop_exn pq in
    block_state_successors ~maxFreeParameters g bp.state
    |> List.iter ~f:(fun child ->
           (* let open Float in *)
           if state_finished child then (
             let p, ts = capture_free_vars child.skeleton in

             let new_vars =
               ts
               |> List.map ~f:(fun t ->
                      let ntv = new no_data_task_val t in
                      let key = "v" ^ string_of_int !(s_ctx.created_vars) in
                      s_ctx.created_vars := !(s_ctx.created_vars) + 1;
                      Hashtbl.add_exn s_ctx.unknown_vars ~key ~data:ntv;
                      key)
             in
             let new_block = { p; inputs = new_vars; outputs = bp.output_vals } in
             s_ctx.operations := new_block :: !(s_ctx.operations);
             ())
           else
             Heap.add pq
               (s_ctx, { state = child; input_vals = bp.input_vals; output_vals = bp.output_vals }))
  done;

  (Heap.to_list hits, !total_number_of_enumerated_programs)
