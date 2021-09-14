open Core
open Grammar
open Task
open Task_with_data
open Type
open Utils
open Program
open Enumeration
open Program_with_data
open Timeout
module Heap = Pairing_heap

module SolutionCtx = struct
  let try_evaluate_program p xs timeout =
    try
      run_for_interval timeout (fun () ->
          [
            ref @@ magical
            @@ run_lazy_analyzed_with_arguments p (List.map xs ~f:(fun ri -> !ri |> magical));
          ])
      (* TODO: allow several return values from the block *)
    with
    (* We have to be a bit careful with exceptions if the
       * synthesized program generated an exception, then we just
       * terminate w/ false but if the enumeration timeout was
       * triggered during program evaluation, we need to pass the
       * exception on
    *)
    | UnknownPrimitive n -> raise (Failure ("Unknown primitive: " ^ n))
    | EnumerationTimeout -> raise EnumerationTimeout
    | _ -> None

  type t = {
    known_vars : (string, task_val) Hashtbl_intf.Hashtbl.t;
    unknown_vars : (string, task_val) Hashtbl_intf.Hashtbl.t;
    example_count : int;
    mutable operations : program_block list;
    mutable created_vars : int;
    parent : t option;
    mutable children : t list;
    timeout : float;
  }

  let create ?parent' (known_vars' : (string * task_val) list)
      (unknown_vars' : (string * task_val) list) timeout' =
    {
      known_vars = Hashtbl.of_alist_exn (module String) known_vars';
      unknown_vars = Hashtbl.of_alist_exn (module String) unknown_vars';
      example_count =
        (match unknown_vars' with [] -> 0 | (_, tv) :: _ -> List.length tv#get_values);
      operations = [];
      created_vars = 0;
      parent = parent';
      children = [];
      timeout = timeout';
    }

  let iter_known_vars sc = Hashtbl.iteri sc.known_vars

  let iter_unknown_vars sc = Hashtbl.iteri sc.unknown_vars

  let map_filter_known_vars sc = Hashtbl.filter_mapi sc.known_vars

  let get_known_var sc k = Hashtbl.find_exn sc.known_vars k

  let get_unknown_var sc k = Hashtbl.find_exn sc.unknown_vars k

  let create_next_var sc =
    sc.created_vars <- sc.created_vars + 1;
    sc.created_vars - 1

  let add_unknown_var sc key var = Hashtbl.add_exn sc.unknown_vars ~key ~data:var

  let get_matches sc keys =
    let rec get_matches' ks prev_matched_ks prev_missed_ks =
      match ks with
      | [] -> prev_matched_ks
      | k :: ks' ->
          let kv = Hashtbl.find_exn sc.unknown_vars k in
          let _matcher_seq = kv#get_matching_seq in
          0 :: get_matches' ks' prev_matched_ks (k :: prev_missed_ks)
    in
    let _matches = get_matches' keys [] [] in
    [ 1 ]

  let add_new_block sc block =
    let unknown_inputs =
      List.filter block.inputs ~f:(fun key -> is_some @@ Hashtbl.find sc.unknown_vars key)
    in
    if List.is_empty unknown_inputs then (
      let inputs = List.map block.inputs ~f:(fun key -> (get_known_var sc key)#get_values) in
      let input_vals =
        List.fold inputs
          ~init:(List.init sc.example_count ~f:(fun _ -> []))
          ~f:(fun acc vals -> List.zip_exn acc vals |> List.map ~f:(fun (a, v) -> v :: a))
        |> List.map ~f:List.rev
      in
      let expected_outputs = List.map block.outputs ~f:(get_unknown_var sc) in
      let out_matchers = List.map expected_outputs ~f:(fun exp -> exp#get_matching_seq) in
      let p = analyze_lazy_evaluation block.p in

      let best_match, _outputs =
        let rec loop inputs out_matchers bm outs =
          match inputs with
          | [] -> (bm, [ List.rev outs ])
          | xs :: rest -> (
              let v = try_evaluate_program p xs sc.timeout in

              match v with
              | None -> (NoMatch', [])
              | _ -> (
                  let v = get_some v in
                  let rec loop_matchers (outs : unit ref list)
                      (matchers : (unit ref -> match_result) Seq.t list) res next_matchers =
                    match outs with
                    | [] -> (res, List.rev next_matchers)
                    | ov :: rest_out -> (
                        match matchers with
                        | [] -> raise (Failure "Dimentions mismatch")
                        | matcher :: rest_matchers -> (
                            match matcher () with
                            | Seq.Nil -> raise (Failure "Dimentions mismatch")
                            | Seq.Cons (matcher_func, next_matcher) -> (
                                let m = matcher_func ov in
                                match m with
                                | NoMatch' -> (NoMatch', [])
                                | _ ->
                                    loop_matchers rest_out rest_matchers (minimal_match res m)
                                      (next_matcher :: next_matchers))))
                  in
                  let m, next_matchers = loop_matchers v out_matchers Strict' [] in
                  match m with
                  | NoMatch' -> (NoMatch', [])
                  | _ -> loop rest next_matchers (minimal_match bm m) (v :: outs)))
        in

        loop input_vals out_matchers Strict' []
      in

      match best_match with
      | NoMatch' ->
          Printf.eprintf "No match: %s\n" (string_of_program block.p);
          Stdlib.flush_all ();
          ()
      | _ ->
          (* TODO: move variable to known ones and create a branch *)
          sc.operations <- block :: sc.operations;
          ())
    else sc.operations <- block :: sc.operations;
    let _matches = get_matches sc unknown_inputs in
    ()
end

type block_prototype = {
  state : best_first_state;
  input_vals : string list;
  output_vals : string list;
}

let initial_block_prototype request (g : grammar) inputs outputs =
  { state = initial_best_first_state request g; input_vals = inputs; output_vals = outputs }

let create_start_solution (td : task_def) timeout : SolutionCtx.t =
  SolutionCtx.create
    (List.mapi
       ~f:(fun i tv -> ("$i" ^ string_of_int i, new task_val tv#get_ty tv#get_values 1.))
       td.train_inputs)
    [ ("$out", new task_val td.train_outputs#get_ty td.train_outputs#get_values 0.) ]
    timeout

let get_candidates_for_known_var (_sol_ctx : SolutionCtx.t) (_key : string) (_value : task_val)
    (_g : contextual_grammar) =
  (* TODO: fill *)
  []

let get_candidates_for_unknown_var (_sol_ctx : SolutionCtx.t) (key : string) (value : task_val)
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

  let start_solution_ctx = create_start_solution td timeout in

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
  SolutionCtx.iter_known_vars start_solution_ctx ~f:(fun ~key ~data ->
      List.iter (get_candidates_for_known_var start_solution_ctx key data g) ~f:(fun candidate ->
          Heap.add pq (start_solution_ctx, candidate)));
  SolutionCtx.iter_unknown_vars start_solution_ctx ~f:(fun ~key ~data ->
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
                      let key = "v" ^ string_of_int (SolutionCtx.create_next_var s_ctx) in
                      SolutionCtx.add_unknown_var s_ctx key ntv;
                      key)
             in
             let new_block = { p; inputs = new_vars; outputs = bp.output_vals } in
             SolutionCtx.add_new_block s_ctx new_block;
             (* match_fields s_ctx new_vars; *)
             ())
           else
             Heap.add pq
               (s_ctx, { state = child; input_vals = bp.input_vals; output_vals = bp.output_vals }))
  done;

  (Heap.to_list hits, !total_number_of_enumerated_programs)
