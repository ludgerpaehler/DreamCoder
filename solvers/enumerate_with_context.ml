open Grammar
open Task
open Task_with_context
open Enumeration
open Core
open Utils
open Program

let enumerate_for_task (g : contextual_grammar) ?(verbose = true) ~maxFreeParameters
    ?(budgetIncrement = 1.) ?(lowerBound = 0.) ?(upperBound = 99.) ?(nc = 1) ~timeout
    (* tasks and maximum frontier sizes *)
      (tf : task_ctx * int) : hit_result list * int =
  (* Returns, for each task, (program,logPrior) as well as the total number of enumerated programs *)
  set_enumeration_timeout timeout;

  let maximumFrontier = snd tf in
  let t_ctx = fst tf in

  let request = t_ctx.task.task_type in

  (* Store the hits in a priority queue *)
  (* We will only ever maintain maximumFrontier best solutions *)
  let hits =
    Heap.create
      ~cmp:(fun h1 h2 ->
        Float.compare (h1.hit_likelihood +. h1.hit_prior) (h2.hit_likelihood +. h2.hit_prior))
      ()
  in

  let lower_bound = ref lowerBound in

  let startTime = Time.now () in

  let total_number_of_enumerated_programs = ref 0 in

  while
    (not (enumeration_timed_out ()))
    && Heap.length hits < maximumFrontier
    && Float.( <= ) (!lower_bound +. budgetIncrement) upperBound
  do
    let number_of_enumerated_programs = ref 0 in
    let final_results =
      (* Returns a list of "final results" *)
      (* Each final result is [Array.map ~f:Heap.to_list hits] *)
      (* We flatten it to get a list of arrays of heaps *)
      enumerate_programs ~maxFreeParameters ~nc g request !lower_bound
        (!lower_bound +. budgetIncrement)
        ~final:(fun () ->
          (* Printf.eprintf "%d\n" !number_of_enumerated_programs; flush_everything(); *)
          [ (Heap.to_list hits, !number_of_enumerated_programs) ])
        (fun p logPrior ->
          incr number_of_enumerated_programs;
          incr total_number_of_enumerated_programs;

          let mdl = 0. -. logPrior in

          assert (Float.( <= ) !lower_bound mdl);
          assert (Float.( < ) mdl (budgetIncrement +. !lower_bound));

          let logLikelihood = t_ctx.task.log_likelihood p in
          if is_valid logLikelihood then (
            let dt = Time.abs_diff startTime (Time.now ()) |> Time.Span.to_sec in
            Heap.add hits
              {
                hit_program = string_of_program p;
                hit_prior = logPrior;
                hit_likelihood = logLikelihood;
                hit_time = dt;
              };
            while Heap.length hits > maximumFrontier do
              Heap.remove_top hits
            done;
            if verbose then
              Printf.eprintf "\t(ocaml) HIT %s w/ %s\n" t_ctx.task.name (string_of_program p)))
      |> List.concat
    in

    if nc > 1 then
      (* merge the results from each of the parallel processes *)
      final_results
      |> List.iter ~f:(fun (new_results, number_enumerated_here) ->
             total_number_of_enumerated_programs :=
               !total_number_of_enumerated_programs + number_enumerated_here;

             List.iter new_results ~f:(fun element ->
                 if not (Heap.mem hits ~equal:equal_hit_result element) then (
                   Heap.add hits element;
                   if Heap.length hits > maximumFrontier then Heap.remove_top hits)));

    lower_bound := budgetIncrement +. !lower_bound
  done;

  (Heap.to_list hits, !total_number_of_enumerated_programs)
