open Grammar
open Utils
open Core
open Type
open Task_with_data
open Task
open Enumerate_with_data

let load_problems channel =
  let open Yojson.Basic.Util in
  let j = Yojson.Basic.from_channel channel in
  let g = j |> member "DSL" in
  let g =
    try deserialize_grammar g |> make_dummy_contextual with _ -> deserialize_contextual_grammar g
  in

  let timeout =
    try j |> member "programTimeout" |> to_number
    with _ ->
      let defaultTimeout = 0.1 in
      Printf.eprintf "\t(ocaml) WARNING: programTimeout not set. Defaulting to %f.\n" defaultTimeout;
      defaultTimeout
  in

  (* Automatic differentiation parameters *)
  let maxParameters = try j |> member "maxParameters" |> to_int with _ -> 99 in

  let rec unpack x =
    try magical (x |> to_int)
    with _ -> (
      try magical (x |> to_number)
      with _ -> (
        try magical (x |> to_bool)
        with _ -> (
          try
            let v = x |> to_string in
            if String.length v = 1 then magical v.[0] else magical v
          with _ -> (
            try x |> to_list |> List.map ~f:unpack |> magical
            with _ -> raise (Failure "could not unpack")))))
  in

  let t = j |> member "task" in
  let e = t |> member "examples" |> to_list in
  let task_type = t |> member "request" |> deserialize_type in
  let examples =
    e
    |> List.map ~f:(fun ex ->
           (ex |> member "inputs" |> to_list |> List.map ~f:unpack, ex |> member "output" |> unpack))
  in
  let maximum_frontier = t |> member "maximumFrontier" |> to_int in
  let name = t |> member "name" |> to_string in
  let test_examples =
    t |> member "test_examples" |> to_list
    |> List.map ~f:(fun ex ->
           (ex |> member "inputs" |> to_list |> List.map ~f:unpack, ex |> member "output" |> unpack))
  in

  let task =
    let handler =
      try
        let special = t |> member "specialTask" |> to_string in
        match special |> Hashtbl.find task_handler with
        | Some handler -> handler (t |> member "extras")
        | None ->
            Printf.eprintf " (ocaml) FATAL: Could not find handler for %s\n" special;
            exit 1
      with _ -> supervised_task
    in
    build_task handler timeout name task_type examples test_examples
  in

  let verbose = try j |> member "verbose" |> to_bool with _ -> false in

  (* let _ : unit = try
         shatter_factor := (j |> member "shatter" |> to_int)
       with _ -> ()
     in *)
  let timeout = j |> member "timeout" |> to_number in
  let nc = try j |> member "nc" |> to_int with _ -> 1 in
  (task, maximum_frontier, g, maxParameters, nc, timeout, verbose)

let export_frontiers number_enumerated td solutions : string =
  let open Yojson.Basic in
  let serialization : Yojson.Basic.t =
    `Assoc
      [
        ("number_enumerated", `Int number_enumerated);
        ( td.task.name,
          `List
            (solutions
            |> List.map ~f:(fun s ->
                   `Assoc
                     [
                       ("program", `String s.hit_program);
                       ("time", `Float s.hit_time);
                       ("logLikelihood", `Float s.hit_likelihood);
                       ("logPrior", `Float s.hit_prior);
                     ])) );
      ]
  in
  pretty_to_string serialization

let (_ : unit) =
  let task, maximum_frontier, g, _mfp, _nc, timeout, _verbose = load_problems Stdlib.stdin in
  let solutions, number_enumerated = enumerate_for_task ~timeout g task maximum_frontier in
  export_frontiers number_enumerated task solutions |> print_string
