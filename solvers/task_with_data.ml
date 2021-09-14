open Type
open Task
open Utils
open Core

type match_result = Strict' | Pattern' | TypeOnly' | NoMatch'

let minimal_match a b =
  match (a, b) with
  | NoMatch', _ -> NoMatch'
  | _, NoMatch' -> NoMatch'
  | TypeOnly', _ -> TypeOnly'
  | _, TypeOnly' -> TypeOnly'
  | Pattern', _ -> Pattern'
  | Strict', t -> t

class task_v (ty' : tp) (values' : unit ref list) =
  object
    val ty = ty'

    val values = values'

    method get_ty = ty

    method get_values = values
  end

class task_val ty' values' (known_share' : float) =
  object
    inherit task_v ty' values'

    val mutable known_share = known_share'

    method get_matching_seq =
      Seq.map
        (fun rv ->
          let matcher (other : unit ref) =
            if Poly.equal (magical !rv) (magical !other) then Strict' else NoMatch'
          in
          matcher)
        (Caml.List.to_seq values)
  end

class no_data_task_val ty' =
  object
    inherit task_val ty' [] 0.
  end

type task_def = { task : task; train_inputs : task_v list; train_outputs : task_v }

let build_task (handler : ?timeout:float -> string -> tp -> ('a list * 'b) list -> task) timeout
    name task_type examples test_examples : task_def =
  {
    task = handler ~timeout name task_type (examples @ test_examples);
    train_inputs =
      (let inputs = examples |> List.map ~f:fst in
       arguments_of_type task_type
       |> List.mapi ~f:(fun i ty ->
              new task_v
                ty
                (List.map ~f:(fun input_vals -> ref @@ magical @@ List.nth input_vals i) inputs)));
    train_outputs =
      examples
      |> List.map ~f:(fun out_val -> ref @@ magical @@ snd out_val)
      |> new task_v (return_of_type task_type);
  }
