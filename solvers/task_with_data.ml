open Type
open Program
open Task

type task_val = { ty : tp; apply_fun : program -> task_val option }

let make_task_val ty _value = { ty; apply_fun = (fun _p -> None) }

type task_ctx = { task : task; train_inputs : task_val list list; train_outputs : task_val list }

let build_task (handler : ?timeout:float -> string -> tp -> ('a list * 'b) list -> task) timeout
    name task_type examples test_examples : task_ctx =
  {
    task = handler ~timeout name task_type (examples @ test_examples);
    train_inputs =
      examples |> List.map fst
      |> List.map (fun input_vals ->
             List.map2 make_task_val (arguments_of_type task_type) input_vals);
    train_outputs =
      examples |> List.map (fun example -> make_task_val (return_of_type task_type) (snd example));
  }
