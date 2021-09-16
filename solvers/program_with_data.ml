
open Program
open Type
open Utils

type program_block = {
  p: program;
  inputs: string list;
  outputs: string list;
}

let copy = Primitive((t0 @> t0), "copy", ref (magical (fun x -> x)))
