open Yojson.Basic
open Dreamcoder.Helmholtz
open Dreamcoder.Dreaming

let (_ : unit) = run_job Stdlib.stdin |> remove_bad_dreams |> output_job |> to_channel Stdlib.stdout
