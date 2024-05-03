open Jasmin
open Mopsa
open Sig.Abstraction.Stateless
open Universal.Ast
open Stubs.Ast
open Ast
open Jasmin.Wsize
module IntItv = Universal.Numeric.Values.Intervals.Integer.Value
module FltItv = Universal.Numeric.Values.Intervals.Float.I

let wsize_to_int = function
  | U8 -> 8
  | U16 -> 16
  | U32 -> 32
  | U64 -> 64
  | U128 -> 128
  | U256 -> 256

let wsize_to_z wsize = Z.of_int @@ wsize_to_int wsize

let wsize_to_range wsize =
  (Z.zero, Z.sub (Z.pow (Z.of_int 2) (wsize_to_int wsize)) (Z.of_int 1))

let range_of typ =
  Debug.debug ~channel:"Utils" "%a" pp_typ typ;
  match typ with
  | T_J_U size -> wsize_to_range size
  | T_int ->
      warn "range_of T_int type ";
      wsize_to_range U16
  | _ -> failwith "not implemented range_of"
