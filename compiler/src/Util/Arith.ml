(* * License
 * -----------------------------------------------------------------------
 * Copyright 2016--2017 IMDEA Software Institute
 * Copyright 2016--2017 Inria
 *
 * Permission is hereby granted, free of charge, to any person obtaining
 * a copy of this software and associated documentation files (the
 * "Software"), to deal in the Software without restriction, including
 * without limitation the rights to use, copy, modify, merge, publish,
 * distribute, sublicense, and/or sell copies of the Software, and to
 * permit persons to whom the Software is furnished to do so, subject to
 * the following conditions:
 *
 * The above copyright notice and this permission notice shall be
 * included in all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
 * EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
 * MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT.
 * IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY
 * CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT,
 * TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE
 * SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 * ----------------------------------------------------------------------- *)

(* * Utility functions (mostly for testing) *)

open Big_int
open Core_kernel.Std
open Util

(* ** Arithmetic
 * ------------------------------------------------------------------------ *)

(* only for testing, this is biased *)
let sample_bigint_insecure p =
  let rec go ~pos ~rem ~res =
    if eq_big_int rem zero_big_int then res
    else (
      let i = Random.bits () in
      go
        ~pos:(pos + 30)
        ~rem:(shift_right_towards_zero_big_int rem 30)
        ~res:(add_big_int (shift_left_big_int (big_int_of_int i) pos) res)
    )
  in mod_big_int (go ~pos:0 ~rem:p ~res:(big_int_of_int 0)) p

type big_int = Big_int.big_int

let big_int_of_sexp _bi =
  failwith "big_int_of_sexp: undefined"

let sexp_of_big_int _bi =
  failwith "sexp_of_big_int: undefined"

let compare_big_int = Big_int.compare_big_int

module Big_int_Infix = struct
  include Big_int
  let (+!)  = add_big_int
  let ( *!) = mult_big_int
  let (-!)  = sub_big_int
  let (^!)  = power_int_positive_int
  let (&!)  x i = extract_big_int x i (i + 1)
  let (>>!) x i = shift_right_big_int x i
  let (<!<) x i = shift_left_big_int x i
  let (===) = eq_big_int
  let (<!)  = lt_big_int
  let (<=!) = le_big_int
  let (%!)  = mod_big_int
end

let parse_big_int s =
  let cs = String.to_list s in
  let base,digits =
    match cs with
    | '0'::'x'::digits -> 16,digits
    | '0'::'b'::digits -> 2,digits
    | _                -> 10,cs
  in
  let base = Big_int.big_int_of_int base in
  let res = ref Big_int.zero_big_int in
  let rec go ds =
    match ds with
    | []      -> !res
    | '_'::ds -> go ds
    | d::ds   ->
      let open Big_int_Infix in
      res := !res *! base;
      let n =
        begin match d with
        | '0' -> 0
        | '1' -> 1
        | '2' -> 2
        | '3' -> 3
        | '4' -> 4
        | '5' -> 5
        | '6' -> 6
        | '7' -> 7
        | '8' -> 8
        | '9' -> 9
        | 'A' | 'a' -> 10
        | 'B' | 'b' -> 11
        | 'C' | 'c' -> 12
        | 'D' | 'd' -> 13
        | 'E' | 'e' -> 14
        | 'F' | 'f' -> 15
        | _ -> assert false
        end
      in
      let n = big_int_of_int n in
      assert (n <! base);
      res := !res +! n;
      go ds
  in
  go digits

let mod_pow_two n m = Big_int.(mod_big_int n (power_int_positive_int 2 m))

module U64 = struct
  open Unsigned
  include Unsigned.UInt64

  let bi_2_64 = Big_int_Infix.(2 ^! 64)
  let to_big_int x = big_int_of_string (UInt64.to_string x)
  let of_big_int x =
    UInt64.of_string
      (string_of_big_int (Big_int.mod_big_int x bi_2_64))
  let of_string s = of_big_int (big_int_of_string s)
  let max_val = of_string "0xffffffffffffffff"
  let is_zero x = compare (of_int 0) x = 0
  let is_one x  = compare (of_int 1) x = 0

  (* See: Volume 2B ... (ADD/ADC, ...) *)
  let add_carry x y cf_in =
    let x = if cf_in then UInt64.succ x else x in
    if x = UInt64.zero && cf_in then (
      (y,true)
    ) else (
      let c = UInt64.add x y in
      let cf = UInt64.compare c y < 0 in
      (c,cf)
    )

  (* See: Volume 2B 4-347 (SBB, Integer Subtraction with borrow) *)
  let sub_carry x y cf_in =
    let x = to_big_int x in
    let y_cf = if cf_in then unit_big_int else zero_big_int in
    let y = Big_int_Infix.(to_big_int y +! y_cf) in
    let z = Big_int_Infix.(x -! y) in
    if Big_int.sign_big_int z < 0 then (
      (of_big_int (Big_int_Infix.(bi_2_64 +! z)), true)
    ) else (
      (of_big_int z, false)
    )
      
  (* See: Volume 2B ... (IMUL, ...) *)
  let imul_trunc x y =
    let x = big_int_of_int64 (to_int64 x) in
    let y = big_int_of_int64 (to_int64 y) in
    let z = Big_int_Infix.(x *! y) in
    (of_big_int z,
        Big_int.gt_big_int z (Big_int.big_int_of_int64 Int64.max_value)
     || Big_int.lt_big_int z (Big_int.big_int_of_int64 Int64.min_value))
 
  (* See: Volume 2B ... (MUL, ...) *)
  let umul x y =
    let x = to_big_int x in
    let y = to_big_int y in
    let z = Big_int_Infix.(x *! y) in
    let l = Big_int.mod_big_int z bi_2_64 in
    let h = Big_int_Infix.(z >>! 64) in
    (of_big_int h,of_big_int l)
 
  module T = struct
    type t = Unsigned.UInt64.t
    let t_of_sexp s = of_string (string_of_sexp s)
    let sexp_of_t x = sexp_of_string (to_string x)
    let compare = compare
    let hash v = Hashtbl.hash v
  end
  include Comparable.Make(T)
  include Hashable.Make(T)
end

type u64 = U64.t

let compare_u64 = U64.compare
let u64_of_sexp s = U64.of_string (string_of_sexp s)
let sexp_of_u64 u = sexp_of_string (U64.to_string u)

module Limb4 = struct
  let of_big_int i =
    let open Big_int_Infix in
    assert (i <! (2^!256));
    (U64.of_big_int (extract_big_int i 0 64),
     U64.of_big_int (extract_big_int i 64 64),
     U64.of_big_int (extract_big_int i 128 64),
     U64.of_big_int (extract_big_int i 192 64))

  let to_big_int (x0,x1,x2,x3) =
    Big_int_Infix.(
      (U64.to_big_int x0)
      +! ((U64.to_big_int x1) <!< 64)
      +! ((U64.to_big_int x2) <!< 128)
      +! ((U64.to_big_int x3) <!< 192)
    )
end

(* list containing [first..last) excluding last *)
let list_from_to ~first ~last =
  assert (U64.compare first last < 0);
  let rec go i acc =
    if U64.compare i last < 0 then
      go (U64.succ i) (i::acc)
    else
      List.rev acc
  in
  go first []

(* list containing [first..last) excluding last *)
let list_from_to_big_int ~first ~last =
  assert (Big_int.compare_big_int first last < 0);
  let rec go i acc =
    if Big_int.compare_big_int i last < 0 then
      go (Big_int.succ_big_int i) (i::acc)
    else
      List.rev acc
  in
  go first []

let u64_prod_list xs =
  List.fold xs
    ~init:(U64.of_int 1)
    ~f:(fun a b -> U64.mul a b)


let u64_sum_list xs =
  List.fold xs
    ~init:(U64.of_int 0)
    ~f:(fun a b -> U64.add a b)

(* ** Pretty-printing
 * ------------------------------------------------------------------------ *)

(* pretty printing as in hex notation with blocks containing i bytes *)
let pph digit_size fmt i =
  let pp_digit i = F.sprintf "%x" i in
  let rec go ~i ~digits =
    if (eq_big_int (big_int_of_int 0) i) then "" else (
      (go ~i:(shift_right_big_int i 4) ~digits:(digits + 1))
      ^(pp_digit (int_of_big_int (extract_big_int i 0 4)))
      ^(if digits mod digit_size = 0 then "|" else "")
    )
  in
  F.fprintf fmt "%s" (go ~i:i ~digits:0)

let pp_uint64 fmt i = F.fprintf fmt "%s" (U64.to_string i)

let pp_int64 fmt i = F.fprintf fmt "%s" (Int64.to_string i)

let pp_int fmt i = F.fprintf fmt "%i" i

let pp_big_int fmt bi = F.fprintf fmt "%s" (Big_int.string_of_big_int bi)
