(* include Ast *)
module Jasmin_lang = Jazz_lang
module Iterators = Iterators
module Integer = Integer
module Memory = Memory
module Array = Array
module Jasmin_stub = Jasmin_stub

let () =
  (* Start Mopsa *)
  Mopsa_analyzer.Framework.Runner.run ()
