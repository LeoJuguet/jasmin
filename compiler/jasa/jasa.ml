include Ast
module Translator = Translator
module Iterators = Iterators
module Integer = Integer
module Memory = Memory

let () =
  (* Start Mopsa *)
  Mopsa_analyzer.Framework.Runner.run ()
