

open LivenessAnalyser
open Annotation

(**
    Dead Variable Checker :
    This module check if an affected variable is used in the program.
*)
val check_prog : (domain annotation, 'asm) Jasmin.Prog.prog -> CompileError.t list
