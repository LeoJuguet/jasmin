open Jasmin
open Cmdliner
open CommonCLI
open Utils

let parse_and_print arch call_conv idirs =
  let module A = (val CoreArchFactory.get_arch_module arch call_conv) in
  let parse file =
    try Compile.parse_file A.arch_info ~idirs file with
    | Annot.AnnotationError (loc, code) ->
        hierror ~loc:(Lone loc) ~kind:"annotation error" "%t" code
    | Pretyping.TyError (loc, code) ->
        hierror ~loc:(Lone loc) ~kind:"typing error" "%a" Pretyping.pp_tyerror
          code
    | Syntax.ParseError (loc, msg) ->
        hierror ~loc:(Lone loc) ~kind:"parse error" "%s"
          (Option.default "" msg)
  in
  fun output file warn ->
    if not warn then Utils.nowarning ();
    let _, _, ast =
      try parse file
      with HiError e -> Format.eprintf "%a@." pp_hierror e; exit 1
    in
    let out, close =
      match output with
      | None -> (stdout, ignore)
      | Some latexfile -> (open_out latexfile, close_out)
    in
    let fmt = Format.formatter_of_out_channel out in
    Format.fprintf fmt "%a@." Latex_printer.pp_prog ast;
    close out

let file =
  let doc = "The Jasmin source file to pretty-print" in
  Arg.(required & pos 0 (some non_dir_file) None & info [] ~docv:"JAZZ" ~doc)

let output =
  let doc =
    "The file in which the result is written (instead of the standard output)"
  in
  Arg.(value & opt (some string) None & info [ "o"; "output" ] ~docv:"TEX" ~doc)

let () =
  let doc = "Pretty-print Jasmin source programs into LATEX" in
  let man =
    [
      `S Manpage.s_environment;
      Manpage.s_environment_intro;
      `I ("OCAMLRUNPARAM", "This is an OCaml program");
      `I ("JASMINPATH", "To resolve $(i,require) directives");
    ]
  in
  let info =
    Cmd.info "jasmin2tex" ~version:Glob_options.version_string ~doc ~man
  in
  Cmd.v info Term.(const parse_and_print $ arch $ call_conv $ idirs $ output $ file
    $ warn)
  |> Cmd.eval |> exit
