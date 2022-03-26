open Core
open Semio

let debug = false

let interpret ~filenames () =
  let ast =
    List.concat_map filenames ~f:(fun filename ->
      In_channel.with_file filename ~f:(fun in_channel ->
        let lexbuf = Lexing.from_channel in_channel in
        lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with pos_fname = filename };
        Parser.program Lexer.token lexbuf))
  in
  if debug then begin
    printf !"unbound:\n%s\n\n%!"
      (String.concat ~sep:"\n" (List.map ast ~f:(sprintf !"%{Unbound.Defn}")))
  end;
  let typed = Elaborate_with_inference.translate ast in
  (* CR wduff: Are there other static checks we should do? *)
  if debug then begin
    printf !"%{sexp: string * Typed.Term.t}\n%!" ("typed", typed)
  end;
  match Dynamics.eval typed with
  | result ->
    printf
      !"%{sexp: string * Typed.Term.t}\n%!"
      ("result", result)
  | exception Dynamics.MatchFailure ->
    printf "(exception MatchFailure)\n%!"
;;

let command =
  let open Command.Let_syntax in
  Command.basic
    ~summary:"interpreter"
    [%map_open
      let filenames = anon (sequence ("FILENAME" %: Filename.arg_type))
      in
      (fun () ->
         Unix.sleep 10;
         interpret ~filenames ();
         Unix.sleep 10;
      )
    ]
;;

let () =
  Command.run command
;;
