{
open! Core
open! Import
open Parser
}

(* CR wduff: Look at the PFPL examples lexer for inspiration. *)
let whitespace = [' ' '\t']
let newline = '\r' | '\n' | "\r\n"
let digit = ['0'-'9']
let lower = ['a'-'z']
let upper = ['A'-'Z']
let alpha = ['a'-'z' 'A'-'Z']
let alphanum = ['0'-'9' 'a'-'z' 'A'-'Z']
let delimiter = ['(' ')' ',' ':' '[' ']' '{' '}' '"' '.']
let printing = ['!'-'~']
let non_quote = [^'"']

rule token = parse
  | whitespace+ {
    token lexbuf
  }
  | newline {
    Lexing.new_line lexbuf;
    token lexbuf
  }
  | "fn" {
    FN
  }
  | "fun" {
    FUN
  }
  | "in" {
    IN
  }
  | "include" {
    INCLUDE
  }
  | "infix" {
    INFIX
  }
  | "let" {
    LET
  }
  | "match" {
    MATCH
  }
  | "mod" {
    MOD
  }
  | "module" {
    MODULE
  }
  | "pat" {
    PAT
  }
  | "built-in" {
    BUILT_IN
  }
  | "sig" {
    SIG
  }
  | "signature" {
    SIGNATURE
  }
  | "type" {
    TYPE
  }
  | "with" {
    WITH
  }
  | '|' {
    BAR
  }
  | "=>" {
    EQARROW
  }
  | "->" {
    ARROW
  }
  | ':' {
    COLON
  }
  | '=' {
    EQUAL
  }
  | "of" {
    OF
  }
  | "." {
    DOT
  }
  | ',' {
    COMMA
  }
  | '"' (non_quote* as str) '"' {
    String str
  }
  | '(' {
    LPAREN
  }
  | ')' {
    RPAREN
  }
  | '{' {
    LBRACE
  }
  | '}' {
    RBRACE
  }
  | "_" {
    WILD
  }
  | "end" {
    END
  }
  | "val" {
    VAL
  }
  | "(*" {
    comment 1 lexbuf; token lexbuf
  }
  | digit+ as num {
    Number (Int64.of_string num)
  }
  | upper(printing#delimiter)* as name {
    NAME name
  }
  | lower(printing#delimiter)* as name {
    Name name
  }
  | ((printing#alphanum)#delimiter)+ as name {
    Name name
  }
  | eof {
    EOF
  }
  | _ {
    failwithf
      !"Illegal character at %{Source_code_position}"
      (Lexing.lexeme_start_p lexbuf)
      ()
  }

and comment depth = parse
  | "(*" {
    comment (depth + 1) lexbuf
  }
  | "*)" {
    if Int.equal depth 1
    then ()
    else comment (depth - 1) lexbuf
  }
  | (printing|whitespace) {
    comment depth lexbuf
  }
  | newline {
    Lexing.new_line lexbuf;
    comment depth lexbuf
  }
  | eof {
    failwithf
      !"EOF before end of comment at %{Source_code_position}"
      (Lexing.lexeme_start_p lexbuf)
      ()
  }
  | _ {
    failwithf
      !"Illegal character in comment at %{Source_code_position}"
      (Lexing.lexeme_start_p lexbuf)
      ()
  }

{
}
