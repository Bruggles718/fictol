{
  open Lexing
  open Parser
  open Printf
  open Stdint

let strbuf = Buffer.create 128

let ignore_new_line lexbuf =
  let lcp = lexbuf.lex_curr_p in
  if lcp != dummy_pos then begin
    lexbuf.lex_curr_p <-
      { lcp with pos_lnum = lcp.pos_lnum + 1; pos_bol = lcp.pos_cnum };
    lexbuf.lex_start_p <- lexbuf.lex_curr_p
  end

}

let dec_digit = ['0'-'9']
let int_suffix = "i8" | "i16" | "i32" | "i64"
(* let signed_int = dec_digit+ | ('-' dec_digit+) *)
let unsigned_int = dec_digit+

let ident = ['a'-'z' 'A'-'Z' '_']['a'-'z' 'A'-'Z' '0'-'9' '_']*

let blank = [' ' '\t']+

let tyident = "'"['a'-'z' 'A'-'Z' '_']['a'-'z' 'A'-'Z' '0'-'9' '_']*

let space = [' ' '\t' '\n']+

rule token = parse
  | '#' [^ '\n']+ { token lexbuf }
  | blank "(" { LPARENSPACE }
  | '\n' "(" { ignore_new_line lexbuf; LPARENSPACE }
  | blank "<=" { LESSEQ }
  | '\n' "<=" { ignore_new_line lexbuf; LESSEQ }
  | blank "<" { LESSSPACE }
  | '\n' "<" { ignore_new_line lexbuf; LESSSPACE }
  | blank { token lexbuf }
  | '\n' { new_line lexbuf; token lexbuf }
  | (unsigned_int as x) (int_suffix? as suff) { INT (Stdint.Uint128.of_string x, suff) }
  | ":=" { COLONEQ }
  | ":" { COLON }
  | "def" { DEF }
  | "and" { ANDDEF }
  | "printStack" { PRINTSTACK }
  | "nil" { NIL }
  | "true" { TRUE }
  | "false" { FALSE }
  | "len" { LEN }
  | "add1" { ADD1 }
  | "sub1" { SUB1 }
  | "lambda" { LAMBDA }
  | "λ" { LAMBDA }
  | "if" { IF }
  | ":" { COLON }
  | "else:" { ELSECOLON }
  | "let" { LET }
  | "in" { IN }
  | "=" { EQUAL }
  | "," { COMMA }
  | "(" { LPARENNOSPACE }
  | ")" { RPAREN }
  | "[" { LBRACK }
  | "]" { RBRACK }
  | "+" { PLUS }
  | "-" { MINUS }
  | "*" { TIMES }
  | "/" { DIVIDE }
  | ":=" { COLONEQ }
  | "==" { EQEQ }
  | "<" { LESSNOSPACE }
  | ">" { GREATER }
  | "<=" { LESSEQ }
  | ">=" { GREATEREQ }
  | "&&" { AND }
  | "||" { OR }
  | "!" { NOT }
  | ";" { SEMI }
  | "begin" { BEGIN }
  | "end" { END }
  | "rec" { REC }
  | "extern" { EXTERN }
  | "->" { ARROW }
  | "." { DOT }
  | "typeclass" { TYPECLASS }
  | "instance" { INSTANCE }
  | "extends" { EXTENDS }
  | ident as x { if x = "_" then UNDERSCORE else ID x }
  | '"' { Buffer.clear strbuf; string_literal lexbuf }
  | eof { EOF }
  | _ as c { failwith (sprintf "Unrecognized character: %c" c) }

and string_literal = parse
  | '"' { STRING (Buffer.contents strbuf) }
  | '\\' 'n' { Buffer.add_char strbuf '\n'; string_literal lexbuf }
  | '\\' 't' { Buffer.add_char strbuf '\t'; string_literal lexbuf }
  | '\\' '\\' { Buffer.add_char strbuf '\\'; string_literal lexbuf }
  | '\\' '"' { Buffer.add_char strbuf '"'; string_literal lexbuf }
  | '\\' _ as c { Buffer.add_char strbuf (String.get c 0); string_literal lexbuf }
  | '\n' { failwith "Unterminated string literal" }
  | eof { failwith "Unterminated string literal (EOF)" }
  | _ as c { Buffer.add_char strbuf c; string_literal lexbuf }
