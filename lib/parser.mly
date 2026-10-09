%{
open Exprs
open Types

let full_span() = (Parsing.symbol_start_pos (), Parsing.symbol_end_pos ())
let tok_span(start, endtok) = (Parsing.rhs_start_pos start, Parsing.rhs_end_pos endtok)

%}

%token <string> STRING
%token <char> CHAR
%token <Stdint.uint64 * string> INT
%token <string> ID
%token BORROW AS FOR TYPECLASS INSTANCE EXTENDS ARROW EXTERN LEN DOT DEF ANDDEF ADD1 SUB1 LPARENSPACE LPARENNOSPACE RPAREN LBRACK RBRACK LET IN EQUAL COMMA PLUS MINUS TIMES DIVIDE IF COLON ELSECOLON EOF PRINT PRINTSTACK TRUE FALSE EQEQ LESSNOSPACE LESSSPACE GREATER LESSEQ GREATEREQ AND OR NOT COLONEQ SEMI NIL LAMBDA BEGIN END REC UNDERSCORE

%right SEMI
%left COLON COLONEQ
%left UMINUS
%left PLUS MINUS TIMES DIVIDE GREATER LESSSPACE GREATEREQ LESSEQ EQEQ AND OR
%left LPARENNOSPACE

%nonassoc LOW
%nonassoc ANDDEF


%type <(Lexing.position * Lexing.position) Exprs.program> program

%start program

%%

const :
  | INT { 
      let (num, text_suff) = $1 in
      let suff = (
        match text_suff with
        | "i8" -> IntSuffix I8
        | "i16" -> IntSuffix I16
        | "i32" | "" -> IntSuffix I32
        | "i64" -> IntSuffix I64
        | "u8" -> UIntSuffix U8
        | "u16" -> UIntSuffix U16
        | "u32" -> UIntSuffix U32
        | "u64" -> UIntSuffix U64
        | _ -> failwith "Unexpected suffix"
      ) in
      ELiteral(LitInt(num, suff), full_span()) 
    }
  | TRUE { ELiteral(LitBool(true), full_span()) }
  | FALSE { ELiteral(LitBool(false), full_span()) }
  | STRING { ELiteral(LitString($1), full_span()) }
  | CHAR { ELiteral(LitChar($1), full_span())}

prim1 :
  | ADD1 { Add1 }
  | SUB1 { Sub1 }
  | NOT { Not }
  | PRINT { Print }
  | PRINTSTACK { PrintStack }

bindings :
  | bind EQUAL expr { [($1, $3, full_span())] }
  | bind EQUAL expr COMMA bindings { ($1, $3, tok_span(1, 3))::$5 }

// namebindings :
//   | namebind EQUAL expr { [($1, $3, full_span())] }
//   | namebind EQUAL expr COMMA namebindings { ($1, $3, tok_span(1, 3))::$5 }

expr :
  | LET bindings IN expr { ELet($2, $4, full_span()) }
  | BORROW expr AS ID FOR ID IN expr { EBorrow($2, $4, $6, $8, full_span()) }
  // | LET REC namebindings IN expr { ELetRec($3, $5, full_span()) }
  | IF expr COLON expr ELSECOLON expr { EIf($2, $4, $6, full_span()) }
  | binop_expr SEMI expr { ESeq($1, $3, full_span()) }
  | binop_expr { $1 }

exprs :
  | expr { [$1] }
  | expr COMMA exprs { $1::$3 }

// tuple_expr :
//   | LPARENNOSPACE RPAREN { ETuple([], full_span()) }
//   | LPARENSPACE RPAREN { ETuple([], full_span()) }
//   | LPARENNOSPACE expr COMMA RPAREN { ETuple([$2], full_span()) }
//   | LPARENSPACE expr COMMA RPAREN { ETuple([$2], full_span()) }
//   | LPARENNOSPACE expr COMMA exprs RPAREN { ETuple($2::$4, full_span()) }
//   | LPARENSPACE expr COMMA exprs RPAREN { ETuple($2::$4, full_span()) }

id :
  | ID %prec COLON { EId($1, full_span()) }


// prim2 :
//   | PLUS { Plus }
//   | MINUS { Minus }
//   | TIMES { Times }
//   | DIVIDE { Divide }
//   | AND { And }
//   | OR { Or }
//   | GREATER { Greater }
//   | GREATEREQ { GreaterEq }
//   | LESSSPACE { Less }
//   | LESSEQ { LessEq }
//   | EQEQ { Eq }

binop_expr :
  | plus_chain { $1 }
  | minus_chain { $1 }
  | times_chain { $1 }
  | divide_chain { $1 }
  | greater_chain { $1 }
  | lessspace_chain { $1 }
  | greatereq_chain { $1 }
  | lesseq_chain { $1 }
  | eqeq_chain { $1 }
  | and_chain { $1 }
  | or_chain { $1 }
  // | binop_expr prim2 binop_operand %prec PLUS { EPrim2($2, $1, $3, full_span()) }
  // | binop_operand COLONEQ binop_expr %prec COLONEQ {
  //     match $1 with
  //     | EGetItem(lhs, idx, _) -> ESetItem(lhs, idx, $3, full_span())
  //     | EGetField(lhs, field_name, _) -> ESetField(lhs, field_name, $3, full_span())
  //     | _ -> raise Parsing.Parse_error
  //   }
  | binop_operand %prec PLUS { $1 } 

binop_operand :
  // Primops
  | MINUS binop_operand %prec UMINUS { EPrim1(Neg, $2, full_span())}
  | prim1 LPARENNOSPACE expr RPAREN { EPrim1($1, $3, full_span()) }
  // Extern
  // | EXTERN id LPARENNOSPACE exprs RPAREN %prec LPARENNOSPACE { EApp($2, $4, CCC, full_span()) }
  // | EXTERN id LPARENNOSPACE RPAREN %prec LPARENNOSPACE { EApp($2, [], CCC, full_span()) }
  // Function calls
  | binop_operand LPARENNOSPACE exprs RPAREN %prec LPARENNOSPACE { EApp($1, $3, full_span()) }
  | binop_operand LPARENNOSPACE RPAREN %prec LPARENNOSPACE { EApp($1, [], full_span()) }
  // Parentheses
  | LPARENSPACE expr RPAREN { $2 }
  | LPARENNOSPACE expr RPAREN { $2 }
  | BEGIN expr END { $2 }
  // Lambdas
  // | LPARENNOSPACE LAMBDA LPARENNOSPACE binds RPAREN COLON expr RPAREN { ELambda($4, $7, full_span()) }
  // | LPARENNOSPACE LAMBDA LPARENSPACE binds RPAREN COLON expr RPAREN { ELambda($4, $7, full_span()) }
  // | LPARENNOSPACE LAMBDA COLON expr RPAREN { ELambda([], $4, full_span()) }
  // | LPARENSPACE LAMBDA LPARENNOSPACE binds RPAREN COLON expr RPAREN { ELambda($4, $7, full_span()) }
  // | LPARENSPACE LAMBDA LPARENSPACE binds RPAREN COLON expr RPAREN { ELambda($4, $7, full_span()) }
  // | LPARENSPACE LAMBDA COLON expr RPAREN { ELambda([], $4, full_span()) }
  // Simple cases
  | const { $1 }
  | id { $1 }

plus_chain :
  | binop_operand PLUS binop_operand { EPrim2(Plus, $1, $3, full_span())}
  | plus_chain PLUS binop_operand { EPrim2(Plus, $1, $3, full_span())}

minus_chain :
  | binop_operand MINUS binop_operand { EPrim2(Minus, $1, $3, full_span())}
  | minus_chain MINUS binop_operand { EPrim2(Minus, $1, $3, full_span())}

times_chain :
  | binop_operand TIMES binop_operand { EPrim2(Times, $1, $3, full_span())}
  | times_chain TIMES binop_operand { EPrim2(Times, $1, $3, full_span())}

divide_chain :
  | binop_operand DIVIDE binop_operand { EPrim2(Divide, $1, $3, full_span())}
  | divide_chain DIVIDE binop_operand { EPrim2(Divide, $1, $3, full_span())}

greater_chain :
  | binop_operand GREATER binop_operand { EPrim2(Greater, $1, $3, full_span())}
  | greater_chain GREATER binop_operand { EPrim2(Greater, $1, $3, full_span())}

lessspace_chain :
  | binop_operand LESSSPACE binop_operand { EPrim2(Less, $1, $3, full_span())}
  | lessspace_chain LESSSPACE binop_operand { EPrim2(Less, $1, $3, full_span())}

greatereq_chain :
  | binop_operand GREATEREQ binop_operand { EPrim2(GreaterEq, $1, $3, full_span())}
  | greatereq_chain GREATEREQ binop_operand { EPrim2(GreaterEq, $1, $3, full_span())}

lesseq_chain :
  | binop_operand LESSEQ binop_operand { EPrim2(LessEq, $1, $3, full_span())}
  | lesseq_chain LESSEQ binop_operand { EPrim2(LessEq, $1, $3, full_span())}

eqeq_chain :
  | binop_operand EQEQ binop_operand { EPrim2(Eq, $1, $3, full_span())}
  | eqeq_chain EQEQ binop_operand { EPrim2(Eq, $1, $3, full_span())}

and_chain :
  | binop_operand AND binop_operand { EPrim2(And, $1, $3, full_span())}
  | and_chain AND binop_operand { EPrim2(And, $1, $3, full_span())}

or_chain :
  | binop_operand OR binop_operand { EPrim2(Or, $1, $3, full_span())}
  | or_chain OR binop_operand { EPrim2(Or, $1, $3, full_span())}

decl :
  | extern_opt DEF ID generics_opt LPARENNOSPACE params_opt RPAREN ret_typ_opt { DExtern($3, $6, $1, $8, full_span()) }
  | extern_opt DEF ID generics_opt LPARENNOSPACE params_opt RPAREN ret_typ_opt COLON expr { DFun($3, $4, $6, $10, $1, $8, full_span()) }
  | TYPECLASS ID LESSNOSPACE ids GREATER extends_opt COLON method_sigs {
    DClass($2, $4, $6, $8, full_span())
  }
  | INSTANCE generics_opt generic_bounds COLON method_impls {
    let impls = List.map (fun decl -> ImplDecl (decl)) $5 in
    match $3 with
    | [pred] -> DInstance($2, pred, impls, full_span())
    | _ -> failwith "Unexpected number of predicates"
  }

method_impls :
  | decl %prec LOW { [$1] }
  | decl ANDDEF method_impls { $1::$3 }

extends_opt :
  | /* empty */ { [] }
  | EXTENDS generic_bounds { $2 }

method_sig :
  | DEF ID generics_opt LPARENNOSPACE params_opt RPAREN ret_typ_opt expr_opt { 
      { ms_name = $2; ms_generics = $3; ms_args = $5; ms_ret = $7; ms_default = $8; ms_span = full_span()} 
    }

method_sigs :
  | method_sig %prec LOW { [$1] }
  | method_sig ANDDEF method_sigs { $1::$3 }

expr_opt :
  | /* empty */ { None }
  | COLON expr { Some($2) }

ids : 
  | ID { [$1] }
  | ID COMMA ids { $1::$3 }

generics_opt:
  | /* empty */ { [] }
  | LESSNOSPACE generics GREATER { $2 }

extern_opt:
  | /* empty */       { FictolFunc }
  | EXTERN STRING     { Extern($2) }

params_opt:
  | /* empty */       { [] }
  | binds             { $1 }

ret_typ_opt:
  | /* empty */ { TyBlank(full_span()) }
  | ARROW typ_name { $2 }

generic :
  | ID %prec SEMI { GBName($1, [], full_span()) }
  | ID COLON generic_bounds %prec SEMI { GBName($1, $3, full_span()) }

typ_name :
  | ID { TyPath([$1], full_span()) }
  | ID LESSNOSPACE typ_names GREATER { TyApp( (TyPath([$1], full_span())), $3) }

typ_names:
  | typ_name { [$1] }
  | typ_name COMMA typ_names { $1::$3 }

generic_bounds :
  | ID LESSNOSPACE typ_names GREATER { [{ pred_class = $1; pred_args = $3 }] }
  | generic_bounds PLUS generic_bounds { $1 @ $3 }

generics :
  | generic { [$1] }
  | generic COMMA generics { $1::$3 }

binds :
  | bind { [$1] }
  | bind COMMA binds { $1::$3 }

bind :
  | namebind { $1 }
  | blankbind { $1 }
  // | LPARENNOSPACE binds RPAREN { BTuple($2, full_span()) }
  // | LPARENSPACE binds RPAREN { BTuple($2, full_span()) }

blankbind :
  | UNDERSCORE %prec SEMI { BBlank(full_span()) }

namebind :
  | ID %prec SEMI { BName($1, false, TyBlank(full_span()), full_span()) }
  | ID COLON typ_name %prec SEMI { BName($1, false, $3, full_span()) }

decls :
  | decl %prec LOW { [$1] }
  | decl decls { $1::$2 }

program :
  | decls EOF { Program($1, full_span()) }

%%
