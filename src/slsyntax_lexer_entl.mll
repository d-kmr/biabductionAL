(* Lexer for biabd 2019/05/11 *)
(* Modified 2019/08/05 for biabduction extention *)

{
  open Slsyntax_parser_entl
}

let space = [' ' '\t']
let eol = ['\n' '\r']
let digit = ['0'-'9']
let alpha = ['A'-'Z' 'a'-'z']
let idhead = alpha | ['$' '#' '_']
let alnum = digit | alpha | ['_' '\'' '%' '#']
let comment = "//"

                
rule token = parse
  | "<<"      { SHL }
  | ">>"      { SHR }           
  | "->"      { PTO }            
  | '<'       { LT }
  | "<="      { LE }
  | '>'       { GT }  
  | ">="      { GE }
  | "=>"      { IMP }  
  | '+'       { PLUS }
  | '-'       { MINUS }
  | '%'       { MOD }
  | '/'       { SLASH }
  | '*'       { AST }
  | "=="      { EQ }
  | '='       { EQ }
  | "!="      { NEQ }  
  | "=/"      { NEQ }
  | "<>"      { NEQ }
  | "True"    { TRUE }
  | "False"   { FALSE }  
  | '('       { LPAREN }
  | ')'       { RPAREN }
  | '['       { LBRACKET }
  | ']'       { RBRACKET }
  | ':'       { COLON }
  | ','       { COMMA }
  | '@'       { ATMARK }
  | "$"       { DOLLAR }
  | "#"       { HASH }

  | "EXint"   { EXint }
  | "ALLint"  { ALLint }
  | "EXnat"   { EXnat }
  | "ALLnat"  { ALLnat }
  | "exists-int"  { EXint }
  | "forall-int"  { ALLint }
  | "exists-int"  { EXnat }
  | "forall-nat"  { ALLnat }
  | "Arr"     { ARR }
  | "Array"   { ARR }
  | "Ls"      { LS }
  | "List"    { LS }    
  | "Str"     { STR }
  | "Stringpart" { STRINGPART }
  | "Emp"     { EMP }
  | '&'       { AND }
  | "&&"      { ANDAND }
  | "AND"     { AND }
  | "and"     { AND }
  | "NOT"     { NOT }
  | "not"     { NOT }  
  | "IMP"     { IMP }
  | "imp"     { IMP }    
  | "OR"      { OR }
  | "or"      { OR }
  | "~"       { TILDE }  
  | '|'       { OR }
  | "||"      { OR }  
  | "|-"      { VDASH }
  | "band"    { BAND }
  | "bor"     { BOR }
  | "bxor"    { BXOR }
  | idhead alnum* { IDENT (Lexing.lexeme lexbuf) }
  | digit*    { NUM (int_of_string (Lexing.lexeme lexbuf)) }  
  | eof       { EOF }
  | eol       { Lexing.new_line lexbuf; token lexbuf }
  | space+    { token lexbuf }
  | comment [^ '\n' '\r']* eol { Lexing.new_line lexbuf; token lexbuf }
  | _
      {
        Format.printf "@[Parse error \"%s\", line %d:@." (lexbuf.lex_start_p.pos_fname) (lexbuf.lex_start_p.pos_lnum);
        Format.printf "@[Unexpected Input: %s@." (Lexing.lexeme lexbuf);
        exit 0
      }

and comment = parse
  | eol     { token lexbuf }
  | eof     { EOF }            
  | _       { comment lexbuf }    
