// Parser for Biabd 2019/05/11
// 2021/08/04: add binary operations
// 2022/01/14: small modification for Strset
                          
%{
open Slsyntax
open Tools
let errstart = ref 0
let errend = ref 0
let errline = ref 1
let updatepos () =
  errstart := Parsing.symbol_start ();
  errend := Parsing.symbol_end ();
  errline := (Parsing.symbol_start_pos ()).pos_lnum
%}

%token <string> IDENT  // x, y, P, ...
%token <int> NUM
            
%token AST      // '*'
%token PLUS     // '+'
%token MINUS	// '-'
%token MOD      // '%'
%token SLASH    // '/'
%token DOLLER   // '$'
            
%token EQ      // '=', "=="
%token NEQ     // "!=","<>","=/"
%token SHL      // "<<"
%token SHR      // ">>"            
%token LT       // "<"
%token LE       // "<="
%token IMP      // "=>"                                                
%token GT       // ">" 
%token GE       // ">="
%token TRUE     // "True"
%token FALSE    // "False"
            
%token LPAREN   // '('
%token RPAREN   // ')'
%token LBRACKET // '['
%token RBRACKET // ']'            
%token COMMA    // ','
%token COLON    // ':'            
%token ATMARK   // '@'
%token DOLLAR   // '$'
%token HASH     // '#' 
            
%token EXint    // "Exint"
%token ALLint   // "Allint"
%token EXnat    // "Exnat"
%token ALLnat   // "Allnat"
%token ARR  	// "Arr"
%token ARR  	// "Array"
%token STR  	// "Str"
%token STRINGPART 	// "Stringpart"
%token LS   	// "Ls","List"
%token EMP  	// "Emp"
%token AND      // '&'
%token ANDAND   // "&&"
%token OR       // '|'
%token NOT      // "NOT"             
%token PTO      // "->"
%token VDASH    // "|-"

%token TILDE    // "~"
%token BAND     // "band"
%token BOR      // "bor"
%token BXOR     // "bxor"

            
%token EOF 

// 結合力(優先度が低い順)
%nonassoc VDASH
%nonassoc EXint EXnat ALLint ALLnat
%nonassoc COLON
%right IMP            
%left OR            
%left AND
%nonassoc NOT            
%left EQ NEQ
%left AST
%nonassoc EQA EQB NEQA NEQB NEQC
%nonassoc LE LT GT GE
%nonassoc PTO
%left SHR SHL            
%left PLUS MINUS
%left MOD SLASH UAST
%left TILDE UMINUS            
%left VAR NIL EMP LPAREN ATMARK DOLLAR

%start main
%type <Slsyntax.QFEntl.t> main
%type <string list> ident_seq
%type <SHterm.t> term
%type <SHspat.t> spat
%type <SHpure.t> pure
%type <QFSH.t> qfsh
%%

// 
main:
  | entl EOF
     { $1 }
;

ident_seq:
  | IDENT
      { [$1] }
  | LPAREN ident_seq RPAREN
	  { $2 }
;

var_attriv_one:
  | IDENT
      {
        match $1 with
        | "PTR" | "ptr" -> Attr.PTR
        | "EXQ" | "exq" -> Attr.EXQ
        | "PARAM" | "param" -> Attr.PARAM
        | "PTRPTR" | "ptrptr" -> Attr.PTRPTR
        | "GLOBAL" | "global" -> Attr.GLOBAL
        | "HAT" | "hat" -> Attr.HAT
        | "BAR" | "bar" -> Attr.BAR
        | "EXTERN" | "extern" -> Attr.EXTERN
        | "TILDE" | "tilde" -> Attr.TILDE
        | "CHECK" | "check" -> Attr.CHECK
        | "DOT" | "dot" -> Attr.DOT
        | "NESTED" | "nested" -> Attr.NESTED
        | "QUESTION" | "question" -> Attr.QUESTION
        | "DOTDOT" | "dotdot" -> Attr.DOTDOT
        | "AQUTE" | "acute" -> Attr.ACUTE
        | "INDIRECT" | "indirect" -> Attr.INDIRECT
        | "PROTO" | "proto" -> Attr.PROTO
        | "ARRAY" | "array" -> Attr.ARRAY [1] 
        | _ -> Attr.STRUCT $1
      }
;
  
var_attriv:
  | ATMARK var_attriv_one
      { Attrs.singleton $2 }
  | var_attriv ATMARK var_attriv_one
      { Attrs.add $3 $1 }
;

variable:
  | HASH IDENT var_attriv
      { SHterm.Var ("#"^$2,$3) }
  | IDENT var_attriv
      { SHterm.Var ($1,$2) }
  | IDENT 
      { SHterm.Var ($1,Attrs.empty) }
;
  
bvariable:  // used for quantifiers
  | HASH IDENT var_attriv
      { "#"^$2 }
  | IDENT var_attriv
      { $1 }
  | IDENT 
      { $1 }
;

bvariable_seq:
  | bvariable
      { Strset.singleton $1 }
  | bvariable_seq COMMA bvariable
      { Strset.add $3 $1 }
  | LPAREN bvariable_seq RPAREN
	  { $2 }
;
  
term:
  | IDENT LPAREN term_seq RPAREN
      { updatepos (); SHterm.Fcall ($1,$3) }
  | variable
      { updatepos (); $1 }
  | NUM
      { updatepos (); SHterm.Int $1 }
  | term PLUS term
      { updatepos (); SHterm.Add [$1;$3] }
  | term PLUS MINUS term
      { updatepos (); SHterm.Sub [$1;$4] }
  | term MINUS term
      { updatepos (); SHterm.Sub [$1;$3] }
  | term MOD term
      { updatepos (); SHterm.Mod ($1,$3) }
  | term AST term %prec UAST
      { updatepos (); SHterm.Mul ($1,$3) }
  | term SLASH term
      { updatepos (); SHterm.Div ($1,$3) }
  | term SHR term
      { updatepos (); SHterm.Shr ($1,$3) }
  | term SHL term
      { updatepos (); SHterm.Shl ($1,$3) }
  | term BAND term
      { updatepos (); SHterm.Band ($1,$3) }
  | term BOR term
      { updatepos (); SHterm.Bor ($1,$3) }
  | term BXOR term
      { updatepos (); SHterm.Bxor ($1,$3) }
  | TILDE term
      { updatepos (); SHterm.Bnot $2 }
  | MINUS term %prec UMINUS
      { updatepos (); SHterm.Sub [SHterm.Int 0;$2] }
  | LPAREN term RPAREN
      { updatepos (); $2 }
;

term_seq:
  | term
      { updatepos (); [$1] }	  
  | term_seq COMMA term
      { updatepos (); $1 @ [$3] }
  | LPAREN term_seq RPAREN
	  { updatepos (); $2 }	  
  | error
      {
        Format.printf "@[Here is term_seq@.";
        raise Parsing.Parse_error
      }
;

termpf:
  | IDENT LPAREN termpf_seq RPAREN
      { updatepos (); SHterm.Fcall ($1,$3) }
  | variable
      { updatepos (); $1 }
  | NUM
      { updatepos (); SHterm.Int $1 }
  | LPAREN PLUS termpf_seq RPAREN
      { updatepos (); SHterm.Add $3 }
  | LPAREN MINUS termpf_seq RPAREN
      { updatepos (); SHterm.Sub $3 }
  | LPAREN MOD termpf termpf RPAREN
      { updatepos (); SHterm.Mod ($3,$4) }
  | LPAREN AST termpf termpf RPAREN
      { updatepos (); SHterm.Mul ($3,$4) }
  | LPAREN SLASH termpf termpf RPAREN
      { updatepos (); SHterm.Div ($3,$4) }
  | LPAREN SHR termpf termpf RPAREN
      { updatepos (); SHterm.Shr ($3,$4) }
  | LPAREN SHL termpf termpf RPAREN
      { updatepos (); SHterm.Shl ($3,$4) }
  | LPAREN BAND termpf termpf RPAREN
      { updatepos (); SHterm.Band ($3,$4) }
  | LPAREN BAND termpf termpf RPAREN
      { updatepos (); SHterm.Bor ($3,$4) }
  | LPAREN BXOR termpf termpf RPAREN
      { updatepos (); SHterm.Bxor ($3,$4) }
  | LPAREN TILDE termpf RPAREN
      { updatepos (); SHterm.Bnot $3 }
  | MINUS termpf %prec UMINUS
      { updatepos (); SHterm.Sub [SHterm.Int 0;$2] }
  | LPAREN termpf RPAREN
      { updatepos (); $2 }
  | error
      {
        Format.printf "@[Here is termpf@.";
        raise Parsing.Parse_error
      }
;

termpf_seq:
  | termpf
      { updatepos (); [$1] }
  | termpf_seq termpf
      { updatepos (); $1 @ [$2] }
  | error
      {
        Format.printf "@[Here is termpf_seq@.";
        raise Parsing.Parse_error
      }
;
  
fieldterm:
  | term
      { updatepos (); ("",$1) }
  | AST COLON term
      { updatepos (); ("*",$3) }
  | IDENT COLON term
      { updatepos (); ($1,$3) }
;

fieldterm_seq:
  | fieldterm
      { updatepos (); [$1] }
  | fieldterm COMMA fieldterm_seq
      { updatepos (); $1 :: $3 }
;
  
pure_atom:
  | TRUE
      { updatepos (); P.True }
  | FALSE
      { updatepos (); P.False }
  | term EQ term
      { updatepos (); P.Atom(P.Eq,[$1;$3]) }
  | term NEQ term
      { updatepos (); P.Atom(P.Neq,[$1;$3]) }
  | term LT term
      { updatepos (); P.Atom(P.Lt,[$1;$3]) }
  | term LE term
      { updatepos (); P.Atom(P.Le,[$1;$3]) }
  | term GT term
      { updatepos (); P.Atom(P.Lt,[$3;$1]) }
  | term GE term
      { updatepos (); P.Atom(P.Le,[$3;$1]) }
  | LPAREN pure RPAREN
      { updatepos (); $2 }
;
  
pure_fact:
  | pure_atom
      { updatepos (); $1 }
  | pure OR pure
      { updatepos (); P.Or [$1;$3] }
  | pure IMP pure
      { updatepos (); P.Imp ($1,$3) }
  | NOT pure 
      { updatepos (); P.Neg $2}
  | ALLint bvariable_seq pure
      { updatepos (); P.All(P.Int,$2,$3) }
  | EXint bvariable_seq pure
      { updatepos (); P.Ex(P.Int,$2,$3) }
  | ALLnat bvariable_seq pure
      { updatepos (); P.All(P.Nat,$2,$3) }
  | EXnat bvariable_seq pure
      { updatepos (); P.Ex(P.Nat,$2,$3) }
;      

pure_fact_seq:
  | pure_fact
      { updatepos (); [$1] }
  | pure_fact AND pure_fact_seq
      { updatepos (); $1 :: $3 }
;
    
pure:
  | pure_fact_seq
      {
        match $1 with
        | [] -> P.True
        | [p] -> p
        | pp -> P.And pp
      }
;
  
pure_last:
  | pure AND
      { updatepos (); $1 }
;

purepf_atom:
  | TRUE
      { updatepos (); P.True }
  | FALSE
      { updatepos (); P.False }
  | LPAREN EQA termpf termpf RPAREN
      { updatepos (); P.Atom(P.Eq,[$3;$4]) }
  | LPAREN EQB termpf termpf RPAREN
      { updatepos (); P.Atom(P.Eq,[$3;$4]) }
  | LPAREN NEQA termpf termpf RPAREN
      { updatepos (); P.Atom(P.Neq,[$3;$4]) }
  | LPAREN NEQB termpf termpf RPAREN
      { updatepos (); P.Atom(P.Neq,[$3;$4]) }
  | LPAREN NEQC termpf termpf RPAREN
      { updatepos (); P.Atom(P.Neq,[$3;$4]) }
  | LPAREN LT termpf termpf RPAREN      
      { updatepos (); P.Atom(P.Lt,[$3;$4]) }
  | LPAREN LE termpf termpf RPAREN      
      { updatepos (); P.Atom(P.Le,[$3;$4]) }
  | LPAREN GT termpf termpf RPAREN      
      { updatepos (); P.Atom(P.Lt,[$4;$3]) }
  | LPAREN GE termpf termpf RPAREN      
      { updatepos (); P.Atom(P.Le,[$4;$3]) }
  | LPAREN purepf RPAREN
      { updatepos (); $2 }
;

purepf:
  | purepf_atom
      { updatepos (); $1 }
  | LPAREN AND purepf_seq RPAREN
      { updatepos (); P.And $3 }
  | LPAREN OR purepf_seq RPAREN      
      { updatepos (); P.Or $3 }
  | LPAREN IMP purepf purepf RPAREN      
      { updatepos (); P.Imp ($3,$4) }
  | LPAREN NOT purepf RPAREN      
      { updatepos (); P.Neg $3 }
  | LPAREN ALLint bvariable_seq purepf RPAREN
      { updatepos (); P.All(P.Int,$3,$4) }
  | LPAREN EXint bvariable_seq purepf RPAREN
      { updatepos (); P.Ex(P.Int,$3,$4) }
  | LPAREN ALLnat bvariable_seq purepf RPAREN
      { updatepos (); P.All(P.Nat,$3,$4) }
  | LPAREN EXnat bvariable_seq purepf RPAREN
      { updatepos (); P.Ex(P.Nat,$3,$4) }
;      

purepf_and:
  | purepf AND
      { updatepos (); $1 }
;

purepf_seq:
  | purepf
      { updatepos (); [$1] }
  | purepf_seq purepf
      { updatepos (); $1 @ [$2] }
;
  
spat_atom:
  | term PTO LPAREN RPAREN
      { updatepos (); S.Pto($1,[]) }
  | term PTO LPAREN fieldterm_seq RPAREN
      { updatepos (); S.Pto($1,$4) }
  | ARR LPAREN term COMMA term RPAREN
      { updatepos (); S.Arr($3,$5) }
  | STR LPAREN term COMMA term RPAREN
      { updatepos (); S.Str($3,$5) }
  | STRINGPART LPAREN term COMMA term RPAREN
      { updatepos (); S.Str($3,$5) }  
  | LS LPAREN term COMMA term RPAREN
      { updatepos (); S.Ind("Ls",[$3;$5]) }
  | error
      { raise (ParseError (!errstart,!errend,!errline)) }
;

spat:
  | EMP
      { updatepos (); [] }
  | spat_atom
      { updatepos (); [$1] }
  | spat_atom AST spat
      { updatepos (); $1 :: $3 }
;

qfsh:
  | spat
      { updatepos (); (P.True,$1) }
  | pure ANDAND spat
      { updatepos (); ($1,$3) }
;
  
entl:
   | qfsh VDASH qfsh
	   { updatepos (); ($1,[$3])  }
;
