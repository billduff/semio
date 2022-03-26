%{
  open Core
  open Unbound

  let make_record_fields raw_fields =
    let _, rev_fields =
      List.fold raw_fields ~init:(0, []) ~f:(fun (index, rev_fields) raw_field ->
        match raw_field with
        | `Labeled (label, value) -> (index, (label, value) :: rev_fields)
        | `Unlabeled value -> (index + 1, (Int.to_string index, value) :: rev_fields))
    in
    List.rev rev_fields
  ;;

  let tag_with_positions start_pos end_pos without_positions =
    { Unbound.With_positions. start_pos; end_pos; without_positions }
  ;;
%}

%type <Unbound.Defn.t list> program
%type <Unbound.Defn.t> defn
%type <Unbound.Term.t> term
%type <Unbound.Typ.t> typ
%type <Lexing.position * string> ident
%type <Lexing.position * string> bigident

%type <string list> rev_path
%type <Unbound.Modl.untagged> apmodl
%type <Unbound.Pat.untagged> appat
%type <Unbound.Term.t list> apterm
%type <Unbound.Typ.t list> aptyp
%type <Unbound.Decl.t> decl
%type <Unbound.Decl.t list> decls
%type <Unbound.Defn.t list> defns
%type <Unbound.Pat.t * Unbound.Term.t> matchcase
%type <(Unbound.Pat.t * Unbound.Term.t) list> matchcases
%type <Unbound.Modl.t> modl
%type <Unbound.Modl.t * string> modlproj
%type <Unbound.Modl.t * string> modlprojbig
%type <Unbound.Pat.t> pat
%type <string list * string> path
%type <(string * Unbound.Typ.t) list> prodtypbody
%type <[`Unlabeled of Unbound.Pat.t | `Labeled of string * Unbound.Pat.t] list> recordbody(pat)
%type <[`Unlabeled of Unbound.Term.t | `Labeled of string * Unbound.Term.t] list> recordbody(term)
%type <Unbound.Sigture.t> sigture
%type <Unbound.Modl.untagged> simpmodl
%type <Unbound.Pat.untagged> simppat
%type <Unbound.Pat.t list> simppats
%type <Unbound.Term.untagged> simpterm
%type <Unbound.Typ.untagged> simptyp
%type <string * Unbound.Typ.t option> sumtypbranch
%type <(string * Unbound.Typ.t option) list> sumtypdefn
%type <Unbound.Tag.t> tag
%type <string list> typargs
%type <[`Alias of Unbound.Typ.t | `Prod of (string * Unbound.Typ.t) list | `Sum of (string * Unbound.Typ.t option) list]> typdefnbody
%type <string * Unbound.Typ.t> typfield
%type <Unbound.Decl.untagged> untagged_decl
%type <Unbound.Defn.untagged> untagged_defn
%type <Unbound.Modl.untagged> untagged_modl
%type <Unbound.Modl.untagged * string> untagged_modlproj
%type <Unbound.Modl.untagged * string> untagged_modlprojbig
%type <Unbound.Pat.untagged> untagged_pat
%type <Unbound.Sigture.untagged> untagged_sigture
%type <Unbound.Tag.untagged> untagged_tag
%type <Unbound.Term.untagged> untagged_term
%type <Unbound.Typ.untagged> untagged_typ


%start program
%token TYPE LET IN FN MATCH WITH OF LPAREN RPAREN LBRACE RBRACE END VAL FUN INFIX INCLUDE MODULE SIGNATURE SIG MOD PAT BUILT_IN
%token EQUAL EQARROW ARROW BAR COLON COMMA DOT WILD EOF
%token <Int64.t> Number
%token <string> String Name NAME

%%

program: defns EOF {$1}
;

ident: Name {($startpos($1), $1)}
(* | EQUAL {"="} ???*)
;

bigident: NAME {($startpos($1), $1)}
;

(* ??? This is not as general as I would like. *)
untagged_modlproj:
  | bigident DOT Name {(Modl.Var $1, $3)}
  | modlprojbig DOT Name {(Modl.Modl_proj $1, $3)}
;

modlproj: untagged_modlproj {
              let (modl, field) = $1 in
              (tag_with_positions $symbolstartpos $endpos modl, field)
            }
;

path:
  | Name {([], $1)}
  | rev_path DOT Name {(List.rev $1, $3)}
;

rev_path:
  | NAME {[$1]}
  | rev_path DOT NAME {$3 :: $1}
;

untagged_modlprojbig:
  | bigident DOT NAME {(Modl.Var $1, $3)}
  | modlprojbig DOT NAME {(Modl.Modl_proj $1, $3)}
;

modlprojbig: untagged_modlprojbig {
                 let (modl, field) = $1 in
                 (tag_with_positions $symbolstartpos $endpos modl, field)
               }
;

simptyp:
  | ident {Typ.Var $1}
  | modlproj {Typ.Modl_proj $1}
  | ARROW {Typ.Var ($startpos($1), "->")}
  | LPAREN untagged_typ RPAREN {$2}
;

aptyp:
  | simptyp simptyp {
              [ tag_with_positions $startpos($1) $endpos($1) $1
              ; tag_with_positions $startpos($2) $endpos($2) $2
              ]
            }
  | simptyp aptyp {tag_with_positions $startpos($1) $endpos($1) $1 :: $2}
;

untagged_typ:
  | simptyp {$1}
  | aptyp {Typ.Ap $1}
  | LPAREN Name COLON TYPE RPAREN ARROW typ {Typ.Forall ($2, $7)}
;

typ: untagged_typ {tag_with_positions $symbolstartpos $endpos $1}
;

typdefnbody:
  | typ {`Alias $1}
  | LBRACE prodtypbody RBRACE {`Prod $2}
  | sumtypdefn {`Sum $1}
  | BAR sumtypdefn {`Sum $2}
;

prodtypbody:
  | typfield {[$1]}
  | typfield COMMA prodtypbody {$1 :: $3}
;

typfield: Name COLON typ {($1, $3)}
;

sumtypdefn:
  | sumtypbranch {[$1]}
  | sumtypbranch BAR sumtypdefn {$1 :: $3}
;

sumtypbranch:
  | NAME {($1, None)}
  | NAME OF typ {($1, Some $3)}
;

untagged_tag:
  | bigident {Tag.Var $1}
  | modlprojbig {Tag.Modl_proj $1}
;

tag: untagged_tag {tag_with_positions $symbolstartpos $endpos $1}

simppat:
  | WILD {Pat.Wild}
  | ident {Pat.Var $1}
  | tag {Pat.Tag ($1, None)}
  | LBRACE RBRACE {Pat.Record []}
  | LBRACE recordbody(pat) RBRACE {Pat.Record (make_record_fields $2)}
  | Number {Pat.Number $1}
  | String {Pat.String $1}
  | LPAREN untagged_pat RPAREN {$2}
  | LPAREN pat COLON typ RPAREN {(*???are parens really required*) Pat.Ascribe ($2, $4)}
;

appat: tag simppat {Pat.Tag ($1, Some (tag_with_positions $startpos($2) $endpos($2) $2))}
;

untagged_pat:
  | simppat {$1}
  | appat {$1}
;

pat: untagged_pat {tag_with_positions $symbolstartpos $endpos $1}
;

simppats:
  | simppat {[tag_with_positions $startpos($1) $endpos($1) $1]}
  | simppat simppats {tag_with_positions $startpos($1) $endpos($1) $1 :: $2}
;

simpterm:
  | ident {Term.Var $1}
  | modlproj {Term.Modl_proj $1}
  | bigident {Term.Var $1}
  | modlprojbig {Term.Modl_proj $1}
  | FN simppats EQARROW term END {Term.Fun ($2, None, $4)}
  | FN simppats COLON typ EQARROW term END {Term.Fun ($2, Some $4, $6)}
  | LBRACE RBRACE {Term.Record []}
  | LBRACE recordbody(term) RBRACE {Term.Record (make_record_fields $2)}
  | MATCH term WITH matchcases END {Term.Match ($2, $4)}
  | MATCH term WITH BAR matchcases END {Term.Match ($2, $5)}
  | Number {Term.Number $1}
  | String {Term.String $1}
  | BUILT_IN String COLON typ END {Term.Built_in ($2, $4)}
  | LET defns IN term END {Term.Let ($2, $4)}
  | LPAREN untagged_term RPAREN {$2}
  | LPAREN term COLON typ RPAREN {(*???are parens really required*) Term.Ascribe ($2, $4)}
;

recordbody(SORT):
  | SORT COMMA SORT {[`Unlabeled $1; `Unlabeled $3]}
  | SORT COMMA Name EQUAL SORT {[`Unlabeled $1; `Labeled ($3, $5)]}
  | Name EQUAL SORT COMMA SORT {[`Labeled ($1, $3); `Unlabeled $5]}
  | Name EQUAL SORT COMMA Name EQUAL SORT {[`Labeled ($1, $3); `Labeled ($5, $7)]}
  | SORT COMMA recordbody(SORT) {`Unlabeled $1 :: $3}
  | Name EQUAL SORT COMMA recordbody(SORT) {`Labeled ($1, $3) :: $5}
;

matchcases:
  | matchcase {[$1]}
  | matchcase BAR matchcases {$1 :: $3}
;

matchcase: pat EQARROW term {($1, $3)}
;

apterm:
  | simpterm simpterm {
               [ tag_with_positions $startpos($1) $endpos($1) $1
               ; tag_with_positions $startpos($1) $endpos($2) $2
               ]
             }
  | simpterm apterm {tag_with_positions $startpos($1) $endpos($1) $1 :: $2}
;

untagged_term:
  | simpterm {$1}
  | apterm {Term.Ap $1}
;

term: untagged_term {tag_with_positions $symbolstartpos $endpos $1}
;

typargs:
  | /* empty */ {[]}
  | ident typargs {snd $1 :: $2}
;

untagged_defn:
  | INFIX TYPE ident {Defn.InfixTyp (snd $3)}
  | INFIX ident {Defn.InfixTerm (snd $2)}
  | TYPE ident typargs EQUAL typdefnbody {
           match $5 with
           | `Alias typ -> Defn.TypAlias (snd $2, $3, typ)
           | `Prod fields ->
              Defn.TypAlias
                (snd $2, $3, tag_with_positions $startpos($5) $endpos($5) (Typ.Record fields))
           | `Sum cases -> Defn.SumTyp (snd $2, $3, cases)
         }
  | PAT ident EQUAL term
        {Defn.Tag (snd $2, None, tag_with_positions $startpos($4) $endpos($4) (Tag.Destr $4))}
  | PAT ident COLON typ EQUAL term
        {Defn.Tag (snd $2, Some ($4, None), tag_with_positions $startpos($6) $endpos($6) (Tag.Destr $6))}
  | PAT ident COLON typ EQARROW typ EQUAL term
        {Defn.Tag (snd $2, Some ($4, Some $6), tag_with_positions $startpos($8) $endpos($8) (Tag.Destr $8))}
  | VAL pat EQUAL term {Defn.Val ($2, $4)}
  | FUN ident simppats EQUAL term {Defn.Fun (snd $2, $3, None, $5)}
  | FUN ident simppats COLON typ EQUAL term {Defn.Fun (snd $2, $3, Some $5, $7)}
  | SIGNATURE bigident EQUAL sigture {Defn.Sigture (snd $2, $4)}
  | MODULE bigident EQUAL modl {Defn.Modl (snd $2, None, None, $4)}
  | MODULE bigident COLON sigture EQUAL modl {Defn.Modl (snd $2, None, Some $4, $6)}
  | MODULE bigident LPAREN bigident COLON sigture RPAREN EQUAL modl
           {Defn.Modl (snd $2, Some (snd $4, $6), None, $9)}
  | MODULE bigident LPAREN bigident COLON sigture RPAREN COLON sigture EQUAL modl
           {Defn.Modl (snd $2, Some (snd $4, $6), Some $9, $11)}
  | INCLUDE modl {Defn.Include $2}
;

defn: untagged_defn {tag_with_positions $symbolstartpos $endpos $1}
;

defns:
  | /* empty */ {[]}
  | defn defns {$1 :: $2}
;

untagged_decl:
  | INFIX TYPE ident {Decl.InfixTyp (snd $3)}
  | INFIX ident {Decl.InfixTerm (snd $2)}
  | TYPE ident typargs {Decl.Typ (snd $2, $3, None)}
  | TYPE ident typargs EQUAL typ {Decl.Typ (snd $2, $3, Some $5)}
  | PAT bigident COLON typ {Decl.Tag (snd $2, $4, None)}
  | PAT bigident COLON typ EQARROW typ {Decl.Tag (snd $2, $4, Some $6)}
  | VAL ident COLON typ {Decl.Val (snd $2, $4)}
  | VAL bigident COLON typ {Decl.Val (snd $2, $4)}
  | SIGNATURE bigident EQUAL sigture {Decl.Sigture (snd $2, $4)}
  | MODULE bigident COLON sigture {Decl.Modl (snd $2, $4)}
  | MODULE bigident LPAREN bigident COLON sigture RPAREN COLON sigture {
             Decl.Modl
               (snd $2,
                tag_with_positions $symbolstartpos $endpos (Sigture.Arrow ((snd $4, $6), $9)))
           }
  | INCLUDE sigture {Decl.Include $2}
;

decl: untagged_decl {tag_with_positions $symbolstartpos $endpos $1}
;

decls:
  | /* empty */ {[]}
  | decl decls {$1 :: $2}
;

untagged_sigture:
  | bigident {Sigture.Var $1}
  | modlprojbig {Sigture.Modl_proj $1}
  | SIG decls END {Sigture.Body $2}
  | sigture WITH TYPE path EQUAL typ {Sigture.With_type ($1, $4, $6)}
;

sigture: untagged_sigture {tag_with_positions $symbolstartpos $endpos $1}
;

simpmodl:
  | bigident {Modl.Var $1}
  | modlprojbig {Modl.Modl_proj $1}
  | MOD defns END {Modl.Body $2}
  | LPAREN untagged_modl RPAREN {$2}
  | LPAREN modl COLON sigture RPAREN {(*???are parens really required*) Modl.Ascribe ($2, $4)}
;

apmodl:
  | simpmodl simpmodl {
               Modl.Ap
                 (tag_with_positions $startpos($1) $endpos($1) $1,
                  tag_with_positions $startpos($2) $endpos($2) $2)
             }
  | simpmodl apmodl {
               Modl.Ap
                 (tag_with_positions $startpos($1) $endpos($1) $1,
                  tag_with_positions $startpos($2) $endpos($2) $2)
             }
;

untagged_modl:
  | simpmodl {$1}
  | apmodl {$1}
;

modl: untagged_modl {tag_with_positions $symbolstartpos $endpos $1}
;
