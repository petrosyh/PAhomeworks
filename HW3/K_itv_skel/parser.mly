/*
 * SNU 4190.310 Programming Languages 
 *
 * K- Interpreter
 */
  

%{       

exception EmptyBinding
exception ParsingError

%}

%token SKIP
%token <int> NUM
%token TRUE FALSE
%token <string> ID
%token PLUS MINUS COLONEQ SEMICOLON IF THEN ELSE LESS EQUAL NOT ANDALSO ORELSE
%token WHILE DO
%token LP RP
%token EOF

%nonassoc SKIP
%left SEMICOLON
%nonassoc THEN
%nonassoc ELSE
%right COLONEQ
%right WRITE 
%left PLUS MINUS
%right NOT
%left ANDALSO ORELSE
%nonassoc LESS EQUAL

%start program
%type <K.K.cmd> program

%%

program:
       cmd EOF { $1 }
    ;

cmd: 
      LP cmd RP { $2 }
	| SKIP {K.K.SKIP}
    | ID COLONEQ expr { K.K.ASSIGN ($1,$3) }
    | cmd SEMICOLON cmd { K.K.SEQ ($1,$3) }
    | IF expr THEN cmd ELSE cmd { K.K.IF ($2, $4, $6) }
    | WHILE expr DO cmd { K.K.WHILE ($2, $4) }
	;
expr:
	| LP expr RP { $2 }
	| MINUS expr { K.K.MINUS ($2)}
	| NUM { K.K.NUM ($1) }
	| ID { K.K.VAR ($1) }
	| expr PLUS expr { K.K.ADD ($1, $3) }
	| TRUE { K.K.TRUE }
	| FALSE { K.K.FALSE }
	| NOT expr { K.K.NOT ($2)}
	| expr ANDALSO expr { K.K.ANDALSO ($1, $3) }
	| expr ORELSE expr { K.K.ORELSE ($1, $3) }
	| expr LESS expr { K.K.LESS ($1, $3) }
%%
