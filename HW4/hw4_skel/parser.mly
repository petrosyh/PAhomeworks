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
%token TRUE FALSE READ
%token <string> ID
%token DEREF AT
%token PLUS MINUS COLONEQ SEMICOLON IF THEN ELSE LESS NOT ANDALSO ORELSE
%token WHILE DO
%token LP RP
%token EOF

%nonassoc SKIP
%left SEMICOLON
%nonassoc WHILE
%nonassoc DO
%nonassoc THEN
%nonassoc ELSE
%right COLONEQ
%left PLUS MINUS
%right DEREF AT
%right NOT
%left ANDALSO ORELSE
%nonassoc LESS

%start program
%type <Program.cmd> program

%%

program:
       cmd EOF { $1 }
    ;

cmd: 
      LP cmd RP { $2 }
	| SKIP {Program.SKIP}
    | ID COLONEQ expr { Program.ASSIGN ($1,$3) }
    | cmd SEMICOLON cmd { Program.SEQ ($1,$3) }
    | IF expr THEN cmd ELSE cmd { Program.IF ($2, $4, $6) }
    | WHILE expr DO cmd { Program.WHILE ($2, $4) }
	| DEREF ID COLONEQ expr {Program.PTRASSIGN ($2, $4)}
	;
expr:
	| LP expr RP { $2 }
	| MINUS expr { Program.MINUS ($2) }
	| NUM { Program.NUM ($1) }
	| ID { Program.VAR ($1) }
	| DEREF ID { Program.DEREF ($2) }
	| AT ID { Program.AT ($2) }
	| expr PLUS expr { Program.ADD ($1, $3) }
	| TRUE { Program.TRUE }
	| FALSE { Program.FALSE }
	| READ { Program.READ }
	| NOT expr { Program.NOT ($2)}
	| expr ANDALSO expr { Program.ANDALSO ($1, $3) }
	| expr ORELSE expr { Program.ORELSE ($1, $3) }
	| expr LESS expr { Program.LESS ($1, $3) }
%%
