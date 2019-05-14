/* IMPLEMENTED BY http://michel.levy.imag.free.fr/ */

%{open Interface
%}


/* tokens for formula */
%token LPAR RPAR NOT IMP EQU DISJ CONJ FALSE 
%token <string> VAR



/* tokens for line and proof */
%token EOL ASSUME THEREFORE  


/* priority */
%left EQU
%right IMP
%left DISJ
%left CONJ
%nonassoc NOT 
%start  formula_alone line
%type <Interface.formula> formula
%type <Interface.formula> formula_alone
%type <Interface.line> line


%%
formula :
	| FALSE                         {False}
	| VAR 				{Var $1}
	| LPAR formula RPAR		{$2}
	| NOT formula			{Neg $2}
	| formula IMP formula		{Imp ($1,$3)}
	| formula EQU formula           {Equiv ($1,$3)}
	| formula DISJ formula          {Disj ($1,$3)}
	| formula CONJ formula          {Conj ($1,$3)}
;

formula_alone :
        | formula EOL                   {$1}
;



line :
	| ASSUME formula EOL          {Assume $2}
	| THEREFORE formula EOL        {Therefore $2}
	| formula EOL                 {Usable $1}
;



