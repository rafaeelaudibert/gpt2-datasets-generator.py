(* IMPLEMENTED BY http://michel.levy.imag.free.fr/ *)

{open Parser;; open Lexing;;
exception Lexical_error  ;; exception Eof;;


let keyword_table = Hashtbl.create 13
  let _ =
    List.iter (fun (kwd, tok) -> Hashtbl.add keyword_table kwd tok)
      [ 
	"assume",ASSUME;
	"therefore",THEREFORE;
	"F",FALSE
      ]          


}
rule terminal = parse
  | [' ''\t''0'-'9']  		
      {terminal lexbuf}
  | '\r'?'\n'
      {lexbuf.lex_curr_p <- 
       {lexbuf.lex_curr_p with pos_lnum =lexbuf.lex_curr_p.pos_lnum+1;
	  pos_bol =lexbuf.lex_curr_p.pos_cnum

       };
       
        terminal lexbuf}	  
  | '('		{LPAR}
  | ')'		{RPAR}
  | "=>"	{IMP}
  | "-"		{NOT}
  | "<=>"       {EQU}
  | "+"        {DISJ}
  | "&"        {CONJ}
  | "."[^'\n''\r']*      {EOL}
  |  ['a'-'z''A'-'Z']['a'-'z''A'-'Z''0'-'9''_']* as id	 	
                  {try
                   Hashtbl.find keyword_table id
		   with Not_found -> VAR id}
  | eof {raise Eof}
  | _	{raise Lexical_error  }
   

{ }
