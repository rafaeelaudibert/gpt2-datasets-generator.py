(* IMPLEMENTED BY http://michel.levy.imag.free.fr/ *)

(* Vérification des preuves *)

open Interface;;
open Lexing;;
open Preuve;;

(* noms des justifications  
*)
let simpE = "=>E";;
let simpI = "=>I";;
let sdisjE = "+E";;
let sdisjI1 = "+I1";;
let sdisjI2 = "+I2";;
let sconjE1 = "&E1";;
let sconjE2 = "&E2";;
let sconjI = "&I";;
let sefq = "Efq";;
let sraa = "Raa";;
let snegE = "-E";;
let snegI = "-I";;
let sequivE1 = "<=>E1";;
let sequivE2 = "<=>E2";;
let sequivI = "<=>I";;

let scopie = "From";;

(* lorsque adroite vaut false les justifications sont placées sous la ligne justifiée *)
let adroite = ref true;;

(* let read_proof buffer =
  (* lecture d'une  preuve sur le buffer buf : c'est une liste de lignes 
  du type ligne *)
  Parser.proof Lexer.terminal buffer;;*)

(* lecture d'une preuve : on décompose la lecture de façon à pouvoir compter 
les lignes.
*)

let debut_preuve = ref [];;

let numero_ligne = ref 1;;

let read_proof buffer = 
  try
    debut_preuve := [];
    numero_ligne := 1;
    while true do
      let line = Parser.line Lexer.terminal buffer in
  numero_ligne := !numero_ligne+1;
	debut_preuve := !debut_preuve @ [line]
    done;
    !debut_preuve
  with Lexer.Eof -> !debut_preuve;;
    

let read_formula buffer =
  (* lecture d'une  formule sur le buffer buf *)
  Parser.formula_alone Lexer.terminal buffer;;



(* fonctions pour la vérification des preuves *)

(* On traite tout d'abord le cas des règles dont la conclusion
désignée par x est quelconque *)


(* Vérification de la règle E2/\ *)
let rec assoc_conjE2 x a =
  (* a : formula * int list est une liste de couples
     l'élement droite de chaque couple est strictement positif
     résultat :
     [i] s'il y a un premier couple (Conj(_,x),i) dans la liste a
     [] sinon
  *)
  match a with
    | [] -> []
    | (Conj (_,y),i)::_  when x = y -> [i]
    | _ :: b -> assoc_conjE2 x b 
;;

(* Vérification de la règle E1/\ *)
let rec assoc_conjE1 x a =
  (* a : formula * int list est une liste de couples
     l'élement gauche de chaque couple est strictement positif
     résultat :
     [i] s'il y a un premier couple (Conj(x,_),i) dans la liste a
     [] sinon
  *)
  match a with
    | [] -> []
    | (Conj (y,_),i)::_  when x = y -> [i]
    | _ :: b -> assoc_conjE1 x b 
;;

let assoc1 x a =
  (* a : 'a * int list est une liste de couples, l'élement droite 
     de chaque couple est strictement positif
     résultat :
     i si le couple (x,i) est dans la liste 
     0 sinon
  *)
  try List.assoc x a
  with Not_found -> 0;;


let rec assoc_imp1 x a = 
  (* a : formula * int list est une liste de couples
     l'élement gauche de chaque couple est strictement positif
     résultat :
     liste des (y,i) tel que  (Imp(y,x),i) dans la liste a
  *)
  match a with
    | [] -> []
    | (Imp (z,y),i)::b  when x = y -> (z,i)::assoc_imp1 x b
    | _ ::b -> assoc_imp1 x b
;;

let rec assoc_imp2 li a =
  (* li,a : formula * int list 
     résultat
     [i;j] si (y,i) dans li et (y,j) dans a
     [] sinon
     (i,j) où i <> 0 et j <> 0 si (y,i) dans li et (y,j) dans a
  *)
  match li with
    | [] -> []
    | (y,i)::b -> let j = assoc1 y a in
	if j <> 0 then [i;j]
	else assoc_imp2 b a
;;


(* Vérification de la règle E=> *)
let assoc_impE  x a =
  (* a : formula * int list
     résultat
     [i;j] si (y=>x,i) et (y,j) dans a 
     [] sinon
  *)
  assoc_imp2 (assoc_imp1 x a) a;;



let rec assoc_disj ld lu c  =
  (* ld, lu : formula * in list
     c : formula
     résultat :
     [i;j;k] si (Disj(a,b),i)dans ld, (j,Imp(a,c)) et (k,Imp(b,c)) dans lu
     [] sinon
  *)
  match ld with
    | [] -> []
    | (Disj(a,b),i)::fld -> 
	let j = assoc1 (Imp(a,c)) lu in
	  if j=0 then assoc_disj fld lu c
	  else let k = assoc1 (Imp(b,c)) lu in
	    if k = 0 then assoc_disj fld lu c
	    else [i;j;k]
    | _ ::fld -> assoc_disj fld lu c
;;
   

(* Vérification de la règle E\/ *)
let assoc_disjE x a =
  assoc_disj a a x
;;

(* Vérification de la règle Efq *)
let assoc_efq x a =
  let j = assoc1 False a in
    if j = 0 then [] else [j];;

(* Vérification de la règle Raa *)
let assoc_raa x a =
  let j = assoc1 (Imp(Imp (x,False),False)) a in
    if j = 0 then [] else [j];;




let rec assoc_neg ln lu =
  (* ln, lu : formula * int list
     résultat
     [i;j] si (Neg a,i) dans ln et (a,j) dans lu
     [] sinon
  *)
  match ln with
    | [] -> []
    | (Neg a,i)::fln -> 
	let j = assoc1 a lu  in
	  if j = 0 then assoc_neg fln lu
	  else [i;j]
    | _::fln -> assoc_neg fln lu
;;



(* Vérification de la règle de copie *)

let assoc_copie x a =
  let i = assoc1 x a in 
    if i = 0 then [] else [i];;



(* fin des règles à conclusion quelconque *)



exception Not_theorem;;
(* levée quand la preuve correcte n'est pas celle de la formule à prouver *)


exception Not_deducible of formula*int;;
(* dans cette exception la formule est accompagnée de
   son numéro de ligne de preuve *)


let regles_de_conclusion_quelconque = 
  [simpE,assoc_impE;sconjE1,assoc_conjE1;sconjE2,assoc_conjE2; 
   sdisjE,assoc_disjE;sefq,assoc_efq;sraa,assoc_raa;scopie,assoc_copie];;

exception Evaluer;;


let evaluer lf x a = 
  (* lf  ('a * ('b -> 'c -> 'd list)) list
     x 'b
     a 'c
     résultat 'a*'d list
     Soit (sr,rr) le premier couple de lf tel que (rr x a) n'est pas la liste
     vide, le résultat est (sr (rr x a))
     Si ce couple n'existe pas lève l'exception Evaluer
 *)
  let rec aux lf = match lf with
    | [] -> raise Evaluer
    | (sr,rr)::slf -> let lp = (rr x a) in if lp =[] then aux slf else (sr,lp)
  in aux lf
;;
  
			     

let premisses nl x a =
  (* nl int
     x formula
     a formula*int list
     résultat
     exception Not_deducible (x,nl) si la déduction de x est impossible
     (s,lp) s nom de la règle lp liste des premisses
  *) 
  try evaluer regles_de_conclusion_quelconque x a
  with 
    | Evaluer ->
	match x with
	  | Conj (b, c) ->
	      let i = assoc1 b a in
		if i <> 0 then
		  let j = assoc1 c a in
		    if j <> 0 then (sconjI,[i;j])
		    else 
		      raise (Not_deducible (x,nl))
		else raise (Not_deducible (x,nl))
	  | Disj (b, c) ->
	      (* print_string "testDisj\n";
	      let (_,fb) = string_of_formula 0 40 1 0 b in print_string fb;
		print_string "\n";
		let (_,fc) = string_of_formula 0 40 1 0 c in print_string fc;
		  print_string "\n";*)
	      let i = assoc1 b a in
		if i <> 0 then (sdisjI1,[i])
		else let i = assoc1 c a in
		  if i <> 0 then (sdisjI2,[i])
		  else raise (Not_deducible (x,nl))
	 
	  | Imp (b, c) ->
	      let i = assoc1 (Equiv (b,c)) a in
		if i <> 0 then (sequivE1,[i])
		else let i = assoc1 (Equiv (c,b)) a in
		  if i <> 0 then (sequivE2, [i])
		  else raise (Not_deducible (x,nl))
		  | _ -> raise (Not_deducible (x,nl))
(* le cas d'une formule x avec negation ou equivalence n'apparait pas car la fonction
   premisses n'est appliquee qu'a des formules depliees
   (voir la fonction deplie dans preuve.ml) *)
							      
;;

		    
			
let sjustification s l =
  (* s : string
     l : int list
     produire la chaîne s suivie des entiers de la liste l 
  séparés par des virgules*)
  s^" "^
  let rec aux l =
    match l with
    | [] -> ""
    | [i]-> string_of_int i
    | i::fl -> string_of_int i^","^aux fl in
    aux l;;


let supposons  k j f =
  (* k, j sont des entiers, f est une formule
     résultat : une chaine composée de
     k, la ligne "assume f" en colonne mg+j, des espaces jusqu'à la
     colonne des justifications (non comprise)
  *)
  let (cf,sf) = string_of_formula (mg+j) (col_justification-ecart) (mg+j+7) 0 f
  and sk = string_of_int k 
  (* la marge droite est mg+j+7, vu les 6 lettres de assume plus 1 espace *)
  in
    sk^ 
    espaces (mg-1+j - (String.length sk))^"assume "^
    sf^"."^
    espaces (col_justification - cf-1)   
;;

let debutligne k j f =
  (* k, j sont des entiers, f est une formule
     résultat : une chaine composée de
     k, la formule f en colonne mg+j, des espaces jusqu'à la
     colonne des justifications (non comprise)
  *)
  let (cf,sf) = string_of_formula (mg+j) (col_justification-ecart) (mg+j) 0 f
  and sk = string_of_int k in
    sk^
    espaces (mg-1+j - (String.length sk))^
    sf^"."^
    espaces (col_justification - cf-1) 
;;




let donc k j f =
  (* k, j sont des entiers, f est une formule
     résultat : une chaine composée de
     k, la ligne "therefore f" en colonne mg+j, des espaces jusqu'à la
     colonne des justifications (non comprise)
  *)
  (* la marge droite est de (mg+j+10) vu les 9 lettres de therefore et 1 espace *)
  let (cf,sf) = string_of_formula (mg+j) (col_justification-ecart) (mg+j+10) 0 f 
  and sk = string_of_int k in
    sk^
    espaces (mg-1+j - (String.length sk))^
    "therefore "^sf^"."^
    espaces (col_justification - cf-1) 
;;






(* Nettoyage des preuves *)

(* Autre simplification des preuves : 	 soit une preuve de la formule a, on enlève
toutes les lignes qui ne sont pas ancêtres de a.
Exemple : 
1    assume p & q & r.
2      p & q.                                              &E1 1
3      r.                                                  &E2 1
4      p.                                                  &E1 2
5    therefore p & q & r => p.                                  =>I 1,4
La ligne 3 est inutile, car 5 est déduite de 1,2,4

Pour cette analyse, on met les preuves sous forme de tableaux comportant
les lignes de la preuve et leurs justifications
*)


let deplie_ligne l =
  (* l est une ligne
     résultat la ligne avec sa conclusion dépliée *)
  match l with
    | Assume a -> Assume (deplie a)
    | Therefore a -> Therefore (deplie a)
    | Usable a -> Usable (deplie a);;



let preuve_tableau_de_preuve_liste lp =
(* conversion d'une preuve de type line list en un tableau de ligne justifiee *)
    let longueur_preuve = List.length lp in
    let preuve_tableau = Array.make (longueur_preuve +1) 
	{content = Assume (Var "x"); justification = "bidon";premisses_list = []} and
	nl = ref 1 and lh = ref [] and lu = ref [[]] 
    in
    (* lp est déplié en dlp 
       les justifications sont construites à partir de la liste dépliée
       Les formules de la liste originelle sont remises dans le tableau *)
    
    let dlp = List.map deplie_ligne lp in
    let construire_ligne_justifiee dligne ligne = 
      let gplat = aplatir !lu in
      (match dligne with
      | Assume a -> 
	  lh := (a, !nl)::!lh; lu := [(a,!nl)]::!lu; 
	  preuve_tableau.(!nl)<-{content=ligne; justification="";premisses_list =[]}
      | Therefore a ->
 	  (match !lh with
	  | [] -> raise (Not_deducible (a,!nl))
	  | (h1,i)::flh ->
	      match a with
	      | Imp (b,c) -> 
		  if h1 = b then let j = assoc1 c gplat in
		  if j <> 0 then 
		    (preuve_tableau.(!nl)<-{content=ligne; justification=simpI;premisses_list =[i; j]};
		     lh:=flh;
		     match !lu with
		     | _::u2::flu -> lu:= ((a,!nl)::u2)::flu
		     | _ -> failwith "la liste !lu a moins de deux éléments")
		  else raise (Not_deducible (a,!nl))
		  else raise (Not_deducible (a,!nl))
	      | _ ->  raise (Not_deducible (a,!nl)))
      | Usable a ->
	  (* pour trace 
	  let (_,fa) = string_of_formula 0 40 1 0 a in print_string fa;
	   print_string "\n";
	  *)
  
	  let (nr, lp) = premisses (!nl) a gplat in
	  preuve_tableau.(!nl)<-{content=ligne; justification=nr;premisses_list =lp};
	  match !lu with
	  | u1::flu -> lu:= ((a,!nl)::u1)::flu
	  | _ -> failwith "la liste !lu est vide ");
      nl:=!nl+1
    in
    (List.iter2 construire_ligne_justifiee dlp lp;
     preuve_tableau)
;;



let preuve_liste_de_preuve_tableau tp =
  (* spécification :
     tp une preuve tableau
     resultat une preuve liste dans laquelle on a éliminé les lignes qui ne servent pas
     dans la preuve de la conclusion de la preuve tableau.
     Note : on perd aussi les justifications, ce qui est stupide, mais normal
     dans la conception de ce site, puisque l'annotatation d'une preuve
     est effectuée sur une preuve sans annotation
     
     *)
   let longueur_preuve = Array.length tp - 1 in
   let ligne_utile = Array.make  (longueur_preuve +1) false in
   let rec marquer_ligne_utile i =
   (* marquage de la ligne i et de ses ancêtres de i *)
     if ligne_utile.(i) = false then
       (ligne_utile.(i)<- true;
	List.iter marquer_ligne_utile tp.(i).premisses_list) 
     else ()
   in
   let lp = ref [] in
   marquer_ligne_utile longueur_preuve;
   for i = longueur_preuve downto 1 
   do 
     if ligne_utile.(i) then lp := tp.(i).content::!lp
   done;
   !lp
;;
   







let preuve_chaine_de_preuve_tableau fin_affichage tp =
  (* tp est une preuve tableau, de type
     justified_line array
     la preuve_chaine est la traduction de la preuve tableau entre
     les indices 1 et fin_affichage
  *)
   let representation_preuve = ref "" and indent = ref 0 in
   let chaine_de_ligne indice =
   (* conversion en chaine de la ligne indice du tableau tp *)
   ( match tp.(indice).content with
   | Assume a ->
	representation_preuve := (!representation_preuve)^(supposons indice !indent a);
	indent := !indent + ind;
    | Therefore a ->
	indent := !indent - ind;
	representation_preuve := (!representation_preuve)^(donc indice !indent a)
	^(if !adroite then "" else "\n     ")^(sjustification simpI tp.(indice).premisses_list)
        (* pour justification a droite enlever ^"\n      " *)
    | Usable a ->
	representation_preuve := !representation_preuve^(debutligne indice !indent a)
	^(if !adroite then "" else "\n     ")^(sjustification tp.(indice).justification tp.(indice).premisses_list));
        (* pour justification a droite enlever ^"\n      " *)
    representation_preuve := !representation_preuve ^"\n"
  in 
  for i = 1 to fin_affichage 
  do
    chaine_de_ligne i
  done;
  !representation_preuve
;;





(* lorsque annotate vaut true la preuve est affichée *)
let annotate = ref true;;


let conclusion l =
(* 10/7/2006 conclusion : Interface.line -> Interface.formula 
   La formule est la conclusion de la ligne *)
   match l with
     | Assume a | Usable a | Therefore a -> a;;

let verifier_preuve fp =
  (* lecture d'une formule puis d'une preuve dans le fichier fp
     résultat : 
     en cas d'erreur dans la preuve un message d'erreur
     en absence d'erreur la preuve est donnée dans representation_preuve
     *)

   let buffer = Lexing.from_channel (open_in fp) in
   try 
     let f = read_formula buffer in
     (try 
       buffer.lex_curr_p <- 
	 {buffer.lex_curr_p with pos_lnum =0};
       let proof = read_proof buffer in 
       let tproof = preuve_tableau_de_preuve_liste  proof in
       let representation_preuve = preuve_chaine_de_preuve_tableau (Array.length tproof -1) tproof in
       let fin_preuve = List.nth proof ((List.length proof)-1) in  
       
       print_string representation_preuve;
       if f <> conclusion fin_preuve then
	 raise Not_theorem;
       if !annotate then print_string ( "proof.\n"^ representation_preuve)
       else print_string "correct proof"
   
   
      with (* preuve incorrecte *)
     | Lexer.Lexical_error | Parsing.Parse_error ->
	 print_string "The line ";
	 print_int !numero_ligne;
	 print_string " is incorrectly written";
	 print_newline ()

     | Not_deducible (a,i) ->
	 print_string "The formula line ";
	 print_int i;
	 print_string " can not be deduced";
	 print_newline ()
     | Not_theorem ->
	 print_string "The proof is correct but does not prove the formula";
   print_newline ())

   with (* formule incorrecte *)
   | Lexer.Lexical_error | Parsing.Parse_error ->
	    print_string "The formula is incorrect line ";
	    let p = lexeme_start_p buffer in
	      (print_int p.pos_lnum ;
	       print_string  " character ";
	       print_int (1+p.pos_cnum-p.pos_bol));
	      print_newline ();
	      	
;;





(* Construction de la preuve *)


let read_formula buffer = 
  (* lecture d'une formule (suivie d'un point) dans buffer *)
  Parser.formula_alone  Lexer.terminal buffer;;


let dnpreuve cf =
  (* cf est un fichier contenant une formule suivie de point
     dnpreuve affiche la preuve de la formule
  *)
  let buffer = Lexing.from_channel (open_in cf) 
  in
    try 
      let a = (read_formula buffer) in
      (try (* produire la preuve sous forme line list, la transformer en preuve_arbre list
	      avant de la compacter *)
	 let p = preuve_classique a in
	 let (pla,_) = preuve_arbre_liste_de_preuve_ligne_liste p in 
	 let (_,pc) = compacter_preuve_arbre_liste pla [] in
	 (* élimination des lignes qui ne servent pas dans la preuve de la
	   conclusion de pc *)
         let tpc = preuve_tableau_de_preuve_liste pc in
         let pc = preuve_liste_de_preuve_tableau tpc in

	   ( (* le mot proof est affiché pour
		que index.php sache que la preuve a été faite *)
	      print_string  "proof.";print_newline ();
       (* la preuve est affichée sans justification *)
       
       print_string (preuve_chaine_de_preuve_tableau (Array.length tpc -1) tpc)
	     (* afficher_preuve pc (* ORIGINAL CODE, WHICH WOULD REMOVE SOME STUFF FROM THE PRINTED PROOF *)*)
	   )
       with
	   Improvable h -> 
	     print_string "The formula can not be proved.\n";
	     print_string "it is false when the following litterals are true :\n";
	     afficher_liste_litteraux (compacter h);
	     print_newline ()
      )
    with (* filtrage des erreurs faites en lisant la formule *)
      | Lexer.Lexical_error | Parsing.Parse_error -> 
	print_string  "The formula is incorrect line "; 
	  let p = lexeme_start_p buffer in
	    (print_int p.pos_lnum ;
	     print_string " character ";
	     print_int (1+p.pos_cnum-p.pos_bol));


	  print_newline ()
;;



match Sys.argv.(1) with
  | "-v" -> annotate := false; verifier_preuve (Sys.argv.(2))
  | "-a" -> annotate := true; verifier_preuve (Sys.argv.(2))
  | "-b" -> annotate := true; adroite := false; verifier_preuve (Sys.argv.(2))
  | "-p" -> dnpreuve (Sys.argv.(2))
  | _ -> failwith  "missing option"
;;
   
