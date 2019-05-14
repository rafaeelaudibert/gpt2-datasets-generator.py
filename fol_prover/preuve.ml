(* IMPLEMENTED BY http://michel.levy.imag.free.fr/ *)

(* preuve intuitioniste d'après Roy *)
open Interface;; 


(* fonctions générales sur les listes *)
let aplatir g =
  (* g a list list
     résultat concaténation des listes de g *)
  List.fold_left (@) [] g;;

let espaces k =
  (* k : int
     résultat : k espaces *)
  if k < 0 then " " else String.make k ' ';;

let assoc1 x a =
  (* a : 'a * int list est une liste de couples, l'élement droite de chaque couple est strictement positif
     résultat :
     i si le couple (x,i) est dans la liste 
     0 sinon
  *)
  try List.assoc x a
  with Not_found -> 0;;

 
let ind = 2;;
(* valeur de l'indentation quand on ajoute une hypothèse 
     utilisée dans la construction et l'annotation des preuves
     Assistant.verifier_ligne, Preuve.afficher_ligne 

*)

let mg = 6;;
(* colonne du début des preuves (après le numéro de ligne) 
     utilisée seulement dans l'annotation pour laisser
     la place des numéros de ligne
*)	

let col_justification = 60;;
(* colonne des justifications 
     utilisée dans la construction et l'annotation des preuves
     Assistant.verifier_ligne, Preuve.afficher_ligne 
*)

let ecart = 10 ;;
(* borne de l'écart entre la fin d'une formule et la colonne des justifications 
     utilisée dans la construction et l'annotation des preuves
     Assistant.verifier_ligne, Preuve.afficher_ligne 
*)


let col_hyp = 80;;
(* colonne de début de l'affichage des listes d'hypothèses
   non utilisée actuellement
*)



let rec entiers_du_contexte  g =
  (* g : formula*int list
     résultat la suite des entiers extraits de g dans l'ordre inverse *)
  match g with
    | [] -> ""
    |[(_,n)] -> string_of_int n
    |(_,n)::fg -> entiers_du_contexte fg^","^string_of_int n ;;


	
(* Affichage des listes de lignes *)

let afficher_ligne tab ligne = 
(* Effet : la ligne est affichée avec la tabulation !tab
   tab est modifiée par Assume (augmentée de ind), Therefore (diminuée de ind)
*)
match ligne with
  | Assume a -> 
      (let (_ , sf)= string_of_formula (!tab) (col_justification -ecart) (!tab+10) 0 a in
	print_string ((espaces !tab)^"assume "^sf^".\n"));
      tab :=!tab+ind
  | Therefore a ->
      tab :=!tab-ind;
      let (_ , sf)= string_of_formula (!tab) (col_justification -ecart) (!tab+10) 0 a in
	print_string ((espaces !tab)^"therefore "^sf^".\n")
  | Usable a ->
      let (_ , sf)= string_of_formula (!tab) (col_justification -ecart) (!tab) 0 a in
	print_string ((espaces !tab)^sf^".\n")
;;


let afficher_preuve p =
(* p : line list 
   Effet : affichage de la preuve p en colonne 1 
   pour afficher en colonne k initialiser tab à la valeur k-1    
*)
  let tab = ref 0 in
    List.iter (afficher_ligne tab) p;;


(* les lemmes *)

let p1 b c = 
  (* preuve de Neg b sachant Neg (Disj (b,c)) *)
  [Assume b; Usable (Disj (b,c)); Usable False ; Therefore (Neg b)]
;;

  
let p2 b c =
  (* preuve de Neg c sachant Neg (Disj (b,c)) *)
  [Assume c; Usable (Disj (b,c)); Usable False ; Therefore (Neg c)]
;;


(* let p3 b c =
  (* preuve de Disj(b,c) sachant Imp(Neg b, c) *)
  [Assume (Neg (Disj(b,c)))]@(p1 b c)@(p2 b c)@
    [Usable c; Usable False; Therefore (Neg (Neg (Disj(b,c))));Usable (Disj(b,c))]
*)

let p3 b c =
  (* preuve de Disj(Neg b,c) sachant Imp(b,c) *)
  [Assume (Neg (Disj(Neg b,c)))]@(p1 (Neg b) c)@[Usable b]@(p2 (Neg b) c)@
    [Usable c; Usable False; Therefore (Neg (Neg (Disj(Neg b,c))));Usable (Disj(Neg b,c))]
;;			

let p5 b c =
  (* preuve de Disj (Neg b, Neg c) sachant Neg (Conj (b,c)) *)
  [ Assume (Neg (Disj (Neg b,Neg c)));
    Assume (Neg b); Usable (Disj (Neg b, Neg c)); Usable False ; Therefore (Neg (Neg b));
    Usable b;
    Assume (Neg c); Usable (Disj (Neg b, Neg c)); Usable False ; Therefore (Neg (Neg c));
    Usable c;
    Usable (Conj (b,c)); Usable False ;
    Therefore (Neg (Neg (Disj (Neg b, Neg c)))); Usable (Disj (Neg b, Neg c))]
;;

let p6 b c =
  (* preuve de b sachant Neg (Imp (b,c)) *)
  [ Assume (Neg b); 
    Assume b ; Usable False; Usable c; Therefore (Imp (b,c)); Usable False ; 
    Therefore (Neg (Neg b)) ; Usable b]
;;



let p7 b c =
  (* preuve de Neg c sachant Neg (Imp (b,c)) *)
  [ Assume c;
    Assume b; Therefore (Imp (b,c)); Usable False ; 
    Therefore  (Neg c)]
;;

let p8 b c =
  (* preuve de Imp (Neg b,c) sachant Neg (Equiv (b,c)) *)
  [ Assume (Neg b); 
    Assume (Neg c); 
    Assume b ; Usable False; Usable c; Therefore (Imp (b,c));
    Assume c ; Usable False; Usable b; Therefore (Imp (c,b)); Usable (Equiv (b,c)); Usable False ;
    Therefore (Neg (Neg c)); Usable c; Therefore (Imp (Neg b,c))]
;;

let p9 b c =
  (* preuve de Imp (c, Neg b) sachant Neg (Equiv (b,c)) *)
  [ Assume c;
    Assume b; 
    Assume b; Therefore (Imp (b,c)); Assume c; Therefore (Imp (c,b));
    Usable (Equiv (b,c)); Usable False ; 
    Therefore (Neg b);  Therefore (Imp (c, Neg b))]
;;





let p10 b c d =
  (* preuve de Imp (c,Imp(d,b)) sachant Imp(Conj(c,d),b) *)
  [ Assume c; Assume d; Usable (Conj (c,d)); Usable b; 
    Therefore (Imp (d,b)); Therefore (Imp (c, Imp(d,b)))]
;;

let p11 b c d =
  (* preuve de Imp (c,b) sachant Imp (Disj (c,d),b) *)
  [ Assume c; Usable (Disj (c,d)); Usable b; Therefore (Imp(c,b))]
;;

let p12 b c d =
  (* preuve de Imp (d,b) sachant Imp (Disj (c,d),b) *)
  [ Assume d; Usable (Disj (c,d)); Usable b; Therefore (Imp(d,b))]
;;

let p13 b c d =
  (* preuve de Imp (d,b) sachant Imp (Imp (c,d),b) *)
  [ Assume d; Assume c; Therefore (Imp (c,d)); Usable b; Therefore (Imp (d,b))]
;;

(* let p14 b c =
  (* preuve de Imp (Imp (b,False),c) sachant Imp (Neg b,c) *)
  [ Assume (Imp(b, False)); Usable (Neg b); Usable c; Therefore (Imp (Imp (b,False),c))]
;;

let p15 b c d =
  (* preuve de Imp (Conj(Imp(b,c),Imp(c,b)),d) sachant Imp(Equiv(b,c),d) *)
  [ Assume (Conj(Imp(b,c),Imp(c,b))); Usable (Imp(b,c));Usable (Imp(c,b)); Usable (Equiv (b,c)); Usable d;
    Therefore (Imp(Conj(Imp(b,c),Imp(c,b)),d))]
;;

*)
(* 
let p16 c d =
  (* preuve de Imp(c,d) sachant Disj(Neg c,d) *)
  [Assume c; Assume (Neg c);Usable False; Usable d; Therefore (Imp(Neg c,d)); Assume d; Therefore (Imp(d,d));
   Usable d; Therefore (Imp (c,d))];;

let p17 b c d =
  (* preuve de Imp(Disj(Neg c,d),b) sachant Imp(Imp(c,d),b) *)
  [Assume (Disj(Neg c,d))]@ (p16 c d) @ [Usable b; Therefore ( Imp(Disj(Neg c,d),b))];;

*) 


exception Improvable of formula list ;;

(* fonctions auxiliaires pour les raisonnements en avant *)
let intersection l1 l2 =
  (* l1, l2 : 'a list
     resultat : intersection des deux listes *)
  List.fold_left (fun l el2 -> if List.mem el2 l1 then el2::l else l) [] l2;;

let remove x l =
  (* l : 'a list
     resultat : la liste obtenue en enlevant de l les éléments égaux à x *)
   List.fold_left (fun l el2 -> if el2 <> x then el2::l else l) [] l;;

let implications gamma a =
  (* gamma : formula list
     a : formula
     resultat : liste des formules x telles que Imp (x,a) est dans gamma *)
  List.fold_left (fun l el2 -> match el2 with | Imp (x, y) when y = a -> x::l |_ -> l) [] gamma;;

let modusponens gamma a =
  (* gamma : formula list
     a : formula
     resultat : true ssi il y a une formule b de gamma telle que a et Imp (b,a) dans gamma *)
  intersection gamma (implications gamma a)  <> [];;

let negations gamma gamma' =
  (* gamma : formula list   
     resultat : liste des formules x telles que x est dans gamma et Neg x est dans gamma' *)
  List.fold_left (fun l el2 -> if List.mem (Neg el2) gamma' then el2::l else l ) [] gamma;;

let contradictions gamma =
  (* gamma : formula list
     a : formula
     resultat : true ssi il y a une formule b de gamma telle que b et Neg b dans gamma *)
  negations gamma gamma <> [];;

let conjonctions gamma a =
  (* gamma : formula list
     a : formula
     resultat : true ssi il y a une formule de gamma de la forme Conj (_,a) ou Conj (a,_) *)
  List.fold_left (fun c el2 -> match el2 with | Conj (x,y) when x = a || y = a -> true | _ -> c) false gamma;;

(* Modification de preuve : le 17 juillet 2008 
On utilise les abréviations *)

let rec deplie a = 
  (* a formule 
     résultat a sans negation ni equivalence *)
  match a with
    | Var _ | False -> a
    | Imp (b,c) -> Imp(deplie b, deplie c)
    | Disj (b,c) -> Disj(deplie b, deplie c)
    | Conj (b,c) -> Conj(deplie b, deplie c)
    | Neg b -> Imp(deplie b, False)
    | Equiv (b,c) -> let db = deplie b and dc = deplie c in Conj(Imp(db,dc),Imp(dc,db));;

let deplie_liste la =
  (* la liste de formules
     resultat la liste des formules deplies *)
  List.map deplie la;;





let negs gamma =
  (* gamma : formula list 
     resultat : liste des Neg x tels que Imp (x,_) dans gamma *)
  List.fold_left (fun l el2 -> match el2 with | Imp (x,_) -> (Neg x):: l |_ -> l) [] gamma;;

let implicationsgauches gamma a =
  (* gamma : formula list
     a : formula
     resultat : liste des formules x telles que Imp(a,x) est dans lf *)
  List.fold_left (fun l el2 -> match el2 with | Imp (y,x) when y = a -> x::l | _ -> l) [] gamma;;


  
(* Construction d'une preuve intuitioniste suivant la méthode de Roy *)


let rec preuve non_examinees atomes implications_atomiques implications_doubles a =
  (* non_examinees formula list
     atomes formula list ne comportant que des atomes
     implications_atomiques formula list de la forme Imp(Var _, _)
     implications_doubles formula list de la forme Imp(Imp(_,_),_)
     a formula
     résultat 
     posons gamma = non_examinees @ atomes @ implications_atomiques @ implications_doubles
     - une preuve intuitioniste (line list) de a sachant gamma
     exception lorsque la preuve n'existe pas 
     - Improvable ll où ll est une  liste de littéraux 
            modèle de gamma  et contre-modèle de a
  *)
  let da = deplie a in
  let dgamma = deplie_liste ( non_examinees @ atomes @ implications_atomiques @ implications_doubles) in
  if (* raisonnement en avant en zero ou un pas *)
    List.mem da dgamma then []
  else if
    List.mem False dgamma || modusponens dgamma da || conjonctions dgamma da then [Usable a]
  else if modusponens dgamma False then [Usable False; Usable a]
  else 
  (* raisonnement en arrière              *)

    match non_examinees, a with
      (* Traitement des conclusions, sauf Disj _  non réversible et  False, Var _  *)
	
      | _, Imp (b,c) ->
	  let r = preuve (b::non_examinees) atomes implications_atomiques implications_doubles c in
	    [Assume b] @ r @ [Therefore a]

      | _, Neg b -> 
	  let r = preuve (b::non_examinees) atomes implications_atomiques implications_doubles False in
	  [Assume b] @ r @ [Therefore a]
	  
      | _, Conj (b,c) ->
	  let r = preuve non_examinees atomes implications_atomiques implications_doubles b   and
	    s = preuve non_examinees atomes implications_atomiques implications_doubles c in
	    r @ s @ [Usable a]

      | _, Equiv (b,c) ->
	  let r = preuve non_examinees atomes implications_atomiques implications_doubles (Imp (b,c)) and
	    s = preuve non_examinees atomes implications_atomiques implications_doubles (Imp (c,b)) in
	    r @ s @ [Usable a]

		      (* Traitement des hypothèses *)

      | ((Var _) as y)::non_examinees',_ ->
	  preuve non_examinees' (y::atomes) implications_atomiques implications_doubles a
	    
      | (Conj (b,c)) :: non_examinees', _ ->
	  let r = preuve (b::c::non_examinees') atomes implications_atomiques implications_doubles a in
	  [Usable b;Usable c] @ r

      | (Disj (b,c)) :: non_examinees', _ ->
	  let r = preuve (b::non_examinees') atomes implications_atomiques implications_doubles a and
	      s = preuve (c::non_examinees') atomes implications_atomiques implications_doubles a in
	  [Assume b] @ r @ [Therefore (Imp (b,a)); Assume c] @ s @ [Therefore (Imp (c,a)); Usable a]
     
      | (Equiv (b,c)) :: non_examinees', _ ->
	  (* on remplace (b <=> c) par (b => c) /\ (c => b) *)
	  preuve ((Conj (Imp(b,c),Imp(c,b)))::non_examinees') atomes implications_atomiques 
	    implications_doubles a 
						       
      | (Neg b) :: non_examinees', _ ->
	  (* On remplace  Neg b par Imp (b,False) *)
	  preuve ((Imp (b,False)) ::non_examinees') atomes implications_atomiques implications_doubles a
 
      | ((Imp (g,b))as y)::non_examinees', _ ->
          (* On tente une preuve directe de Imp(g,b) en prouvant g puis une preuve de a sachant b
	     et en cas d'échec, on utilise les règles de LJT de Roy Dickhoff
	     Le cas particulier est celui de la règle =>G 1 où g est élément de non_examinés'
	     et où pg = []
	  *)
	  (try
	    let pg = preuve non_examinees' atomes implications_atomiques implications_doubles g
	    in let pa = preuve (b::non_examinees') atomes implications_atomiques implications_doubles a
	    in pg @ [Usable b] @ pa
	  with Improvable _ -> 

	    match g with
	      
	      | (Var x)  ->
		preuve non_examinees' atomes (y::implications_atomiques) implications_doubles a

	      | Conj (c,d) ->
		(* LJT p797 =>G 2 *)
		    let paux = preuve (Imp (c, Imp(d,b))::non_examinees')
		      atomes implications_atomiques implications_doubles a 
		    in (p10 b c d) @ paux

	      | Disj (c,d) ->
		(* LJT p797 =>G 3 *)
		    let paux = preuve (Imp (c,b)::Imp (d,b)::non_examinees')
		      atomes implications_atomiques implications_doubles a 
		    in (p11 b c d)@ (p12 b c d) @ paux

	      | Imp (c,d) -> 
		    preuve non_examinees' atomes implications_atomiques (y::implications_doubles) a

	      | Neg c ->
		    (* idem cas ci-dessus *)
		    preuve non_examinees' atomes implications_atomiques 
		      (Imp (Imp(c,False),b)::implications_doubles) a

	      | Equiv (c,d) ->
		    (* remplacement de c <=> d par (c => d) /\ (d => c) *)
		    preuve (Imp (Conj (Imp(c,d),Imp(d,c)),b)::non_examinees') 
		      atomes implications_atomiques implications_doubles a 

	      | False  ->
		    (* False => b peut-être enlevée *)
		    preuve non_examinees' atomes implications_atomiques implications_doubles a

	  )
      
      | [], a ->
	  (* toutes les hypothèses ont été examinées ainsi que toutes les conclusions sauf
	     celles de la forme False, Var _, Disj _  
	     On applique la règle L0=> réversible

	   *)
   
	  let rec l0imp variables = match variables with
	  | [] -> non_reversibles atomes implications_atomiques implications_doubles a
	  | var::fvar -> 
	      let lg = implicationsgauches implications_atomiques var in
	      (* lg est la liste des b tels que  Imp (var,b) est dans la liste implications_atomiques *)
	      if lg = [] then l0imp fvar
	      else let b = List.hd lg in
	      let paux = preuve [b] atomes (remove (Imp (var,b)) implications_atomiques) 
		implications_doubles a
	      in Usable b :: paux
	  in l0imp atomes
      | _ -> failwith "erreur dans preuve"

and
    non_reversibles atomes implications_atomiques implications_doubles a =
  (* préconditions : 
     Aucune déduction n'est possible sans l'emploi des règles non_réversibles, en particulier
     la règle L0=> n'est pas applicable, autrement dit il n'y a pas de x tel que Var x dans
     la liste atomes et Imp(Var x,_) dans la liste implications_atomiques 
     la conclusion  a est de l'un des formes False, Var _, Disj _ *)
  let rec limpimp ids = match ids with
  | [] -> (match a with
    | False -> raise (Improvable (atomes @ negs implications_atomiques))

    | Var _ -> (* a n'est pas dans gamma donc pas dans atomes *)
		raise (Improvable ((Neg a)::atomes @ negs implications_atomiques))

    |  Disj (b,c) -> 
	(try let pb = preuve [] atomes implications_atomiques implications_doubles b in 
	pb @ [Usable a] 
	with
	| Improvable _ -> 
	    let pc = preuve [] atomes implications_atomiques implications_doubles c in
	    pc @ [Usable a] ))
  | ((Imp (Imp(c,d),b))as y)::fids ->
      let reste_implications_doubles = remove y implications_doubles in
      try 
	let paux1 = preuve [c; Imp(d,b)] atomes implications_atomiques reste_implications_doubles d
	and 
	    paux2 = preuve [b] atomes implications_atomiques reste_implications_doubles a
	in
	(p13 b c d) @ [Assume c] @ paux1 @ [Therefore (Imp (c, d)); Usable b] @ paux2
      with Improvable _ -> limpimp fids

  in limpimp implications_doubles

;;

	    
(* Construction d'une preuve classique suivant une méthode ad'hoc *)

let rec 
    preuvec hypotheses_non_vues hypotheses_exigeant_raa hypotheses_litteraux a =
  (* nommons gamma la liste des hypotheses. le résultat est
   - soit une preuve de a dans l'environnement gamma
   - soit la levée de l'exception (Improuvable ll) où ll est une liste de littéraux modele de gamma et pas de a
  *)
  let da = deplie a in
  let dgamma = deplie_liste (hypotheses_non_vues@hypotheses_exigeant_raa@hypotheses_litteraux) in
    if (* raisonnement en avant *)
      List.mem da dgamma then []
    else if 
      List.mem False dgamma || modusponens dgamma da || conjonctions dgamma da then [Usable a]
    else if modusponens dgamma False then [Usable False; Usable a]
    else (* raisonnement en arriere : on sait qu'il n'y a pas de contradiction immédiate dans le contexte *)
      (* if hypotheses_non_vues = [] && hypotheses_exigeant_raa = [] then 
	 match a with
	 | False -> raise (Improvable hypotheses_litteraux)
	 | Var _ -> (* on sait que : a n'est pas gamma *) raise (Improvable ((Neg a)::hypotheses_litteraux))
	 else *)

      match a with
	| Imp (b,c) -> let r = preuvec (b::hypotheses_non_vues) hypotheses_exigeant_raa hypotheses_litteraux c in
	    [Assume b] @ r @ [Therefore a]
	| Neg b -> let r = preuvec (b::hypotheses_non_vues) hypotheses_exigeant_raa hypotheses_litteraux False in
	      [Assume b] @ r @ [Therefore a]
	| Conj(b,c) -> 
	    let r = preuvec hypotheses_non_vues hypotheses_exigeant_raa hypotheses_litteraux b and
		s = preuvec hypotheses_non_vues hypotheses_exigeant_raa hypotheses_litteraux c in
	      r @ s @ [Usable a]
	| Equiv (b,c) -> 
	    let r = preuvec hypotheses_non_vues hypotheses_exigeant_raa hypotheses_litteraux (Imp (b,c))  and
		s = preuvec hypotheses_non_vues hypotheses_exigeant_raa hypotheses_litteraux (Imp (c,b))  in
	      r @ s @ [Usable a]
	| Disj (b,c) ->
	    (* on tente de prouver b puis c, en cas d'échec on essaie de décomposer les hypotheses *)
	    (try let pb = preuvec hypotheses_non_vues hypotheses_exigeant_raa hypotheses_litteraux b in
	       pb @ [Usable a] 
	     with
	       | Improvable _ ->
		   try let pc = preuvec hypotheses_non_vues hypotheses_exigeant_raa hypotheses_litteraux c in
		     pc @ [Usable a] with
		       | Improvable _ -> 
			   preuve_hypotheses_non_vues 
			     hypotheses_non_vues hypotheses_exigeant_raa hypotheses_litteraux a )
	| _ -> 
	      (* la conclusion est une variable ou False, on essaie de décomposer les hypotheses *)
	    preuve_hypotheses_non_vues hypotheses_non_vues hypotheses_exigeant_raa hypotheses_litteraux a
	      

and 
    preuve_hypotheses_non_vues hypotheses_non_vues hypotheses_exigeant_raa hypotheses_litteraux a =
  (* requiert a est soit une disjonction b \/ c où ni b, ni c ne sont prouvables, soit False, soit une variable  
     a n'est pas dans les hypotheses, il n'y a pas de contradictions immédiates dans les hypotheses
  *)
  if hypotheses_non_vues = [] then 
    (match a with
       | False | Var _ -> preuve_hypotheses_raa  hypotheses_exigeant_raa hypotheses_litteraux a
       | Disj(b,c) -> (* RAA est inévitable, on l'applique pour prouver la conclusion *)
	       
	   let r = preuvec [Neg b]  hypotheses_exigeant_raa hypotheses_litteraux c in
	     [Assume (Neg a);Assume b; Usable a; Usable False; Therefore (Neg b)]
	       @ r @ [Usable a; Usable False;Therefore (Neg (Neg a));Usable a]
	       

    (* Solution écartée 
       let r = preuvec [Neg b;Neg c] hypotheses_exigeant_raa hypotheses_litteraux False in
    (* p1 b c est une preuve de Neg b sachant Neg (Disj (b,c))
       p2 b c est une preuve de Neg c sachant Neg (Disj (b,c)) *)
       [Assume (Neg a)] @ (p1 b c) @ (p2 b c) @ 
       r @ [Therefore (Neg (Neg a))] @ [Usable a]
       Fin solution écartée *)
    )
	    
  else
    let (premiere_hypothese :: fin_hypotheses_non_vues) =  hypotheses_non_vues  in
      match premiere_hypothese with
	| Var _ -> 
	    preuve_hypotheses_non_vues fin_hypotheses_non_vues hypotheses_exigeant_raa 
	      (premiere_hypothese::hypotheses_litteraux) a
	| Neg (Var _) ->
	    preuve_hypotheses_non_vues fin_hypotheses_non_vues hypotheses_exigeant_raa 
	      (premiere_hypothese::hypotheses_litteraux) a
	| Conj (b,c)  -> 
	    let r = preuvec (b::c::fin_hypotheses_non_vues) hypotheses_exigeant_raa hypotheses_litteraux a
	    in [Usable b;Usable c] @ r
	| Disj (b,c) ->
	    let r = preuvec (b::fin_hypotheses_non_vues) hypotheses_exigeant_raa hypotheses_litteraux a
	    and s = preuvec (c::fin_hypotheses_non_vues) hypotheses_exigeant_raa hypotheses_litteraux a
	    in [Assume b] @ r @ [Therefore (Imp (b,a)); Assume c] @ s @ [Therefore (Imp (c,a)); Usable a]
	| Equiv (b,c) ->
	    let r = preuvec (Imp (b,c)::Imp(c,b)::fin_hypotheses_non_vues) 
	      hypotheses_exigeant_raa hypotheses_litteraux a
	    in [Usable (Imp(b,c));Usable (Imp(c,b))] @ r

	
	| Neg False | Imp(False, False)->
	    preuve_hypotheses_non_vues fin_hypotheses_non_vues hypotheses_exigeant_raa 
	      hypotheses_litteraux a
	| Neg (Disj (b,c))| Imp(Disj(b,c),False) ->
	    let r = preuvec (Neg b::Neg c::fin_hypotheses_non_vues) hypotheses_exigeant_raa 
	      hypotheses_litteraux a
	    in (p1 b c) @ (p2 b c) @ r
	| Neg (Neg _)  | Imp (Neg _, False) | Neg (Conj _)| Imp(Conj _,False)
	| Neg (Imp _) | Imp (Imp _, False)  | Neg (Equiv _)| Imp(Equiv _, False) ->
	    preuve_hypotheses_non_vues fin_hypotheses_non_vues 
	      (premiere_hypothese::hypotheses_exigeant_raa) hypotheses_litteraux a 
	| Imp (b,c) ->
	    (* On tente une preuve tout d'abord de prouver b (sans l'implication) puis a à partir de c *)
	    (try 
	       let pb = preuvec fin_hypotheses_non_vues hypotheses_exigeant_raa hypotheses_litteraux b
	       in let pa = preuvec (c::fin_hypotheses_non_vues) hypotheses_exigeant_raa 
		   hypotheses_litteraux a in
		 pb @ [Usable c] @ pa
	     with Improvable _ ->
	       match b with
		 | Conj (d,e) ->
		     (* cas LJT => 2 p797 *)
		     (* (p10 c d e) = preuve de d => (e => c) à partir de (d & e) => c *)
		     let paux = preuvec (Imp(d, Imp(e,c))::fin_hypotheses_non_vues) 
		       hypotheses_exigeant_raa hypotheses_litteraux a 
		     in (p10 c d e) @ paux
		 | Equiv (d,e) ->
		     preuvec (Imp (Conj (Imp(d,e),Imp(e,d)),c) :: fin_hypotheses_non_vues) 
		       hypotheses_exigeant_raa hypotheses_litteraux a 
		 | Disj (d,e) ->
		     (* cas LJT => 3 p797 *)
		     let paux =  preuvec (Imp (d,c)::Imp (e,c)::fin_hypotheses_non_vues)
		       hypotheses_exigeant_raa hypotheses_litteraux a 
		    in (p11 c d e)@ (p12 c d e) @ paux
		 | _ -> preuve_hypotheses_non_vues  fin_hypotheses_non_vues 
		       (premiere_hypothese :: hypotheses_exigeant_raa) hypotheses_litteraux a
	    )		       

	| _ -> failwith "erreur dans preuve_hypotheses_non_vues"

and
    preuve_hypotheses_raa  hypotheses_exigeant_raa hypotheses_litteraux a =
  (* requiert : a est False ou une variable, 
     a n'est pas dans les hypotheses, il n'y a pas de contradictions immédiates dans les hypotheses 
     Les hypotheses exigeant raa sont de l'une des formes Imp(b,c) où b non prouvable et c différent 
     de False,
     Neg (Neg _), Imp (Neg _,False),Neg (Conj _), Imp(Conj _, False), Neg (Imp _), Imp(Imp _,False),
     Neg (Equiv _ ), Imp(Equiv _, False)
  *)
  if hypotheses_exigeant_raa = [] then
    match a with
      | False -> raise (Improvable hypotheses_litteraux)
      | Var _ -> raise (Improvable ((Neg a)::hypotheses_litteraux))
  else
    let (premiere_hypothese::fin_hypotheses)= hypotheses_exigeant_raa in
      match premiere_hypothese with

	| Neg (Neg b) | Imp(Neg b,False) -> 
	    let r = preuvec [b] fin_hypotheses hypotheses_litteraux a
	    in [Usable b] @ r
	| Neg (Conj (b,c)) | Imp(Conj(b,c),False)  ->
	    (* rappel : (p5 b c) est une preuve de Disj(Neg b,Neg c) sachant Neg (Conj(b,c)) *)
	    let r =  preuvec [Neg b] fin_hypotheses hypotheses_litteraux a
	    and s =  preuvec [Neg c] fin_hypotheses hypotheses_litteraux a in
	      (p5 b c) @
	       [Assume (Neg b)]@ r @ [Therefore (Imp (Neg b,a));Assume (Neg c)] @ s @ 
	       [Therefore (Imp (Neg c,a)); Usable a]

	    (* Solution écartée
	    (* rappel : p5 b c est une preuve de Disj(Neg b,Neg c) sachant Neg (Conj(b,c)) *)
	    (p5 b c) @  preuve [Disj (Neg b,Neg c)] fin_hypotheses hypotheses_litteraux a
	    fin solution écartée *)

	| Neg (Imp (b,c)) | Imp(Imp(b,c),False) ->
	    let r = preuvec [b; Neg c] fin_hypotheses hypotheses_litteraux a in
	      (* rappel p6 est une preuve de b sachant Neg (Imp (b,c))
		 p7 est une preuve de Neg c sachant Neg (Imp (b,c)) *)
	      (p6 b c)@ (p7 b c) @ r
	| Neg (Equiv (b,c)) | Imp(Equiv(b,c),False) -> 
	    (* On rappelle qu'une équivalence est une conjonction *)
	    let r = preuvec [Neg (Imp(b,c))] fin_hypotheses hypotheses_litteraux a
	    and s = preuvec [Neg (Imp(c,b))] fin_hypotheses hypotheses_litteraux a  in
	      (p5 (Imp(b,c)) (Imp(c,b))) @
		[Assume (Neg (Imp(b,c)))]@ r @ 
		[Therefore (Imp (Neg (Imp(b,c)),a));Assume (Neg (Imp (c,b)))] @ s @ 
	       [Therefore (Imp (Neg (Imp(c,b)),a)); Usable a]
		

	| Imp(b,c) -> 

	    (* Remarque : c n'est pas False 
	       b est une variable, une implication ou une negation 
	    *)
	    if deplie b = deplie (Neg a) then
	      (* on cherche une preuve par réduction à l'absurde *)
	      (try let pf = preuvec [c] fin_hypotheses hypotheses_litteraux False in
		 [Assume b; Usable c]@pf@[Therefore (Neg b); Usable a]
	       with 
		 | Improvable _ -> 
		     (* rappel : (p3 b c) est une preuve de Disj(Neg b, c) à partir de Imp(b,c) *)
		     let r = preuvec [Neg b] fin_hypotheses hypotheses_litteraux a
		     and s = preuvec [c]  fin_hypotheses hypotheses_litteraux a in
		       (p3 b c) @
			 [Assume (Neg b)]@ r @ [Therefore (Imp (Neg b,a));Assume c] @ s @ 
			 [Therefore (Imp (c,a)); Usable a])
	    else
		
	      let r = preuvec [Neg b] fin_hypotheses hypotheses_litteraux a
	      and s = preuvec [c]  fin_hypotheses hypotheses_litteraux a in
		(p3 b c) @ 
		  [Assume (Neg b)]@ r @ [Therefore (Imp (Neg b,a));Assume c] @ s @ 
		  [Therefore (Imp (c,a)); Usable a]


	       (* Solution écartée 

	    (if c = False then preuve_hypotheses_non_vues [Neg b] fin_hypotheses hypotheses_litteraux a
	    else if  deplie b = deplie (Neg a) then
	      (* on cherche une preuve par réduction à l'absurde *)
		  (try let pf = preuve [c] fin_hypotheses hypotheses_litteraux False in
		  [Assume b; Usable c]@pf@[Therefore (Neg b); Usable a]
		  with 
		  | Improvable _ -> 
		     (p3 b c)@  preuve [Disj (Neg b,c)] fin_hypotheses hypotheses_litteraux a)
		  else (p3 b c)@ preuve [Disj (Neg b,c)] fin_hypotheses hypotheses_litteraux a)

		  fin solution écartée *)

	

	    (* Solution écartée 
	    let r = preuve [Imp (Neg b,c); Imp (c,Neg b)] fin_hypotheses hypotheses_litteraux a in
	      (* p8 est une preuve de Imp (Neg b,c) sachant Neg (Equiv (b,c))
		 p9 est une preuve de Imp (c,Neg b) sachant Neg (Equiv (b,c)) *)
	      (p8 b c) @ (p9 b c) @ r
	    *)
	| _ -> failwith "erreur dans preuve:_hypotheses_raa"
;;
    



let preuve_classique a =
   (* a est une formule
      resultat : si a est classiquement prouvable alors une preuve de a
      exception : Improvable ll une liste de littéraux contre-modèle de a 
      si a est prouvable intuitionistiquement, on en donne une preuve sans raa
      sinon on recherche une preuve classique, si possible  courte (ce qui est
      subjectif) sans utiliser le théorème de Glivenko

   *)
   try preuve [] [] [] [] a
   with | Improvable _ ->  preuvec [] [] []  a ;;




let rec compacter l =
  (* suppression des éléments répétés de l*)
  match l with
    | [] -> []
    | x::m -> if List.mem x m then compacter m else x::compacter m;;

let rec afficher_liste_litteraux l =
  (* l formula list
     effet : affichage des éléments de l séparés par des virgules 
     exception : levée par string_of_litteral si une des formules de l
       n'est pas un littéral
  *)
  match l
  with
    | [] -> ()
    | [a] ->print_string (string_of_litteral a); 
    | a::fl ->print_string (string_of_litteral a);print_string ",";afficher_liste_litteraux fl
;;  
     
(* Compacter une preuve consiste à enlever les lignes de la preuve faisant partie des formules utilisables 
   Il est facile d'enlever les lignes Usable
   Il est plus difficile d'enlever les lignes Therefore car cela impose d'enlever un "bloc"
   Aussi une preuve a une double structure
   - liste de ligne (line list)
   - liste de formules et de preuves
     type preuve_arbre = Atome of formula | Bloc of formula*preuve_arbre list*formula
     Dans une preuve Bloc(h,p,c), h est l'hypothèse du bloc, c la conclusion et p la preuve sous hypothèse c 
   Exemple :
   La preuve                         
   assume p
   p+q
   therefore p => p+q
   assume p
   p+q
   therefore p => p+q
   (p => p+q) & (p => p+q)
   On donne seulement la représentation comme preuve_arbre et on écrit les formules en clair
   [Bloc (p, [Atome p+q],p=>p+q);Bloc (p;[Atome p+q], p=>p+q);Atome (p => p+q) & (p => p+q)] 

   Cette structure permet aisément le compactage des preuves (Atome a, resp Bloc(_,_,a) sont
   inutiles s'ils font partie de la liste des formules utilisables.
   Le passage de la forme arbre_preuve à liste_preuve (=line list) est trivial.
   Le passage inverse est de l'analyse syntaxique descendante LL1 suivant les règles
   preuve -> vide
             Usable a ; preuve
             Assume h; preuve ; Therefore c;preuve

   Pour conclure : on aurait pu ne conserver qu'une seule structure preuve_arbre list
   cela éviterait les conversions entre les deux formats des preuves.
   
 *)


let rec preuve_arbre_liste_de_preuve_ligne_liste l =
  (* l : line list
     résultat (res,lr) 
     res est la première preuve de la liste l 
     lr est  ce qui reste à lire après la reconnaissance de cette première preuve *)

  match l with
    | [] -> ([],[])              (* preuve vide *)
    | Therefore _ ::_ -> ([],l)  (* preuve vide *)
    | Usable a ::l1 -> let (res,l2)=  preuve_arbre_liste_de_preuve_ligne_liste l1 in
	(Atome a::res),l2
    | Assume h :: l1 -> 
	let (res1,l2) = preuve_arbre_liste_de_preuve_ligne_liste l1 in
	  match l2 with
	    | Therefore c::l3 -> 
		let (res2,l4) = preuve_arbre_liste_de_preuve_ligne_liste l3 in
		  (Bloc (h,res1,c)::res2),l4
	    | _ -> failwith "Therefore manquant "
;;
		
	
let rec compacter_preuve_arbre_liste arbre_liste utilisables =
   (* transforme et compacte la preuve arbre_liste dans le contexte utilisables des
      formules utilisables
      résultat (utilisables1,ligne_liste) 
      utilisable1 les formules utilisables après la preuve arbre_liste
      ligne_liste la preuve arbre_liste transformée en ligne_liste 
   *)
  match arbre_liste with
    | [] -> (utilisables,[])
    | arbre::arbre_liste1 ->
	let (utilisable1,preuve_liste_ligne1) = compacter_preuve_arbre arbre utilisables in
	let (utilisable2,preuve_liste_ligne2) = compacter_preuve_arbre_liste arbre_liste1 utilisable1 in
	  utilisable2, (preuve_liste_ligne1 @ preuve_liste_ligne2)
and compacter_preuve_arbre arbre utilisables = 
  match arbre with
    | Atome b -> if List.mem b utilisables then (utilisables,[]) else (b::utilisables),[Usable b]
    | Bloc (h,pla,c) -> 
	if List.mem c utilisables then (utilisables,[])
	else 
	  let (_,pll) = compacter_preuve_arbre_liste pla (h::utilisables) in
	    (c::utilisables),((Assume h ::pll)@[Therefore c])
;;
  


	  





   
   






	    
	 
    
    


