
type prop =
  | Symb of string
  | Top
  | Bot
  | Not of prop
  | And of prop * prop
  | Or of prop * prop
  | Imp of prop * prop
  | Equ of prop * prop;;


let f= Equ(And(Symb "a", Symb "c"),Or(Not(Symb "b"),Imp(Symb "c", And(Bot,Top))));;

(* Question 01 *)

let f1= Equ(And(Symb "a", Symb "b"),Or(Not(Symb "a"),Symb "b"));;

let f2= Or(Not(And(Symb "a",Not(Symb "b"))), Not(Imp(Symb "a",Symb "b")));;

let f3= And(Not(Imp(Symb "a", Or(Symb "a",Symb "b"))), Not(Not(And(Symb "a", Or(Symb "b",Not(Symb "c"))))));;

let f4= And(And(And(And(And(Or(Or(Not(Symb "a"),Symb "b"),Symb "d"),Or(Not(Symb "d"),Symb "c")),Or(Symb "c",Symb "a")),Or(Not(Symb "c"),Symb "b")),Or(Not(Symb "c"),Not(Symb "b"))),Or(Not(Symb "b"),Symb "d"));;

(* Question 02 *)

let rec nbc: prop -> int = function
  |Symb x -> 0
  |Top 
  |Bot -> 0
  |Not(p) -> 1+nbc(p)
  |Or(p,q) 
  |And(p,q)
  |Imp(p,q)
  |Equ(p,q) -> 1+nbc(p)+nbc(q);;

(* Question 03 *)

let rec prof: prop -> int = function 
  |Symb x -> 0
  |Top
  |Bot -> 0
  |Not(p) -> 1+prof p
  |Or(p,q)
  |And(p,q)
  |Imp(p,q)
  |Equ(p,q) -> 1+(max(prof p) (prof q));;

(* Question O4 *)

let rec ajouteSiAbsent: 'a -> 'a list -> 'a list= fun x li ->
  match (x,li) with
  |(x,[]) -> [x]
  |(x,t::q) when t<>x -> t::ajouteSiAbsent x q
  |(x,l) -> l;;

let mylist= [1; 2; 3]
let updatedlist = ajouteSiAbsent 3 mylist ;;

let rec union: 'a list -> 'a list -> 'a list = fun l1 l2 -> 
  match(l1,l2) with
  |(l,[]) 
  |([],l) -> l
  |(t::q,x) -> ajouteSiAbsent t (union x q);;

let list1 = [1; 2; 3; 4]
let list2 = [3; 4; 5; 6]
let result = union list1 list2 ;;

let rec sp: prop -> string list =function 
  |Symb x -> [x]
  |Top
  |Bot -> []
  |Not(p) -> (sp p)
  |And(p,q)
  |Or(p,q)
  |Imp(p,q)
  |Equ(p,q) -> (union (sp p) (sp q));;

(* Question 05 *)
  


let rec affiche: prop -> string = function
  | Symb s -> s
  | Top -> "⊤"
  | Bot -> "⊥"
  | Not(p) -> "¬"^affiche(p)
  | And(p,q) -> "("^affiche(p)^" ∧ "^affiche(q)^")"
  | Or(p,q) -> "("^affiche(p)^" ∨ "^affiche(q)^")"
  | Imp(p,q) -> "("^affiche(p)^" ⇒ "^affiche(q)^")"
  | Equ(p,q) -> "("^affiche(p)^" ⇔ "^affiche(q)^")"
;;

(* Question 06 *)

let rec affichePri: prop -> string = fun fbf ->
  match fbf with
  |Symb x -> x
  |Top -> "⊤"
  |Bot -> "⊥"
  |Not(Imp(x,y))->"¬("^affichePri (Imp(x,y))^")" 
  |And(Imp(x,y),z)->"("^affichePri (Imp(x,y))^")∧"^(affichePri z)
  |Or(Imp(x,y),z)->"("^affichePri (Imp(x,y))^")∨"^(affichePri z)
  |Not(Equ(x,y))->"¬("^affichePri (Equ(x,y))^")" 
  |And(Equ(x,y),z)->"("^affichePri (Equ(x,y))^")∧"^(affichePri z)
  |Or(Equ(x,y),z)->"("^affichePri (Equ(x,y))^")∨"^(affichePri z) 
  |Not(x)->"¬"^(affichePri x)
  |And(x,y)->(affiche x)^ " ∧ "^(affichePri y)
  |Or(x,y)->(affiche x)^" ∨ "^(affichePri y)
  |Imp(x,y)->(affiche x)^" ⇒ "^(affichePri y)
  |Equ(x,y)->(affiche x)^" ⇔ "^(affichePri y);;

(* Semantique des propositions *)

type valVerite = Zero | Un ;;
type interpretation = (string * valVerite) list ;;

(* Question 07 *)
 
let i1= [("a",Un);("b",Zero);("c",Un)];;
let i2=[("a",Zero);("b",Zero);("c",Zero)];;
let i3=[("a",Un);("b",Un);("c",Un)];;

(* Question 08 *)

let rec intSymb: string -> interpretation -> valVerite = fun symb inter ->
  match inter with
  |[] -> Zero
  |(x,y)::l ->
      if x=symb then y
      else intSymb symb l;;


(* Question 09 *)

let intNeg: valVerite -> valVerite = function 
  |Zero -> Un
  |Un -> Zero;;

let intAnd: valVerite -> valVerite -> valVerite = fun a b ->
  match a,b with
  |Un,Un -> Un
  |_,_ -> Zero;;

let intOr: valVerite -> valVerite -> valVerite = fun a b ->
  match a,b with
  |Zero,Zero -> Zero
  |_,_ -> Un;;

let intImp: valVerite -> valVerite -> valVerite = fun a b ->
  match a,b with
  |Un,Zero -> Zero
  |_,_ -> Un;;

let intEqu: valVerite -> valVerite -> valVerite = fun a b ->
  match a,b with
  |Zero,Zero -> Un
  |Un,Un -> Un
  |_,_ -> Zero;;

let intTop = Un;;
let intBot = Zero;;

(* Question 10 *)

let rec valV: prop -> interpretation -> valVerite = fun fbf i ->
  match fbf with
  |Top -> intTop
  |Bot -> intBot
  |Symb a -> intSymb a i
  |Not a -> intNeg (valV a i)
  |And(x,y) -> intAnd (valV x i) (valV y i)
  |Or(x,y) -> intOr (valV x i) (valV y i)
  |Imp(x,y) -> intImp (valV x i) (valV y i)
  |Equ(x,y) -> intEqu (valV x i) (valV y i);;

(* Question 11 *)

let modele: prop -> interpretation -> bool = fun fbf inter ->
  valV fbf inter = Un ;;

(* SATISFIABILITE ET VALIDITE *)

(* Question 12 *)

type listeinterpretation = interpretation list;;

let p q = [[("p",Zero);("q",Zero)];[("p",Zero);("q",Un)];[("p",Un);("q",Zero)];[("p",Un);("q",Un)]];;

(* Question 13 *)

let rec consTous: 'a -> 'a list list -> 'a list list = fun e li ->
  match li with 
  |[] -> []
  |hd::tl -> (e::hd)::(consTous e tl);;

let rec ensInt: string list -> listeinterpretation = function
  |[] -> [[]]
  |hd::tl -> (consTous (hd, Zero) (ensInt tl)) @ (consTous (hd,Un) (ensInt tl));;

(* Question 14 *)

let rec existeModele: prop -> listeinterpretation -> bool = fun fbf i ->
  match i with
  |[] -> false
  |hd::tl -> if modele fbf hd = true then true
      else existeModele fbf tl;;

let satisfiable fbf=
  existeModele fbf (ensInt (sp fbf));;

satisfiable (Symb "a");;
satisfiable (Not(Symb "a"));;
satisfiable (And(Symb "a", Symb "b"));;
satisfiable (And(And(Symb "a", Symb "b"), Not(Symb "a")));;
satisfiable f1;;
satisfiable f2;;
satisfiable f3;;
satisfiable f4;;

(* Question 15 *)

let rec tousModele: prop -> listeinterpretation -> bool = fun fbf i -> 
  match i with 
  |[] -> true
  |hd::tl -> if (valV fbf hd) = Zero then false
      else tousModele fbf tl;;

let valide: prop -> bool =fun fbf ->
  tousModele fbf (ensInt(sp fbf));;

valide (Symb "a");;
valide (Not(Symb "a"));;
valide (And(Symb "a", Symb "b"));;
valide (And(And(Symb "a", Symb "b"), Not(Symb "a")));;
valide f1;;
valide f2;;
valide f3;;
valide f4;;

(* Question 16 *)
let rec aucunModele: prop -> (string * valVerite) list list -> bool = 
  fun f l -> match l with
    | [] -> true
    | hd::tl -> if (modele f hd) then false else aucunModele f tl
;;
  
let insatisfiable: prop -> bool = fun fbf -> 
  aucunModele fbf (ensInt (sp fbf))
;;

insatisfiable (And(Symb "a", Not(Symb "a")));;

(* EQUIVALENCE ET CONSEQUENCE LOGIQUE *)

(* Question 16 *)

let rec memesModeles: prop -> prop -> listeinterpretation -> bool= fun f1 f2 li ->
  match (f1,f2,li) with
  |(f1,f2,[]) -> true
  |(f1,f2,hd::tl) when (valV f1 hd)=(valV f2 hd) -> memesModeles f1 f2 tl
  |(_,_,_) -> false ;;

let equivalent1: prop -> prop -> bool = fun f1 f2 ->
  memesModeles f1 f2 (ensInt (union (sp f1) (sp f2))) ;;

let equivalent2 : prop -> prop -> bool = fun f1 f2 ->
  valide(Equ(f1,f2));;


let f5 = Or(Or(Symb "a", Symb "b"), Not(Symb "a"));;
let f6 = Not(And(And(Symb "c", Symb "d"), Not(Symb "c")));;

equivalent1 f5 f6;;
equivalent2 f5 f6;;

(* Question 18 *)

let consequence2: prop -> prop -> bool = fun l1 l2 ->
  valide(Imp(f1, f2))
;;

consequence2 (Symb "a") (Or(Symb "a", Symb "b"));; (* true *)
consequence2 (Symb "a") (And(Symb "a", Symb "b"));; (* false *)
consequence2 f5 f6;; (* true *)
consequence2 (And(And(Symb "a", Symb "b"), Not(Symb "a"))) (Or(Symb "c", Symb "d"));; (* true *)
  

(* Question 19 *)
let rec tousSp: prop list -> string list = function
  |[] -> []
  |hd::tl -> union (sp hd) (tousSp tl) ;;

(* Question 20 *)

let rec modeleCommun: prop list -> interpretation -> bool = fun li i ->
  match li with 
  |[] -> true
  |hd::tl -> if modele hd i then modeleCommun tl i
      else false ;;

(* Question 21 *) 

let rec aucunModeleCommun: prop list -> (string * valVerite) list list -> bool = 
  fun l1 l2 -> match l2 with
    | [] -> true
    | hd::tl -> if (modeleCommun l1 hd) then false else aucunModeleCommun l1 tl
;; 

let contradictoire: prop list -> bool = fun l ->
  aucunModeleCommun l (ensInt (tousSp l))
;;
(* Question 22 *)


let rec modeleCommunEtModele: prop list -> (string * valVerite) list list -> prop -> bool =
  fun l1 l2 fbf -> match l2 with
    | [] -> true
    | hd::tl -> if (modeleCommun l1 hd && not (modele fbf hd)) then false else modeleCommunEtModele l1 tl fbf
;;

let consequence: prop list -> prop -> bool = fun l fbf ->
  modeleCommunEtModele l (ensInt (tousSp l)) fbf
;;

(* Question 23 *)

let rec conjonction: prop list -> prop = function 
  |[]->Top
  |hd::tl->if tl=[] then hd
      else And(hd,conjonction tl);;

let consequenceV:prop list -> prop -> bool =fun ensProp prop -> 
  valide (Imp(conjonction ensProp,prop));;

(* Question 24 *)

let consequenceI:prop list -> prop -> bool= fun ensProp fbf ->
  insatisfiable(conjonction (ensProp @ [Not(fbf)]));;


consequence [And(Symb "a", Symb "b"); Not(Symb "a"); Imp(Symb "b", Symb "d")] (Imp(Symb "c", Symb "d"));; 
consequenceV [And(Symb "a", Symb "b"); Not(Symb "a"); Imp(Symb "b", Symb "d")] (Imp(Symb "c", Symb "d"));;
consequenceI [And(Symb "a", Symb "b"); Not(Symb "a"); Imp(Symb "b", Symb "d")] (Imp(Symb "c", Symb "d"));;
       
let pl = [And(Symb "a", Symb "b");Not(Symb "c");Imp(Symb "d", Symb "a")];;
let cons = Not(Symb "b");;

consequence pl cons;;
consequenceV pl cons;;
consequenceI pl cons;;
