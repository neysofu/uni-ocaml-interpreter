type ide = string;;

(* Questi sono tutti i costrutti e le operazioni permesse nel linguaggio didattico. Comprende tutte le operazioni del linguaggio base più:
 * - L'intruduzione delle stringhe.
 * - L'intruduzione degli insiemi.
 * - Le operazioni sugli insiemi. *)
type exp =
  | Eint of int
  | Ebool of bool
  | Estring of string
  | Eset of string
  | Singleton of exp * exp
  (* Operazioni di base sugli insiemi. *)
  | Union of exp * exp
  | Intersection of exp * exp
  | SetDifference of exp * exp
  | SetAdd of exp * exp
  | SetRemove of exp * exp
  | IsEmpty of exp
  | IsIn of exp * exp
  | IsSubsetOf of exp * exp
  | Min of exp
  | Max of exp
  (* Operazioni di natura funzionale sugli insiemi. *)
  | ForAll of exp * exp
  | Exists of exp * exp
  | Filter of exp * exp
  | Map of exp * exp
  (* Altri operatori di base e costrutti inclusi nel linguaggio. *)
  | Den of ide
  | Prod of exp * exp
  | Sum of exp * exp
  | Diff of exp * exp
  | Eq of exp * exp
  | Minus of exp
  | IsZero of exp
  | Or of exp * exp
  | And of exp * exp
  | Not of exp
  | Ifthenelse of exp * exp * exp
  | Let of ide * exp * exp
  | Fun of ide * exp
  | FunCall of exp * exp
  | Letrec of ide * exp * exp;;

(* Ambiente polimorfo. *)
type 't env = ide -> 't;;

let emptyenv (v : 't) = function x -> v;;

let applyenv (r : 't env) (i : ide) = r i;;

let bind (r : 't env) (i : ide) (v : 't) = function
  | x -> if x = i then v else applyenv r x;;

(* Tipi esprimibili. *)
type evT =
  | Int of int
  | Bool of bool
  | String of string
  (* `Set` è parametrizzato su un tipo a scelta tra `Int`, `Bool` e `String`.
   * Vedi `typecheck_set` per maggiori informazioni.
   *
   * La struttura interna di implementazione è una lista. *)
  | Set of string * evT list
  | Unbound
  | FunVal of evFun
  | RecFunVal of ide * evFun
  and evFun = ide * exp * evT env;;

(* Questa funzione ottiene l'ambiente all'interno del quale è definita una
 * funzione, ricorsiva o meno. *)
let get_env (v : evT) : evT env = match v with
  | FunVal (_, _, r) -> r
  | RecFunVal (_, (_, _, r)) -> r
  | _ -> failwith "No environment"

(* === RTS: === *)

(* --- Type checking. --- *)

let typecheck (s : string) (v : evT) : bool =
  match s with
  | "int" -> (match v with Int _ -> true | _ -> false)
  | "bool" -> (match v with Bool _ -> true | _ -> false)
  | "string" -> (match v with String _ -> true | _ -> false)
  | "function" -> (match v with FunVal _ -> true | RecFunVal _ -> true | _ -> false)
  | _ -> failwith "Not a valid type";;

(* Verifica che la parametrizzazione di `Set` sia su uno dei tipi consentiti.
 * Se è così allora la funzione restituisce il suo input invariato (identità),
 * altrimenti solleva un'eccezione. *)
let typecheck_set (v : evT) : evT =
  match v with
  | Set ("int", _) -> v
  | Set ("bool", _) -> v
  | Set ("string", _) -> v
  | _ -> failwith "Invalid set type";;

(* --- Funzioni di utility. --- *)

let rec list_contains (ls : 'a list) (x : 'a) : bool =
  match ls with
  | [] -> false
  | v::t -> v = x || list_contains t x;;

let rec list_remove (ls : 'a list) (x : 'a) : 'a list =
  match ls with
  | [] -> []
  | v::t -> if v = x then t else v::(list_remove t x);;

let rec list_as_set_eq (l1: 'a list) (l2: 'a list) : bool =
  match l1 with
  | [] -> l2 = []
  | x::t -> (list_contains l2 x) && list_as_set_eq t (list_remove l2 x)

(* Questa funzione viene usata nelle operazioni su `Set` per rimuovere i
 * possibili duplicati. *)
let rec list_unique (ls: 'a list) : 'a list =
  match ls with
  | [] -> []
  | v::tail -> if list_contains tail v then list_unique tail else v :: list_unique tail;;

(* --- Operazioni di base sugli insiemi. --- *)

let set_add set value = match set with
  | Set (t, ls) when typecheck t value ->
      if list_contains ls value then set else Set (t, value::ls)
  | _ -> failwith "Type error";;

let set_remove set value = match set with
  | Set (t, ls) when typecheck t value -> Set (t, list_remove ls value)
  | _ -> failwith "Type error";;

let isempty s = match s with
  | Set (_, []) -> Bool true
  | Set (_, _) -> Bool false
  | _ -> failwith "Type error";;

let rec contains s v = match s with
  | Set (_, ls) -> Bool (list_contains ls v)
  | _ -> failwith "Type error";;

let rec issubsetof set1 set2 =
  let rec list_is_subset l1 l2 = match l1 with
    | [] -> true
    | x::tail -> list_contains l2 x && list_is_subset tail l2 in
  match (set1, set2) with
  | Set (t1, _), Set (t2, _) when t1 <> t2 -> failwith "Type error"
  | Set (_, l1), Set (_, l2) -> Bool (list_is_subset l1 l2)
  | _ -> failwith "Type error";;

(* Trova l'elemento "migliore" in un insieme secondo una qualche metrica `f`
 * (usato per trovare il massimo e il minimo). *)
let best s f =
  let rec find_best (ls : 'a list) (x : 'a) : 'a = match ls with
    | [] -> x
    | y::tail -> find_best tail (f x y) in
  match s with
  | Set (_, []) -> failwith "Unexpected empty set"
  | Set (_, v::t) -> find_best t v
  | _ -> failwith "Type error";;

let min s = best s (fun x y -> if x < y then x else y);;

let max s = best s (fun x y -> if x > y then x else y);;

let rec union set1 set2 = match (set1, set2) with
  | Set (t1, _), Set (t2, _) when t1 <> t2 -> failwith "Type error"
  (* Alla fine eliminiamo i possibili duplicati. *)
  | Set (t, ls), Set (_, []) -> Set (t, list_unique ls)
  | Set _, Set (_, v::_) -> union (set_add set1 v) (set_remove set2 v)
  | _ -> failwith "Type error";;

let intersection set1 set2 = match (set1, set2) with
  | Set (t1, _), Set (t2, _) when t1 <> t2 -> failwith "Type error"
  | Set (t, l1), Set (_, l2) ->
      let rec common_elements (l : 'a list) (acc : 'a list) : 'a list =
        match l with
        | [] -> acc
        | v::t -> common_elements t (if list_contains l2 v then v::acc else acc) in
      (* Non c'è bisogno di rimuovere i duplicati dopo l'intersezione. *)
      Set (t, common_elements l1 [])
  | _ -> failwith "Type error";;

let set_difference set1 set2 = match (set1, set2) with
  | Set (t1, _), Set (t2, _) when t1 <> t2 -> failwith "Type error"
  | Set (t, l1), Set (_, l2) ->
      let rec diff_elements (l : 'a list) (acc : 'a list) : 'a list =
        match l with
        | [] -> acc
        | v::t -> diff_elements t (if not (list_contains l2 v) then v::acc else acc) in
      (* Non c'è bisogno di rimuovere i duplicati dopo la differenza. *)
      Set (t, diff_elements l1 [])
  | _ -> failwith "Type error";;

(* --- Operazioni di natura funzionale sugli insiemi. --- *)

let rec forall pred set caller =
  let env = get_env pred in
  match (pred, set) with
    | f, Set (t, []) -> Bool true
    | f, Set (t, v::tail) ->
        let valid = caller pred v env in
        if valid = Bool true then forall pred (Set (t, tail)) caller
        else Bool false
    | _ -> failwith "Type error";;
    
let rec exists pred set caller =
  let env = get_env pred in
  match (pred, set) with
    | f, Set (t, []) -> Bool false
    | f, Set (t, v::tail) ->
        let found = caller pred v env in
        if found = Bool true then found
        else exists pred (Set (t, tail)) caller
    | _ -> failwith "Type error";;

let filter pred set caller =
  let env = get_env pred in
  let rec filter_list (ls : evT list) : evT list = match ls with
    | [] -> []
    | v::tail ->
        let valid = caller pred v env in
        if valid = Bool true then v :: filter_list tail
        else filter_list tail in
  match set with
    | Set (t, ls) -> Set (t, filter_list ls)
    | _ -> failwith "Type error";;

let map f set caller =
  let env = get_env f in
  let rec map_list (ls : evT list) : evT list = match ls with
    | [] -> []
    | v::tail -> caller f v env :: map_list tail in
  match set with
    (* Alla fine rimuoviamo i possibili duplicati. *)
    | Set (t, ls) -> Set (t, list_unique (map_list ls))
    | _ -> failwith "Type error";;

(* --- Altri operatori di base inclusi nel linguaggio. --- *)

let prod x y = match (x, y) with
  | Int n, Int m -> Int (n * m)
  | _ -> failwith "Type error";;

let sum x y = match (x, y) with
  | Int n, Int m -> Int (n + m)
  | String set1, String set2 -> String (set1 ^ set2)
  | _ -> failwith "Type error";;

let minus x = match x with
  | Int n -> Int (-n)
  | _ -> failwith "Type error";;

let diff x y = match (x, y) with
  | Int n, Int m -> Int (n - m)
  | _ -> failwith "Type error";;

let iszero x = match x with
  | Int n -> Bool (n = 0)
  | _ -> failwith "Type error";;

let eq x y = match (x, y) with
  | Int n, Int m -> Bool (n = m)
  | String set1, String set2 -> Bool (set1 = set2)
  | Bool s, Bool t -> Bool (s = t)
  | Set (t1, l1), Set (t2, l2) when t1 = t2 -> Bool (list_as_set_eq l1 l2)
  | _ -> failwith "Type error";;

let vel x y = match (x, y) with
  | Bool s, Bool t -> Bool (s || t)
  | _ -> failwith "Type error";;

let et x y = match (x, y) with
  | Bool s, Bool t -> Bool (s && t)
  | _ -> failwith "Type error";;

let non x = match x with
  | Bool true -> Bool false
  | Bool false -> Bool true
  | _ -> failwith "Type error";;

(* Interprete. *)
let rec eval (e : exp) (r : evT env) : evT = match e with
  (* Construttori per le costanti. *)
  | Eint n -> Int n
  | Ebool b -> Bool b
  | Estring s -> String s
  | Eset t -> typecheck_set (Set (t, []))
  | Singleton (v, t) -> (match t with
      | Estring t -> typecheck_set (Set (t, [eval v r]))
      | _ -> failwith "A set's type parameter must be a string")
  (* Operazioni di base sugli insiemi. *)
  | Union (s, t) -> union (eval s r) (eval t r)
  | Intersection (s, t) -> intersection (eval s r) (eval t r)
  | SetDifference (s, t) -> set_difference (eval s r) (eval t r)
  | SetAdd (s, x) -> set_add (eval s r) (eval x r)
  | SetRemove (s, x) -> set_remove (eval s r) (eval x r)
  | IsEmpty s -> isempty (eval s r)
  | IsIn (v, s) -> contains (eval s r) (eval v r)
  | IsSubsetOf (s, t) -> issubsetof (eval s r) (eval t r)
  | Min s -> min (eval s r)
  | Max s -> max (eval s r)
  | ForAll (p, s) -> forall (eval p r) (eval s r) call
  | Exists (p, s) -> exists (eval p r) (eval s r) call
  | Filter (p, s) -> filter (eval p r) (eval s r) call
  | Map (p, s) -> map (eval p r) (eval s r) call
  (* Altri operatori di base e costrutti inclusi nel linguaggio. *)
  | IsZero a -> iszero (eval a r)
  | Den i -> applyenv r i
  | Eq (a, b) -> eq (eval a r) (eval b r)
  | Prod (a, b) -> prod (eval a r) (eval b r)
  | Sum (a, b) -> sum (eval a r) (eval b r)
  | Diff (a, b) -> diff (eval a r) (eval b r)
  | Minus a -> minus (eval a r)
  | And (a, b) -> et (eval a r) (eval b r)
  | Or (a, b) -> vel (eval a r) (eval b r)
  | Not a -> non (eval a r)
  | Ifthenelse (a, b, c) ->
      let g = eval a r in
      if g = Bool true then eval b r
      else if g = Bool false then eval c r
      else failwith "Non-boolean guard"
  | Let (i, e1, e2) -> eval e2 (bind r i (eval e1 r))
  | Fun (i, a) -> FunVal (i, a, r)
  | FunCall (f, eArg) -> call (eval f r) (eval eArg r) r
  | Letrec (f, funDef, letBody) -> (
      match funDef with
      | Fun (i, fBody) ->
          let r1 = bind r f (RecFunVal (f, (i, fBody, r))) in
          eval letBody r1
      | _ -> failwith "non functional def")
and call fClosure aVal r =
  match fClosure with
  | FunVal (arg, fBody, fDecEnv) ->
      eval fBody (bind fDecEnv arg aVal)
  | RecFunVal (g, (arg, fBody, fDecEnv)) ->
      let rEnv = bind fDecEnv g fClosure in
      let aEnv = bind rEnv arg aVal in
      eval fBody aEnv
  | _ -> failwith "Non-functional value";;

(* === TESTS === *)

(* Ambiente vuoto (senza 'let'). *)
let env0 = emptyenv Unbound;;

let result = eval (FunCall (Fun ("y", Sum (Den "y", Eint 1)), Eint 3)) env0 in
assert (result = Int 4);;

let result = eval (FunCall (Let ("x", Eint 2, Fun ("y", Sum (Den "y", Den "x"))), Eint 3)) env0 in
assert (result = Int 5);;

let result = eval (ForAll (Fun ("y", Ebool true), Eset "string")) env0 in
assert (result = Bool true);;

let result = eval (Exists (Fun ("y", Ebool true), Eset "string")) env0 in
assert (result = Bool false);;

let result = eval (Exists (Fun ("y", Eq (Den ("y"), Eint 42)), (Singleton (Eint 42, Estring "int")))) env0 in
assert (result = Bool true);;

let result = eval (IsEmpty (SetRemove (Union (Singleton (Estring "foo", Estring "string"),
                                              Singleton (Estring "foo", Estring "string")),
                                      Estring "foo"))) env0 in
assert (result = Bool true);;

let result = eval (IsEmpty (Intersection (Singleton (Estring "foo", Estring "string"),
                                          Singleton (Estring "bar", Estring "string")))) env0 in
assert (result = Bool true);;

let result = eval (IsIn (Estring "foobar",
                         SetDifference (SetAdd (Singleton (Estring "foobar", Estring "string"), Estring "foo"),
                                        Singleton (Estring "foobar", Estring "string")))) env0 in
assert (result = Bool false);;

let result = eval (ForAll (Fun ("y", Eq (Den ("y"), Eint 42)), (Singleton (Eint 42, Estring "int")))) env0 in
assert (result = Bool true);;

let result = eval (IsEmpty (SetRemove (SetAdd (Eset "int", Eint 100), Eint 100))) env0 in
assert (result = Bool true);;

let result = eval (IsSubsetOf (Eset "int", Singleton (Eint 100, Estring "int"))) env0 in
assert (result = Bool true);;

let test_pred = Fun ("y", Or (Eq (Den "y", Eint 42), IsZero (Den "y")));;

let result = eval (IsEmpty (Filter (test_pred, Singleton (Eint 42, Estring "int")))) env0 in
assert (result = Bool false);;

let result = eval (ForAll (test_pred, Singleton (Eint 42, Estring "int"))) env0 in
assert (result = Bool true);;

let result = eval (ForAll (test_pred, SetAdd (Singleton (Eint 42, Estring "int"), Eint 43))) env0 in
assert (result = Bool false);;

let result = eval (Min (SetAdd (Singleton (Eint 42, Estring "int"), Eint 43))) env0 in
assert (result = Int 42);;

let result = eval (Max (SetAdd (Singleton (Eint 42, Estring "int"), Eint 43))) env0 in
assert (result = Int 43);;

let result = eval (Max (SetAdd (Singleton (Ebool true, Estring "bool"), Ebool false))) env0 in
assert (result = Bool true);;

let plus_1 = Fun ("y", Sum (Den "y", Eint 1));;

let result = eval (Min (Map (plus_1, SetAdd (Singleton (Eint 42, Estring "int"), Eint 43)))) env0 in
assert (result = Int 43);;