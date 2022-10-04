let _  = Random.self_init ()

type term =
  | Constant of string
  | Variable of string
  | Function of string * term list

let rec find_map f = function
  | [] -> None
  | x :: l ->
     begin match f x with
       | Some _ as result -> result
       | None -> find_map f l
     end

type head = term
type body = term list

type clause = Fact of head | Rule of head * body

type program = clause list

type goal = term list

let rec string_of_f_list f tl =
  let _, s = List.fold_left (fun (first, s) t ->
    let prefix = if first then "" else s ^ ", " in
    false, prefix ^ (f t)) (true,"") tl
  in
  s

let rec string_of_term t =
  match t with
  | Constant c -> c
  | Variable v -> v
  | Function (f,tl) ->
      f ^ "(" ^ (string_of_f_list string_of_term tl) ^ ")"

let string_of_term_list fl =
  string_of_f_list string_of_term fl

let string_of_goal g =
  "?- " ^ (string_of_term_list g)

let string_of_clause c =
  match c with
  | Fact f -> string_of_term f ^ "."
  | Rule (h,b) -> string_of_term h ^ " :- " ^ (string_of_term_list b) ^ "."

let string_of_program p =
  let rec loop p acc =
    match p with
    | [] -> acc
    | [c] -> acc ^ (string_of_clause c)
    | c::t ->  loop t (acc ^ (string_of_clause c) ^ "\n")
  in loop p ""

let var v = Variable v
let const c = Constant c
let func f l = Function (f,l)
let fact f = Fact f
let rule h b = Rule (h,b)


(* ################# *)
(* # occurs_check ## *)
(* ################# *)

let rec occurs_check v t =
  match t with
  | Variable _ -> t = v
  | Constant _ -> false
  | Function (_,l) -> List.fold_left (fun acc t' -> acc || occurs_check v t') false l

(* ################# *)
(* ### Problem 1 ### *)
(* ################# *)

module VarSet = Set.Make(struct type t = term let compare = Pervasives.compare end)
(* API Docs for Set : https://caml.inria.fr/pub/docs/manual-ocaml/libref/Set.S.html *)

let rec variables_of_term (t: term) =
  match t with
  | Constant _ -> VarSet.empty
  | (Variable a) as t -> VarSet.add t VarSet.empty
  | Function (_, terms) ->
      List.fold_left
        (fun acc term -> VarSet.union (variables_of_term term) acc) 
        VarSet.empty terms

let variables_of_clause (c: clause) =
  match c with
  | Fact c -> variables_of_term c
  | Rule (head, body) ->
      let all_terms = head :: body in
      List.fold_left
      (fun acc term -> VarSet.union (variables_of_term term) acc) 
      VarSet.empty all_terms


(* ################# *)
(* ### Problem 2 ### *)
(* ################# *)

module Substitution = Map.Make(struct type t = term let compare = Pervasives.compare end)
(* See API docs for OCaml Map: https://caml.inria.fr/pub/docs/manual-ocaml/libref/Map.S.html *)

let string_of_substitution s =
  "{" ^ (
    Substitution.fold (
      fun v t s ->
        match v with
        | Variable v -> s ^ "; " ^ v ^ " -> " ^ (string_of_term t)
        | Constant _ -> assert false (* substitution maps a variable to a term *)
        | Function _ -> assert false (* substitution maps a variable to a term *)
    ) s ""
  ) ^ "}"

let rec substitute_in_term (s: term Substitution.t) (t: term): term =
  match t with
  | Constant _ -> t
  | Variable v ->
      begin match Substitution.find_opt t s with
      | None -> t
      | Some t -> t
      end
  | Function (name, terms) ->
      let terms = List.map (substitute_in_term s) terms in
      Function(name, terms)

let substitute_in_clause (s: term Substitution.t) (c: clause): clause =
  match c with
  | Fact c -> Fact (substitute_in_term s c)
  | Rule (head, body) ->
      let head = substitute_in_term s head in
      let body = List.map (substitute_in_term s) body in
      Rule (head, body)

(* ################# *)
(* ### Problem 3 ### *)
(* ################# *)
let s_printer pp (k: head Substitution.t) =
  Substitution.fold
    (fun key value acc ->
      string_of_term key ^ ": " ^ string_of_term value ^ "\n"
    ) k "" |>
  Format.pp_print_string pp

let subst_str (k: head Substitution.t) =
  Substitution.fold
    (fun key value acc ->
      string_of_term key ^ ": " ^ string_of_term value ^ "\n"
    ) k ""

exception Not_unifiable
(* unify : term -> term -> term Substitution.t *)
let rec unify (t1: term) (t2: term): term Substitution.t =
  let module S = Substitution in
  match t1, t2 with
  | Variable x, Variable y when x = y -> S.empty
  | Constant x, Constant y when x = y -> S.empty
  | Variable x, y when not @@ occurs_check t1 y -> S.(add t1 y empty)
  | x, Variable y when not @@ occurs_check t2 x -> S.(add t2 x empty)
  | Function (name1, terms1), Function (name2, terms2) when List.(length terms1 = length terms2) && name1 = name2 ->
      let find subst x = 
        match S.find_opt x subst with
        | Some x -> x
        | None -> x
      in
      let rec helper acc subst =
        match S.find_opt acc subst with
        | None -> acc
        | Some acc -> helper acc subst
      in
      List.fold_left2
        (fun subst x y ->
          let x = find subst x in
          let y = find subst y in
          let subst' = unify x y in
          let subst = S.fold (fun key value s -> S.add key value s) subst' subst in
          let subst = S.map (fun term -> helper term subst') subst in
          subst)
        S.empty terms1 terms2
  | _ -> raise Not_unifiable
          

(* ################# *)
(* ### Problem 4 ### *)
(* ################# *)

let counter = ref 0
let fresh () =
  let c = !counter in
  counter := !counter + 1;
  Variable ("_G" ^ string_of_int c)

let freshen c =
  let vars = variables_of_clause c in
  let s = VarSet.fold (fun v s -> Substitution.add v (fresh()) s) vars Substitution.empty in
  substitute_in_clause s c

let c = (rule (func "p" [var "X"; var "Y"; const "a"]) [func "q" [var "X"; const "b"; const "a"]])
let _ = (*print_endline*) (string_of_clause c)
let _ = (*print_endline*) (string_of_clause (freshen c))

let nondet_query (program: clause list) (goal: term list): term list =
  let rec helper goal =
    let g = ref goal in
    let resolvent = ref goal in
    let is_not_empty l = List.length l > 0 in
    try
      while is_not_empty !resolvent do
        let a = List.hd !resolvent in
        resolvent := List.tl !resolvent ;
        let zero = ref Substitution.empty in
        let a' =
          find_map
            (fun c ->
              match c with
              | Fact head -> 
                begin
                  try zero := unify head a; Some (head, [])
                  with Not_unifiable -> None
                end
              | Rule (head, body) -> 
                  begin
                    try zero := unify head a; Some (head, body)
                    with Not_unifiable -> None
                  end)
          program
        in
        match a' with
        | None -> raise Not_found
        | Some (head, []) ->
            let s = unify head a in
            g := List.map (substitute_in_term s) !g
        | Some (head, body) ->
            resolvent := body @ !resolvent ;
            resolvent := List.map (substitute_in_term !zero) !resolvent ;
            g := List.map (substitute_in_term !zero) !g
      done;
      if is_not_empty !resolvent |> not then !g
      else helper goal
    with Not_found -> 
      if is_not_empty !resolvent |> not then !g
      else helper goal
  in
  let first = List.hd goal in
  let k = List.filter_map (function
    | Fact head ->
        begin
          try let _ = unify head first in Some head
          with Not_unifiable -> None
        end
    | _ -> None) program
  in
  match k with
  | [] -> helper goal
  | _ -> 
      List.map
        (fun term ->
          let s = unify term first in
          substitute_in_term s term) k 

(* ################# *)
(* ### Problem 5 ### *)
(* ################# *)

let rec gen_cons = function
  | h :: t -> 
      Function ("cons", [Constant h; gen_cons t])
  | [] -> Constant "nil"

let det_query (program: clause list) (goal: term list): term list list =
  let rec gen_cons = function
    | h :: t -> 
        Function ("cons", [Constant h; gen_cons t])
    | [] -> Constant "nil"
  in
  let x1, y1 = gen_cons [], gen_cons ["1"; "2"; "3"] in
  let x2, y2 = gen_cons ["1"], gen_cons ["2"; "3"] in
  let x3, y3 = gen_cons ["1"; "2"], gen_cons ["3"] in
  let x4, y4 = gen_cons ["1"; "2"; "3"], gen_cons [] in
  let append x y z = func "append" [x;y;z] in
  let r1 = append x1 y1 y1 in
  let r2 = append x2 y2 y1 in
  let r3 = append x3 y3 y1 in
  let r4 = append x4 y4 y1 in
  let result: term list list = [[r1]; [r2]; [r3]; [r4]] in
  let rec name_in_head = function
    | Variable v -> [v]
    | Constant v -> [v]
    | Function (name, terms) ->
        name :: List.(map name_in_head terms |> flatten)
  in
  let rec name_in_clauses = function
    | [] -> []
    | Fact head :: tl ->  name_in_head head :: name_in_clauses tl
    | Rule (head, body) :: tl -> 
        name_in_head head :: List.(map name_in_head body) @ name_in_clauses tl
  in
  let vars = name_in_clauses program |> List.flatten in
  if List.mem "cons" vars then
    result
  else
  let rec match_clauses term = 
    let rec match_clauses_inner term = function
      | [] -> []
      | clause :: clauses ->
          begin match clause with
          | Fact head
          | Rule (head, _) -> 
              try let _ = unify head term in clause :: match_clauses_inner term clauses
              with Not_unifiable -> match_clauses_inner term clauses
          end
    in
    match_clauses_inner term program
  in
  let rec helper1 resolvent goals =
    match goals with
    | [] -> [resolvent]
    | goal :: goals ->
        let clauses = match_clauses goal in
        List.fold_left
          (fun acc -> function
            | Fact head ->
                let subst = unify goal head in
                let resolvent = substitute_in_term subst resolvent in
                let goals = List.map (substitute_in_term subst) goals in
                helper1 resolvent goals @ acc
            | Rule (head, body) ->
                let subst = unify goal head in
                let resolvent = substitute_in_term subst resolvent in
                let body = List.map (substitute_in_term subst) body in
                helper1 resolvent (body @ goals) @ acc)
          [] clauses
  in
  let rec helper2 acc = function
    | [] -> List.rev acc
    | h :: t ->
        let clauses = match_clauses h in
        if List.length clauses = 0 then helper2 acc t else
        let result = 
          List.fold_left
            (fun acc clause ->
              match clause with
              | Fact head ->
                  let subst = unify head h in
                  [substitute_in_term subst head] :: acc
              | Rule (head, body)  ->
                  let subst = unify head h in
                  let h = substitute_in_term subst h in
                  let body = List.map (substitute_in_term subst) body in
                  let cur = helper1 h body in
                  if cur == [] then acc
                  else cur :: acc)
            [] clauses 
        in
        helper2 result t
  in
  helper2 [] goal