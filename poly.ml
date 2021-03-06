open Expr

(* Sum type to encode efficiently polynomial expressions *)
type pExp =
  | Term of int*int (*
      First int is the constant
      Second int is the power of x
      10  -> Term(10,0)
      2x -> Term(2,1)
      3x^20 -> Term(3, 20)
    *)
  | Plus of pExp list
  (*
    List of terms added
    Plus([Term(2,1); Term(1,0)])
  *)
  | Times of pExp list (* List of terms multiplied *)

(*
  Function to translate betwen AST expressions
  to pExp expressions
*)
let rec from_expr (_e: Expr.expr) : pExp =
    match _e with
      | Num(i) -> Term(i, 0)
      | Var(c) -> Term(1, 1)
      | Add(e1,e2) -> Plus([from_expr e1; from_expr e2])
      | Sub(e1,e2) -> Plus([from_expr e1; from_expr (Neg(e2))])
      | Mul(e1,e2) -> Times([from_expr e1; from_expr e2])
      | Pow(e,i) -> Times( (Array.make i (from_expr e) |> Array.to_list) )
      | Pos(e) -> from_expr e
      | Neg(e) -> Times([Term(-1,0); from_expr e])

(*
  Returns the max degree from a list of pExp expressions
*)
let rec maxDegree (pList: pExp list) (relMax: int): int =
  match pList with
  | [] -> relMax
  | hd::tail ->
    match hd with
    | Term(n,m) ->
      if m > relMax then maxDegree tail m
      else maxDegree tail relMax
    | Plus(ps) -> maxDegree tail ( maxDegree ps relMax )
    | Times(ps) -> maxDegree tail ( sumDegrees ps relMax )

(*
  Returns the sum of degrees from a list of pExp expressions
*)
and sumDegrees (pList: pExp list) (sum: int): int =
  match pList with
  | [] -> sum
  | hd::tail ->
    match hd with
    | Term(n,m) -> sumDegrees tail (m + sum)
    | Plus(ps) -> sumDegrees tail ( maxDegree ps sum )
    | Times(ps) -> sumDegrees tail ( sumDegrees ps sum )

(*
  Compute degree of a polynomial expression.

  Hint 1: Degree of Term(n,m) is m
  Hint 2: Degree of Plus[...] is the max of the degree of args
  Hint 3: Degree of Times[...] is the sum of the degree of args
*)
let degree (_e:pExp): int =
  match _e with
  | Term(n,m) -> m
  | Plus(pList) -> maxDegree pList 0
  | Times(pList) -> sumDegrees pList 0

let compareDegree (e1:pExp) (e2:pExp): int =
  degree e2 - degree e1

(*
  Comparison function useful for sorting of Plus[..] args
  to "normalize them". This way, terms that need to be reduced
  show up one after another.
  *)
let compare (e1: pExp) (e2: pExp) : bool =
  degree e1 > degree e2

(* Print a pExpr nicely
  Term(3,0) -> 3
  Term(5,1) -> 5x
  Term(4,2) -> 4x^2
  Plus... -> () + ()
  Times ... -> ()() .. ()

  Hint 1: Print () around elements that are not Term()
  Hint 2: Recurse on the elements of Plus[..] or Times[..]
*)
let rec print_pExp (_e: pExp): unit =
  match _e with
  | Term(n,m) -> (
    if m = 0 then print_int n
    else if m > 0 then (
      if n > 1 then print_int n
      else print_string "";
      print_string "x";
      if m >= 2 then Printf.printf "^%i" m
    )
  )
  | Plus(pList) -> (
    match pList with
    | hd::tail ->  (
      Printf.printf "("; print_pExp hd; Printf.printf " + ";
      print_pExp_list_plus tail; Printf.printf ")"
    )
    | [] -> ()
  )
  | Times(pList) -> (
    match pList with
    | hd::tail ->  (
      Printf.printf "("; print_pExp hd; Printf.printf " * ";
      print_pExp_list_times tail; Printf.printf ")"
    )
    | [] -> ()
  )

and print_pExp_list_plus (ps:pExp list): unit =
 match ps with
	 | [] -> ()
	 | hd::[] -> print_pExp hd;
	 | hd::tail -> print_pExp hd; Printf.printf " + "; print_pExp_list_plus tail

and print_pExp_list_times (ps:pExp list): unit =
 	match ps with
	| [] -> ()
	| hd::[] -> print_pExp hd;
	| hd::tail -> print_pExp hd; Printf.printf " * "; print_pExp_list_times tail


let distribute (p:pExp) (elem:pExp): pExp =
  Times([p; elem])

let rec flattenTimes (p:pExp list) (fin:pExp list): pExp list =
  match p with
  | [] -> fin
  | hd::tail ->
    match hd with
    | Times(l) -> flattenTimes (l@tail) fin
      | _ -> flattenTimes tail (hd::fin)

let rec flattenPlus (p:pExp list) (fin:pExp list): pExp list =
  match p with
  | [] -> fin
  | hd::tail ->
    match hd with
      | Plus(l) -> flattenPlus (l@tail) fin
      | _ -> flattenPlus tail (hd::fin)

let rec distributer (p:pExp list) (fin:pExp list): pExp list =
  match p with
  | [] -> fin
  | hd::tail ->
    match hd with
      | Plus(l) -> (
        let f el = distribute (List.hd tail) el in
         (Plus((List.map f l)))::fin
      )
      | _ -> distributer tail (hd::fin)

(*
  Function to simplify (one pass) pExpr

  n1 x^m1 * n2 x^m2 -> n1*n2 x^(m1+m2)
  Term(n1,m1)*Term(n2,m2) -> Term(n1*n2,m1+m2)

  Hint 1: Keep terms in Plus[...] sorted
  Hint 2: flatten plus, i.e. Plus[ Plus[..], ..] => Plus[..]
  Hint 3: flatten times, i.e. times of times is times
  Hint 4: Accumulate terms. Term(n1,m)+Term(n2,m) => Term(n1+n2,m)
          Term(n1, m1)*Term(n2,m2) => Term(n1*n2, m1+m2)
  Hint 5: Use distributivity, i.e. Times[Plus[..],] => Plus[Times[..],]
    i.e. Times[Plus[Term(1,1); Term(2,2)]; Term(3,3)]
      => Plus[Times[Term(1,1); Term(3,3)]; Times[Term(2,2); Term(3,3)]]
      => Plus[Term(2,3); Term(6,5)]
  Hint 6: Find other situations that can arise
  TODO: implement
*)
let rec simplify1 (e:pExp): pExp =
    match e with
    | Term(n,m) -> e
    | Plus(pList) -> (
      (*let pp = (List.stable_sort compareDegree pList) in*)
      match pList with
      | [] -> raise (Failure "Plus: did not receive enough arguments")
      | x::[] -> simplify1 x
      | l -> (
        flattenPlus l [] |>
        List.stable_sort compareDegree |>
        List.map simplify1 |>
        applyPlus|>
        Plus
      )
    )
    | Times(pList) -> (
      match pList with
      | [] -> raise (Failure "Times: did not receive enough arguments")
      | x::[] -> simplify1 x
      | l -> (
        let ll = flattenTimes l [] in
        distributer ll [] |>
        List.map simplify1 |>
        applyTimes |>
        Times
      )
    )

and applyPlus (l:pExp list): pExp list =
    match l with
    | [] -> []
    | x::[] -> [x]
    | x::y::tail -> (
      (*try to add x and y*)
      match x, y with
      | Term(n1, m1), Term(n2, m2) -> (
        if m1 = m2 then Term(n1+n2, m1)::tail (*add terms of like degree*)
        else if n1 = 0 && n2 = 0 then tail (*remove 0 terms*)
        else if n1 = 0 then Term(n2, m2)::tail
        else if n2 = 0 then Term(n1, m1)::tail
        else (*can't add x and y, try tail*) (
          x::(applyPlus (y::tail))
        )
      )
      |_,_ -> [simplify1 x; simplify1 y]@tail
    )

and applyTimes (l:pExp list): pExp list =
    match l with
    | [] -> []
    | x::[] -> [x]
    | x::y::tail -> (
      (*multiply x and y*)
      match x, y with
      | Term(n1, m1), Term(n2, m2) -> (
        if n1 = 0 || n2 = 0 then tail
        else Term(n1*n2, m1+m2)::tail
      )
      |_,_ -> [simplify1 x; simplify1 y]@tail
    )

(*
  Compute if two pExp are the same
  Make sure this code works before you work on simplify1
*)
let equal_pExp (_e1: pExp) (_e2: pExp): bool =
  match _e1, _e2 with
  | Term(n1,m1), Term(n2, m2) -> (
	if (n1 = n2 && m1 = m2) then true
  	else false
  )
  | Plus(l1), Plus(l2) -> (
    if l1 = l2 then true
  	else false
  )
  | Times(l1), Times(l2) -> (
    if l1 = l2 then true
  	else false
  )
  | _ -> false

(* Fixed point version of simplify1
  i.e. Apply simplify1 until no
  progress is made
*)
let rec simplify (e:pExp): pExp =
    let rE = simplify1(e) in
      if (equal_pExp e rE) then
        (e)
      else
        (simplify(rE))
