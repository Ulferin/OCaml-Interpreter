(* Exceptions *)
exception Unbound of string;;
exception UnknowType of string;;
exception TypeError of string;;
exception NonFunctionalValue of string;;

(* Environment *)
type 't env = (string * 't) list;;


(* Environment lookup function *)
let rec applyenv(x, env) = match env with
  |[] -> raise (Unbound(x))
  |(x1, v1)::env1 -> if x = x1 then v1 else applyenv(x, env1);;    


(* Environment extension *)
let bind(x, v, r) = (x, v)::r;;


(* Environment extension with list *)
let rec bindlist(l, r) = match l with
  |[] -> r
  |(x1,v1)::r1 -> bindlist(r1, bind(x1, v1, r));;


(* Syntax *)
type ide = string;;

type exp = 
  |Eint of int
  |Ebool of bool
  |Den of ide                     (* Identifiers *)
  |Sum of exp * exp
  |Diff of exp * exp
  |Prod of exp * exp
  |Eq of exp * exp
  |Minus of exp
  |Iszero of exp
  |Or of exp * exp
  |And of exp * exp
  |Not of exp
  |Ifthenelse of exp * exp * exp  (* Conditional *)
  |Let of ide * exp * exp         (* Declaration *)
  |Fun of ide * exp               (* Function declaration *)
  |Apply of exp * exp             (* Function application *)
  |Etup of tuple
  |Pipe of tuple                  (* Function concatenation *)
  |ManyTimes of int * exp         (* Iterative function application *)
and tuple =
  |Nil
  |Seq of exp * tuple;;


(* Values (function are also values in a functional language) *)
type eval =
  |Int of int 
  |Bool of bool
  |Tup of eval list
  |Funval of ide * exp * eval env;;


(* Dynamic typechecker *)
let typecheck(x, y) = match x with
  |"int" -> (match y with 
                |Int(n) -> true
                |_ -> false)
  |"bool" -> (match y with
                |Bool(b) -> true
                |_->false)
  |_ -> raise (UnknowType(x));;


(* Semantics functions *)


(* Sum *)
let sum(x, y) = 
  if typecheck("int", x) && typecheck("int", y) then  
    (match (x,y) with 
      |(Int(u), Int(v)) -> Int(u + v)
      | _ -> failwith ("Sum: error"))
  else raise (TypeError("Sum"));;


(* Diff *)
let diff(x, y) =
  if typecheck("int", x) && typecheck("int", y) then
    (match (x,y) with 
      |(Int(u), Int(v)) -> Int(u - v)
      |_ -> failwith ("Diff: error"))
  else raise (TypeError("Diff"));;


(* Prod *)
let prod(x, y) =
  if typecheck("int", x) && typecheck("int", y) then
    (match (x, y) with 
      |(Int(u), Int(v)) -> Int(u * v)
      |_ -> failwith ("Prod: error"))
  else raise (TypeError("Prod"));;


(* Zero check *)
let iszero(x) =
  if typecheck("int",x) then
    (match x with
      |Int(u)->if u=0 then Bool(true) else Bool(false)
      |_ -> failwith ("Iszero: error"))
  else raise (TypeError("Iszero"));;


(* Equality *)
let eq(x, y) =
  if typecheck("int", x) && typecheck("int", y) then
    (match (x, y) with 
      |(Int(u), Int(w)) -> if u=w then Bool(true) else Bool(false)
      |_ -> failwith ("Eq: error"))
  else raise (TypeError("Eq"));;


(* Opposite *)
let minus(x) =
  if typecheck("int",x) then
    (match x with
      |Int(u)->Int(-u)
      |_ -> failwith ("Minus: error"))
  else raise (TypeError("Minus"));;


(* And *)
let b_and(x, y) =
  if typecheck("bool", x) && typecheck("bool", y) then
    (match (x, y) with 
      |(Bool(u), Bool(w)) -> Bool(u && w)
      |_ -> failwith("And: error"))
  else raise (TypeError("And"));;


(* Or *)
let b_or(x, y) =
  if typecheck("bool",x) && typecheck("bool", y) then
    (match (x, y) with 
      |(Bool(u), Bool(w)) -> Bool(u || w)
      |_ -> failwith ("Or: error"))
  else raise (TypeError("Or"));;


(* Negation *)
let b_not(x) =
  if typecheck("bool", x) then
    (match x with 
      |Bool(u) -> Bool(not(u))
      |_ -> failwith ("Not: error"))
  else raise (TypeError("Not"));;


(* Auxiliary function Apply with closure Tup(l) *)
let rec reverse l = match l with
  |[] -> []
  |e1::tl -> match e1 with
              |Funval(x1,b1,r4) -> reverse tl @ [e1]
              |Tup(l1) -> reverse tl @ reverse l1
              |_ -> raise (NonFunctionalValue("reverse"));;


(* Static scope language interpreter *)
let rec sem((e:exp),(r:eval env)) : eval = match e with
  |Eint(n) -> Int(n)
  |Ebool(b) -> Bool(b)
  |Den(i) -> applyenv(i,r)
  |Sum(e1,e2) -> sum(sem(e1,r), sem(e2,r))
  |Diff(e1,e2) -> diff(sem(e1,r), sem(e2,r))
  |Prod(e1,e2) -> prod(sem(e1,r), sem(e2,r))
  |Eq(e1,e2) -> eq(sem(e1,r), sem(e2,r))
  |Minus(e1) -> minus(sem(e1,r))
  |Iszero(e1) -> iszero(sem(e1,r))
  |Or(e1,e2) -> b_or(sem(e1,r), sem(e2,r))
  |And(e1,e2) -> b_and(sem(e1,r), sem(e2,r))
  |Not(e1) -> b_not(sem(e1,r))
  |Ifthenelse(g,e1,e2) -> let guard = sem(g,r) in
      if typecheck("bool", guard) then
        (if guard = Bool(true) then sem(e1,r) else sem(e2,r))
      else raise (TypeError("Ifthenelse(non-boolean guard)"))
  |Let(x,v,lb) -> sem(lb,bind(x,sem(v,r),r))
  |Fun(p,fb) -> Funval(p,fb,r)
  |Apply(fname,arg) -> (let v = sem(arg,r) in
                        let closure = sem(fname,r) in
                          match closure with
                            |Funval(par,fbody,fenv) -> sem(fbody,bind(par,v,fenv))
                            |Tup(l) -> let rec sem_list lst v = match lst with
                                          |Funval(par,fbody,fenv)::[] -> sem(fbody,bind(par,v,fenv))
                                          |Funval(par,fbody,fenv)::tl -> sem(fbody,bind(par,sem_list tl v,fenv))
                                          |_ -> raise (NonFunctionalValue("Apply(sem_list)"))
                                       in sem_list (reverse l) v
                            |_ -> raise (NonFunctionalValue("Apply")))
  |Etup(t) -> let rec tup_list(t) = match t with
                |Nil -> []
                |Seq(e1,t1) -> sem(e1,r)::(tup_list t1)
              in Tup(tup_list t)
  |Pipe(t) -> let rec tup_list(t) = match t with
                |Nil -> []
                |Seq(Den(f),t1) -> sem(Den(f),r)::(tup_list t1)
                |Seq(ManyTimes(n,f),t1) -> sem(ManyTimes(n,f),r)::(tup_list t1)
                |Seq(_,_) -> raise (NonFunctionalValue("tup_list"))
              in Tup(tup_list t) (* Function concatenation *)
  |ManyTimes(n,f) -> let rec n_times ((n:int), (foo:exp)) = 
                        match n with
                          |0 -> []
                          |_ -> sem(foo,r)::n_times(n-1,foo)
                     in Tup(n_times(n,f)) (* Iterative function application *);;



(* TESTS *)


(* 1 - Function declaration and function call *)
print_string("Test 1: ");;
if(
  sem(
    Let("incr",Fun("x",Sum(Eint(1),Den("x"))),    (* incr function declaration *)
      Apply(Den("incr"),Eint(5)))                 (* incr application on 5 *)
  ,[]) = Int(6)) then print_string("ok\n") else print_string("fallito\n");;   (* expected result: Int(6) *)


(* 2 - Declaration and call of functions in pipe inside apply *)
print_string("Test 2: ");;
if(
  sem(
    Let("incr", Fun("x",Sum(Eint(1),Den("x"))),       (* Function declaration incr *)
      Let("decr", Fun("x",Diff(Den("x"),Eint(1))),    (* Function declaration decr *)
        Let("add5", Fun("x",Sum(Eint(5),Den("x"))),   (* Function declaration add5 *)
          Apply(                                      (* call on undefined pipe *)
            Pipe(Seq(Den("add5"),Seq(Den("incr"),Nil))),Eint(5)
          )
        )
      )
    )
  ,[]) = Int(11)) then print_string("ok\n") else print_string("fallito\n");;  (* expected result: Int(11) *)


(* 3 - Declaration and call of functions in pipe (x) with manytimes *)
print_string("Test 3: ");;
if(
  sem (
    Let("incr", Fun("x",Sum(Eint(1),Den("x"))),       (* Function declaration incr *)
      Let("decr", Fun("x",Diff(Den("x"),Eint(1))),    (* Function declaration decr *)
        Let("add5", Fun("x",Sum(Eint(5),Den("x"))),   (* Function declaration add5 *)
          Let("x",Pipe(Seq(Den("add5"),Seq(Den("incr"),Seq(ManyTimes(5,Den("incr")),Nil)))),  (* Pipe declaration *)
            Apply(                                    (* call of previously declared Pipe *)
              Den("x"),Eint(5)
            )
          )
        )
      )
    )
  ,[]) = Int(16)) then print_string("ok\n") else print_string("fallito\n");;  (* expected result: Int(16) *)


(* 4 - Function declaration, manytimes declaration, pipe declaration *)
print_string("Test 4: ");;
if(
  sem(
    Let("incr",Fun("x",Sum(Den("x"),Eint(1))),        (* Function declaration incr *)
      Let("decr", Fun("x",Diff(Den("x"),Eint(1))),    (* Function declaration decr *)
        Let("add5", Fun("x",Sum(Eint(5),Den("x"))),   (* Function declaration add5 *)
          Let("many5_add5",ManyTimes(5,Den("add5")),  (* ManyTimes declaration add5 *)
            Let("p",Pipe(Seq(Den("many5_add5"),Seq(Den("add5"),Seq(Den("incr"),Seq(Den("incr"),Nil))))),  (* Pipe declaration *)
              Apply(                                   (* call of previously declared Pipe *)
                Den("p"),Eint(0)
              )
            )  
          )
        )
      )
    )
  ,[]) = Int(32)) then print_string("ok\n") else print_string("fallito\n");;  (* expected result: Int(32) *)


(* 5 - Non functional value (many5_add5) in pipe *)
(* fails with NonFunctionalValue for violation of requirements "functional value in Pipe" *)
print_string("Test 5: ");;
if(
  (try sem(
    Let("incr",Fun("x",Sum(Eint(1),Den("x"))),        (* Function declaration incr *)
      Let("decr", Fun("x",Diff(Den("x"),Eint(1))),    (* Function declaration decr *)
        Let("add5", Fun("x",Sum(Eint(5),Den("x"))),   (* Function declaration add5 *)
          Let("many5_add5",Eint(1),                   (* Declaration of constant many5_add5 *)
            Let("p",Pipe(Seq(Den("many5_add5"),Seq(Den("add5"),Seq(Den("incr"),Seq(Den("incr"),Nil))))),  (* Pipe declaration *)
              Apply(                                  (* call of previously declared Pipe *)
                Den("p"),Eint(0)
              )
            )  
          )
        )
      )
    )
  ,[])
  with NonFunctionalValue(_) -> Bool(true)) = Bool(true)
) then print_string("ok\n") else print_string("fallito\n");;  (* expected result: Bool(true), returned if exception is thrown *)


(* 6 - Functions declaration, manytimes declaration *)
(* fails with NonFunctionalValue for non-functional value in Apply *)
print_string("Test 6: ");;
if(
  (try sem(
    Let("x",Eint(5),                                  (* Declaration of constant x*)
      Let("decr", Fun("x",Diff(Den("x"),Eint(1))),    (* Function declaration decr *)
        Let("add5", Fun("x",Sum(Eint(5),Den("x"))),   (* Function declaration add5 *)
          Let("many5_add5",ManyTimes(5,Den("add5")),  (* Declaration of add5 Manytimes *)
            Apply(                                    (* Call on constant *)
              Den("x"),Eint(0)
            )  
          )
        )
      )
    )
  ,[])
  with NonFunctionalValue(_) -> Bool(true)) = Bool(true)
) then print_string("ok\n") else print_string("fallito\n");;  (* expected result: Bool(true), returned if exception is thrown *)


(* 7 - Functions declaration, manytimes declaration *)
(* fails with NonFunctionalValue for non-functional value in Pipe *)
print_string("Test 7: ");;
if(
  (try sem(
    Let("x",Eint(5),                                  (* Declaration of constant x *)
      Let("decr", Fun("x",Diff(Den("x"),Eint(1))),    (* Function declaration decr *)
        Let("add5", Fun("x",Sum(Eint(5),Den("x"))),   (* Function declaration add5 *)
          Let("many5_add5",Eint(1),                   (* Declaration of constant many5_add5 *)
            Let("p",Pipe(Seq(Den("many5_add5"),Seq(Den("add5"),Seq(Eint(5),Nil)))),
              Apply(                                  (* call on previously declared Pipe *)
                Den("p"),Eint(0)
              )
            ) 
          )
        )
      )
    )
  ,[])
  with NonFunctionalValue(_) -> Bool(true)) = Bool(true)
) then print_string("ok\n") else print_string("fallito\n");;  (* expected result: Bool(true), returned if exception is thrown *)


(* 8 - Call of undeclared function *)
(* fails with Unbound *)
print_string("Test 8: ");;
if(
  (try sem(
      Apply(                    (* call of undeclared function *)
        Den("incr"),Eint(5)
      )
  ,[])
  with Unbound(_) -> Bool(true)) = Bool(true)
) then print_string("ok\n") else print_string("fallito\n");;  (* expected result: Bool(true), returned if exception is thrown *)


(* 9 - Tuple evaluation *)
print_string("Test 9: ");;
if(
  sem(
    Etup(
      Seq(Sum(Eint(5),Eint(4)),Seq(Diff(Eint(5),Eint(4)),Seq(Iszero(Eint(0)),Nil)))
    )
  ,[]) = Tup(Int(9)::Int(1)::Bool(true)::[])
) then print_string("ok\n") else print_string("fallito\n");;