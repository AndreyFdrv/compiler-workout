(* Opening a library for generic programming (https://github.com/dboulytchev/GT).
   The library provides "@type ..." syntax extension and plugins like show, etc.
*)
open GT

(* Opening a library for combinator-based syntax analysis *)
open Ostap
open Combinators

let rec listInit i size f = 
	if i < size
		then (f i) :: (listInit (i + 1) size f) 
	else 
		[]

(* Values *)
module Value =
  struct

    @type t = Int of int | String of string | Array of t list | Sexp of string * t list with show

    let to_int = function 
    | Int n -> n 
    | _ -> failwith "int value expected"

    let to_string = function 
    | String s -> s 
    | _ -> failwith "string value expected"

    let to_array = function
    | Array a -> a
    | _       -> failwith "array value expected"

    let sexp   s vs = Sexp (s, vs)
    let of_int    n = Int    n
    let of_string s = String s
    let of_array  a = Array  a

    let tag_of = function
    | Sexp (t, _) -> t
    | _ -> failwith "symbolic expression expected"

    let update_string s i x = String.init (String.length s) (fun j -> if j = i then x else s.[j])
    let update_array  a i x = listInit 0   (List.length a)   (fun j -> if j = i then x else List.nth a j)

  end
       
(* States *)
module State =
  struct
                                                                
    (* State: global state, local state, scope variables *)
    type t =
    | G of (string -> Value.t)
    | L of string list * (string -> Value.t) * t

    (* Undefined state *)
    let undefined x = failwith (Printf.sprintf "Undefined variable: %s" x)

    (* Bind a variable to a value in a state *)
    let bind x v s = fun y -> if x = y then v else s y 

    (* Empty state *)
    let empty = G undefined

    (* Update: non-destructively "modifies" the state s by binding the variable x 
       to value v and returns the new state w.r.t. a scope
    *)
    let update x v s =
      let rec inner = function
      | G s -> G (bind x v s)
      | L (scope, s, enclosing) ->
         if List.mem x scope then L (scope, bind x v s, enclosing) else L (scope, s, inner enclosing)
      in
      inner s

    (* Evals a variable in a state w.r.t. a scope *)
    let rec eval s x =
      match s with
      | G s -> s x
      | L (scope, s, enclosing) -> if List.mem x scope then s x else eval enclosing x

    (* Creates a new scope, based on a given state *)
    let rec enter st xs =
      match st with
      | G _         -> L (xs, undefined, st)
      | L (_, _, e) -> enter e xs

    (* Drops a scope *)
    let leave st st' =
      let rec get = function
      | G _ as st -> st
      | L (_, _, e) -> get e
      in
      let g = get st in
      let rec recurse = function
      | L (scope, s, e) -> L (scope, s, recurse e)
      | G _             -> g
      in
      recurse st'

    (* Push a new local scope *)
    let push st s xs = L (xs, s, st)

    (* Drop a local scope *)
    let drop (L (_, _, e)) = e
                               
  end

(* Builtins *)
module Builtin =
  struct
      
    let eval (st, i, o, _) args = function
    | "read"     -> (match i with z::i' -> (st, i', o, Some (Value.of_int z)) | _ -> failwith "Unexpected end of input")
    | "write"    -> (st, i, o @ [Value.to_int @@ List.hd args], None)
    | ".elem"    -> let [b; j] = args in
                    (st, i, o, let i = Value.to_int j in
                               Some (match b with
                                     | Value.String   s  -> Value.of_int @@ Char.code s.[i]
                                     | Value.Array    a  -> List.nth a i
                                     | Value.Sexp (_, a) -> List.nth a i
                               )
                    )         
    | ".length"  -> (st, i, o, Some (Value.of_int (match List.hd args with Value.Array a -> List.length a | Value.String s -> String.length s)))
    | ".array"   -> (st, i, o, Some (Value.of_array args))
    | "isArray"  -> let [a] = args in (st, i, o, Some (Value.of_int @@ match a with Value.Array  _ -> 1 | _ -> 0))
    | "isString" -> let [a] = args in (st, i, o, Some (Value.of_int @@ match a with Value.String _ -> 1 | _ -> 0))                     
       
  end
    
(* Simple expressions: syntax and semantics *)
module Expr =
  struct
    
    (* The type for expressions. Note, in regular OCaml there is no "@type..." 
       notation, it came from GT. 
    *)
    @type t =
    (* integer constant   *) | Const  of int
    (* array              *) | Array  of t list
    (* string             *) | String of string
    (* S-expressions      *) | Sexp   of string * t list
    (* variable           *) | Var    of string
    (* binary operator    *) | Binop  of string * t * t
    (* element extraction *) | Elem   of t * t
    (* length             *) | Length of t 
    (* function call      *) | Call   of string * t list with show

    (* Available binary operators:
        !!                   --- disjunction
        &&                   --- conjunction
        ==, !=, <=, <, >=, > --- comparisons
        +, -                 --- addition, subtraction
        *, /, %              --- multiplication, division, reminder
    *)

    (* The type of configuration: a state, an input stream, an output stream, an optional value *)
    type config = State.t * int list * int list * Value.t option
                                                            
    (* Expression evaluator

          val eval : env -> config -> t -> config


       Takes an environment, a configuration and an expresion, and returns another configuration. The 
       environment supplies the following method

           method definition : env -> string -> int list -> config -> config

       which takes an environment (of the same type), a name of the function, a list of actual parameters and a configuration, 
       an returns resulting configuration
    *)                                                       
    let to_func op =
      let bti   = function true -> 1 | _ -> 0 in
      let itb b = b <> 0 in
      let (|>) f g   = fun x y -> f (g x y) in
      match op with
      | "+"  -> (+)
      | "-"  -> (-)
      | "*"  -> ( * )
      | "/"  -> (/)
      | "%"  -> (mod)
      | "<"  -> bti |> (< )
      | "<=" -> bti |> (<=)
      | ">"  -> bti |> (> )
      | ">=" -> bti |> (>=)
      | "==" -> bti |> (= )
      | "!=" -> bti |> (<>)
      | "&&" -> fun x y -> bti (itb x && itb y)
      | "!!" -> fun x y -> bti (itb x || itb y)
      | _    -> failwith (Printf.sprintf "Unknown binary operator %s" op)    
    
      let rec eval env ((st, i, o, r) as conf) exp = 
        match exp with
         Const c -> (st, i, o, Some (Value.of_int c))
         |Var v -> (st, i, o, Some (State.eval st v))
	 |Call(f_name, args) -> 
		let conf, args = 
			List.fold_left (fun (conf', evaled) expr -> 
                		let (_, _, _, Some v) as conf' = eval env conf' expr in
                        	(conf', evaled @ [v])) (conf, []) args 
		in
            	env#definition env f_name args conf
	 |Binop(op, left, right) ->
		let (st, i, o, Some left) = eval env conf left in
		let (st, i, o, Some right) =  eval env (st, i, o, Some left) right in
		let left = Value.to_int left in
		let right = Value.to_int right in
		(st, i, o, Some (Value.of_int (to_func op left right)))	
	 |Array arr -> let (st, i, o, arr) = eval_list env conf arr in
		(st, i, o, Some (Value.of_array arr))
	 |String str -> (st, i, o, Some (Value.of_string str))
	 |Elem(lst, index) -> let (st, i, o, Some index) = eval env conf index in
		let (st, i, o, Some lst) = eval env conf lst in
          	(st, i, o, Some (match lst with
			Value.Array arr -> List.nth arr @@ Value.to_int index
            		|Value.String str -> Value.of_int @@ Char.code @@ String.get str @@ Value.to_int index)
		)
	 |Length lst -> let (st, i, o, Some lst) = eval env conf lst in
		(st, i, o, Some (match lst with
	        	Value.Array arr -> Value.of_int @@ List.length arr
			|Value.String str -> Value.of_int @@ String.length str)
		)
	 |Sexp(str, lst) -> let (st, i, o, lst) = eval_list env conf lst in
		(st, i, o, Some (Value.Sexp (str, lst))) 
    and eval_list env conf xs =
      let vs, (st, i, o, _) =
        List.fold_left
          (fun (acc, conf) x ->
            let (_, _, _, Some v) as conf = eval env conf x in
            v::acc, conf
          )
          ([], conf)
          xs
      in
      (st, i, o, List.rev vs)
         
    (* Expression parser. You can use the following terminals:

         IDENT   --- a non-empty identifier a-zA-Z[a-zA-Z0-9_]* as a string
         DECIMAL --- a decimal constant [0-9]+ as a string                                                                                                                  
    *)
    ostap (                                      
      parse: expr;                                    
      expr:
      !(Ostap.Util.expr 
          (fun x -> x)
	  (Array.map (fun (a, s) -> a, 
          	List.map  (fun s -> ostap(- $(s)), (fun x y -> Binop (s, x, y))) s
    	  )
          [|                
		`Lefta, ["!!"];
		`Lefta, ["&&"];
		`Nona, ["=="; "!="; "<="; "<"; ">="; ">"];
		`Lefta, ["+" ; "-"];
		`Lefta, ["*" ; "/"; "%"];
          |] 
	)
	primary);
      primary: o:obj m:(-"[" i:parse -"]" {`Elem i} 
        	| -"." %"length" {`Len}
        ) * {List.fold_left (fun x -> function `Elem i -> Elem (x, i) | `Len -> Length x) o m};
      obj: n:DECIMAL {Const n} 
	| x:IDENT s:("(" args:!(Util.list0)[expr] ")" {Call (x, args)} | empty {Var x}) {s} 
        | str:STRING {String (String.sub str 1 (String.length str - 2))}
        | c:CHAR {Const (Char.code c)}
        | "`" t:IDENT args:(-"(" !(Util.list)[parse] -")")? {Sexp (t, match args with None -> [] | Some args -> args)}
        | -"[" elements:!(Util.list0)[parse] -"]" {Array elements}
	| -"(" parse -")"
    )
    
  end
                    
(* Simple statements: syntax and sematics *)
module Stmt =
  struct

    (* Patterns in statements *)
    module Pattern =
      struct

        (* The type for patterns *)
        @type t =
        (* wildcard "-"     *) | Wildcard
        (* S-expression     *) | Sexp   of string * t list
        (* identifier       *) | Ident  of string
        with show, foldl

        (* Pattern parser *)                                 
        ostap (
          parse:  
            "_" {Wildcard}
            | "`" str:IDENT lst:(-"(" !(Ostap.Util.list)[parse] -")")? {Sexp (str, match lst with None -> [] | Some lst -> lst)}
            | x:IDENT {Ident x}
        )
        
        let vars p =
          transform(t) (object inherit [string list] @t[foldl] method c_Ident s _ name = name::s end) [] p
        
      end
        
    (* The type for statements *)
    @type t =
    (* assignment                       *) | Assign of string * Expr.t list * Expr.t
    (* composition                      *) | Seq    of t * t 
    (* empty statement                  *) | Skip
    (* conditional                      *) | If     of Expr.t * t * t
    (* loop with a pre-condition        *) | While  of Expr.t * t
    (* loop with a post-condition       *) | Repeat of t * Expr.t
    (* pattern-matching                 *) | Case   of Expr.t * (Pattern.t * t) list
    (* return statement                 *) | Return of Expr.t option
    (* call a procedure                 *) | Call   of string * Expr.t list 
    (* leave a scope                    *) | Leave  with show
                                                                                   
    (* Statement evaluator

         val eval : env -> config -> t -> config

       Takes an environment, a configuration and a statement, and returns another configuration. The 
       environment is the same as for expressions
    *)
    let update st x v is =
      let rec update a v = function
      | []    -> v           
      | i::tl ->
          let i = Value.to_int i in
          (match a with
           | Value.String s when tl = [] -> Value.String (Value.update_string s i (Char.chr @@ Value.to_int v))
           | Value.Array a               -> Value.Array  (Value.update_array  a i (update (List.nth a i) v tl))
          ) 
      in
      State.update x (match is with [] -> v | _ -> update (State.eval st x) v is) st

    let rec eval env ((st, i, o, r) as conf) k stmt = 
     	match stmt with
		Assign(x, indices, exp) -> let (_, _, _, indices) = Expr.eval_list env conf indices in
			let (st, i, o, Some exp_value) = Expr.eval env conf exp in
			eval env ((update st x exp_value indices), i, o, r) Skip k
		|Seq(left, right) -> eval env conf (if k = Skip then right else Seq (right, k)) left
		|Skip -> if k = Skip then conf else eval env conf Skip k
		|If(condition, true_body, false_body) -> let (st, i, o, Some exp_value) = Expr.eval env conf condition in
			eval env (st, i, o, Some exp_value) k (if Value.to_int exp_value <> 0 then true_body else false_body)
		|While(condition, body) -> let (st, i, o, Some exp_value) = Expr.eval env conf condition in 
			if (Value.to_int exp_value <> 0)
				then eval env (st, i, o, Some exp_value) 
					(if k = Skip then While(condition, body) else Seq (While(condition, body), k)) 
					body
			else eval env (st, i, o, Some exp_value) Skip k
		|Repeat(body, condition) -> eval env conf k (Seq (
						  			body, 
						  			While(Expr.Binop("==", condition, Expr.Const(0)), body)
					       		         ))
        	|Call(func_name, args) -> let conf = Expr.eval env conf (Expr.Call(func_name, args)) in
			eval env conf Skip k
        	|Return exp -> (match exp with
          		None -> conf
          		|Some exp -> Expr.eval env conf exp)
    		|Case(exp, branches) -> let (st, i, o, Some exp_value) = Expr.eval env conf exp in
      			let rec match_branch exp branch =
        			(match (exp, branch) with
         				_, Pattern.Wildcard -> Some []
         				|exp, Pattern.Ident x -> Some [x, exp]
         				|Value.Sexp(left_str, left_lst), Pattern.Sexp(right_str, right_lst) 
						when (left_str = right_str && List.length left_lst = List.length right_lst) ->
           						List.fold_left2 (fun x y z -> 
								match (x, (match_branch y z)) with
        								_, None -> None
       								|None, _ -> None
        								|Some x, Some y -> Some (x @ y) 
							) (Some []) left_lst right_lst
         				|_ -> None
				) 
			in
      			let rec match_branches = function
        			(first, next)::rest ->
          				(match (match_branch exp_value first) with
          					|None -> match_branches rest
          					|Some branch -> let n = List.fold_left (fun x (y, z) -> State.bind y z x) 								State.undefined branch 
							in
            						eval env (State.push st n (List.map fst branch), i, o, None) k 
								(Seq(next, Leave)))
        					|[] -> eval env conf Skip k 
			in
      			match_branches branches
    		|Leave -> eval env (State.drop st, i, o, r) Skip k

    (* Used in statement parser

         val parseElseBody : t -> t

       Takes an else body from parser, and returns else body for evaluator
    *)
    let parseElseBody else_body =
	match else_body with
	None -> Skip
      		|Some body -> body

    (* Used in statement parser

         val parseFalseBodies : (Expr.t * t) list -> t -> t

       Takes an elif bodies and else body from parser, and returns elif and else bodies for evaluator
    *)
    let rec parseFalseBodies elif_bodies else_body =
    	match elif_bodies with
      		[] -> else_body
      		|(condition, body)::tail -> If(condition, body, parseFalseBodies tail else_body) 
                                                       
    (* Statement parser *)
    ostap (
      parse: statements;
      statements:
        !(Ostap.Util.expr
           (fun x -> x)
           [|
             `Righta, [ostap (";"), (fun l r -> Seq(l, r))]
           |]
           stmt
	);
      stmt: x:IDENT indices:(-"[" !(Expr.parse) -"]")* ":=" y:!(Expr.expr) {Assign(x, indices, y)}
	    | %"if" condition:!(Expr.expr) 
		%"then" true_body:statements
		elif_bodies:(%"elif"!(Expr.expr) %"then" statements)* 
		else_body:(%"else" statements)?
        	%"fi"
        	{If(condition, true_body, parseFalseBodies elif_bodies (parseElseBody else_body))}
	    | %"skip" {Skip}
	    | %"while" condition:!(Expr.expr) %"do" body:statements %"od" {While(condition, body)}
	    | %"for" init:statements "," condition:!(Expr.expr) "," step:statements %"do" body:statements %"od"
		{Seq(init, While(condition, Seq(body, step)))}
	    | %"repeat" body:statements %"until" condition:!(Expr.expr) {Repeat(body, condition)}
	    | func:IDENT "(" args:!(Expr.parse)* ")" {Call(func, args)}
	    | %"return" exp:!(Expr.expr)? {Return exp}
	    | %"case" exp:!(Expr.parse) %"of" branches:!(Ostap.Util.listBy)[ostap ("|")][case_branch] %"esac" {Case (exp, branches)};
     case_branch: pattern:!(Pattern.parse) "->" action:!(parse) {pattern, action}
    )
      
  end

(* Function and procedure definitions *)
module Definition =
  struct

    (* The type for a definition: name, argument list, local variables, body *)
    type t = string * (string list * string list * Stmt.t)

    ostap (     
      argument: IDENT;
      parse: %"fun" functionName:IDENT "(" args: !(Util.list0 argument) ")"
        locals: (%"local" !(Util.list argument))?
        "{" body: !(Stmt.parse) "}" { (functionName, (args, (match locals with None -> [] | Some l -> l), body))}
    )

  end
    
(* The top-level definitions *)

(* The top-level syntax category is a pair of definition list and statement (program body) *)
type t = Definition.t list * Stmt.t    

(* Top-level evaluator

     eval : t -> int list -> int list

   Takes a program and its input stream, and returns the output stream
*)
let eval (defs, body) i =
  let module M = Map.Make (String) in
  let m          = List.fold_left (fun m ((name, _) as def) -> M.add name def m) M.empty defs in  
  let _, _, o, _ =
    Stmt.eval
      (object
         method definition env f args ((st, i, o, r) as conf) =
           try
             let xs, locs, s      =  snd @@ M.find f m in
             let st'              = List.fold_left (fun st (x, a) -> State.update x a st) (State.enter st (xs @ locs)) (List.combine xs args) in
             let st'', i', o', r' = Stmt.eval env (st', i, o, r) Stmt.Skip s in
             (State.leave st'' st, i', o', r')
           with Not_found -> Builtin.eval conf args f
       end)
      (State.empty, i, [], None)
      Stmt.Skip
      body
  in
  o

(* Top-level parser *)
let parse = ostap (!(Definition.parse)* !(Stmt.parse))
