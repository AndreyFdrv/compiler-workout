open GT       
open Language
       
(* The type for the stack machine instructions *)
@type insn =
(* binary operator                 *) | BINOP   of string
(* put a constant on the stack     *) | CONST   of int
(* put a string on the stack       *) | STRING  of string
(* create an S-expression          *) | SEXP    of string * int
(* load a variable to the stack    *) | LD      of string
(* store a variable from the stack *) | ST      of string
(* store in an array               *) | STA     of string * int
(* a label                         *) | LABEL   of string
(* unconditional jump              *) | JMP     of string
(* conditional jump                *) | CJMP    of string * string
(* begins procedure definition     *) | BEGIN   of string * string list * string list
(* end procedure definition        *) | END
(* calls a function/procedure      *) | CALL    of string * int * bool
(* returns from a function         *) | RET     of bool
(* drops the top element off       *) | DROP
(* duplicates the top element      *) | DUP
(* swaps two top elements          *) | SWAP
(* checks the tag of S-expression  *) | TAG     of string
(* enters a scope                  *) | ENTER   of string list
(* leaves a scope                  *) | LEAVE
with show
                                                   
(* The type for the stack machine program *)
type prg = insn list
                            
(* The type for the stack machine configuration: control stack, stack and configuration from statement
   interpreter
*)
type config = (prg * State.t) list * Value.t list * Expr.config

(* Stack machine interpreter

     val eval : env -> config -> prg -> config

   Takes an environment, a configuration and a program, and returns a configuration as a result. The
   environment is used to locate a label to jump to (via method env#labeled <label_name>)
*)
let split n l =
  let rec unzip (taken, rest) = function
  | 0 -> (List.rev taken, rest)
  | n -> let h::tl = rest in unzip (h::taken, tl) (n-1)
  in
  unzip ([], l) n
          
let rec eval environment (cstack, stack, ((st, i, o) as c)) p = 
	if (List.length p) = 0 then (cstack, stack, c)
	else
	(match (List.hd p) with
      		LABEL l -> eval environment (cstack, stack, c) (List.tl p)
      		|JMP l -> eval environment (cstack, stack, c) (environment#labeled l)
      		|CJMP(condition, l) -> eval environment (cstack, List.tl stack, c) 
			(if (condition = "nz" && (Value.to_int (List.hd stack)) != 0 || 
				condition = "z" && (Value.to_int (List.hd stack)) = 0) 
             			then (environment#labeled l) 
			else (List.tl p))
    		|BEGIN (_, arg_names, local_names) -> let bind ((first :: rest), st) x = (rest, State.update x first st) in
      			let (stack, st) = List.fold_left bind (stack, State.enter st (arg_names @ local_names)) arg_names in
      			eval environment (cstack, stack, (st, i, o)) (List.tl p)
      		|END | RET _ -> (
          				match cstack with
            					[] -> (cstack, stack, c)
            					|(frame::cstack') -> let (p', state') = frame in
              						eval environment (cstack', stack, (State.leave st state', i, o)) p'
        			)
		|CALL (func, n, isProcedure) -> if environment#is_label func
				then eval environment ((List.tl p, st) :: cstack, stack, c) (environment#labeled func) 
				else eval environment (environment#builtin (cstack, stack, c) func n isProcedure
			) (List.tl p)
        	|BINOP op -> eval environment (match stack with first::second::rest -> 
			let first = Value.to_int first in
		let second = Value.to_int second in
              		let result = match op with 
				"+" -> second + first
         			|"-" -> second - first
         			|"*" -> second * first
	 			|"/" -> second / first
         			|"%" -> second mod first
         			|"<" -> if second < first then 1 else 0
         			|"<=" -> if second <= first then 1 else 0
         			|">" -> if second > first then 1 else 0
         			|">=" -> if second >= first then 1 else 0
         			|"==" -> if second = first then 1 else 0
         			|"!=" -> if second <> first then 1 else 0
         			|"!!" -> if (if second = 0 then false else true) || (if first = 0 then false else true) 
						then 1 
			   		 else 0
         			|"&&" -> if (if second = 0 then false else true) && (if first = 0 then false else true) 
						then 1 
			       	   	 else 0
			in
              		(cstack, (Value.of_int result)::rest, c)
          		) (List.tl p)
      		|CONST x -> eval environment (cstack, (Value.of_int x)::stack, c) (List.tl p)
      		|LD var -> eval environment (cstack, State.eval st var :: stack, c) (List.tl p)
      		|ST var -> let (x :: stack') = stack in 	
			eval environment (cstack, stack', (State.update var x st, i, o)) (List.tl p)
		|STRING str -> eval environment (cstack, (Value.of_string str :: stack), c) (List.tl p)
		|STA (arr, size) -> let first::rest, stack = split (size + 1) stack in
      			eval environment (cstack, stack, (Language.Stmt.update st arr first (List.rev rest), i, o)) (List.tl p)
		|SEXP (str, n) -> let v, stack = split n stack in 
			eval environment (cstack, (Value.sexp str (List.rev v))::stack, c) (List.tl p)
		|DROP -> eval environment (cstack, List.tl stack, c) (List.tl p)
		|DUP -> eval environment (cstack, List.hd stack :: stack, c) (List.tl p)
		|SWAP -> let first::second::rest = stack in 
			eval environment (cstack, second::first::rest, c) (List.tl p)
		|TAG tag -> let first::rest = stack in
			let res = if (Value.tag_of first = tag) then 1 else 0 in
			eval environment (cstack, (Value.of_int res)::rest, c) (List.tl p)
		|ENTER lst -> let values, stack = split (List.length lst) stack in 
			let combined = List.combine lst values in
			let st = State.push st (List.fold_left (fun s (x, v) -> State.bind x v s) State.undefined combined) lst in
			eval environment (cstack, stack, (st, i, o)) (List.tl p)
		|LEAVE -> eval environment (cstack, stack, (State.drop st, i, o)) (List.tl p)
	)

(* Top-level evaluation

     val run : prg -> int list -> int list

   Takes a program, an input stream, and returns an output stream this program calculates
*)
let run p i =
  let module M = Map.Make (String) in
  let rec make_map m = function
  | []              -> m
  | (LABEL l) :: tl -> make_map (M.add l tl m) tl
  | _ :: tl         -> make_map m tl
  in
  let m = make_map M.empty p in
  let (_, _, (_, _, o)) =
    eval
      (object
         method is_label l = M.mem l m
         method labeled l = M.find l m
         method builtin (cstack, stack, (st, i, o)) f n p =
           let f = match f.[0] with 'L' -> String.sub f 1 (String.length f - 1) | _ -> f in
           let args, stack' = split n stack in
           let (st, i, o, r) = Language.Builtin.eval (st, i, o, None) (List.rev args) f in
           let stack'' = if p then stack' else let Some r = r in r::stack' in
           Printf.printf "Builtin: %s\n";
           (cstack, stack'', (st, i, o))
       end
      )
      ([], [], (State.empty, i, []))
      p
  in
  o

(* Stack machine compiler

     val compile : Language.t -> prg

   Takes a program in the source language and returns an equivalent program for the
   stack machine
*)
let compile (defs, p) = 
  let label s = "L" ^ s in
  let rec call f args p =
    let args_code = List.concat @@ List.map expr args in
    args_code @ [CALL (f, List.length args, p)]
  and pattern lfalse p =
  	(let rec comp pat = 
    		(match pat with
      			Stmt.Pattern.Wildcard -> [DROP]
    			|Stmt.Pattern.Ident x -> [DROP]
    			|Stmt.Pattern.Sexp (tag, ps) -> 
				let res, _ = (List.fold_left 
					(fun (acc, pos) pat -> (acc @ [DUP; CONST pos; CALL (".elem", 2, false)] @ (comp pat)), 
						pos + 1) ([], 0) ps) 
				in
      				[DUP; TAG tag; CJMP ("z", lfalse)] @ res
		)
	in
  comp p)
  and bindings p =
  	let rec bind cp = 
    		(match cp with
      			Stmt.Pattern.Wildcard -> [DROP]
    			|Stmt.Pattern.Ident x -> [SWAP]
    			|Stmt.Pattern.Sexp (_, xs) -> 
				let res, _ = List.fold_left (fun (acc, pos) curp -> 
					(acc @ [DUP; CONST pos; CALL (".elem", 2, false)] @ bind curp, pos + 1)) 
					([], 0) xs 
				in
				res @ [DROP]
		)
	in
  bind p @ [ENTER (Stmt.Pattern.vars p)]
  and expr = function
	Expr.Const value -> [CONST value]
	|Expr.Var variable -> [LD variable]
	|Expr.String str -> [STRING str]
	|Expr.Array elements ->  call ".array" elements false
	|Expr.Sexp (tag, es) -> let args = List.fold_left (fun acc index -> acc @ (expr index)) [] es in 
		args @ [SEXP (tag, List.length es)]
    	|Expr.Elem (elements, i) ->  call ".elem" [elements; i] false
    	|Expr.Length e -> call ".length" [e] false
    	|Expr.Binop (operation, left, right) -> expr left @ expr right @ [BINOP operation]
    	|Expr.Call (name, args) -> call (label name) (List.rev args) false
  in
  let rec compile_stmt l env = function  
	Stmt.Assign (variable, [], e) -> env, false, expr e @ [ST variable]
    	|Stmt.Assign (variable, indexes, e) -> 
		env, false, List.concat (List.map expr (indexes @ [e])) @ [STA (variable, List.length indexes)]
    	|Stmt.Seq (left_stmt, right_stmt) -> let env, _, left = compile_stmt l env left_stmt in
      		let env, _, right = compile_stmt l env right_stmt in
      		env, false, left @ right
    	|Stmt.Skip -> env, false, []
    	|Stmt.If (e, th, el) -> let label_else, env = env#get_label in 
      		let label_fi, env = env#get_label in
      		let env, _, th_compile = compile_stmt l env th in
      		let env, _, el_compile = compile_stmt l env el in
      		env, false, expr e @ [CJMP ("z", label_else)] @ th_compile @ [JMP label_fi; LABEL label_else] @ el_compile @ 
			[LABEL label_fi]
    	|Stmt.While (e, while_stmt) -> let label_check, env = env#get_label in
      		let label_loop, env = env#get_label in
      		let env, _, while_body = compile_stmt l env while_stmt in
      		env, false, [JMP label_check; LABEL label_loop] @ while_body @ [LABEL label_check] @ expr e @ 
			[CJMP ("nz", label_loop)]
    	|Stmt.Repeat (repeat_stmt,e) -> let label_loop, env = env#get_label in
      		let env, _, repeat_body = compile_stmt l env repeat_stmt in
      		env, false, [LABEL label_loop] @ repeat_body @ expr e @ [CJMP ("z", label_loop)]
    	|Stmt.Call (name, args) -> env, false, call (label name) (List.rev args) true  
    	|Stmt.Leave -> env, false, [LEAVE]
    	|Stmt.Case (e, ptrns) -> 
		let rec comp_pat ps env lbl isFirst lend = 
        		(match ps with
          			[] -> env, []
        			|(p, act)::tl -> let env, _, body = compile_stmt l env act in 
          				let lfalse, env = env#get_label
          				and start = if isFirst then [] else [LABEL lbl] 
					in
          				let env, code = comp_pat tl env lfalse false lend in
          				env, start @ (pattern lfalse p) @ bindings p @ body @ [LEAVE; JMP lend] @ code
			) 
		in
      		let lend, env = env#get_label in
      		let env, code = comp_pat ptrns env "" true lend in
      		env, false, expr e @ code @ [LABEL lend]
    	|Stmt.Return e -> 
		(match e with
      			None -> env, false, [RET false]
      			|Some e -> env, false, expr e @ [RET true] )
  in
  let compile_def env (name, (args, locals, stmt)) =
    let lend, env       = env#get_label in
    let env, flag, code = compile_stmt lend env stmt in
    env,
    [LABEL name; BEGIN (name, args, locals)] @
    code @
    (if flag then [LABEL lend] else []) @
    [END]
  in
  let env =
    object
      val ls = 0
      method get_label = (label @@ string_of_int ls), {< ls = ls + 1 >}
    end
  in
  let env, def_code =
    List.fold_left
      (fun (env, code) (name, others) -> let env, code' = compile_def env (label name, others) in env, code'::code)
      (env, [])
      defs
  in
  let lend, env = env#get_label in
  let _, flag, code = compile_stmt lend env p in
  (if flag then code @ [LABEL lend] else code) @ [END] @ (List.concat def_code) 

