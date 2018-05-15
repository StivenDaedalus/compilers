open GT       
open Language
       
(* The type for the stack machine instructions *)
@type insn =
(* binary operator                 *) | BINOP   of string
(* put a constant on the stack     *) | CONST   of int
(* put a string on the stack       *) | STRING  of string                      
(* load a variable to the stack    *) | LD      of string
(* store a variable from the stack *) | ST      of string
(* store in an array               *) | STA     of string * int
(* a label                         *) | LABEL   of string
(* unconditional jump              *) | JMP     of string
(* conditional jump                *) | CJMP    of string * string
(* begins procedure definition     *) | BEGIN   of string * string list * string list
(* end procedure definition        *) | END
(* calls a function/procedure      *) | CALL    of string * int * bool
(* returns from a function         *) | RET     of bool with show
                                                   
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
                      
let rec eval env conf prog =
        match prog with
        | [] -> conf
        |inst::tail -> (
                match conf, inst with
                | (cstack, y::x::stack, tm_conf), BINOP operation -> 
                        let value = Language.Expr.binop operation(Value.to_int x) (Value.to_int y) in
                        eval env (cstack, (Value.of_int value)::stack, tm_conf) tail
                | (cstack, stack, tm_conf), CONST value ->
                        eval env (cstack, (Value.of_int value)::stack, tm_conf) tail
                | (cstack, stack, stmt_conf), STRING str -> 
                        eval env (cstack, (Value.of_string str)::stack, stmt_conf) tail
		| (cstack, stack, (st, input, output)), LD x -> 
                        let value = State.eval st x in
                        eval env (cstack, value::stack, (st, input, output)) tail
                | (cstack, z::stack, (st, input, output)), ST x -> 
			let stt = State.update x z st in
                        eval env (cstack, stack, (stt, input, output)) tail
                | (cstack, stack, (st, input, output)), STA (variable, n) -> 
                  let v::ind, stack' = split (n + 1) stack in 
                  eval env (cstack, stack', (Language.Stmt.update st variable v (List.rev ind), input, output)) tail
                | conf, LABEL label -> eval env conf tail
                | conf, JMP label -> eval env conf (env#labeled label)
                | (cstack, z::stack, tm_conf), CJMP (suf, label) -> (
                        match suf with
                        | "z" -> if Value.to_int z == 0 then eval env (cstack, stack, tm_conf) (env#labeled label)
                                 else eval env (cstack, stack, tm_conf) tail
                        | "nz" -> if Value.to_int z <> 0 then eval env (cstack, stack, tm_conf) (env#labeled label)
                                  else eval env (cstack, stack, tm_conf) tail
                        | _ -> failwith("Undefined suffix!")
                )
                | (cstack, stack, (st, input, output)), CALL (name, n, flag) -> 
                  if env#is_label name 
                  then eval env ((tail, st)::cstack, stack,(st, input, output)) (env#labeled name)
                  else eval env (env#builtin conf name n flag) tail
                | (cstack, stack, (st, input, output)), BEGIN (_, args, locals) -> 
                        let rec associate st args stack =
                                match args, stack with
                                | arg::args', z::stack' ->
                                       let st', stack'' = associate st args' stack' in
                                       (State.update arg z st', stack'')
                                | [], stack' -> (st, stack') in
                        let st', stack' = associate (State.enter st (args @ locals)) args stack in
                        eval env (cstack, stack',(st',input, output)) tail	
                | (cstack, stack, (st, input, output)), END | (cstack, stack, (st, input, output)), RET _-> (
                        match cstack with
                        | (tail', st')::cstack' -> 
                               eval env (cstack', stack, (State.leave st st', input, output)) tail'
                        | [] -> conf
                )
                
        )
(* Top-level evaluation

     val run : prg -> int list -> int list

   Takes a program, an input stream, and returns an output stream this program calculates
*)
let run p i =
  (*print_prg p;*)
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
let rec compileExpr expr = 
        match expr with
        | Language.Expr.Const c -> [CONST c]
        | Language.Expr.Var x -> [LD x]
        | Language.Expr.String str -> [STRING str]
        | Language.Expr.Array elements -> List.flatten (List.map compileExpr elements) @ [CALL ("$array", List.length elements, false)]
        | Language.Expr.Elem (elements, i) -> compileExpr elements @ compileExpr i @ [CALL ("$elem", 2, false)]
        | Language.Expr.Length expr -> compileExpr expr @ [CALL ("$length", 1, false)];
        | Language.Expr.Binop (operation, left_op, right_op) -> compileExpr left_op @ compileExpr right_op @ [BINOP operation]
        | Language.Expr.Call (name, args) -> List.concat (List.map compileExpr (List.rev args)) @ [CALL ("L" ^ name, List.length args, false)]


let rec compileControl st env = 
        match st with
        | Language.Stmt.Assign (x,[], expr) -> compileExpr expr @ [ST x], env
        | Language.Stmt.Assign (variable, indexs, expr) -> List.flatten (List.map compileExpr (indexs @ [expr])) @ [STA (variable, List.length indexs)], env
        | Language.Stmt.Seq (frts_stmt, scnd_stmt) -> 
                let frts, env = compileControl frts_stmt env in
                let scnd, env = compileControl scnd_stmt env in
                 frts @ scnd, env
        | Language.Stmt.Skip -> [], env
        | Language.Stmt.If (expr, frts_stmt, scnd_stmt) ->
                let label_else, env = env#generate in
                let label_fi, env = env#generate in
                let fr_compile, env = compileControl frts_stmt env in
		let sc_compile, env = compileControl scnd_stmt env in
                compileExpr expr @ [CJMP ("z", label_else)] @ fr_compile @ [JMP label_fi; LABEL label_else] @ sc_compile @ [LABEL label_fi], env
        | Language.Stmt.While (expr, st) ->
                let label_check, env = env#generate in
                let label_loop, env = env#generate in
                let while_body, env = compileControl st env in
                [JMP label_check; LABEL label_loop] @ while_body @ [LABEL label_check] @ compileExpr expr @ [CJMP ("nz", label_loop)], env
        | Language.Stmt.Repeat (expr, st) ->(
                let label_loop, env = env#generate in
                let repeat_body, env = compileControl st env in
                [LABEL label_loop] @ repeat_body @ compileExpr expr @ [CJMP ("z", label_loop)]), env
        | Language.Stmt.Call (name, args) -> List.concat (List.map compileExpr (List.rev args)) @ [CALL ("L" ^ name, List.length args, true)], env
        | Language.Stmt.Return expr ->
          match expr with
          | None -> [RET false], env
          | Some expr -> compileExpr expr @ [RET true], env

let compile (defs, stmt) = 
        let env = 
          object
              val count_label = 0
              method generate = "LABEL_" ^ string_of_int count_label, {< count_label = count_label + 1 >}
             end in
        let prg, env = compileControl stmt env in
        let rec compile_defs env defs =
                match defs with
                | (name, (args, locals, body))::defs' ->
                    let body_defs, env = compile_defs env defs' in
                    let compile_body, env = compileControl body env in
                    [LABEL ("L" ^ name); BEGIN ("L" ^ name, args, locals)] @ compile_body @ [END] @ body_defs, env
                | [] -> [], env in
        let cdefs, _ = compile_defs env defs in
        prg @ [END] @ cdefs
    

