open GT       
open Language
       
(* The type for the stack machine instructions *)
@type insn =
(* binary operator                 *) | BINOP of string
(* put a constant on the stack     *) | CONST of int                 
(* read to stack                   *) | READ
(* write from stack                *) | WRITE
(* load a variable to the stack    *) | LD    of string
(* store a variable from the stack *) | ST    of string
(* a label                         *) | LABEL of string
(* unconditional jump              *) | JMP   of string                                                                                                                
(* conditional jump                *) | CJMP  of string * string
(* begins procedure definition     *) | BEGIN of string list * string list
(* end procedure definition        *) | END
(* calls a procedure               *) | CALL  of string with show
                                                   
(* The type for the stack machine program *)                                                               
type prg = insn list

(* The type for the stack machine configuration: control stack, stack and configuration from statement
   interpreter
 *)
type config = (prg * State.t) list * int list * Stmt.config

(* Stack machine interpreter

     val eval : env -> config -> prg -> config

   Takes an environment, a configuration and a program, and returns a configuration as a result. The
   environment is used to locate a label to jump to (via method env#labeled <label_name>)
*)                         
let rec eval env conf prog =
        match prog with
        | [] -> conf
        |inst::tail -> (
                match conf, inst with
                | (y::x::stack, tm_conf), BINOP operation -> 
                        let value = Language.Expr.binop operation x y in
                        eval env (value::stack, tm_conf) tail
                | (stack, tm_conf), CONST value ->
                        eval env (value::stack, tm_conf) tail
		| (stack, (st, z::input, output)), READ -> 
                        eval env (z::stack, (st, input, output)) tail
                | (z::stack, (st, input, output)), WRITE -> 
                        eval env (stack, (st, input, output @ [z])) tail
		| (stack, (st, input, output)), LD x -> 
                        let value = st x in
                        eval env (value::stack, (st, input, output)) tail
                | (z::stack, (st, input, output)), ST x -> 
			let stt = Language.Expr.update x z st in
                        eval env (stack, (stt, input, output)) tail
                | conf, LABEL label -> eval env conf tail
                | (z::stack, tm_conf), CJMP (suf, label) ->
                        match suf with
                        | "z" -> if z == 0 then eval env (stack, tm_conf) (env#labeled label)
                                 else eval env (stack, tm_conf) tail
                        | "nz" -> if z <> 0 then eval env (stack, tm_conf) (env#labeled label)
                                  else eval env (stack, tm_conf) tail
                        | _ -> failwith("Undefined suffix!")
                | _ -> failwith("Undefined operation!")
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
  let (_, _, (_, _, o)) = eval (object method labeled l = M.find l m end) ([], [], (State.empty, i, [])) p in o

(* Stack machine compiler

     val compile : Language.t -> prg

   Takes a program in the source language and returns an equivalent program for the
   stack machine
*)
let rec compileExpr expr = 
        match expr with
        | Language.Expr.Const c -> [CONST c]
        | Language.Expr.Var x -> [LD x]
        | Language.Expr.Binop (operation, left_op, right_op) -> compileExpr left_op @ compileExpr right_op @ [BINOP operation]


let rec compileControl st env = 
        match st with
        | Language.Stmt.Assign (x, expr) -> compileExpr expr @ [ST x], env
        | Language.Stmt.Read x -> [READ; ST x], env
        | Language.Stmt.Write expr -> compileExpr expr @ [WRITE], env
        | Language.Stmt.Seq (frts_stmt, scnd_stmt) -> 
                let frts_stmt, env = compileControl frts_stmt env in
                let scnd_stmt, env = compileControl scnd_stmt env in
                 frts_stmt @ scnd_stmt, env
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

let compile stmt = 
        let env = object
        val count_label = 0
        method generate = "LABEL_" ^ string_of_int count_label, {< count_label = count_label + 1 >}
        end in
        let prg, _ = compileControl stmt env in
        prg
    

