(*
 *      Typer Compiler
 *
 * ---------------------------------------------------------------------------
 *
 *      Copyright (C) 2011-2017  Free Software Foundation, Inc.
 *
 *   Author: Pierre Delaunay <pierre.delaunay@hec.ca>
 *   Keywords: languages, lisp, dependent types.
 *
 *   This file is part of Typer.
 *
 *   Typer is free software; you can redistribute it and/or modify it under the
 *   terms of the GNU General Public License as published by the Free Software
 *   Foundation, either version 3 of the License, or (at your option) any
 *   later version.
 *
 *   Typer is distributed in the hope that it will be useful, but WITHOUT ANY
 *   WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS
 *   FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
 *   more details.
 *
 *   You should have received a copy of the GNU General Public License along
 *   with this program.  If not, see <http://www.gnu.org/licenses/>.
 *
 * ---------------------------------------------------------------------------
 *
 *      Description:
 *          Simple interpreter
 *
 * --------------------------------------------------------------------------- *)

open Util
open Fmt

open Sexp
open Pexp       (* Arg_kind *)
open Lexp       (* Varbind *)

open Elexp
open Builtin
open Grammar
open Debruijn
open Env
open Printf           (* IO Monad *)
module OL = Opslexp


type eval_debug_info = elexp list * elexp list

let dloc = dummy_location
let _global_eval_trace = ref ([], [])
let _global_eval_ctx = ref make_runtime_ctx
let _eval_max_recursion_depth = ref 23000

let builtin_functions
  = ref (SMap.empty : ((location -> eval_debug_info
                        -> value_type list -> value_type)
                       (* The primitive's arity.  *)
                       * int) SMap.t)

let add_builtin_function name f arity =
  builtin_functions := SMap.add name (f, arity) (!builtin_functions)

let append_eval_trace trace (expr : elexp) =
  let (a, b) = trace in
  let r = expr::a, b in
    _global_eval_trace := r; r

let append_typer_trace trace (expr : elexp) =
  let (a, b) = trace in
  let r = (a, expr::b) in
    _global_eval_trace := r; r

let get_trace () = !_global_eval_trace

let rec_depth trace =
  let (a, b) = trace in
    List.length b

(* eval error are always fatal *)
let error loc msg =
    msg_error "EVAL" loc msg;
    flush stdout;
    raise (internal_error msg)

let fatal = msg_fatal "EVAL"
let warning = msg_warning "EVAL"

(*  Print a message that look like this:
 *
 * [Ln   8, cl   6] ./samples/error.typer
 *   [X] Fatal     EVAL     MESSAGE
 *       > ....
 *       > ....
 *
 *)

let debug_messages error_type loc message messages =
  let msg = List.fold_left (fun str msg ->
    str ^ "\n        > " ^ msg) message messages in
      error_type loc (msg ^ "\n")

let root_string () =
  let a, _ = !_global_eval_trace in
  match List.rev a with
    | [] -> ""
    | e::_ -> elexp_string e

let debug_message error_type type_name type_string loc expr message =
  debug_messages error_type loc
    message [
      (type_name expr) ^ ": " ^ (type_string expr);
      "Root: " ^ (root_string ());
    ]

(* Print value name followed by the value in itself, finally throw an exception *)
let value_fatal = debug_message fatal value_name value_string
let value_error = debug_message error value_name value_string
let elexp_fatal = debug_message fatal elexp_name elexp_string


(* FIXME: We're not using predef here.  This will break if we change
 * the definition of `Bool` in builtins.typer.  *)
let ttrue = Vcons ((dloc, "true"), [])
let tfalse = Vcons ((dloc, "false"), [])
let o2v_bool b = if b then ttrue else tfalse

(*
 *                  Builtins
 *)
(* Builtin of builtin * string * ltype *)
let add_binary_iop name f =
  let name = "Int." ^ name in
  let f loc (depth : eval_debug_info) (args_val: value_type list) =
    match args_val with
    | [Vint (v); Vint (w)] -> Vint (f v w)
    | _ -> error loc ("`" ^ name ^ "` expects 2 Int arguments") in
  add_builtin_function name f 2

let _ = add_binary_iop "+"  (+);
        add_binary_iop "-"  (-);
        add_binary_iop "*" ( * );
        add_binary_iop "/"  (/)

let add_binary_bool_iop name f =
  let name = "Int." ^ name in
  let f loc (depth : eval_debug_info) (args_val: value_type list) =
    match args_val with
    | [Vint (v); Vint (w)] -> o2v_bool (f v w)
    | _ -> error loc ("`" ^ name ^ "` expects 2 Int arguments") in
  add_builtin_function name f 2

let _ = add_binary_bool_iop "<"  (<);
        add_binary_bool_iop ">"  (>);
        add_binary_bool_iop "="  (=);
        add_binary_bool_iop ">="  (>=);
        add_binary_bool_iop "<="  (<=)

let add_binary_fop name f =
  let name = "Float." ^ name in
  let f loc (depth : eval_debug_info) (args_val: value_type list) =
    match args_val with
    | [Vfloat (v); Vfloat (w)] -> Vfloat (f v w)
    | _ -> error loc ("`" ^ name ^ "` expects 2 Float arguments") in
  add_builtin_function name f 2

let _ = add_binary_fop "+"  (+.);
        add_binary_fop "-"  (-.);
        add_binary_fop "*" ( *. );
        add_binary_fop "/"  (/.)

let make_symbol loc depth args_val  = match args_val with
  | [Vstring str] -> Vsexp (Symbol (loc, str))
  | _ -> error loc "Sexp.symbol expects one string as argument"

let make_node loc depth args_val = match args_val with
  | [Vsexp (op); lst] ->
     let args = v2o_list lst in

     let s = List.map (fun g -> match g with
                                | Vsexp(sxp)  -> sxp
                                | _ ->
                                   (* print_rte_ctx ctx; *)
                                   value_error loc g "Sexp.node expects `List Sexp` second as arguments") args in

     Vsexp (Node (op, s))

  | _  -> error loc "Sexp.node expects a `Sexp` and a `List Sexp`"


let make_string loc depth args_val  = match args_val with
  | [Vstring str] -> Vsexp (String (loc, str))
  | _ -> error loc "Sexp.string expects one string as argument"

let make_integer loc depth args_val = match args_val with
  | [Vint (str)] -> Vsexp (Integer (loc, str))
  | _ -> error loc "Sexp.integer expects one integer as argument"


let make_float loc depth args_val   = match args_val with
  | [Vfloat x] -> Vsexp (Float (loc, x))
  | _ -> error loc "Sexp.float expects one float as argument"

(* let make_block loc depth args_val   = match args_val with
 *   | [Vblock b] -> Vsexp (Block (loc, b))
 *   | _ -> error loc "Sexp.block expects one block as argument" *)

let string_eq loc depth args_val = match args_val with
  | [Vstring s1; Vstring s2] -> o2v_bool (s1 = s2)
  | _ -> error loc "string_eq expects 2 strings"

let sexp_eq loc depth args_val = match args_val with
  | [Vsexp (s1); Vsexp (s2)] -> o2v_bool (sexp_equal s1 s2)
  | _ -> error loc "Sexp.= expects 2 sexps"

let file_open loc depth args_val = match args_val with
  | [Vstring (file); Vstring (mode)] ->
     (* open file *) (* return a file handle *)
     Vcommand(fun () ->
         match mode with
         | "r" -> Vin (open_in file)
         | "w" -> Vout (open_out file)
         | _ -> error loc "wrong open mode")

  | _ -> error loc "File.open expects 2 strings"

let file_read loc depth args_val = match args_val with
  (* FIXME: Either rename it to "readline" and drop the second arg,
   * or actually pay attention to the second arg.  *)
  | [Vin channel; Vint n] -> Vstring (input_line channel)
  | _ -> List.iter (fun v -> value_print v; print_string "\n") args_val;
         error loc "File.read expects an in_channel"

let file_write loc depth args_val = match args_val with
  | [Vout channel; Vstring msg]
    -> Vcommand (fun () -> fprintf channel "%s" msg;
                       (* FIXME: This should be the unit value!  *)
                       Vundefined)
  | _ -> List.iter (fun v -> value_print v) args_val;
         error loc "File.write expects an out_channel and a string"

let rec _eval lxp (ctx : Env.runtime_env) (trace : eval_debug_info): (value_type) =

    let trace = append_eval_trace trace lxp in
    let eval lxp ctx = _eval lxp ctx trace in

    (* This creates an O(N^2) cost for deep recursion because rec_depth
     * uses `length` on the stack trace.  *)
    (* (if (rec_depth trace) > (!_eval_max_recursion_depth) then
     *     fatal (elexp_location lxp) "Recursion Depth exceeded"); *)

    (* Save current trace in a global variable. If an error occur,
       we will be able to retrieve the most recent trace and context *)
    _global_eval_ctx := ctx;
    _global_eval_trace := trace;

    match lxp with
        (*  Leafs           *)
        (* ---------------- *)
        | Imm(Integer (_, i))       -> Vint (i)
        | Imm(String (_, s))        -> Vstring (s)
        | Imm(sxp)                  -> Vsexp (sxp)
        | Cons (label)              -> Vcons (label, [])
        | Lambda ((_, n), lxp)      -> Closure (n, lxp, ctx)
        | Builtin ((_, str))        -> Vbuiltin (str)

        (* Return a value stored in env *)
        | Var((loc, name), idx) as e ->
          eval_var ctx e ((loc, name), idx)

        (*  Nodes           *)
        (* ---------------- *)
        | Let(_, decls, inst) ->
          let nctx = _eval_decls decls ctx trace in
            eval inst nctx

        (* Function call *)
        | Call (f, args) ->
            eval_call (elexp_location f) f trace
                      (_eval f ctx trace)
                      (List.map (fun e -> _eval e ctx trace) args)

        (* Case *)
        | Case (loc, target, pat, dflt)
          -> (eval_case ctx trace loc target pat dflt)

        (* FIXME: Here, we'd want to apply `ctx` to `e`, but we can't
         * apply a runtime-ctx to a lexp!
         * E.g. say we have `λt ≡> Ind (arg : t)`: by the time we get here,
         * Our `Type` carries `Ind (arg : t)` but `t` is not in `ctx`!
         * So we should either use an elexp instead of a lexp,
         * or somehow recover a lexp-ctx from the runtime-ctx (maybe
         * with extra info that `Type` could carry),
         * or find another trick.
         * Hence, the `e` carried by `Vtype` is just indicative and not
         * something we can use.  *)
        | Type e -> Vtype e


and eval_var ctx lxp v =
    let ((loc, name), idx) = v in
    try get_rte_variable (Some name) (idx) ctx
    with e ->
      elexp_fatal loc lxp
        ("Variable: " ^ name ^ (str_idx idx) ^ " was not found ")

(* unef: unevaluated function (to make the trace readable) *)
and eval_call loc unef i f args =
  match f, args with
  (* return result of eval *)
  | _, [] -> f

  | Vcons (n, fields), _
    -> Vcons (n, List.append fields args)

  | Closure (x, e, ctx), v::vs
    -> let rec bindargs e vs ctx = match (vs, e) with
       | (v::vs, Lambda ((_, x), e))
         (* "Uncurry" on the fly.  *)
         -> bindargs e vs (add_rte_variable (Some x) v ctx)
       | ([], _) ->
        let trace = append_typer_trace i unef in
        _eval e ctx trace
       | _ -> eval_call loc unef i (_eval e ctx i) vs in
     bindargs e vs (add_rte_variable (Some x) v ctx)

  | Vbuiltin (name), args
    -> (try let (builtin, arity) = SMap.find name !builtin_functions in
           let nargs = List.length args in
           if nargs = arity then
             builtin loc i args        (* Fast common case.  *)
           else if nargs > arity then
             let rec split n vs acc = match (n, vs) with
               | 0, _ -> let v = eval_call loc unef i f (List.rev acc) in
                        eval_call loc unef i v vs
               | _, (v::vs) -> split (n - 1) vs (v::acc)
               | _ -> error loc "Impossible!"
             in split nargs args []
           else
             let rec buildctx args ctx = match args with
               | [] -> ctx
               | arg::args -> buildctx args (add_rte_variable None arg ctx) in
             let rec buildargs n =
               if n >= 0
               then (Var ((loc, "<dummy>"), n))::buildargs (n - 1)
               else [] in
             let rec buildbody n =
               if n > 0 then
                 Lambda ((loc, "<dummy>"), buildbody (n - 1))
               else Call (Builtin (dloc, name), buildargs (arity - 1)) in
             Closure ("<dummy>",
                      buildbody (arity - nargs - 1),
                      buildctx args Myers.nil)

        with Not_found
             -> error loc ("Requested Built-in `" ^ name ^ "` does not exist")
           | e -> error loc ("Exception thrown from primitive `" ^ name ^"`"))

  | Vtype e, _
   (* We may call a Vlexp e.g. for "x = Map Int String".
    * FIXME: The arg will sometimes be a Vlexp but not always, so this is
    * really just broken!  *)
    -> Vtype (L.mkCall (e, [(Aexplicit, Var ((dummy_location, "?"), -1))]))
  | _ -> value_fatal loc f "Trying to call a non-function!"

and eval_case ctx i loc target pat dflt =
    (* Eval target *)
    let v = _eval target ctx i in

    (* extract constructor name and arguments *)
    let ctor_name, args = match v with
        | Vcons((_, cname), args)  -> cname, args
        | _ -> elexp_fatal loc target "Target is not a Constructor" in

    (*  Get working pattern *)
    try let (_, pat_args, exp) = SMap.find ctor_name pat in
        (* build context (List.fold2 has problem with some cases)  *)
        (* This is more robust                                     *)
        let rec fold2 nctx pats args =
            match pats, args with
            | pat::pats, arg::args
              -> let nctx = add_rte_variable (match pat with
                                             | Some (_, name) -> Some name
                                             | _ -> None) arg nctx in
                fold2 nctx pats args
            (* Errors: those should not happen but they might  *)
            (* List.fold2 would complain. we print more info   *)
            | _::_, [] -> warning loc "a) Eval::Case Pattern Error"; nctx
            | [], _::_ -> warning loc "b) Eval::Case Pattern Error"; nctx
            (* Normal case *)
            | [], [] -> nctx in

        let nctx = fold2 ctx pat_args args in
            _eval exp nctx i

    (* Run default *)
    with Not_found -> (match dflt with
        | Some (var, lxp)
          -> let var' = match var with None -> None | Some (_, n) -> Some n in
            _eval lxp (add_rte_variable var' v ctx) i
        | _ -> error loc "Match Failure")

and build_arg_list args ctx i =
    (*  _eval every args *)
    let arg_val = List.map (fun (k, e) -> _eval e ctx i) args in

    (*  Add args inside context *)
    List.fold_left (fun c v -> add_rte_variable None v c) ctx arg_val

and _eval_decls (decls: (vname * elexp) list)
                        (ctx: runtime_env) i: runtime_env =

    let n = (List.length decls) - 1 in

    (* Read declarations once and push them *)
    let nctx = List.fold_left (fun ctx ((_, name), _) ->
      add_rte_variable (Some name) Vundefined ctx) ctx decls in

    List.iteri
      (fun idx ((_, name), e) ->
        let e = Optimize.optimize nctx e in
        let v = _eval e nctx i in
        let offset = n - idx in
        ignore (set_rte_variable offset (Some name) v nctx))
      decls;

        nctx

(* -------------------------------------------------------------------------- *)
(*              Builtin Implementation  (Some require eval)                   *)

(* Sexp -> (Sexp -> List Sexp -> Sexp) -> (String -> Sexp) ->
    (String -> Sexp) -> (Int -> Sexp) -> (Float -> Sexp) -> (List Sexp -> Sexp)
        ->  Sexp *)
and sexp_dispatch loc depth args =
    let eval a b = _eval a b depth in
    let sxp, nd, ctx_nd,
            sym, ctx_sym,
            str, ctx_str,
             it, ctx_it,
            flt, ctx_flt,
            blk, ctx_blk = match args with

        | [sxp; Closure(_, nd,  ctx_nd); Closure(_, sym, ctx_sym);
                Closure(_, str, ctx_str); Closure(_, it, ctx_it);
                Closure(_, flt, ctx_flt); Closure(_, blk, ctx_blk)] ->
            sxp, nd, ctx_nd, sym, ctx_sym, str, ctx_str, it, ctx_it,
            flt, ctx_flt, blk, ctx_blk
        | _ ->  error loc "sexp_dispatch expects 7 arguments" in

    let sxp = match sxp with
        | Vsexp(sxp)   -> sxp
        | _ -> value_fatal loc sxp "sexp_dispatch expects a Sexp as 1st arg" in

    match sxp with
        | Node    (op, s)    ->(
            let rctx = ctx_nd in
            let rctx = add_rte_variable None (Vsexp(op)) rctx in
            let rctx = add_rte_variable None (o2v_list s) rctx in
                match eval nd rctx with
                    | Closure(_, nd, _) -> eval nd rctx
                    | _ -> error loc "Node has 2 arguments")

        | Symbol  (_ , s)    ->
             let rctx = ctx_sym in
             eval sym (add_rte_variable None (Vstring(s)) rctx)
        | String  (_ , s)    ->
             let rctx = ctx_str in
             eval str (add_rte_variable None (Vstring(s)) rctx)
        | Integer (_ , i)    ->
             let rctx = ctx_it in
             eval it (add_rte_variable None (Vint(i)) rctx)
        | Float   (_ , f)    ->
             let rctx = ctx_flt in
             eval flt (add_rte_variable None (Vfloat(f)) rctx) (*
        | Block   (_ , s, _) ->
             eval blk (add_rte_variable None (o2v_list s)) *)
        | _ ->
          print_string "match error\n"; flush stdout;
          error loc "sexp_dispatch error"

(* -------------------------------------------------------------------------- *)
and print_eval_result i lxp =
    print_string "     Out[";
    ralign_print_int i 2;
    print_string "] >> ";
    value_print lxp; print_string "\n";

and print_typer_trace' trace =

  let trace = List.rev trace in

  print_string (Fmt.make_title "Typer Trace");
  print_string (Fmt.make_sep '-');

  let _ = List.iteri (fun i expr ->
    print_string "    ";
    Fmt._print_ct_tree i; print_string "+- ";
    print_string ((elexp_string expr) ^ "\n")) trace in

  print_string (Fmt.make_sep '=')

and print_typer_trace trace =
  match trace with
    | Some t -> print_typer_trace' t
    | None -> let (a, b) = !_global_eval_trace in
      print_typer_trace' b

and print_trace title trace default =
  (* If no trace is provided take the most revent one *)
  let trace = match trace with
    | Some trace -> trace
    | None -> default in

  (* Trace is upside down by default *)
  let trace = List.rev trace in

  (* Now eval trace and lparse trace are the same *)
  let print_trace = (fun type_name type_string type_loc i expr ->
    (* Print location info *)
    print_string ("    [" ^ (loc_string (type_loc expr)) ^ "] ");

    (* Print call trace visualization *)
    Fmt._print_ct_tree i; print_string "+- ";

    (* Print element *)
    print_string ((type_name expr) ^ ": " ^ (type_string expr) ^ "\n")
  ) in

  let elexp_trace = print_trace elexp_name elexp_string elexp_location in

  (* Print the trace*)
  print_string (Fmt.make_title title);
  print_string (Fmt.make_sep '-');
  let _ = List.iteri elexp_trace trace in
  print_string (Fmt.make_sep '=')

and print_eval_trace trace =
    let (a, b) = !_global_eval_trace in
      print_trace " EVAL TRACE " trace a

let io_bind loc depth args_val =
  let trace_dum = (Var ((loc, "<dummy>"), -1)) in

  match args_val with
  | [Vcommand cmd; callback]
    -> (* bind returns another Vcommand *)
     Vcommand (fun ()
               -> match eval_call loc trace_dum depth callback [cmd ()] with
                 | Vcommand cmd -> cmd ()
                 | _ -> error loc "IO.bind second arg did not return a command")
  | _ -> error loc "Wrong number of args or wrong first arg value in `IO.bind`"

let io_run loc depth args_val = match args_val with
    | [Vcommand cmd; v] -> let _ = cmd () in v
    | _ -> error loc "IO.run expects a monad and a function as arguments"

let io_return loc depth args_val = match args_val with
  | [v] -> Vcommand (fun () -> v)
  | _ -> error loc "IO.return takes a single argument"

let float_to_string loc depth args_val = match args_val with
  | [Vfloat x] -> Vstring (string_of_float x)
  | _ -> error loc "Float.to_string expects one Float arg"

let sys_exit loc depth args_val = match args_val with
  | [Vint n] -> Vcommand (fun _ -> exit n)
  | _ -> error loc "Sys.exit takes a single Int argument"

let y_operator loc depth args =
  match args with
  | [f] -> let aname = "<anon>" in
          let yf_ref = ref Vundefined in
          let yf = Closure(aname,
                           Call (Var ((dloc, "f"), 1),
                                 [Var ((dloc, "yf"), 2);
                                  Var ((dloc, aname), 0)]),
                           Myers.cons (Some "f", ref f)
                                      (Myers.cons (Some "yf", yf_ref)
                                                  Myers.nil)) in
          yf_ref := yf;
          yf
  | _ -> error loc ("Y expects 1 (function) argument")

let arity0_fun loc _ _ = error loc "Called a 0-arity function!?"
let nop_fun loc _ vs = match vs with
  | [v] -> v
  | _ -> error loc "Wrong number of argument to nop"

let register_builtin_functions () =
  List.iter (fun (name, f, arity) -> add_builtin_function name f arity)
            [
              (* ("Sexp.block" , make_block, 1); *)
              ("Sexp.symbol"   , make_symbol, 1);
              ("Sexp.string"   , make_string, 1);
              ("Sexp.integer"  , make_integer, 1);
              ("Sexp.float"    , make_float, 1);
              ("Sexp.node"     , make_node, 2);
              ("Sexp.dispatch" , sexp_dispatch, 7);
              ("String.="      , string_eq, 2);
              ("Sexp.="        , sexp_eq, 2);
              ("Float.to_string", float_to_string, 1);
              ("IO.bind"       , io_bind, 2);
              ("IO.return"     , io_return, 1);
              ("IO.run"        , io_run, 2);
              ("Sys.exit"      , sys_exit, 1);
              ("File.open"     , file_open, 2);
              ("File.read"     , file_read, 2);
              ("File.write"    , file_write, 2);
              ("Eq.refl"       , arity0_fun, 0);
              ("Eq.cast"       , nop_fun, 1);
              ("Y"             , y_operator, 1);
            ]
let _ = register_builtin_functions ()

let builtin_constant v loc depth args_val = match args_val with
  (* FIXME: Dummy arg because we currently can't define a Builtin
   * *constant* (except for cases like Eq.refl where the contant is not
   * actually used).  *)
  | [_] -> v
  | _ -> error loc "Builtin almost-constant takes a unit argument"

let register_builtin_constants () =
  List.iter (fun (name, v) -> add_builtin_function name (builtin_constant v) 1)
            [
              ("File.stdout", Vout stdout);
              ("Sys.cpu_time", Vcommand (fun () -> Vfloat (Sys.time ())))
            ]
let _ = register_builtin_constants ()

let eval lxp ctx = _eval lxp ctx ([], [])

let debug_eval lxp ctx =
    try eval lxp ctx
    with e -> (
        print_rte_ctx (!_global_eval_ctx);
        print_eval_trace None;
        raise e)


let eval_decls decls ctx = _eval_decls decls ctx ([], [])

let eval_decls_toplevel (decls: (vname * elexp) list list) ctx =
  (* Add toplevel decls function *)
  List.fold_left (fun ctx decls -> eval_decls decls ctx)
                 ctx decls

(*  Eval a list of lexp *)
let eval_all lxps rctx silent =
    let evalfun = if silent then eval else debug_eval in
    List.map (fun g -> evalfun g rctx) lxps


let varname s = match s with Some (_, v) -> v | _ -> "<anon>"

let roname loname = (match (loname : symbol option) with
                     | Some (_, name) -> Some name
                     | _ -> None)

module CMap
  (* Memoization table.  FIXME: Ideally the keys should be "weak", but
   * I haven't found any such functionality in OCaml's libs.  *)
  = Hashtbl.Make
      (struct type t = lexp_context let hash = Hashtbl.hash let equal = (==) end)
let ctx_memo = CMap.create 1000

let not_closed rctx ((o, vm) : DB.set) =
  VMap.fold (fun i () nc -> let i = i + o in
                         let (_, rc) = Myers.nth i rctx in
                         match !rc with Vundefined -> i::nc | _ -> nc)
            vm []

let closed_p rctx (fvs, mvs) =
  not_closed rctx fvs = []
  (* FIXME: Handle metavars!  *)
  && VMap.is_empty mvs

let from_lctx meta_ctx (lctx: lexp_context): runtime_env =
  (* FIXME: `eval` with a disabled IO.run.  *)
  let rec from_lctx' (lctx: lexp_context): runtime_env =
    match lctx_view lctx with
    | CVempty -> Myers.nil
    | CVlet (loname, def, _, lctx)
      -> let rctx = from_lctx lctx in
         Myers.cons (roname loname,
                     ref (match def with
                          | LetDef e
                            -> let e = L.clean meta_ctx e in
                               if closed_p rctx (OL.fv e) then
                                 eval (OL.erase_type e) rctx
                               else Vundefined
                          | _ -> Vundefined))
                    rctx
    | CVfix (defs, lctx)
      -> let fvs = List.fold_left
                     (fun fvs (_, odef, _)
                      -> match odef with
                         | LetDef e
                           -> OL.fv_union fvs (OL.fv (L.clean meta_ctx e))
                         | _ -> fvs)
                     OL.fv_empty
                     defs in
         let rctx = from_lctx lctx in
         let (nrctx, evs, alldefs)
           = List.fold_left (fun (rctx, evs, alldefs) (loname, odef, _)
                             -> let rc = ref Vundefined in
                                let nrctx = Myers.cons (roname loname, rc) rctx in
                                match odef with
                                | LetDef e -> (nrctx, (e, rc)::evs, alldefs)
                                | _ -> nrctx, [], false)
                            (rctx, [], true) defs in
         let _ =
           (* FIXME: Evaluate those defs that we can, even if not all defs
            * are present!  *)
           if alldefs && closed_p rctx (OL.fv_hoist (List.length defs) fvs) then
             List.iter (fun (e, rc) -> rc := eval (OL.erase_type e) nrctx) evs
           else () in
         nrctx
  and from_lctx lctx =
    try CMap.find ctx_memo lctx
    with Not_found
         -> let r = from_lctx' lctx in
            CMap.add ctx_memo lctx r;
            r
  in from_lctx lctx

(* build a rctx from a ectx.  *)
let from_ectx meta_ctx (ctx: elab_context): runtime_env =
  from_lctx meta_ctx (ectx_to_lctx ctx)
