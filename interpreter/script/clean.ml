open Ast
open Types
open Source
open Values
open Utf8
open Parse.Module

let dummy_pos : pos = {
  file = "dummy";
  line = 42;
  column = 42;
}

let dummy_region : region = {
  left = dummy_pos;
  right = dummy_pos;
}

let wrap (x : 'a) : 'a Source.phrase =
  { it = x; at = dummy_region }

let default_value_instrs : value_type -> instr = function
  | NumType I32Type -> wrap (Const (wrap (I32 42l)))
  | NumType I64Type -> wrap (Const (wrap (I64 42L)))
  | NumType F32Type -> wrap (Const (wrap (F32 (F32.of_float 42.2))))
  | NumType F64Type -> wrap (Const (wrap (F64 (F64.of_float 42.2))))
  | _               -> failwith "default_value only generates instructions for NumType"

let stub_instrs : func_type -> instr list = function
  | FuncType (_, r) -> List.map default_value_instrs r

let get_imports : module_ -> import' list = function
  | m -> List.map (fun f -> f.it) m.it.imports

let get_type (m : module_) (c : codepoint) : func_type =
  let cth = List.nth (m.it.types) c in cth.it

let filter_envs : import' list -> (codepoint * import') list = function
  | i -> let
           i_mapped = (List.mapi (fun i x -> (i, x)) i)
         in
           List.filter (fun (_, f) -> encode (f.module_name) = "env") i_mapped

(* The int32 below represents the type of the imported function *)
let get_func_imports_types : (codepoint * import') list -> (codepoint * int32) list = function
  | xs -> List.map (fun (i, x) -> match x with FuncImport fi -> (i, fi.it) | _ -> failwith "fiError")
                                               (List.map (fun (i, f) -> (i, f.idesc.it)) xs)

let make_stub_funcs (m : module_) (fits : (codepoint * int32) list) : (codepoint * func) list =
    let f i = get_type m (Int32.to_int i) in
    let g i = wrap ({ftype = wrap i; locals = []; body = stub_instrs (f i)}) in 
    List.map (fun (c, v) -> (c, g v)) fits

let count_greater_than (x : int) (xs : int list) : int =
  List.fold_left (fun acc y -> if x > y then acc + 1 else acc) 0 xs

let recalc (m : module_) (cs : codepoint list) (c : codepoint) : codepoint =
  let max_import_cp = List.length (m.it.imports) - 1 in
  let max_cp = List.length (m.it.imports) + List.length (m.it.funcs) - List.length cs in
  match cs with
    | _ when List.mem c cs                 -> Option.get (List.find_index (fun e -> e = c) cs) + max_cp
    | _ when cs <> [] && c < max_import_cp -> c - count_greater_than c cs
    | _                                    -> c - List.length cs

let add_stubs (m : module_') (stubs : func list) : module_' =
  let old_funcs = m.funcs in
  { m with funcs = old_funcs @ stubs }

let recalc_var m cs v = (wrap (Int32.of_int (recalc m cs (Int32.to_int v.it))))

let change_calls (m : module_) (cs : codepoint list) : module_ =
  let rec f x = 
    let f' = List.map (fun e -> wrap (f e)) in
    match x.it with 
    | Call v             -> Call (recalc_var m cs v)
    | Block (bt, is)     -> Block (bt, f' is)
    | Loop (lt, is)      -> Loop (lt, f' is)
    | If (ift, is1, is2) -> If (ift, f' is1, f' is2)
    | i                  -> i in
  let g x = { x.it with body = List.map (fun e -> wrap (f e)) (x.it.body) } in
  let changed_calls = List.map (fun e -> wrap (g e)) (m.it.funcs) in
  wrap ({ m.it with funcs = changed_calls })

let remove_envs : module_ -> module_ = function
  | m -> 
      let envs = List.map snd (filter_envs (get_imports m)) in
      let imps = get_imports m in
      let removed_imps' = List.filter (fun x -> not (List.mem x envs)) imps in
      let removed_imps = List.map wrap removed_imps' in
      wrap ({ m.it with imports = removed_imps })

let change_exports (m : module_) (cs : codepoint list) : module_ =
  let f x = match x.it.edesc.it with
    | FuncExport v -> wrap ({ name = x.it.name; edesc = wrap (FuncExport (recalc_var m cs v)) })
    | ep           -> wrap ({ name = x.it.name; edesc = wrap ep }) in
  let changed_exports = List.map f m.it.exports in
  wrap ({ m.it with exports = changed_exports })

let find_main_set_start (m : module_) : module_ =
  let mf' = List.filter (fun x -> encode x.it.name = "main") m.it.exports in
  let mf = List.hd mf' in
  match mf.it.edesc.it with
    | FuncExport v -> wrap ({ m.it with start = Some (wrap({ sfunc = v })) })
    | _            -> failwith "main can only be a FuncExport"

(* What an annoying function to write :) *)
let change_calls_in_elem (m : module_) (cs : codepoint list) : module_ =
  let es = List.map (fun x -> x.it) m.it.elems in
  let f (x : instr) = match x.it with
    | RefFunc v -> RefFunc (recalc_var m cs v)
    | i         -> i in
  let g (x : const list) : const list = 
    List.map (fun e -> wrap (List.map (fun e' -> wrap (f e')) e.it)) x in
  let h (x : elem_segment') = { x with einit = g (x.einit) } in
  let changed_es : elem_segment list = List.map (fun e -> wrap (h e)) es in
  wrap ({ m.it with elems = changed_es })
 
let go = 
  let pf = parse_file "/home/spirit/Desktop/Programs/VU-Coding-Assignment/readme/grep-re/grep-clean.wat" in
  let (_, d) = pf in
  let d' = d.it in
  let output_file = "/home/spirit/Desktop/Programs/VU-Coding-Assignment/readme/grep-re/grep-cleaned.wat" in
  let oc = open_out output_file in
  match d' with
    | Script.Textual m -> 
        let stubbed_funcs = make_stub_funcs m (get_func_imports_types (filter_envs (get_imports m))) in
        let cs            = List.map fst stubbed_funcs in
        let calls_chngd_m = change_calls m cs in 
        let added_funcs_m = wrap (add_stubs calls_chngd_m.it (List.map snd stubbed_funcs)) in
        let remvd_funcs_m = remove_envs added_funcs_m in
        let chngd_exprt_m = change_exports remvd_funcs_m cs in
        let chngd_elems_m = change_calls_in_elem chngd_exprt_m cs in
        let start_set_m   = find_main_set_start chngd_elems_m in
        Print.module_ oc 80 start_set_m
    | _                -> failwith "Why is parsed file not a module?"
