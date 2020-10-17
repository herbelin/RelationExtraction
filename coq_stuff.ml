(****************************************************************************)
(*  RelationExtraction - Extraction of inductive relations for Coq          *)
(*                                                                          *)
(*  This program is free software: you can redistribute it and/or modify    *)
(*  it under the terms of the GNU General Public License as published by    *)
(*  the Free Software Foundation, either version 3 of the License, or       *)
(*  (at your option) any later version.                                     *)
(*                                                                          *)
(*  This program is distributed in the hope that it will be useful,         *)
(*  but WITHOUT ANY WARRANTY; without even the implied warranty of          *)
(*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the           *)
(*  GNU General Public License for more details.                            *)
(*                                                                          *)
(*  You should have received a copy of the GNU General Public License       *)
(*  along with this program.  If not, see <http://www.gnu.org/licenses/>.   *)
(*                                                                          *)
(*  Copyright 2011, 2012 CNAM-ENSIIE                                        *)
(*                 Catherine Dubois <dubois@ensiie.fr>                      *)
(*                 David Delahaye <david.delahaye@cnam.fr>                  *)
(*                 Pierre-Nicolas Tollitte <tollitte@ensiie.fr>             *)
(****************************************************************************)

open Host_stuff
open Pred
open Libnames
open Nametab
open Util
open Pp
open Context.Rel.Declaration

type htyp = Constr.types option

type henv = {
  ind_refs : (ident * Libnames.qualid) list;
  ind_grefs : (ident * Names.GlobRef.t) list;
  cstrs : (ident * Constr.constr) list;
}

let coq_get_fake_type () = None

let coq_get_bool_type () = (["true"; "false"], 
  Some (UnivGen.constr_of_monomorphic_global (locate (qualid_of_string "Coq.Init.Datatypes.bool"))))

let coq_functions = {
  h_get_fake_type = coq_get_fake_type;
  h_get_bool_type = coq_get_bool_type;
}


(* Extraction of dependencies *)
let extract_dependencies henv =
  (* We need a list of references; Extraction missing an entry point with GlobRef.t ?? *)
  let refl = List.map (fun (_, c) -> 
    match Constr.kind c with
      | Constr.Construct _ | Constr.Const _ ->
         Constrextern.extern_reference Names.Id.Set.empty (fst (Constr.destRef c))
      | _ -> assert false
  ) henv.cstrs in
  (* Not required anymore (Coq bool is mapped to OCaml bool) *)
  (*let refl = (Libnames.Qualid 
    (Util.dummy_loc, Libnames.qualid_of_string "Coq.Init.Datatypes.bool"))::
    refl in *)
  Extraction_plugin.Extract_env.full_extraction None refl


(* Generates mode arguments for nb parameters. *)
let rec gen_param_args nb =
  if nb = 0 then []
  else (gen_param_args (nb-1))@[nb]

let adapt_mode ind_ref mode = 
  let ind,_ = Constr.destInd (UnivGen.constr_of_monomorphic_global (Nametab.global ind_ref)) in
  let _, oib = Inductive.lookup_mind_specif (Global.env ()) ind in
  let parameters = oib.Declarations.mind_arity_ctxt in
  let fil = List.filter (get_name %> Names.Name.is_name) parameters in
  let param_nb = List.length fil in
  let mode = List.map (fun i -> i + param_nb) mode in
  (gen_param_args param_nb) @ mode

(* Checks if x is present in the list option l. *)
let rec list_mem_option x l = match l with
  | Some (a::tl) -> x = a || list_mem_option x (Some tl)
  | Some [] -> false
  | _ -> true


(* Gets the type of one inductive body *)
let get_user_arity = function
  | Declarations.RegularArity m -> m.Declarations.mind_user_arity
  | _ -> CErrors.user_err (Pp.str "Cannot deal with polymorphic inductive arity")

let make_mode ind_glb user_mode =
  let ind, _ = Constr.destInd (UnivGen.constr_of_monomorphic_global ind_glb) in
  let _, oib = Inductive.lookup_mind_specif (Global.env ()) ind in
  let typ = get_user_arity oib.Declarations.mind_arity in
  let (args_real, _) = Term.decompose_prod typ in
  let args_nb = List.length args_real in

  let args_imp = match Impargs.implicits_of_global ind_glb with
    | (_, a)::_ -> a
    | _ -> [] in

  let args = if args_nb > (List.length args_imp) then
    Array.to_list (Array.make args_nb false)
  else
    List.map Impargs.is_status_implicit args_imp in

  let rec rec_mode args i = match args with
    | [] -> []
    | a::tl_args -> if a then
(* This would be needed in the case where implicit arguments were not 
   parameters... *)
        (*MSkip::(rec_mode tl_args i)*)
(* The following line assumes that all implicit arguments are included in the
   mode. This is done by the adapt_mode function when implicit arguments are
   parameters. So we assume that all implicits arguments are parameters detected
   by adapt_mode. *)
        MSkip::(rec_mode tl_args (i+1))
      else if list_mem_option i user_mode then
        MInput::(rec_mode tl_args (i+1))
      else MOutput::(rec_mode tl_args (i+1)) in
  rec_mode args 1

let pp_coq_constr c = Pp.string_of_ppcmds (Printer.pr_econstr_env (Global.env()) (Evd.from_env (Global.env())) c)

let get_coq_type (_,t) = match t with
  | Some ct -> ct
  | _ -> CErrors.anomaly ~label:"RelationExtraction" (str "Missing type information")

let get_in_types (env, id) =
  let rec get_in_rec args mode = match (args, mode) with
    | (a::tl_args, MInput::tl_mode) -> a::(get_in_rec tl_args tl_mode)
    | (_::tl_args, MOutput::tl_mode) -> get_in_rec tl_args tl_mode
    | (_, MSkip::tl_mode) -> get_in_rec args tl_mode
    | _ -> [] in
  let mode = List.hd (extr_get_modes env id) in
  let args_types = (extr_get_spec env id).spec_args_types in
  let mode, args_types = match fix_get_recursion_style env id with
    | FixCount ->
      (* When a function is extracted with a counter, we have to add
         an argument (at first position) of type nat. *)
      let coq_nat = Some (UnivGen.constr_of_monomorphic_global
          (locate (qualid_of_string "Coq.Init.Datatypes.nat"))) in
      let nat_typ = CTSum [ident_of_string "O"; ident_of_string "S"], coq_nat in
      MInput::mode, nat_typ::args_types
    | _ -> mode, args_types in
  get_in_rec args_types mode

let get_out_type opt (env, id) =
  let fun_name = (extr_get_mlfun env id).mlfun_name in 
  let comp = fix_get_completion_status env fun_name in
  let rec get_out_rec args mode = match (args, mode) with
    | (a::tl_args, MOutput::tl_mode) -> a::(get_out_rec tl_args tl_mode)
    | (_::tl_args, MInput::tl_mode) -> get_out_rec tl_args tl_mode
    | (_, MSkip::tl_mode) -> get_out_rec args tl_mode
    | _ -> [] in
  let mode = List.hd (extr_get_modes env id) in
  let args_types = (extr_get_spec env id).spec_args_types in
  match get_out_rec args_types mode with
    | [] -> UnivGen.constr_of_monomorphic_global
              (locate (qualid_of_string "Coq.Init.Datatypes.bool"))
    | (_ , Some t)::_ -> if opt && comp then
      let opt = UnivGen.constr_of_monomorphic_global
              (locate (qualid_of_string "Coq.Init.Datatypes.option")) in
      Constr.mkApp (opt, [|t|])
      else t
    | _ -> CErrors.anomaly ~label:"RelationExtraction" (str "Missing type information")

let find_coq_constr_s s = 
  UnivGen.constr_of_monomorphic_global (locate (qualid_of_string s))

let find_coq_constr_i i = 
  find_coq_constr_s (string_of_ident i)


