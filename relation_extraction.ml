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
(*  Copyright 2011, 2012, 2014 CNAM-ENSIIE                                  *)
(*                 Catherine Dubois <dubois@ensiie.fr>                      *)
(*                 David Delahaye <david.delahaye@cnam.fr>                  *)
(*                 Pierre-Nicolas Tollitte <tollitte@ensiie.fr>             *)
(****************************************************************************)

open Util
open Pp
open Declarations
open Names
open Nametab
open Pred
open Coq_stuff
open Fixpred
open Fixpointgen


(************************)
(* Predicate extraction *)
(************************)

(* TODO: order specifications (by dependency) befrore doing a fixpoint 
         extratction. *)

let ident_of_string_option s_opt = match s_opt with
  | None -> None
  | Some s -> Some (ident_of_string s)

let rec find_func_name ind_ref modes = match modes with
  | (fn, ind_ref', _, rs)::modes ->
      if ind_ref == ind_ref' then (ident_of_string_option fn, rs)
      else find_func_name ind_ref modes
  | [] -> raise Not_found

(* Main routine *)
let extract_relation_common dep ord ind_ref modes =
  (* Initial henv *)
  let ind_refs, ind_grefs = List.split (List.map ( fun (_, ind_ref, _, _) ->
    let ind = Globnames.destIndRef (global ind_ref) in
    let _, oib = Inductive.lookup_mind_specif (Global.env ()) ind in
    let id = ident_of_string (Id.to_string oib.mind_typename) in
    (id, ind_ref), (id, global ind_ref) ) modes) in
  let henv = { ind_refs = ind_refs; ind_grefs = ind_grefs; cstrs = [] } in
  
  (* Extractions *)
  let ids = List.map (fun ind_ref ->
    let ind = Globnames.destIndRef (global ind_ref) in
    let _, oib = Inductive.lookup_mind_specif (Global.env ()) ind in
  (*let idrs = List.map (fun oib -> Ident (dummy_loc, oib.mind_typename)) 
             oibs in*)
  (*TODO: add irds to ind_refs if they are not present ? 
          ie no mode given, or fail ? *)
    ident_of_string (Id.to_string oib.mind_typename), ind_ref
  ) ind_ref in
  let extractions = List.map (fun (id, ind_ref) ->
    let (fn, rs) = find_func_name ind_ref modes in
  id, (fn, ord, rs)) ids in

  (* Modes *)
  let modes = List.map ( fun (_, ind_ref, mode, _) ->
    let ind_glb = global ind_ref in
    let ind = Globnames.destIndRef ind_glb in
    let _, oib = Inductive.lookup_mind_specif (Global.env ()) ind in
    let id = ident_of_string (Id.to_string oib.mind_typename) in
    (id, [make_mode ind_glb (Some (adapt_mode ind_ref mode))]) 
  ) modes in
  let eq_modes = [[MSkip;MInput;MOutput]; [MSkip;MOutput;MInput]; 
                  [MSkip;MInput;MInput]] in
  let modes = (ident_of_string "eq", eq_modes)::modes in

  (* Compilation *)
  let empty_env = {
    extr_modes = modes;
    extr_extractions = extractions;
    extr_specs = [];
    extr_trees = [];
    extr_mlfuns = [];
    extr_fixfuns = [];
    extr_henv = henv;
    extr_hf = coq_functions;
    extr_fix_env = [];
  } in
  let env = Host2spec.find_specifications empty_env in
  (*Printf.eprintf "%s\n" (pp_extract_env env);*)
  let env = try Pred.make_trees env with
    | RelationExtractionProp (Some p_id, s) -> CErrors.user_err ~hdr:"RelationExtraction"
      (str ("Extraction failed at " ^ string_of_ident p_id ^ ": " ^ s))
    | RelationExtractionProp (None, s) -> CErrors.user_err ~hdr:"RelationExtraction"
      (str ("Extraction failed: " ^ s))
  in
 (*Printf.eprintf "%s\n" (pp_extract_env env); *)
  let env = Pred.make_ml_funs env in
  (* Printf.eprintf "%s\n" *)
  env

let extract_relation_miniml dep ord ind_ref modes =
  let env = extract_relation_common dep ord ind_ref modes in
  (* Before generating the MiniML code, we first extract all the dependences *)
  let _ = if dep then extract_dependencies env.extr_henv else () in

  Minimlgen.gen_miniml env


let relation_extraction_single modes =
  let (_, ind_ref, _, _) = List.hd modes in
  extract_relation_miniml false false [ind_ref] modes

let relation_extraction_single_order modes =
  let (_, ind_ref, _, _) = List.hd modes in
  extract_relation_miniml false true [ind_ref] modes

let relation_extraction modes =
  let ind_refs = List.map (fun (_, ind_ref, _, _) -> ind_ref) modes in
  extract_relation_miniml true false ind_refs modes

let relation_extraction_order modes =
  let ind_refs = List.map (fun (_, ind_ref, _, _) -> ind_ref) modes in
  extract_relation_miniml true true ind_refs modes

let relation_extraction_fixpoint ~pstate modes =
  let ind_refs = List.map (fun (_, ind_ref, _, _) -> ind_ref) modes in
  let env = extract_relation_common false false ind_refs modes in
  let env = build_all_fixfuns env in
  gen_fixpoint pstate env

let relation_extraction_fixpoint_order ~pstate modes =
  let ind_refs = List.map (fun (_, ind_ref, _, _) -> ind_ref) modes in
  let env = extract_relation_common false true ind_refs modes in
  let env = build_all_fixfuns env in
  gen_fixpoint pstate env

(* DEBUG HINT: Displaying a constant idr:
let cstr = constr_of_global (global idr) in
constr_display cstr; let cst = destConst cstr in
let cst_body = Global.lookup_constant cst in
let cstr = match cst_body.Declarations.const_body with 
  Def cs -> Declarations.force cs in
constr_display cstr *)

 
let extraction_print str =
  Printf.printf "%s\n" str
