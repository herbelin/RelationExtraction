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
(*  Copyright 2012 CNAM-ENSIIE                                              *)
(*                 Catherine Dubois <dubois@ensiie.fr>                      *)
(*                 David Delahaye <david.delahaye@cnam.fr>                  *)
(*                 Pierre-Nicolas Tollitte <tollitte@ensiie.fr>             *)
(****************************************************************************)


open Constr
open Names
open Util
open Declarations
open EConstr

open Pred
open Proof_scheme
open Coq_stuff

let debug_print_goals = false
let debug_print_tacs = false

(****************)
(* Proofs stuff *)
(****************)

(* A pattern to search in the proof goal. *)
type 'a goal_finder = Id.t option -> EConstr.constr -> 'a option

(* goal_iterator : 
     bool -> bool -> bool -> 'a goal_finder -> evar_map -> econstr -> int -> (int * 'a)
   goal_iterator browses the goal and try to identify one part of the product
   with f and return the f result and the position of the product part in the
   goal.
   The three boolean flags indicate if goal_iterator must call f on foralls,
   letins, and premisses.
*)
(* TODO: check that forall term = type ? *)
let goal_iterator fa li pr f sigma goal start =
  let rec rec_it i term = match EConstr.kind sigma term with
    | Prod ({Context.binder_name = Name n}, c, c_next) when (fa || pr) && i >= start && 
        Id.to_string n <> "H" (* H is rec hyp name *) ->
      begin match f (Some n) sigma c with
      | Some res -> i, res
      | None -> rec_it (i+1) c_next end
    | Prod ({Context.binder_name = Anonymous}, c, c_next) when pr && i >= start -> 
      begin match f None sigma c with
      | Some res -> i, res
      | None -> rec_it (i+1) c_next end
    | Prod (_, _, c_next) -> rec_it (i+1) c_next
    | LetIn ({Context.binder_name = Name n}, c, _, c_next) when li && i >= start -> 
      begin match f (Some n) sigma c with
      | Some res -> i, res
      | None -> rec_it (i+1) c_next end
    | LetIn (_, _, _, c_next) -> rec_it (i+1) c_next
    | _ -> raise Not_found in
  rec_it 1 goal

(* Hypothesis number in a goal. *)
let get_hyp_num sigma goal =
  let rec rec_ghn i term = match EConstr.kind sigma term with
    | Prod (_, _, c_next) -> rec_ghn (i+1) c_next
    | LetIn (_, _, _, c_next) -> rec_ghn (i+1) c_next
    | _ -> i in
  rec_ghn 0 goal

type hyp_finder = constr option -> Evd.evar_map -> EConstr.constr -> EConstr.constr

(* How to find a coq constr. It is either the constr itself or a place to find
   it in an hypothesis. *)
type coq_constr_loc =
  | CoqConstr of constr
  | LocInHyp of string * hyp_finder

(* A coq tactic. *)
type tac_atom =
  | INTRO of string
  | INTROS of string list
  | INTROSUNTIL of int (* intros until i *)
  | REVERT of string list
  | SYMMETRY of string
  | SUBST of string
  | APPLY of string
  | APPLYIN of string * string
  | EAPPLY of string
  | APPLYPROP of string (* spec constr name *)
  | APPLYPROPIN of string (* spec constr name *) * string
  | APPLYIND of string (* fun name *)
  | CHANGEV of string * string * coq_constr_loc 
    (* CHANGEV (h, v, c) : change v with c if h is v = c *)
  | CHANGEC of string * coq_constr_loc * coq_constr_loc 
    (* CHANGEC (h, cp, c) : change cp with c if h is cp = c *)
  | ASSERTEQUAL of string * string * coq_constr_loc * types
    (* ASSERTEQUAL (h, v, c, t) : assert (h : v = c) if c has type t *)
  | AUTO

(* Pretty printers. *)

let rec concat_list l sep = match l with
  | [] -> ""
  | [a] -> a
  | a::tl -> a ^ sep ^ (concat_list tl sep)

let pp_coq_constr_loc ccl = match ccl with
  | CoqConstr _ -> "[constr]"
  | LocInHyp (h, _) -> "[in hyp: " ^ h ^ "]"

let pp_tac_atom ta = match ta with
  | INTRO s -> "INTRO " ^ s
  | INTROS sl -> "INTROS " ^ concat_list sl " "
  | INTROSUNTIL i -> "INTROSUNTIL" ^ string_of_int i
  | REVERT sl -> "REVERT " ^ concat_list sl " "
  | SYMMETRY s -> "SYMMETRY " ^ s
  | SUBST s -> "SUBST " ^ s
  | APPLY s -> "APPLY " ^ s
  | APPLYIN (s, h) -> "APPLY " ^ s ^ " IN " ^ h
  | EAPPLY s -> "EAPPLY " ^ s
  | APPLYPROP s -> "APPLYPROP " ^ s
  | APPLYPROPIN (s, h) -> "APPLYPROP " ^ s ^ " IN " ^ h
  | APPLYIND s -> "APPLYIND " ^ s
  | CHANGEV (h, v, c) -> 
    "CHANGEV " ^ h ^ ": " ^ v ^ " -> " ^ pp_coq_constr_loc c
  | CHANGEC (h, c1, c2) ->  
    "CHANGEC " ^ h ^ ": " ^ pp_coq_constr_loc c1 ^ " -> " ^ pp_coq_constr_loc c2
  | ASSERTEQUAL (h, v, c, _) -> 
    "ASSERTEQUAL " ^ h ^ ": " ^ v ^ " = " ^ pp_coq_constr_loc c
  | AUTO -> "AUTO"

let pp_tac_atom_list tal = concat_list (List.map pp_tac_atom tal) " ; "

(* Tactics, to be applied at each step of the proof. *)
type tac_info = {
  ti_before_intros : tac_atom list;
  ti_after_intros : tac_atom list;
  ti_normal : tac_atom list;
  ti_after_prop : tac_atom list;
}

let pp_tac_info ti =
  "BI: " ^ pp_tac_atom_list ti.ti_before_intros ^ "\n" ^
  "AI: " ^ pp_tac_atom_list ti.ti_after_intros ^ "\n" ^
  "NN: " ^ pp_tac_atom_list ti.ti_normal ^ "\n" ^
  "AP: " ^ pp_tac_atom_list ti.ti_after_prop ^ "\n"

(* A set of tactics to be applied in order to prove a subgoal. *)
type tacts = 
  | Prop_tacs of tac_info list * string
  | Tac_list of tac_atom list

let pp_tacts tacts = match tacts with
  | Prop_tacs (til, s) -> "Prop tacs (" ^ s ^ "):\n" ^
    concat_list (List.map pp_tac_info til) "\n"
  | Tac_list tal -> "List tacs:\n" ^ pp_tac_atom_list tal

(* The result returned by a prover. *)
type prover_result = {
  pres_intros : string list;
  pres_tacts : tacts;
}

let pp_prover_result pr =
  "Prover result:\nIntros: " ^ concat_list pr.pres_intros " " ^
  "\n" ^ pp_tacts pr.pres_tacts

(* The type of a prover. *)
type scheme_prover = {
  prov_intro : 
    ((htyp, henv) extract_env * ident) -> (htyp fix_term) proof_scheme -> tacts;
  prov_branch : ((htyp, henv) extract_env * ident) -> 
    (htyp fix_term) ps_branch -> Evd.evar_map -> EConstr.constr -> prover_result;
  prov_concl : 
    ((htyp, henv) extract_env * ident) -> (htyp fix_term) proof_scheme -> tacts;
}

(* Coq useful functions. *)

let get_goal =
  let goal = ref (EConstr.mkRel 1) in
  let tac = Proofview.Goal.enter ( fun goal_s ->
    goal := Proofview.Goal.concl goal_s; Tacticals.New.tclIDTAC) in
  fun pstate -> (ignore (Pfedit.by tac pstate); !goal)

(* return type : named_declaration list = 
                   (identifier * constr option * types) list *)
let get_hyps_in f =
  Proofview.Goal.enter (fun goal_s -> f (EConstr.named_context (Proofview.Goal.env goal_s)))

let get_hyps =
  let hyps = ref ([]) in
  let tac = get_hyps_in (fun thehyps -> hyps := thehyps; Tacticals.New.tclIDTAC) in
  fun pstate -> (ignore (Pfedit.by tac pstate); !hyps)

let get_evarmap_in f =
  Proofview.Goal.enter (fun goal_s -> f (Proofview.Goal.sigma goal_s))

let get_evarmap =
  let evm = ref (Evd.empty) in
  let tac = get_evarmap_in (fun sigma -> evm := sigma; Tacticals.New.tclIDTAC ) in
  fun pstate -> (ignore (Pfedit.by tac pstate); !evm)

let pat_from_constr pstate constr =
  let evm = get_evarmap pstate in
  Patternops.pattern_of_constr (Global.env()) evm constr

let get_proof_from_tac (env, id) lemma prover branch =
  let term = Lemmas.pf_fold get_goal lemma in
  let sigma = Lemmas.pf_fold get_evarmap lemma in
  prover (env, id) branch sigma term

let rec get_hyp_by_name hn hyps = match hyps with
  | [] -> raise Not_found
  | decl::hyps_tl -> let (id, topt, t) = Context.Named.Declaration.to_tuple decl in
    if Id.to_string (Context.binder_name id) = hn then topt, t else
    get_hyp_by_name hn hyps_tl

let constr_of_constr_loc_in cstr_loc f =
  match cstr_loc with
  | CoqConstr cstr -> f cstr
  | LocInHyp (hn, hyp_finder) ->
    get_hyps_in (fun hyps -> let h_cstr_opt, h_cstr = get_hyp_by_name hn hyps in
    get_evarmap_in (fun sigma -> f (hyp_finder h_cstr_opt sigma h_cstr)))

let constr_of_constr_loc pstate cstr_loc = match cstr_loc with
  | CoqConstr cstr -> cstr
  | LocInHyp (hn, hyp_finder) -> let h_cstr_opt, h_cstr = 
    get_hyp_by_name hn (get_hyps pstate) in
    hyp_finder h_cstr_opt (get_evarmap pstate) h_cstr

let intros_until_n_wored i = Tactics.intros_until (Tactypes.AnonHyp i) (* TODO: is with red ok *)
let symmetry_in id = Tactics.intros_symmetry (Locusops.onHyp id)
let replace_in hid cstr_pat cstr = Equality.replace_in_clause_maybe_by cstr_pat cstr (Locusops.onHyp hid) None

let print_subgoals = Lemmas.pf_fold (fun lemma -> Feedback.msg_notice (Printer.pr_open_subgoals ~proof:(Proof_global.get_proof lemma)))

(* Makes real Coq tactics and applies them. *)
let rec build_tac_atom ta = match ta with
  | INTRO str -> 
    if debug_print_tacs then Printf.eprintf "intro %s.\n" str
    else ();
    Tactics.intro_using (Id.of_string str)
  | INTROS strl -> 
    if debug_print_tacs then Printf.eprintf "intros %s.\n" (concat_list strl " ")
    else ();
    Tactics.intros_using (List.map Id.of_string strl)
  | INTROSUNTIL i -> 
    if debug_print_tacs then Printf.eprintf "intros until %d.\n" i
    else ();
    if i = 0 then
      Tactics.intros_patterns false [CAst.make (Tactypes.IntroForthcoming true)]
    else
      intros_until_n_wored i
  | REVERT (strl) -> 
    if debug_print_tacs && List.length strl > 0 then 
      Printf.eprintf "revert %s.\n" (concat_list strl " ")
    else ();
    Tactics.revert (List.map Id.of_string strl)
  | SYMMETRY str -> 
    if debug_print_tacs then Printf.eprintf "symmetry in %s.\n" str
    else ();
    symmetry_in (Id.of_string str)
  | SUBST str -> 
    if debug_print_tacs then Printf.eprintf "subst %s.\n" str
    else ();
    Equality.subst [Id.of_string str]
  | APPLY str -> let cstr = find_coq_constr_s str in 
    if debug_print_tacs then Printf.eprintf "apply %s.\n" str
    else ();
    Tactics.apply (EConstr.of_constr cstr)
  | APPLYIN (str, h) -> let cstr = find_coq_constr_s str in 
    if debug_print_tacs then Printf.eprintf "apply %s in %s.\n" str h
    else ();
    Tactics.apply_in true false (Id.of_string h) [None,CAst.make (EConstr.of_constr cstr,Tactypes.NoBindings)] None
  | EAPPLY str -> let cstr = find_coq_constr_s str in 
    if debug_print_tacs then Printf.eprintf "eapply %s.\n" str
    else ();
    Tactics.eapply (EConstr.of_constr cstr)
  | APPLYPROP str -> let cstr = find_coq_constr_s str in 
    if debug_print_tacs then Printf.eprintf "apply %s; try assumption.\n" str
    else ();
    Tacticals.New.tclTHEN (Tactics.apply (EConstr.of_constr cstr))
      (Tacticals.New.tclTRY Tactics.assumption)
  | APPLYPROPIN (str, h) -> let cstr = find_coq_constr_s str in
    if debug_print_tacs then 
      Printf.eprintf "apply %s in %s; try assumption.\n" str h
    else ();
    Tacticals.New.tclTHEN (Tactics.apply_in true false (Id.of_string h) [None,CAst.make (EConstr.of_constr cstr,Tactypes.NoBindings)] None)
      (Tacticals.New.tclTRY Tactics.assumption)
  | APPLYIND str -> let ind_scheme = str ^ "_ind" in
    build_tac_atom (APPLY ind_scheme)
  | CHANGEC (h, cstr_pat, cloc) ->
    constr_of_constr_loc_in cstr_pat (fun cstr_pat ->
    constr_of_constr_loc_in cloc (fun cstr ->
    get_hyps_in (fun hyps ->
    let hyps_ids = List.map Context.Named.Declaration.get_id hyps in
    let orig_hyp_id = Id.of_string h in
    let tac = Equality.replace cstr_pat cstr in
    let t = List.fold_right (fun hid tac -> 
      if orig_hyp_id = hid then tac else
        Tacticals.New.tclTHEN (replace_in hid cstr_pat cstr) tac
    ) hyps_ids tac in
    let s = "replace (" ^ (pp_coq_constr cstr_pat) ^ ") with (" ^
          (pp_coq_constr cstr) ^ ") in *" in
    if debug_print_tacs then Printf.eprintf "%s.\n" s
    else ();
    t)))
  | CHANGEV (h, v, cloc) -> 
    let cstr_pat = mkVar (Id.of_string v) in
    build_tac_atom (CHANGEC (h, CoqConstr cstr_pat, cloc))
  | ASSERTEQUAL (h, v, cloc, t) -> 
    constr_of_constr_loc_in cloc (fun cstr ->
    let eq = find_coq_constr_s "eq" in
    let var = mkVar (Id.of_string v) in
    let assert_cstr = mkApp (EConstr.of_constr eq, [|t; var; cstr|]) in
    if debug_print_tacs then 
      Printf.eprintf "assert (%s : %s).\n" h (pp_coq_constr assert_cstr)
    else ();
    Tactics.assert_before (Name (Id.of_string h)) assert_cstr)
  | AUTO -> 
    if debug_print_tacs then Printf.eprintf "auto.\n"
    else ();
    Auto.default_auto

(* Proves a goal, with a given prover. *)
let make_proof (env, id) lemma prover ps =
  if debug_print_tacs then
    let (fixfun, _) = extr_get_fixfun env id in
    let fn = string_of_ident fixfun.fixfun_name in
    let in_s = concat_list (List.map string_of_ident fixfun.fixfun_args) " " in
    let lem = "Lemma " ^ fn ^ "_correct_printed : forall " ^ in_s ^ " po, " ^
              fn ^ " " ^ in_s ^ " = po -> " ^ string_of_ident id ^ " " ^ in_s ^
              " po." in
    Printf.eprintf "\n\n\n%s\nProof.\n" lem
  else ();
  let intro = prover.prov_intro (env, id) ps in
  let concl = prover.prov_concl (env, id) ps in
  let prover = prover.prov_branch in
  let rec apply_tacs lemma tacs = match tacs with
    | Prop_tacs _ -> assert false
    | Tac_list (t::tl) -> 
      begin if debug_print_goals then 
        begin Printf.printf "\n\n%s\n\n" (pp_tac_atom t); 
        print_subgoals lemma end
      else () end;
      let (lemma,_) = Lemmas.by (build_tac_atom t) lemma in apply_tacs lemma (Tac_list tl)
    | Tac_list [] -> lemma in
  let lemma = apply_tacs lemma intro in
  let lemma = List.fold_left (fun lemma branch ->
    if debug_print_goals then print_subgoals lemma
    else ();
    let proof = get_proof_from_tac (env, id) lemma prover branch in
    let intros_tac = Tac_list [INTROS proof.pres_intros] in
    match proof.pres_tacts with
      | Tac_list _ -> let lemma = apply_tacs lemma intros_tac in
        apply_tacs lemma proof.pres_tacts
      | Prop_tacs (til, prop) -> let bint, aint, norm, apro = 
          List.fold_right (fun ti (bi, ai, n, ap) -> 
            ti.ti_before_intros::bi, ti.ti_after_intros::ai, 
            ti.ti_normal::n, ti.ti_after_prop::ap) til ([], [], [], []) in
        let bi_tac = Tac_list (List.flatten bint) in
        let ai_tac = Tac_list (List.flatten aint) in
        let n_tac = Tac_list (List.flatten norm) in
        let ap_tac = Tac_list (List.flatten apro) in
        let prop_tac = Tac_list [APPLYPROP prop] in
        let lemma = apply_tacs lemma bi_tac in
        let lemma = apply_tacs lemma intros_tac in
        let lemma = apply_tacs lemma ai_tac in
        let lemma = apply_tacs lemma n_tac in
        let lemma = apply_tacs lemma prop_tac in
        apply_tacs lemma ap_tac
  ) lemma ps.scheme_branches in
  let lemma = apply_tacs lemma concl in
  if debug_print_tacs then
    Printf.eprintf "Qed.\n"
  else ();
  lemma


(****************)
(* Goal finders *)
(****************)

(* Utils *)

let isEq sigma constr =
  if EConstr.isInd sigma constr then
    let ind,_ = EConstr.destInd sigma constr in
    let _,oid = Inductive.lookup_mind_specif (Global.env ()) ind in
    (Id.to_string oid.mind_typename = "eq")
  else false

(* Goal finders *)

let find_eq_get_sides = fun _ sigma constr -> match EConstr.kind sigma constr with
  | App (f, [|_;c1;c2|]) when isEq sigma f -> Some (c1, c2)
  | _ -> None

let find_let_in_cstr v = fun n _ cstr -> match n with
  | Some n -> if v = Id.to_string n then Some cstr else None
  | None -> None

let find_fa_name = fun n _ _ -> match n with
  | Some n -> Some (Id.to_string n)
  | None -> None


(***************)
(* Hyp finders *)
(***************)

let hyp_whole_hyp _ _ c = c

let hyp_eq_right _ sigma c = match EConstr.kind sigma c with
  | App (f, [|_;_;c|]) when isEq sigma f -> c
  | _ -> raise Not_found

let hyp_eq_left _ sigma c = match EConstr.kind sigma c with
  | App (f, [|_;c;_|]) when isEq sigma f -> c
  | _ -> raise Not_found

let hyp_def c _ _ = match c with | Some c -> c | _ -> raise Not_found

(***********)
(* Provers *)
(***********)

let mk_ti_bi tal = {
  ti_before_intros = tal;
  ti_after_intros = [];
  ti_normal = [];
  ti_after_prop = [];
}
let mk_ti_ai tal = {
  ti_before_intros = [];
  ti_after_intros = tal;
  ti_normal = [];
  ti_after_prop = [];
}
let mk_ti_n tal = {
  ti_before_intros = [];
  ti_after_intros = [];
  ti_normal = tal;
  ti_after_prop = [];
}
let mk_ti_ap tal = {
  ti_before_intros = [];
  ti_after_intros = [];
  ti_normal = [];
  ti_after_prop = tal;
}
let mk_ti_ai_n tal1 tal2 = {
  ti_before_intros = [];
  ti_after_intros = tal1;
  ti_normal = tal2;
  ti_after_prop = [];
}

(*********************************************************)
(*                     SIMPLE PROVER                     *)
(* - only partial mode                                   *)
(* - only complete specifications                        *)
(* - no equalities, no linearization,                    *)
(*   no logical connectors                               *)
(*********************************************************)

let simple_pc_intro (env, id) _ = 
  let f_name = string_of_ident (fst (extr_get_fixfun env id)).fixfun_name in
  Tac_list [
    (* intros predicate arguments *)
    INTROSUNTIL 0;
    (* intro H (lemma premisse) *)
    INTRO "H";
    (* rewrite H (or subst H or change right with left) *)
    SUBST "po";
    (* apply ind scheme *)
    APPLYIND f_name
  ]

let simple_pc_concl _ _ = Tac_list []

let list_pos l e =
  let rec rec_pos l i = match l with
    | [] -> raise Not_found
    | e'::tl -> if e = e' then i else rec_pos tl (i+1) in
  rec_pos l 0

let rec get_pmterm_name_order pm = match pm with
  | PMTerm (_, Some n) -> [n]
  | PMNot (pm, _) -> get_pmterm_name_order pm
  | PMOr (pml, _) -> List.flatten (List.map get_pmterm_name_order pml)
  | PMAnd (pml, _) -> List.flatten (List.map get_pmterm_name_order pml)
  | PMChoice (pml, _) -> assert false 
                         (* not imp yet, TODO: find wich one is used. *)
  | _ -> []

let get_init_prem_order (env, id) prop_name = 
  let spec = extr_get_spec env id in
  let prop = List.find (fun prop -> match prop.prop_name with 
    | Some pn -> pn = prop_name 
    | None -> false) spec.spec_props in
  List.flatten (List.map get_pmterm_name_order prop.prop_prems)
  

let simple_pc_branch (env, id) branch sigma goal =
  let fun_name = string_of_ident (fst (extr_get_fixfun env id)).fixfun_name in
  let prop_name = match branch.psb_prop_name with Some n -> n 
    | _ -> assert false in
  let (hname_index, til, _, _, recvars) = 
    List.fold_left (fun (hname_index, til, pmn, last_i, recvars) (at, _) -> 
    let dep_pred, pmn = match at with 
      | (LetVar (_, (t, _), po) | CaseConstr ((t, _), _, _, po)) -> 
      let n = po.po_prem_name in if n = "" then None, pmn else
        begin match pmn with | None ->
         begin match t with
           | FixFun(f, _) -> let f = string_of_ident f in
             if f = fun_name then None, Some n
             else Some f, Some n
           | _ -> None, Some n
         end
        | Some pmn when n <> pmn -> 
         begin match t with
           | FixFun(f, _) -> let f = string_of_ident f in
             if f = fun_name then None, Some n
             else Some f, Some n
           | _ -> None, Some n
         end
        | _ -> None, pmn
        end
      | _ -> None, pmn in
    if dep_pred <> None then 
      let dep_pred = match dep_pred with Some n -> n | _ -> assert false in
      let hrec = fresh_string_id "HREC_" () in
      let i, tacs, hn, rv = match at with
        | LetVar (pi, (_, (_, Some t)), _) -> 
          let v = pi.pi_func_name in
          let i, _ = goal_iterator false true false 
                          (find_let_in_cstr v) sigma goal (last_i+1) in
          let hn = (*fresh_string_id "HLREC_" () in *) v in
          i, [ASSERTEQUAL (hrec, v, LocInHyp (hn, hyp_def), EConstr.of_constr t); AUTO;
              SYMMETRY hrec], hn, [v,hrec]
        | CaseConstr (_, cstr_name, pil, _) ->
          let i, (_, _) = goal_iterator false false true 
                              find_eq_get_sides sigma goal (last_i+1) in
          i, [], hrec, []
        | _ -> assert false (* TODO? *) in

      let ti = mk_ti_n (tacs@[APPLYPROPIN (dep_pred ^ "_correct", hrec)]) in
      ((i, hn)::hname_index, ti::til, pmn, i, recvars@rv)
    else match at with
      | LetVar (pi, (_, (_, Some t)), _) 
      | LetDum (pi, (_, (_, Some t))) -> 
        let v = pi.pi_func_name in
        let i, _ = goal_iterator false true false 
                          (find_let_in_cstr v) sigma goal (last_i+1) in
        let hname = (*fresh_string_id "HLV_" ()*) v in
        let eqhname = hname ^ "EQ" in
        let ti = mk_ti_ai_n 
                  [ASSERTEQUAL (eqhname, v, LocInHyp (hname, hyp_def), EConstr.of_constr t); AUTO]
                  [CHANGEV (eqhname, v, LocInHyp (eqhname, hyp_eq_right))] in
        ((i, hname)::hname_index, til@[ti], pmn, i, recvars)
      | CaseConstr (mt, cstr_name, pil, _) -> 
        let i, (c1, _) = goal_iterator false false true 
                                        find_eq_get_sides sigma goal (last_i+1) in
        let hname = fresh_string_id "HCC_" () in
        let ti = mk_ti_n [CHANGEC (hname, LocInHyp (hname, hyp_eq_left), 
                                   LocInHyp (hname, hyp_eq_right))] in
        ((i, hname)::hname_index, til@[ti], pmn, i, recvars)
      | CaseDum _ -> 
        let i, _ = goal_iterator false false true 
                                        find_eq_get_sides sigma goal (last_i+1) in
        let hname = fresh_string_id "HCD_" () in
        ((i, hname)::hname_index, til, pmn, i, recvars)
(* old code for LetDums, they are now processed as LetVars... *)
(*      | LetDum (pi, _) -> 
        let v = pi.pi_func_name in
        let i, _ = goal_iterator false true false 
                          (find_let_in_cstr v) sigma goal (last_i+1) in
        let hname = fresh_string_id "HLD_" () in
        ((i, hname)::hname_index, til, pmn, i, recvars) *)
      | _ -> (hname_index, til, pmn, last_i, recvars)
  ) ([], [], None, 0, []) branch.psb_branch in
  let nb_h = get_hyp_num sigma goal in
  let hnames, p_h = let rec mk_hnames hnames p_h nb_h = 
   if nb_h = 0 then hnames, p_h else
    let hn, p_h = try List.assoc nb_h hname_index, p_h
        with Not_found -> try let i, n = 
            goal_iterator true false false find_fa_name sigma goal nb_h in
(*old*)(*          if i = nb_h then n, p_h*)
(* modified for proof printing. TODO: find a solution to keep real names? *)
(*new*)          if i = nb_h then fresh_string_id "na_" (), p_h
          else raise Not_found
        with Not_found -> let n = fresh_string_id "HREC_" () in n, n::p_h in
    (mk_hnames (hn::hnames) p_h (nb_h-1)) in mk_hnames [] [] nb_h in
    (* new p_h version *)
    let p_h = List.filter (fun hn -> try String.sub hn 0 5 = "HREC_" || 
                           List.mem_assoc hn recvars with _ -> false) hnames in
    let p_h = List.map (fun hn -> if List.mem_assoc hn recvars then 
                                     List.assoc hn recvars else hn) p_h in
    let get_branch_prem_order atl = List.fold_right (fun (at, _) (pml, ono) -> 
        let hno = match at with
          | LetVar (_, _, po) -> let n = po.po_prem_name in 
                                 if n = "" then None else Some n
          | CaseConstr (_, _, _, po) -> let n = po.po_prem_name in 
                                        if n = "" then None else Some n
          | _ -> None in
        match hno with
          | Some hn -> if ono = hno then (pml, ono) else (hn::pml, hno)
          | None -> (pml, ono)
    ) atl ([], None) in
    let premisse_reorder p_h =
      let prop_name = 
        match branch.psb_prop_name with Some n -> n | _ -> assert false in
      let init_order = 
        get_init_prem_order (env, id) (ident_of_string prop_name) in
      let init_order = List.map string_of_ident init_order in
      let branch_order, _ = get_branch_prem_order branch.psb_branch in
      let rec order_prem pml init branch = match init with 
        | [] -> []
        | i::init -> (List.nth pml (list_pos branch i))::
                                      (order_prem pml init branch)
      in
(*TODO: find all the HRECs !*)
      order_prem p_h init_order branch_order
    in
    let p_h = premisse_reorder p_h in
    let ti_revert_rec = mk_ti_n [REVERT (List.rev p_h)] in
  { pres_intros = hnames;
    pres_tacts = Prop_tacs (til@[ti_revert_rec], prop_name);
  }

let simple_pc = {
  prov_intro = simple_pc_intro;
  prov_branch = simple_pc_branch;
  prov_concl = simple_pc_concl;
}
