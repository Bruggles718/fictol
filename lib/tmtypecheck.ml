open Errors
open Types
open Terms
open Compiler_common
open Pretty

type sourcespan = Lexing.position * Lexing.position

let rec tm_free_vars tm =
  match tm with
  | TmVar (x, tag) -> [ x ]
  | TmApp (m, n, tag) -> tm_free_vars m @ tm_free_vars n
  | TmLambda (x, a, m, _, tag) | TmLet(x, a, m, tag) -> tm_free_vars a @ List.filter (( <> ) x) (tm_free_vars m)
  | TmPi (x, a, preds, m, _, tag) -> 
    let ftv_predicates =
        List.concat (List.map ftv_tmpred preds)
      in
    ftv_predicates @ tm_free_vars a @ List.filter (( <> ) x) (tm_free_vars m)
  | TmSeq (t1, t2, tag) -> tm_free_vars t1 @ tm_free_vars t2
  | TmPrim1 (op, body, tag) -> tm_free_vars body
  | TmPrim2 (op, l, r, tag) -> tm_free_vars l @ tm_free_vars r
  | TmIf (cond, thn, els, tag) -> tm_free_vars cond @ tm_free_vars thn @ tm_free_vars els
  | TmGetReference (body, tag) -> tm_free_vars body
  | TmUniverse _ | TmLiteral _ -> []

and ftv_tmpred (p : 'a tmpredicate) : (string list) =
  List.fold_left (fun acc t -> (tm_free_vars t) @ acc) [] p.pred_args
;;

let rec binders tm =
  match tm with
  | TmApp (m, n, tag) -> binders m @ binders n
  | TmLambda (x, a, m, _, tag) | TmLet(x, a, m, tag) -> [x] @ binders a @ (binders m)
  | TmPi (x, a, preds, m,_, tag) -> [x] @ binders a @ (List.concat (List.map binders_tmpred preds)) @ (binders m)
  | TmSeq (t1, t2, tag) -> binders t1 @ binders t2
  | TmPrim1 (op, body, tag) -> binders body
  | TmPrim2 (op, l, r, tag) -> binders l @ binders r
  | TmIf (cond, thn, els, tag) -> binders cond @ binders thn @ binders els
  | TmGetReference (body, tag) -> binders body
  | TmUniverse _ | TmLiteral _ | TmVar _ -> []

and binders_tmpred p =
  List.fold_left (fun acc t -> (binders t) @ acc) [] p.pred_args

let all_vars tm = tm_free_vars tm @ binders tm

let rec freshen (banlist : string list) (base : string) =
  if List.mem base banlist then freshen banlist (base ^ "'") else base



let rec subst x m tm =
  match tm with
  | TmVar (y, tag) when x = y -> m
  | TmApp (m', n, tag) -> TmApp(subst x m m', subst x m n, tag)
  | TmLambda (y, a, n, call_type, tag) when x = y -> TmLambda (y, subst x m a, n, call_type, tag)
  | TmLambda (y, a, n, call_type, tag) when List.mem y (tm_free_vars m) ->
      let banlist = tm_free_vars m @ all_vars n in
      subst x m (rename (freshen banlist y) tm)
  | TmLambda (y, a, n, call_type, tag) -> TmLambda (y, subst x m a, subst x m n, call_type, tag)
  | TmPi (y, a, preds, n, call_type, tag) when x = y -> TmPi (y, subst x m a, List.map (subst_tmpred x m) preds, n, call_type, tag)
  | TmPi (y, a, preds, n, call_type, tag) when List.mem y (tm_free_vars m) ->
      let banlist = tm_free_vars m @ all_vars n in
      subst x m (rename (freshen banlist y) tm)
  | TmPi (y, a, preds, n, call_type, tag) -> TmPi (y, subst x m a, List.map (subst_tmpred x m) preds, subst x m n, call_type, tag)
  | TmLet(y, a, n, tag) when x = y -> TmLet (y, subst x m a, n, tag)
  | TmLet (y, a, n, tag) when List.mem y (tm_free_vars m) ->
      let banlist = tm_free_vars m @ all_vars n in
      subst x m (rename (freshen banlist y) tm)
  | TmLet (y, a, n, tag) -> TmLet (y, subst x m a, subst x m n, tag)
  | TmSeq (t1, t2, tag) -> TmSeq(subst x m t1, subst x m t2, tag)
  | TmPrim1 (op, body, tag) -> TmPrim1(op, subst x m body, tag)
  | TmPrim2 (op, l, r, tag) -> TmPrim2(op, subst x m l, subst x m r, tag)
  | TmIf (cond, thn, els, tag) -> TmIf(subst x m cond, subst x m thn, subst x m els, tag)
  | TmGetReference (body, tag) -> TmGetReference(subst x m body, tag)
  | TmLiteral _ | TmVar _ | TmUniverse _ -> tm

and subst_tmpred x m pred =
  { pred_class=pred.pred_class; pred_args=(List.map (subst x m) pred.pred_args) }

and rename x' binder =
  match binder with
  | TmLambda (x, a, m, call_type, tag) -> TmLambda (x', a, (subst x (TmVar (x',tag)) m), call_type, tag)
  | TmPi (x, a, preds, m, call_type, tag) -> TmPi (x', a, List.map (subst_tmpred x (TmVar(x', tag))) preds, (subst x (TmVar (x',tag)) m), call_type, tag)
  | TmLet (x, a, m, tag) -> TmLet (x', a, (subst x (TmVar (x',tag)) m), tag)
  | _ -> raise (InternalCompilerError("rename term failure: Given non binder"))
  
let rec alpha_eq tm1 tm2 =
  match tm1, tm2 with
  | TmVar(x, _), TmVar(y, _) -> x = y
  | TmApp(a1, b1, _), TmApp(a2, b2, _) -> alpha_eq a1 a2 && alpha_eq b1 b2
  | TmLambda(x1, a1, m1, call_type1, _), TmLambda(x2, a2, m2, call_type2, _) when x1 = x2 ->
    call_type1 = call_type2 && alpha_eq a1 a2 && alpha_eq m1 m2
  | TmLet(x1, a1, m1, _), TmLet(x2, a2, m2, _) when x1 = x2 ->
    alpha_eq a1 a2 && alpha_eq m1 m2
  | TmPi(x1, a1, preds1, m1, call_type1, _), TmPi(x2, a2, preds2, m2, call_type2, _) when x1 = x2 ->
    let eq_preds = (List.map (fun (p1, p2) -> alpha_eq_preds p1 p2) (List.combine preds1 preds2)) in
    let eq_preds_folded = List.fold_left (fun acc result -> result && acc) true eq_preds in
    call_type1 = call_type2 && alpha_eq a1 a2 && eq_preds_folded && alpha_eq m1 m2
  | TmLambda(x1, a1, m1, _, _), TmLambda(x2, a2, m2, _, _)
  | TmLet(x1, a1, m1, _), TmLet(x2, a2, m2, _) ->
    let banlist = all_vars m1 @ all_vars m2 in
    let fresh_x = freshen banlist x1 in
    alpha_eq (rename fresh_x tm1) (rename fresh_x tm2)
  | TmPi(x1, a1, preds1, m1, _, _), TmPi(x2, a2, preds2, m2, _, _) ->
    let banlist = all_vars m1 @ all_vars m2 in
    let fresh_x = freshen banlist x1 in
    alpha_eq (rename fresh_x tm1) (rename fresh_x tm2)
  | TmSeq(t11, t21, _), TmSeq(t12, t22, _) ->
    alpha_eq t11 t12 && alpha_eq t21 t22
  | TmPrim1(op1, body1, _), TmPrim1(op2, body2, _) ->
    op1 = op2 && alpha_eq body1 body2
  | TmPrim2(op1, l1, r1, _), TmPrim2(op2, l2, r2, _) ->
    op1 = op2 && alpha_eq l1 l2 && alpha_eq r1 r2
  | TmIf(cond1, thn1, els1, _), TmIf(cond2, thn2, els2, _) ->
    alpha_eq cond1 cond2 && alpha_eq thn1 thn2 && alpha_eq els1 els2
  | TmLiteral(l1, _), TmLiteral(l2, _) ->
    l1 = l2
  | TmGetReference(body1, _), TmGetReference(body2, _) ->
    alpha_eq body1 body2
  | TmUniverse(lvl1), TmUniverse(lvl2) -> lvl1 = lvl2
  | _, _ -> false

and alpha_eq_preds pred1 pred2 =
  let terms_eq = List.map (fun (t1, t2) -> alpha_eq t1 t2) (List.combine pred1.pred_args pred2.pred_args) in
  let all_terms_eq = List.fold_left (fun acc result -> result && acc) true terms_eq in
  pred1.pred_class = pred2.pred_class && all_terms_eq

let rec eval tm =
  match tm with
  | TmApp (m, n, tag) -> eval_app (eval m) (eval n) tag
  | TmLambda (x, a, m, call_type, tag) -> TmLambda (x, eval a, eval m, call_type, tag)
  | TmPi (x, a, preds, m, call_type, tag) -> TmPi (x, eval a, List.map eval_pred preds, eval m, call_type, tag)
  | TmLet (x, a, m, tag) -> TmLet (x, eval a, eval m, tag)
  | TmSeq (t1, t2, tag) -> TmSeq(eval t1, eval t2, tag)
  | TmPrim1 (op, body, tag) -> TmPrim1(op, eval body, tag)
  | TmPrim2 (op, l, r, tag) -> TmPrim2(op, eval l, eval r, tag)
  | TmIf (cond, thn, els, tag) -> TmIf(eval cond, eval thn, eval els, tag)
  | TmGetReference (body, tag) -> TmGetReference (eval body, tag)
  | TmLiteral _ | TmVar _ | TmUniverse _ -> tm

and eval_pred pred =
  { pred_class = pred.pred_class; pred_args = List.map eval pred.pred_args }

and eval_app m n tag =
  match m with
  | TmLambda(x, a, m, call_type, tag) -> eval (subst x n m)
  | _ -> TmApp (m, n, tag)


type 'a context = (string * 'a term) list

type span_term_pair = (sourcespan * (sourcespan term))

let rec infer_type_term (ctx) (tm) : (sourcespan term * sourcespan tmwanted list * span_term_pair term) =
  match tm with
  | TmUniverse lvl -> 
    let typ = TmUniverse (lvl + 1) in
    (typ, [], TmUniverse(lvl))
  | TmLiteral (LitString s, loc) ->
    let typ = TmApp(TmApp(TmVar("ref", dummy_span), TmVar("char", dummy_span), dummy_span), TmVar("Static", dummy_span), dummy_span) in
    (typ, [], TmLiteral(LitString s, (loc, typ)))
  | TmLiteral (LitChar c, loc) ->
    let typ = TmVar("char", dummy_span) in
    (typ, [], TmLiteral(LitChar c, (loc, typ)))
  | TmLiteral (LitBool b, loc) ->
    let typ = TmVar("bool", dummy_span) in
    (typ, [], TmLiteral(LitBool b, (loc, typ)))
  | TmLiteral (LitInt (n, suffix), loc) ->
    let inttyp = (
      match suffix with
      | IntSuffix width -> Int width
      | UIntSuffix width -> UInt width
    ) in
    let typstr = string_of_tykind inttyp in
    let typ = TmVar(typstr, dummy_span) in
    (typ, [], TmLiteral(LitInt(n, suffix), (loc, typ)))
  | TmVar (x, loc) -> 
    let typ = eval (List.assoc x ctx) in
    let (typ_typ, typ_wanteds, new_typ) = infer_type_term ctx typ in
    (typ, typ_wanteds, (TmVar(x, (loc, typ))))
  | TmLambda (x, a, m, call_type, loc) ->
    let (a_typ, a_wanteds, new_a) = infer_type_term ctx a in
    let (m_typ, m_wanteds, new_m) = infer_type_term ((x, a) :: ctx) m in
    let lam_typ = TmPi(x, a, [], m_typ, call_type, loc) in
    let _ = infer_type_term ctx lam_typ in
    let evaluated_lam_typ = eval lam_typ in
    (evaluated_lam_typ, a_wanteds @ m_wanteds, TmLambda(x, new_a, new_m, call_type, (loc, evaluated_lam_typ)))
  | TmPi (x, a, preds, m, call_type, loc) ->
    let (_, a_wanteds, new_a) = infer_universe ctx a in
    let (pred_wanteds, new_preds) = List.split (List.map (infer_tmpred ctx) preds) in
    let (m_typ, m_wanteds, new_m) = infer_universe ctx m in
    (m_typ, a_wanteds @ List.concat pred_wanteds @ m_wanteds, TmPi(x, new_a, new_preds, new_m, call_type, (loc, m_typ)))
  | TmLet (x, a, m, loc) ->
    let (a_typ, a_wanteds, new_a) = infer_type_term ctx a in
    let (m_typ, m_wanteds, new_m) = infer_type_term ((x, a) :: ctx) m in
    (m_typ, a_wanteds @ m_wanteds, TmLet(x, new_a, new_m, (loc, m_typ)))
  | TmSeq (t1, t2, loc) ->
    infer_type_term ctx t2
  (* | TmPrim1 (op, body, loc) -> *)
    

and infer_tmpred ctx pred =
  let (arg_typs, wanteds, new_args) = 
    List.fold_right (fun (arg_typ, arg_wanteds, new_arg) (res_types, res_wanteds, res_args)  ->
      (arg_typ :: res_types, arg_wanteds @ res_wanteds, new_arg :: res_args)) (List.map (infer_type_term ctx) pred.pred_args) ([], [], []) in
  (wanteds, {pred_class = pred.pred_class; pred_args = new_args})



and infer_universe ctx t =
  match infer_type_term ctx t with
  | (TmUniverse(lvl), twanteds, new_t) -> (TmUniverse(lvl), twanteds, new_t)
  | _ -> raise (InternalCompilerError("infer universe failure: inferred non universe"))
    

    