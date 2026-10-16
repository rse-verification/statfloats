open Cil_types
open Mpfr_utils

type sDom = F | R

type dVar = (Cil_types.logic_var * sDom)
type logOp = Pand | Por | Pimplies
type binOp = Cil_types.binop
type relOp = Cil_types.binop


type dExpr = Cil_types.term_node
type dPred = Cil_types.predicate_node
(*(*Deterministic expr*)
type dExpr = dVar of dVar | DConst of Cil_types.logic_const
              | DBinOp of (binOp dExpr * dExpr * dExpr)
(*Deterministic pred*)
type dPred = DLogOp of (logOp * dPred * dPred) | DNeg of dPred |
              | DRelOp of (relOp * dExpr * dExpr)
*)

(*Probabilistic expr*)
type pExpr =
  | Pr of dPred (* e.g., \mathbb{P}(x > 2.5) *)
  | PBinop of (binOp * pExpr * pExpr)
  | PConst of float

(*Probabilistic pred*)
type pPred =
  | PLogOp of logOp * pPred * pPred
  | PNeg of pPred
  | PBinOp of (binOp * pExpr * pExpr)

type dist =  {
    dvar: Cil_types.term; (*var as term as can be e.g. struct member*)
    dname: string;
    dparams: Cil_types.term list;
}

let get_dist_var {dvar=t;_} = t
let is_uniform {dname=n; _} = (n = "Uniform")
let get_uniform_params {dname="Uniform";dparams=[lo;hi];_} = (lo,hi)

class prob_contract = object (self)
  val mutable probPred : pPred option = None
  val mutable confLevel: float option = None
  val mutable dists : dist list = []

  method get_probPreb () = Option.get probPred
  method get_confLevel () = Option.get confLevel
  method get_dists () = dists

  method set_probPred p = probPred <- Some p
  method set_confLevel c = confLevel <- Some c
  method set_dists d = dists <- d

  method add_dist d = dists <- d::dists


end

                  (*Class specifically for flteq probPreds*)
let abs_fun = { bl_name = "\\fabs"; bl_params = []; bl_profile = ["x",Lreal];
                   bl_type = Some Lreal; bl_labels = []}
let mkTerm ?(loc=unknown_loc) ?(typ=Lreal) tnode  =
  { term_node = tnode;
    term_loc = loc;
    term_type = typ;
    term_name = [] }

(*TODO: Move code here that is now in parse_prob_contract*)
class flteq_contract = object (self)
  inherit prob_contract
  val mutable diff: Cil_types.term option = None
  val mutable e1: Cil_types.term option = None
  val mutable e2: Cil_types.term option = None
  val mutable prob : float option = None

  method get_diff () = Option.get diff
  method get_e1 () = Option.get e1
  method get_e2 () = Option.get e2
  method get_prob () = Option.get prob

  method get_fl_diff () = term_to_fl_const (self#get_diff ())


  method private set_diff d = diff <- Some d
  method private set_e1 e = e1 <- Some e
  method private set_e2 e = e2 <- Some e
  method private set_prob p = prob <- Some p

  method set_prob_and_pred e1 e2 diff pr =
    self#set_e1 e1;
    self#set_e2 e2;
    self#set_diff diff;
    self#set_prob pr;
    let pred' = Prel (Rlt, mkTerm (TBinOp (MinusA, e1, e2)), diff) in (*TODO: SHould be abs also but to lazy to fix now*)
    probPred <- Some (PBinOp (Gt, Pr(pred'), PConst pr));

  method set_prob_and_round_error error_term x tolerance pr =
    self#set_e1 x;
    self#set_e2 x;
    self#set_diff tolerance;
    self#set_prob pr;
    let pred' = Prel (Rle, error_term, tolerance) in
    probPred <- Some (PBinOp (Gt, Pr(pred'), PConst pr))
end
