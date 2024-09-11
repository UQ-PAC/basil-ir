(*Generated by Lem from test.lem.*)


open Lem_bool
open Lem_num
open Lem_list
open Lem_set
open Lem_set_extra
open Lem_map
open Lem_map_extra
open Lem_basic_classes
open Lem_maybe
open Lem_assert_extra

type btype = 
  BitvecType of int
  | BoolType

type bVOp = 
  BVADD
  | BVAND
  | BVOR
  | BVXOR
  | BVSDIV
  | BVUDIV
  | BVSREM
  | BVUREM
  | BVSMOD
  | BVMUL
  | BVASHR
  | BVLSHR
  | BVSHL

type expr = Bvexpr | Boolexpr

type bvexpr = 
  | BVConstant of int * int
  | BinExpr of bVOp * int * bvexpr * bvexpr
  | BVNot of int * bvexpr
  | BVNeg of int * bvexpr
  | BVVar of int * string 
  | Extend of int *  bvexpr 
  | BVFApply of string * expr list * int


type boolexpr = 
  BoolConstant of bool
  | BVCOMP of bvexpr * bvexpr
  | BVULT of bvexpr * bvexpr
  | BVSLT of bvexpr * bvexpr
  | BVEQ of bvexpr * bvexpr
  | BoolEQ of boolexpr * boolexpr
  | BoolAND of boolexpr * boolexpr
  | BoolOR of boolexpr * boolexpr
  | BoolNOT of boolexpr
  | BoolVar of string 
  | BoolFApply of string * expr list

let evalbool (b:boolexpr) : bool=  ((match b with
  BoolConstant b -> b
  | BVCOMP( e1, e2) -> unsafe_structural_inequality e1 e2
  | _ -> false
  ))

type ident = string

type endian = 
  LittleEndian
  | BigEndian

type stmt = 
  | Decl of btype
  | BoolDefAssign of ident * boolexpr
  | BVDefAssign of ident * int * bvexpr
  | Store of ident * ident * bvexpr * bvexpr
  | Load of ident * ident * bvexpr * int
  | Call of ident * expr list
  | PureCallAssign of ident * ident * expr list

type blockterm = 
  Goto of ident list 
  | Stop
  | Unreachable

type block = { 
  block_label: ident;
  stmts: stmt list;
  terminator: blockterm;
}

type proc = {
  proc_label: ident;
  entry_block: ident;
  blocks: (ident, block) Pmap.map
}



let outgoing (b: blockterm) : ident list=  ((match b with
  | Goto is -> is
  | _ -> []
))

let incoming (p: proc) : (ident, ( ident Pset.set)) Pmap.map=
   (let outgoing1 = (Pset.map (pairCompare compare (Pset.compare_by compare)) (fun a -> (a, (Pset.from_list compare (outgoing a.terminator)))) ((Pmap.range compare p.blocks))) in
  let get_incoming_for (i:ident) : ident Pset.set=  (Pset.map compare (fun (b, og) -> b.block_label) (Pset.filter (fun (b, og) -> Pset.mem i og) outgoing1)) in
  let bids : ident Pset.set = (Pmap.domain p.blocks) in
  let x = (Pmap.from_set (fun x -> get_incoming_for x) bids) in
  x)

let option_get (x:  'a option):'a=  ((match x with 
  | Some y -> y
  | None -> failwith "Unsafe maybe get"
  ))


(* two val boolean lattice *)

let bool_bottom:bool=  false
let bool_xf (i: bool) (s:stmt) : bool=  false
let bool_join (l:bool) (r:bool) : bool=  (l || r)

let rec worklist_solver dict_Basic_classes_Eq_a (p:proc) (worklist: ident list) (xf: 'a -> stmt -> 'a) (join : 'a -> 'a -> 'a) (res: (ident, 'a) Pmap.map) (bottom: 'a) (incoming1: (ident, ( ident Pset.set)) Pmap.map): (ident, 'a) Pmap.map= 
   ((match worklist with 
    | h::worklist -> 
      let getExisting i=  ((match (Pmap.lookup i res) with 
        | Some x -> x
        | None -> bottom
        )) in
      let base : 'a = (getExisting h) in
      let bl = (option_get (Pmap.lookup h p.blocks)) in
      let xfed : 'a = (List.fold_left xf base bl.stmts) in
      let nres = (Pmap.add h xfed res) in
      let indeps = (Pset.elements (option_get (Pmap.lookup h incoming1))) in
      let indeps = (Lem_list.map getExisting indeps) in
      let xfed = ((match indeps with 
        | [] -> xfed
        | indeps -> List.fold_left join xfed indeps
      )) in
      let worklist = (if ( 
  dict_Basic_classes_Eq_a.isInequal_method xfed base) then ( List.rev_append (List.rev (outgoing bl.terminator)) worklist) else worklist) in
      worklist_solver 
  dict_Basic_classes_Eq_a p worklist xf join res bottom incoming1
    | [] -> res
  ))

let wl_init dict_Basic_classes_Eq_a (p:proc) (xf: 'a -> stmt -> 'a) (join : 'a -> 'a -> 'a) (bottom: 'a) : (ident, 'a) Pmap.map= 
   (let worklist = (Pset.elements (Pmap.domain p.blocks)) in
  worklist_solver dict_Basic_classes_Eq_a p worklist xf join (Pmap.empty compare) bottom (incoming p))