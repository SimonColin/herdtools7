(*********************************************************************)
(*                        Memevents                                  *)
(*                                                                   *)
(* Jade Alglave, Luc Maranget, INRIA Paris-Rocquencourt, France.     *)
(* Susmit Sarkar, Peter Sewell, University of Cambridge, UK.         *)
(*                                                                   *)
(*  Copyright 2010 Institut National de Recherche en Informatique et *)
(*  en Automatique and the authors. All rights reserved.             *)
(*  This file is distributed  under the terms of the Lesser GNU      *)
(*  General Public License.                                          *)
(*********************************************************************)

(** Closed signature for basic view of architectures *)

module type S = sig
  type pins (* Parsed instruction *)
  type ins  (* Final instruction  *)

  type reg_arg

  type 'ins kpseudo =
    | Nop
    | Label of string * 'ins kpseudo
    | Instruction of 'ins
    | Macro of string * reg_arg list

  type pseudo = ins kpseudo
  type parsedPseudo = pins kpseudo


(* Lifting of fold/map *)
  val pseudo_map : ('a -> 'b) -> 'a kpseudo -> 'b kpseudo
  val pseudo_fold : ('a -> 'b -> 'a) -> 'a -> 'b kpseudo -> 'a
  val pseudo_iter : ('a -> unit) -> 'a kpseudo -> unit

(* Fold/Map over labels *)
  val fold_labels : ('a -> string -> 'a) -> 'a -> pseudo -> 'a
  val map_labels : (string -> string) -> pseudo -> pseudo

(* For printing the program, code per processor *)
  type nice_prog = (int * pseudo list) list

(* Counting (static) memory accesses *)
  val get_naccesses : pseudo list -> int

(* Translare from parsed instructions *)
  val pseudo_parsed_tr : parsedPseudo -> pseudo

end

(* Input signature *)
module type I = sig
  type ins
  type pins
  type reg_arg
(* translate from parsed *)
  val parsed_tr : pins -> ins

(* Number of memory access per instruction *)
  val get_naccesses : ins -> int
(* fold/map over labels in instructions,
   used for label normalisation *)
  val fold_labels : 'a -> ('a -> string -> 'a) -> ins -> 'a
  val map_labels : (string -> string) -> ins -> ins

end

(* Common to all arch, memevents and  litmus *)

module Make
    (I : I) : S
with type ins = I.ins and type pins = I.pins and type reg_arg = I.reg_arg
=
struct
  type ins = I.ins
  type pins = I.pins
  type reg_arg = I.reg_arg
(* Parsed instructions, ie instructions enriched with labels *)
  type 'ins kpseudo =
    | Nop
    | Label of string * 'ins kpseudo
    | Instruction of 'ins
    | Macro of string * reg_arg list

  type pseudo = ins kpseudo
  type parsedPseudo = pins kpseudo

(* Fold/Map lifting *)
  let rec pseudo_map f ins = match ins with
    | Nop -> Nop
    | Instruction ins -> Instruction (f ins)
    | Label (lbl,ins) -> Label (lbl, pseudo_map f ins)
    | Macro (_,_) -> assert false

  let rec pseudo_fold f k ins = match ins with
    | Nop -> k
    | Instruction ins -> f k ins
    | Label (_,ins) -> pseudo_fold f k ins
    | Macro (_,_) -> assert false

  let pseudo_iter f ins = pseudo_fold (fun () ins -> f ins) () ins

(* Fold/Map over labels *)

  let rec fold_labels f k ins = match ins with
  | Nop -> k
  | Instruction ins -> I.fold_labels k f ins
  | Label (lbl,ins) -> fold_labels f (f k lbl) ins
  | Macro _ -> assert false

  let rec map_labels f ins = match ins with
  | Nop -> Nop
  | Instruction ins -> Instruction (I.map_labels f ins)
  | Label (lbl,ins) -> Label (f lbl, map_labels f ins)
  | Macro _ -> assert false

(* For printing the program, code per processor *)
  type nice_prog = (int * pseudo list) list

(* Counting memory accesses *)
  let get_naccesses code =
    List.fold_left
      (pseudo_fold
         (fun k ins -> k + I.get_naccesses ins))
      0 code

(* Translate *)
  let pseudo_parsed_tr p = pseudo_map I.parsed_tr p

end
