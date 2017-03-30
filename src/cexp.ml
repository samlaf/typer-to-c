(* cexp.ml --- Intermediate representation at a C-like level
 *
 *      Copyright (C) 2017  Free Software Foundation, Inc.
 *
 * Author: Stefan Monnier <monnier@iro.umontreal.ca>
 *
 * This file is part of Typer.
 *
 * Typer is free software; you can redistribute it and/or modify it under the
 * terms of the GNU General Public License as published by the Free Software
 * Foundation, either version 3 of the License, or (at your option) any
 * later version.
 *
 * Typer is distributed in the hope that it will be useful, but WITHOUT ANY
 * WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS
 * FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
 * more details.
 *
 * You should have received a copy of the GNU General Public License along
 * with this program.  If not, see <http://www.gnu.org/licenses/>.
 *
 *** Commentary:
 *
 * This is meant to follow `elexp` and has the following differences:
 * - No nested functions.
 * - Instead, there is now a global environment.
 * - Functions take several arguments.
 * - `Call` is not curried any more.
 * - `Case` expressions now only do dispatch.
 * - New operations to construct and access record fields.
 *
 * -------------------------------------------------------------------------- *)


open Sexp (* Sexp type *)

module U = Util
module L = Lexp

type vname = U.vname
type vref = U.vref

module SMap = U.SMap

type cexp =
  (* A constant, either string, integer, or float.  *)
  | Imm of sexp

  (* A builtin constant, typically a function implemented in Ocaml.  *)
  | Builtin of vname

  (* A variable reference, using deBruijn indexing.
   * The bool is `true` for a global reference and `false` for a
   * reference to a variable defined within the current expression.  *)
  | Var of bool * vref

  (* Recursive `let` binding.  *)
  | Let of U.location * (vname * cexp) list * cexp

  (* A (non-curried) function call.  *)
  | Call of cexp * cexp list

  (* A data constructor, such as `cons` or `nil`.  *)
  | MkRecord of symbol * cexp list

  (* Extract field of a record.  *)
  | Select of cexp * int

  (* Case analysis on an agebraic datatype.
   * I.e. tests the special `symbol` field of a record.  *)
  | Case of U.location * cexp
            * (U.location * cexp) SMap.t
            * cexp option

  (* A Type expression.  There's no useful operation we can apply to it,
   * but they can appear in the code.  *)
  | Type of L.lexp

(* Top-level expression.  *)
type ctexp =
  | Lambda of vname list * cexp
  | Cexp of cexp

(* The content of a whole file.  *)
type cfile = (vname * ctexp) list
