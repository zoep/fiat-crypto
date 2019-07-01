From Coq Require Import ZArith.ZArith MSets.MSetPositive FSets.FMapPositive
     Strings.String Strings.Ascii Bool.Bool Lists.List.
Require Import Crypto.Util.ListUtil Lists.List.
Require Crypto.Util.Strings.String.
Require Import Crypto.Util.Strings.Decimal.
Require Import Crypto.Util.Strings.HexString.
Require Import Crypto.Util.Strings.Show.
Require Import Crypto.Util.ZRange.
Require Import Crypto.Util.ZRange.Operations.
Require Import Crypto.Util.ZRange.Show.
Require Import Crypto.Util.Option.
Require Import Crypto.Util.OptionList.
Require Import Crypto.Language.
Require Import Crypto.AbstractInterpretation.
Require Import Crypto.Util.Bool.Equality.
Require Import Crypto.Util.Notations.
From Crypto Require Import CStringification.

Import ListNotations.

Local Open Scope zrange_scope.
Local Open Scope Z_scope.

Module C := Compilers.ToString.C. (* module alias *)

Module Rust.

  (* Header imports *)
  Definition imports : string := "use std::prelude;".

  (* Header imports and type defs *)
  Definition typedef_header (prefix : string) (bitwidths_used : PositiveSet.t)
  : list string :=
    ([imports]
       ++ (if PositiveSet.mem 1 bitwidths_used
           then ["type " ++ prefix ++ "u1 = u8;"; (* C: typedef unsigned char prefix_uint1 *)
                   "type " ++ prefix ++ "i1 = i8;" ]%string (* C: typedef signed char prefix_int1 *)
           else [])
       ++ (if PositiveSet.mem 128 bitwidths_used
           then ["type" ++ prefix ++ "u128 = u128;"; (* Since 128 bit integers exists in (nightly) rust consider removing the *)
                                                    (* type synonym and extending stdint_ditwidths *)
                   "type " ++ prefix ++ "i128 = i128;"]%string
           else []))%list.

  (* Supported integer bitwidths *)
  Definition stdint_bitwidths : list Z := [8; 16; 32; 64].
  Definition is_special_bitwidth (bw : Z) := negb (existsb (Z.eqb bw) stdint_bitwidths).


  Definition int_type_to_string (prefix : string) (t : C.int.type) : string :=
    ((if is_special_bitwidth (C.int.bitwidth_of t) then prefix else "")
       ++ (if C.int.is_unsigned t then "u" else "i")
       ++ decimal_string_of_Z (C.int.bitwidth_of t))%string.

  (* XXX That uses <<Macros for minimum-width integer constants>>. Find
   * out how to do this correcly in Rust. Not used *)
  Definition to_literal_macro_string (t : C.int.type) : option string :=
    if Z.ltb (C.int.bitwidth_of t) 8
    then None
    else Some ((if C.int.is_unsigned t then "U" else "")
                 ++ "INT"
                 ++ decimal_string_of_Z (C.int.bitwidth_of t)
                 ++ "_C")%string.

  (* Instead of "macros for minimum-width integer constants" let's try to
     use numeric casts in Rust *)
  Definition cast_literal (prefix : string) (t : C.int.type) : option string :=
    if Z.ltb (C.int.bitwidth_of t) 8
    then None
    else Some (" as " ++ int_type_to_string prefix t)%string.


  (* In fiat-crypto C functions are void and as such, they receive
     pointers to the result as argumnets. The C code before calling a
     function, declares uninitializedinteger pointers and passes them as
     arguments.  In rust to do that, we declare an initialized (to 0)
     mutable, and pass a mutable reference to the callee.:

     In the longer term, we should examine whether we should use
     non-void function and just return the result *)

  (* Fiat-crypto groups inputs and outputs to arrays but only at top-level
     functions *)


  Definition primitive_type_to_string (prefix : string) (t : C.type.primitive)
             (r : option C.int.type) : string :=
    match t with
    | C.type.Zptr => "&mut "
    | C.type.Z => ""
    end ++ match r with
           | Some int_t => int_type_to_string prefix int_t
           | None => "ℤ" (* XXX what is this unicode symbol?? *)
           end.

  (* Integer literal to string *)
  Definition int_literal_to_string (prefix : string) (t : C.type.primitive) (v : BinInt.Z) : string :=
    match t, cast_literal prefix (C.int.of_zrange_relaxed r[v ~> v]) with
    | C.type.Z, Some cast => "(" ++ HexString.of_Z v ++ cast ++ ")"
    | C.type.Z, None => (* just print hex value, no cast *) HexString.of_Z v
    | C.type.Zptr, _ => "#error ""literal address " ++ HexString.of_Z v ++ """;"
    end.

  Import C.Notations.

  Fixpoint arith_to_string (prefix : string) {t} (e : C.arith_expr t) : string
    := match e with
       (* integer literals *)
       | (C.literal v @@ _) => int_literal_to_string prefix C.type.Z v
       (* array dereference *)
       | (C.List_nth n @@ C.Var _ v) => "(" ++ v ++ "[" ++ decimal_string_of_Z (Z.of_nat n) ++ "])"
       (* (de)referencing *)
       | (C.Addr @@ C.Var _ v) => "&mut " ++ v (* borrow a mutable ref to v *)
       | (C.Dereference @@ e) => "( *" ++ arith_to_string prefix e ++ " )"
       (* bitwise operations *)
       | (C.Z_shiftr offset @@ e) =>
         "(" ++ arith_to_string prefix e ++ " >> " ++ decimal_string_of_Z offset ++ ")"
       | (C.Z_shiftl offset @@ e) =>
         "(" ++ arith_to_string prefix e ++ " << " ++ decimal_string_of_Z offset ++ ")"
       | (C.Z_land @@ (e1, e2)) =>
         "(" ++ arith_to_string prefix e1 ++ " & " ++ arith_to_string prefix e2 ++ ")"
       | (C.Z_lor @@ (e1, e2)) =>
         "(" ++ arith_to_string prefix e1 ++ " | " ++ arith_to_string prefix e2 ++ ")"
       | (C.Z_lnot _ @@ e) => "(!" ++ arith_to_string prefix e ++ ")"
       (* arithmetic operations *)
       | (C.Z_add @@ (x1, x2)) =>
         "(" ++ arith_to_string prefix x1 ++ " + " ++ arith_to_string prefix x2 ++ ")"
       | (C.Z_mul @@ (x1, x2)) =>
         "(" ++ arith_to_string prefix x1 ++ " * " ++ arith_to_string prefix x2 ++ ")"
       | (C.Z_sub @@ (x1, x2)) =>
         "(" ++ arith_to_string prefix x1 ++ " - " ++ arith_to_string prefix x2 ++ ")"
       | (C.Z_opp @@ e) => "(-" ++ arith_to_string prefix e ++ ")" (* arithmetic negation *)
       | (C.Z_bneg @@ e) => "(!" ++ arith_to_string prefix e ++ ")" (* logical negation. XXX this has different semantics for numbers <>
                                                                     0 or 1 than it did before *)
       (* TODO these are function calls, check if borrows are passed correcly *)
       | (C.Z_mul_split lg2s @@ args) =>
         prefix
           ++ "mulx_u"
           ++ decimal_string_of_Z lg2s ++ "(" ++ arith_to_string prefix args ++ ")"
       | (C.Z_add_with_get_carry lg2s @@ args) =>
         prefix
           ++ "addcarryx_u"
           ++ decimal_string_of_Z lg2s ++ "(" ++ arith_to_string prefix args ++ ")"
       | (C.Z_sub_with_get_borrow lg2s @@ args) =>
         prefix
           ++ "subborrowx_u"
           ++ decimal_string_of_Z lg2s ++ "(" ++ arith_to_string prefix args ++ ")"
       | (C.Z_zselect ty @@ args) =>
         prefix
           ++ "cmovznz_"
           ++ (if C.int.is_unsigned ty then "u" else "")
           ++ decimal_string_of_Z (C.int.bitwidth_of ty) ++ "(" ++ @arith_to_string prefix _ args ++ ")"
       | (C.Z_static_cast int_t @@ e) =>
         "(" ++ arith_to_string prefix e ++ " as " ++ primitive_type_to_string prefix C.type.Z (Some int_t) ++ ")"
       | C.Var _ v => v
       | C.Pair A B a b => arith_to_string prefix a ++ ", " ++ arith_to_string prefix b
       | (C.Z_add_modulo @@ (x1, x2, x3)) => "#error addmodulo;"
       | (C.List_nth _ @@ _)
       | (C.Addr @@ _)
       | (C.Z_add @@ _)
       | (C.Z_mul @@ _)
       | (C.Z_sub @@ _)
       | (C.Z_land @@ _)
       | (C.Z_lor @@ _)
       | (C.Z_add_modulo @@ _) => "#error bad_arg;"
       | TT => "#error tt;"
       end%string%Cexpr.

  Fixpoint stmt_to_string (prefix : string) (e : C.stmt) : string :=
    match e with
    | C.Call val => arith_to_string prefix val ++ ";"
    | C.Assign true t sz name val =>
      (* local npn-mutable declaration with initialization *)
      "let " ++ name ++ ": " ++ primitive_type_to_string prefix t sz ++ " = " ++ arith_to_string prefix val ++ ";"
    | C.Assign false _ sz name val =>
    (* This corresponds to assignment to a non-pointer variable and should never ever
       happen in our generated code. Fiat-crypto handles it but I
       haven't found and instance of this to their generated code *)
    (* code : name ++ " = " ++ arith_to_string prefix val ++ ";" *)
      "#error trying to assign value to non-mutable variable;"
    | C.AssignZPtr name sz val =>
      "*" ++ name ++ " = " ++ arith_to_string prefix val ++ ";"
    | C.DeclareVar t sz name =>
      (* Local uninitialized declarations become mut declarations, and
         are initialized to 0. *)
      (* The assumptions here, based on fiat-crypto code generation
         patterns, are that 1.) this variable will be an argument to a
         call that will store its result in this variable. 2.) this will
         have a non-pointer an integer type XXX initialize *)
      "let mut " ++ name ++ ": " ++ primitive_type_to_string prefix t sz ++ ";"
    | C.AssignNth name n val =>
      name ++ "[" ++ decimal_string_of_Z (Z.of_nat n) ++ "] = " ++ arith_to_string prefix val ++ ";"
    end.

  Definition to_strings (prefix : string) (e : C.expr) : list string :=
    List.map (stmt_to_string prefix) e.

  Import Crypto.Language.Compilers Crypto.Language.Compilers.defaults C.OfPHOAS.

  Inductive Mode := In | Out.


  (* This would have been nice, but coercions don't work *)
  (* Module Base := Crypto.Language.Compilers.base. *)

  Fixpoint to_base_arg_list (prefix : string) (mode : Mode) {t} : C.OfPHOAS.base_var_data t -> list string :=
    match t return base_var_data t -> _ with
    | base.type.Z =>
      let typ := match mode with In => C.type.Z | Out => C.type.Zptr end in
      fun '(n, r) => [n ++ ": " ++ primitive_type_to_string prefix typ r]
    | base.type.prod A B =>
      fun '(va, vb) => (to_base_arg_list prefix mode va ++ to_base_arg_list prefix mode vb)%list
    | base.type.list base.type.Z =>
      fun '(n, r, len) =>
        match mode with
        | In => (* arrays for inputs are immutable borrows *)
          [ n ++ ": " ++
              "&[" ++ primitive_type_to_string prefix C.type.Z r  ++
              "; " ++ decimal_string_of_Z (Z.of_nat len) ++ "]" ]
        | Out => (* arrays for outputs are mutable borrows *)
          [ n ++ ": " ++
              "&mut [" ++ primitive_type_to_string prefix C.type.Z r ++
              "; " ++ decimal_string_of_Z (Z.of_nat len) ++ "]" ]
        end
    | base.type.list _ => fun _ => ["#error ""complex list"";"]
    | base.type.option _ => fun _ => ["#error option;"]
    | base.type.unit => fun _ => ["#error unit;"]
    | base.type.nat => fun _ => ["#error ℕ;"]
    | base.type.bool => fun _ => ["#error bool;"]
    | base.type.zrange => fun _ => ["#error zrange;"]
    end%string.

  Definition to_arg_list (prefix : string) (mode : Mode) {t} : var_data t -> list string :=
    match t return var_data t -> _ with
    | type.base t => to_base_arg_list prefix mode
    | type.arrow _ _ => fun _ => ["#error arrow;"]
    end%string.

  Fixpoint to_arg_list_for_each_lhs_of_arrow (prefix : string) {t} : type.for_each_lhs_of_arrow var_data t -> list string
    := match t return type.for_each_lhs_of_arrow var_data t -> _ with
       | type.base t => fun _ => nil
       | type.arrow s d
         => fun '(x, xs)
            => to_arg_list prefix In x ++ @to_arg_list_for_each_lhs_of_arrow prefix d xs
       end%list.

  (* Used in comment *)
  Fixpoint bound_to_string {t : base.type} : var_data t -> Compilers.ZRange.type.base.option.interp t -> list string :=
    match t return var_data t -> Compilers.ZRange.type.base.option.interp t -> list string with
    | base.type.Z
      => fun '(name, _) arg
         => [(name ++ ": ")
               ++ match arg with
                  | Some arg => show false arg
                  | None => show false arg
                  end]%string
    | base.type.prod A B
      => fun '(va, vb) '(a, b)
         => @bound_to_string A va a ++ @bound_to_string B vb b
    | base.type.list A
      => fun '(name, _, _) arg
         => [(name ++ ": ")
               ++ match Compilers.ZRange.type.base.option.lift_Some arg with
                  | Some arg => show false arg
                  | None => show false arg
                  end]%string
    | base.type.option _
    | base.type.unit
    | base.type.bool
    | base.type.nat
    | base.type.zrange => fun _ _ => []
    end%list.

  (* Used in comment *)
  Fixpoint input_bounds_to_string {t}
    : type.for_each_lhs_of_arrow var_data t -> type.for_each_lhs_of_arrow Compilers.ZRange.type.option.interp t -> list string :=
    match t return type.for_each_lhs_of_arrow var_data t -> type.for_each_lhs_of_arrow Compilers.ZRange.type.option.interp t -> list string with
    | type.base t => fun _ _ => nil
    | type.arrow (type.base s) d =>
      fun '(v, vs) '(arg, args) =>
        (bound_to_string v arg)
          ++ @input_bounds_to_string d vs args
    | type.arrow s d =>
      fun '(absurd, _) => match absurd : Empty_set with end
    end%list.

  Definition to_function_lines (static : bool) (prefix : string) (name : string)
             {t}
             (f : type.for_each_lhs_of_arrow var_data t * var_data (type.final_codomain t) * C.expr)
    : list string
    := let '(args, rets, body) := f in
       ((if static then "fn " else "pub fn ") ++ name ++
         "(" ++ String.concat ", " (to_arg_list prefix Out rets ++ to_arg_list_for_each_lhs_of_arrow prefix args) ++
         ") -> () {")%string :: (List.map (fun s => "  " ++ s)%string (to_strings prefix body)) ++ ["}"%string]%list.

  Definition ToFunctionLines (do_bounds_check : bool) (static : bool) (prefix : string) (name : string)
             {t}
             (e : @Compilers.expr.Expr base.type ident.ident t)
             (comment : type.for_each_lhs_of_arrow var_data t -> var_data (type.final_codomain t) -> list string)
             (name_list : option (list string))
             (inbounds : type.for_each_lhs_of_arrow Compilers.ZRange.type.option.interp t)
             (outbounds : Compilers.ZRange.type.base.option.interp (type.final_codomain t))
    : (list string * C.ident_infos) + string
    := match ExprOfPHOAS do_bounds_check e name_list inbounds with
       | inl (indata, outdata, f)
         => inl ((["/*"%string]
                    ++ (List.map (fun s => if (String.length s =? 0)%nat then " *" else (" * " ++ s))%string (comment indata outdata))
                    ++ [" * Input Bounds:"%string]
                    ++ List.map (fun v => " *   "%string ++ v)%string (input_bounds_to_string indata inbounds)
                    ++ [" * Output Bounds:"%string]
                    ++ List.map (fun v => " *   "%string ++ v)%string (bound_to_string outdata outbounds)
                    ++ [" */"%string]
                    ++ to_function_lines static prefix name (indata, outdata, f))%list,
                 C.collect_infos f)
       | inr nil
         => inr ("Unknown internal error in converting " ++ name ++ " to Rust")%string
       | inr [err]
         => inr ("Error in converting " ++ name ++ " to Rust:" ++ String.NewLine ++ err)%string
       | inr errs
         => inr ("Errors in converting " ++ name ++ " to Rust:" ++ String.NewLine ++ String.concat String.NewLine errs)%string
       end.

End Rust.
