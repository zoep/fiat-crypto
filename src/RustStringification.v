From Coq Require Import ZArith.ZArith MSets.MSetPositive FSets.FMapPositive
     Strings.String Strings.Ascii Bool.Bool Lists.List.
From Crypto.Util Require Import
     ListUtil
     Strings.String Strings.Decimal Strings.HexString Strings.Show
     ZRange ZRange.Operations ZRange.Show
     Option OptionList Equality Notations
     Bool.Equality.

From Crypto Require Import IR CStringification Language AbstractInterpretation.

Import ListNotations.

Local Open Scope zrange_scope.
Local Open Scope Z_scope.

Module IR := IR.Compilers.ToString.IR.
Module ToString := LanguageStringification.Compilers.ToString.

Module Rust.

  (* Header imports *)
  Definition imports : string := "use std::prelude;".

  (* Header imports and type defs *)
  (* TODO thrad static flag to append pub *)
  Definition typedef_header (prefix : string) (bitwidths_used : PositiveSet.t)
  : list string :=
    ([imports]
       ++ (if PositiveSet.mem 1 bitwidths_used
           then ["pub type " ++ prefix ++ "u1 = u8;"; (* C: typedef unsigned char prefix_uint1 *)
                   "pub type " ++ prefix ++ "i1 = i8;" ]%string (* C: typedef signed char prefix_int1 *)
           else [])
       ++ (if PositiveSet.mem 128 bitwidths_used
           then ["pub type " ++ prefix ++ "u128 = u128;"; (* Since 128 bit integers exist in (nightly) rust consider removing the *)
                                                      (* type synonym and extending stdint_ditwidths *)
                   "pub type " ++ prefix ++ "i128 = i128;"]%string
           else []))%list.

  (* Supported integer bitwidths *)
  Definition stdint_bitwidths : list Z := [8; 16; 32; 64].
  Definition is_special_bitwidth (bw : Z) := negb (existsb (Z.eqb bw) stdint_bitwidths).


  Definition int_type_to_string (prefix : string) (t : ToString.int.type) : string :=
    ((if is_special_bitwidth (ToString.int.bitwidth_of t) then prefix else "")
       ++ (if ToString.int.is_unsigned t then "u" else "i")
       ++ decimal_string_of_Z (ToString.int.bitwidth_of t))%string.

  (* XXX That uses <<Macros for minimum-width integer constants>>. Find
   * out how to do this correcly in Rust. Not used *)
  Definition to_literal_macro_string (t : ToString.int.type) : option string :=
    if Z.ltb (ToString.int.bitwidth_of t) 8
    then None
    else Some ((if ToString.int.is_unsigned t then "U" else "")
                 ++ "INT"
                 ++ decimal_string_of_Z (ToString.int.bitwidth_of t)
                 ++ "_C")%string.

  (* Instead of "macros for minimum-width integer constants" let's try to
     use numeric casts in Rust *)
  Definition cast_literal (prefix : string) (t : ToString.int.type) : option string :=
    if Z.ltb (ToString.int.bitwidth_of t) 8
    then None
    else None.
    (* Zoe: Disable direct casts on literals for now *)
    (* Some (" as " ++ int_type_to_string prefix t)%string. *)


  (* In fiat-crypto C functions are void and as such, they receive
     pointers to the result as argumnets. The C code before calling a
     function, declares uninitializedinteger pointers and passes them as
     arguments.  In rust to do that, we declare an initialized (to 0)
     mutable, and pass a mutable reference to the callee.:

     In the longer term, we should examine whether we should use
     non-void function and just return the result *)

  (* Fiat-crypto groups inputs and outputs to arrays but only at top-level
     functions *)


  Definition primitive_type_to_string (prefix : string) (t : IR.type.primitive)
             (r : option ToString.int.type) : string :=
    match t with
    | IR.type.Zptr => "&mut "
    | IR.type.Z => ""
    end ++ match r with
           | Some int_t => int_type_to_string prefix int_t
           | None => "ℤ" (* XXX what is this unicode symbol?? *)
           end.

  (* Integer literal to string *)
  Definition int_literal_to_string (prefix : string) (t : IR.type.primitive) (v : BinInt.Z) : string :=
    match t, cast_literal prefix (ToString.int.of_zrange_relaxed r[v ~> v]) with
    | IR.type.Z, Some cast => "(" ++ HexString.of_Z v ++ cast ++ ")"
    | IR.type.Z, None => (* just print hex value, no cast *) HexString.of_Z v
    | IR.type.Zptr, _ => "#error ""literal address " ++ HexString.of_Z v ++ """;"
    end.

  Import IR.Notations.

  Fixpoint arith_to_string (prefix : string) {t} (e : IR.arith_expr t) : string
    := match e with
       (* integer literals *)
       | (IR.literal v @@ _) => int_literal_to_string prefix IR.type.Z v
       (* array dereference *)
       | (IR.List_nth n @@ IR.Var _ v) => "(" ++ v ++ "[" ++ decimal_string_of_Z (Z.of_nat n) ++ "])"
       (* (de)referencing *)
       | (IR.Addr @@ IR.Var _ v) => "&mut " ++ v (* borrow a mutable ref to v *)
       | (IR.Dereference @@ e) => "( *" ++ arith_to_string prefix e ++ " )"
       (* bitwise operations *)
       | (IR.Z_shiftr offset @@ e) =>
         "(" ++ arith_to_string prefix e ++ " >> " ++ decimal_string_of_Z offset ++ ")"
       | (IR.Z_shiftl offset @@ e) =>
         "(" ++ arith_to_string prefix e ++ " << " ++ decimal_string_of_Z offset ++ ")"
       | (IR.Z_land @@ (e1, e2)) =>
         "(" ++ arith_to_string prefix e1 ++ " & " ++ arith_to_string prefix e2 ++ ")"
       | (IR.Z_lor @@ (e1, e2)) =>
         "(" ++ arith_to_string prefix e1 ++ " | " ++ arith_to_string prefix e2 ++ ")"
       | (IR.Z_lnot _ @@ e) => "(!" ++ arith_to_string prefix e ++ ")"
       (* arithmetic operations *)
       | (IR.Z_add @@ (x1, x2)) =>
         "(" ++ arith_to_string prefix x1 ++ " + " ++ arith_to_string prefix x2 ++ ")"
       | (IR.Z_mul @@ (x1, x2)) =>
         "(" ++ arith_to_string prefix x1 ++ " * " ++ arith_to_string prefix x2 ++ ")"
       | (IR.Z_sub @@ (x1, x2)) =>
         "(" ++ arith_to_string prefix x1 ++ " - " ++ arith_to_string prefix x2 ++ ")"
       | (IR.Z_opp @@ e) => "(-" ++ arith_to_string prefix e ++ ")" (* arithmetic negation *)
       | (IR.Z_bneg @@ e) => "(!" ++ arith_to_string prefix e ++ ")" (* logical negation. XXX this has different semantics for numbers <>
                                                                     0 or 1 than it did before *)
       (* TODO these are function calls, check if borrows are passed correcly *)
       | (IR.Z_mul_split lg2s @@ args) =>
         prefix
           ++ "mulx_u"
           ++ decimal_string_of_Z lg2s ++ "(" ++ arith_to_string prefix args ++ ")"
       | (IR.Z_add_with_get_carry lg2s @@ args) =>
         prefix
           ++ "addcarryx_u"
           ++ decimal_string_of_Z lg2s ++ "(" ++ arith_to_string prefix args ++ ")"
       | (IR.Z_sub_with_get_borrow lg2s @@ args) =>
         prefix
           ++ "subborrowx_u"
           ++ decimal_string_of_Z lg2s ++ "(" ++ arith_to_string prefix args ++ ")"
       | (IR.Z_zselect ty @@ args) =>
         prefix
           ++ "cmovznz_"
           ++ (if ToString.int.is_unsigned ty then "u" else "")
           ++ decimal_string_of_Z (ToString.int.bitwidth_of ty) ++ "(" ++ @arith_to_string prefix _ args ++ ")"
       | (IR.Z_static_cast int_t @@ e) =>
         "(" ++ arith_to_string prefix e ++ " as " ++ primitive_type_to_string prefix IR.type.Z (Some int_t) ++ ")"
       | IR.Var _ v => v
       | IR.Pair A B a b => arith_to_string prefix a ++ ", " ++ arith_to_string prefix b
       | (IR.Z_add_modulo @@ (x1, x2, x3)) => "#error addmodulo;"
       | (IR.List_nth _ @@ _)
       | (IR.Addr @@ _)
       | (IR.Z_add @@ _)
       | (IR.Z_mul @@ _)
       | (IR.Z_sub @@ _)
       | (IR.Z_land @@ _)
       | (IR.Z_lor @@ _)
       | (IR.Z_add_modulo @@ _) => "#error bad_arg;"
       | TT => "#error tt;"
       end%string%Cexpr.

  Fixpoint stmt_to_string (prefix : string) (e : IR.stmt) : string :=
    match e with
    | IR.Call val => arith_to_string prefix val ++ ";"
    | IR.Assign true t sz name val =>
      (* local npn-mutable declaration with initialization *)
      "let " ++ name ++ ": " ++ primitive_type_to_string prefix t sz ++ " = " ++ arith_to_string prefix val ++ ";"
    | IR.Assign false _ sz name val =>
    (* This corresponds to assignment to a non-pointer variable and should never ever
       happen in our generated code. Fiat-crypto handles it but I
       haven't found and instance of this to their generated code *)
    (* code : name ++ " = " ++ arith_to_string prefix val ++ ";" *)
      "#error trying to assign value to non-mutable variable;"
    | IR.AssignZPtr name sz val =>
      "*" ++ name ++ " = " ++ arith_to_string prefix val ++ ";"
    | IR.DeclareVar t sz name =>
      (* Local uninitialized declarations become mut declarations, and
         are initialized to 0. *)
      (* The assumptions here, based on fiat-crypto code generation
         patterns, are that 1.) this variable will be an argument to a
         call that will store its result in this variable. 2.) this will
         have a non-pointer an integer type XXX initialize *)
      "let mut " ++ name ++ ": " ++ primitive_type_to_string prefix t sz ++ " = 0;"
    | IR.AssignNth name n val =>
      name ++ "[" ++ decimal_string_of_Z (Z.of_nat n) ++ "] = " ++ arith_to_string prefix val ++ ";"
    end.

  Definition to_strings (prefix : string) (e : IR.expr) : list string :=
    List.map (stmt_to_string prefix) e.

  Import Crypto.Language.Compilers Crypto.Language.Compilers.defaults IR.OfPHOAS.

  Inductive Mode := In | Out.


  (* This would have been nice, but coercions don't work *)
  (* Module Base := Crypto.Language.Compilers.base. *)

  Fixpoint to_base_arg_list (prefix : string) (mode : Mode) {t} : ToString.OfPHOAS.base_var_data t -> list string :=
    match t return base_var_data t -> _ with
    | base.type.Z =>
      let typ := match mode with In => IR.type.Z | Out => IR.type.Zptr end in
      fun '(n, r) => [n ++ ": " ++ primitive_type_to_string prefix typ r]
    | base.type.prod A B =>
      fun '(va, vb) => (to_base_arg_list prefix mode va ++ to_base_arg_list prefix mode vb)%list
    | base.type.list base.type.Z =>
      fun '(n, r, len) =>
        match mode with
        | In => (* arrays for inputs are immutable borrows *)
          [ n ++ ": " ++
              "&[" ++ primitive_type_to_string prefix IR.type.Z r  ++
              "; " ++ decimal_string_of_Z (Z.of_nat len) ++ "]" ]
        | Out => (* arrays for outputs are mutable borrows *)
          [ n ++ ": " ++
              "&mut [" ++ primitive_type_to_string prefix IR.type.Z r ++
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
    match t return type.for_each_lhs_of_arrow var_data t ->
                   type.for_each_lhs_of_arrow Compilers.ZRange.type.option.interp t -> list string
    with
    | type.base t => fun _ _ => nil
    | type.arrow (type.base s) d =>
      fun '(v, vs) '(arg, args) =>
        (bound_to_string v arg)
          ++ @input_bounds_to_string d vs args
    | type.arrow s d =>
      fun '(absurd, _) => match absurd : Empty_set with end
    end%list.


  (** * Language-specific numeric conversions to be passed to the PHOAS -> IR translation *)

  (* Zoe: Verbatim from C translation, but without integer promotions *)

  Definition rank (r : ToString.int.type) : BinInt.Z := ToString.int.bitwidth_of r.

  Definition common_type (t1 t2 : ToString.int.type) : ToString.int.type :=
    (** - If the types after promotion are the same, that
          type is the common type *)
    if ToString.int.type_beq t1 t2 then
      t1
    (** - Otherwise, if both operands after promotion have
          the same signedness (both signed or both unsigned),
          the operand with the lesser conversion rank (see
          below) is implicitly converted to the type of the
          operand with the greater conversion rank *)

    else if bool_beq (ToString.int.is_signed t1) (ToString.int.is_signed t2) then
      (if rank t1 >=? rank t2 then t1 else t2)
      (** - Otherwise, the signedness is different: If the
            operand with the unsigned type has conversion rank
            greater or equal than the rank of the type of the
            signed operand, then the operand with the signed
            type is implicitly converted to the unsigned type
       *)
    else if ToString.int.is_unsigned t1 && (rank t1 >=? rank t2) then
      t1
    else if ToString.int.is_unsigned t2 && (rank t2 >=? rank t1) then
      t2
    (** - Otherwise, the signedness is different and the
          signed operand's rank is greater than unsigned
          operand's rank. In this case, if the signed type
          can represent all values of the unsigned type, then
          the operand with the unsigned type is implicitly
          converted to the type of the signed operand. *)
    else if ToString.int.is_signed t1 && ToString.int.is_tighter_than t2 t1 then
      t1
    else if ToString.int.is_signed t2 && ToString.int.is_tighter_than t1 t2 then
      t2
    (** - Otherwise, both operands undergo implicit
          conversion to the unsigned type counterpart of the
          signed operand's type. *)
    (** N.B. This case ought to be impossible in our code,
        where [rank] is the bitwidth. *)
    else if ToString.int.is_signed t1 then
      ToString.int.unsigned_counterpart_of t1
    else
      ToString.int.unsigned_counterpart_of t2.

  Definition Rust_bin_op_conversion
             (desired_type : option ToString.int.type)
             (args : arith_expr_for (base.type.Z * base.type.Z))
    : arith_expr_for (base.type.Z * base.type.Z) :=
    match desired_type with
    | None => args
    | Some _ =>
      let '((e1, t1), (e2, t2)) := args in
      match t1, t2 with
      | None, _ | _, None => args
      | Some t1', Some t2' =>
        (Zcast_up_if_needed desired_type (e1, t1),
         Zcast_up_if_needed desired_type (e2, t2))
      end
    end.

  Definition Rust_un_op_conversion (desired_type : option ToString.int.type)
             (arg : arith_expr_for base.type.Z)
    : arith_expr_for base.type.Z :=
    let '(e, r) := arg in
    Zcast_up_if_needed desired_type (e, r).

  Local Instance CLanguageCasts : LanguageCasts :=
    Build_LanguageCasts
      common_type
      Rust_bin_op_conversion
      Rust_un_op_conversion.
      (* Zoe: Halp! what are these "Error: Not a projection" messages I'm
         getting when using record notation *)


  Definition to_function_lines (static : bool) (prefix : string) (name : string)
             {t}
             (f : type.for_each_lhs_of_arrow var_data t * var_data (type.final_codomain t) * IR.expr)
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
    : (list string * ToString.ident_infos) + string
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
                 (* Zoe: This is a function in the CStringification file *)
                 Compilers.ToString.C.collect_infos f)
       | inr nil
         => inr ("Unknown internal error in converting " ++ name ++ " to Rust")%string
       | inr [err]
         => inr ("Error in converting " ++ name ++ " to Rust:" ++ String.NewLine ++ err)%string
       | inr errs
         => inr ("Errors in converting " ++ name ++ " to Rust:" ++ String.NewLine ++ String.concat String.NewLine errs)%string
       end.

  Definition OutputRustAPI : ToString.OutputLanguageAPI :=
    ToString.Build_OutputLanguageAPI (* XXX Record notation raises (spurious?) Error: comment_block: Not a projection *)
      (List.map (fun line => "/* " ++ line ++ " */")%string)
      ToFunctionLines
      typedef_header.

End Rust.
