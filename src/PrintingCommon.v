From Coq Require Import Strings.String. 
From Crypto Require Import Rust CStringification.

Import Crypto.Language.Compilers Crypto.Language.Compilers.defaults C.OfPHOAS.

Module PrettyPrint.

  Inductive Backend := C | Rust.

  Definition LinesToString (lines : list string) : string :=
    String.concat String.NewLine lines.

  Definition ToFunctionLines (backend : Backend) (do_bounds_check static : bool) (prefix name : string) {t : type} :=
    match backend with
    | Rust => @Rust.ToFunctionLines do_bounds_check static prefix name t
    | C => @Compilers.ToString.C.ToFunctionLines do_bounds_check static prefix name t
    end.
 
  Definition ToFunctionString (backend : Backend) (do_bounds_check : bool) (static : bool) (prefix : string) (name : string)
             {t}
             (e : @expr.Expr base.type ident.ident t)
             (comment : type.for_each_lhs_of_arrow var_data t -> var_data (type.final_codomain t) -> list string)
             (name_list : option (list string))
             (inbounds : type.for_each_lhs_of_arrow AbstractInterpretation.Compilers.ZRange.type.option.interp t)
             (outbounds : AbstractInterpretation.Compilers.ZRange.type.option.interp (type.final_codomain t))
    : (string * C.ident_infos) + string
    := match ToFunctionLines backend do_bounds_check static prefix name e comment name_list inbounds outbounds with
       | inl (ls, used_types) => inl (LinesToString ls, used_types)
       | inr err => inr err
       end.

End PrettyPrint.
