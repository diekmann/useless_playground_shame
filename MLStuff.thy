theory MLStuff
imports Main
begin



definition "test = ''asdf''"
definition "test_list = [''asdf'', ''foo'']"


ML {*
Context.theory_name @{theory}
*}

ML{*
val testML = rep_thm (@{thm test_def}) |> #prop;
val testlistML = rep_thm (@{thm test_list_def}) |> #prop;


Syntax.pretty_term @{context} testML |> Pretty.backquote |> Pretty.writeln;

exception MatchNetExhaustiveButThisIsYourFault;

fun extract_trueprop trm = 
    case trm
      of Const ("HOL.Trueprop", @{typ "bool \<Rightarrow> prop"}) $ t1 => t1
      | _ => raise MatchNetExhaustiveButThisIsYourFault;

exception extract_eq_rhs_full_name_exception
exception extract_eq_rhs_type_exception

fun extract_eq_rhs typ name_def trm = 
    case trm
      of (Const ("HOL.eq", _) $ Const (full_name', typ')) $ t1 => 
        let val full_name = ((Context.theory_name @{theory}) ^ "."  ^ name_def) 
        in 
          if full_name' = full_name then 
            if typ' = typ then t1 else raise extract_eq_rhs_type_exception else raise extract_eq_rhs_full_name_exception
        end
      | _ => raise MatchNetExhaustiveButThisIsYourFault;

fun extract_Cons_list_list trm = 
    case trm
      of (Const ("List.list.Cons", _)) $ t1 $ t2 => SOME (t1, t2)
      | (Const ("List.list.Nil", _)) => NONE
      | _ => raise MatchNetExhaustiveButThisIsYourFault;


fun iter_Cons_list_list trm = 
    let val x = (extract_Cons_list_list trm)
    in case x of SOME (trm1, trm2) => (Syntax.pretty_term @{context} trm1 |> Pretty.writeln; iter_Cons_list_list trm2)
                 | NONE => writeln "Nil"
    end
*}

ML {*
extract_trueprop testML |> extract_eq_rhs @{typ "char list"} "test" |> Syntax.pretty_term @{context} |> Pretty.string_of;
extract_trueprop testML |> extract_eq_rhs @{typ "char list"} "test" |> Syntax.pretty_term @{context} |> Pretty.writeln;
*}
ML {*
extract_trueprop testlistML |> extract_eq_rhs @{typ "char list list"} "test_list" |> iter_Cons_list_list;
*}

end
