theory MLStuff
imports Main
begin



definition "test = ''asdf''"
definition "test_list = [(3::nat, ''asdf''), (4, ''foo'')]"
thm test_list_def


ML {*
Context.theory_name @{theory}
*}

ML{*
val testML = rep_thm (@{thm test_def}) |> #prop;
val testlistML = rep_thm (@{thm test_list_def}) |> #prop;


Syntax.pretty_term @{context} testML |> Pretty.backquote |> Pretty.writeln;

exception MatchNotExhaustiveButThisIsYourFault_extract_trueprop;

fun extract_trueprop trm = 
    case trm
      of Const ("HOL.Trueprop", @{typ "bool \<Rightarrow> prop"}) $ t1 => t1
      | _ => raise MatchNotExhaustiveButThisIsYourFault_extract_trueprop;

exception extract_eq_rhs_full_name_exception
exception extract_eq_rhs_type_exception

exception MatchNotExhaustiveButThisIsYourFault_extract_eq_rhs;

fun extract_eq_rhs typ name_def trm = 
    case trm
      of (Const ("HOL.eq", _) $ Const (full_name', typ')) $ t1 => 
        let val full_name = ((Context.theory_name @{theory}) ^ "."  ^ name_def) 
        in 
          if full_name' = full_name then 
            if typ' = typ then t1 else raise extract_eq_rhs_type_exception else raise extract_eq_rhs_full_name_exception
        end
      | _ => raise MatchNotExhaustiveButThisIsYourFault_extract_eq_rhs;


exception MatchNotExhaustiveButThisIsYourFault_parse_pair;
exception parse_pair_exception;

fun parse_pair typ (trm: term) : (term * term) =
  case trm
    of Const ("Product_Type.Pair", typ') $ trm1 $ trm2 => if typ' = typ then (trm1, trm2) else raise parse_pair_exception
    | _ => raise MatchNotExhaustiveButThisIsYourFault_parse_pair


exception MatchNotExhaustiveButThisIsYourFault_extract_Cons_list_list;

fun extract_Cons_list_list trm = 
    case trm
      of (Const ("List.list.Cons", _)) $ t1 $ t2 => SOME (t1, t2)
      | (Const ("List.list.Nil", _)) => NONE
      | _ => raise MatchNotExhaustiveButThisIsYourFault_extract_Cons_list_list;


fun iter_Cons_list_list (trm: term) = 
    let val x = (extract_Cons_list_list trm)
    in case x of SOME (trm1, trm2) => (Syntax.pretty_term @{context} trm1 |> Pretty.writeln; iter_Cons_list_list trm2)
                 | NONE => writeln "Nil"
    end

(* fold-like for a Cons-term *)
fun iter_Cons_fold (f: (term * 'a) -> 'a) (a: 'a) (trm: term): 'a = 
    let val x = (extract_Cons_list_list trm)
    in case x of SOME (trm1, trm2) => f ( trm1, iter_Cons_fold f a trm2)
                 | NONE => a
    end

val iter_Cons_to_list = iter_Cons_fold (fn (trm, a) => [trm]@a) []
*}

ML {*
extract_trueprop testML |> extract_eq_rhs @{typ "char list"} "test" |> Syntax.pretty_term @{context} |> Pretty.string_of;
extract_trueprop testML |> extract_eq_rhs @{typ "char list"} "test" |> Syntax.pretty_term @{context} |> Pretty.writeln;
*}
ML {*
extract_trueprop testlistML |> extract_eq_rhs @{typ "(nat \<times> char list) list"} "test_list" |> iter_Cons_list_list;
*}
ML {*
extract_trueprop testlistML
  |> extract_eq_rhs @{typ "(nat \<times> char list) list"} "test_list"
  |> iter_Cons_to_list
  |> map (fn trm => parse_pair @{typ "nat \<Rightarrow> char list \<Rightarrow> nat \<times> char list"} trm)
  (*|> map (fn trm => writeln (@{make_string} trm))*)
  |> map (fn (trm1, trm2) => Syntax.pretty_term @{context} trm2 |> Pretty.writeln)
  (*Syntax.pretty_term @{context} trm |> Pretty.writeln*)
*}

end
