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

fun extract_trueprop trm = HOLogic.dest_Trueprop trm
    (* case trm
      of Const ("HOL.Trueprop", @{typ "bool \<Rightarrow> prop"}) $ t1 => t1
      | _ => raise MatchNotExhaustiveButThisIsYourFault_extract_trueprop;*)

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
fun is_valid_char (c : char) : bool =
    (c <= #"z" andalso c >= #"a") orelse (c <= #"Z" andalso c >= #"A") orelse
    (c <= #"9" andalso c >= #"0");

fun sanitize_string (s: string) : string =
  String.map (fn c => if is_valid_char c then c else #"a") s;

sanitize_string "asdsa sjhsa saklj \"/$(Tnd 098z8    9"
*}


ML {*
fun format_dot_edges (trm: (term * term) list): string list =
  let
    val format_node = Syntax.pretty_term @{context} #> Pretty.string_of #> ATP_Util.unyxml #> sanitize_string
    fun format_dot_edge (t1, t2) = format_node t1 ^ " -> " ^ format_node t2 ^ ";"
  in
    writeln "TODO: name clashes?"; map format_dot_edge trm
  end;

fun concat_str (s:string list) : string = 
  fold (fn e => fn a  => a ^ (e^"\n")) s ("")

fun format_dot (ts: (term * term) list) : string =
  "digraph graphname {\n" ^ concat_str (format_dot_edges ts) ^ "}"


*}

ML {*
extract_trueprop testML |> extract_eq_rhs @{typ "char list"} "test" |> Syntax.pretty_term @{context} |> Pretty.string_of;
extract_trueprop testML |> extract_eq_rhs @{typ "char list"} "test" |> Syntax.pretty_term @{context} |> Pretty.writeln;
*}

ML {*
extract_trueprop testlistML |> extract_eq_rhs @{typ "(nat \<times> string) list"} "test_list" |> iter_Cons_list_list;
*}



ML {*
fun write_to_tmpfile (t: string): Path.T = 
     let 
      val p = Isabelle_System.create_tmp_path "graphviz" "graph_tmp.dot";
      val p_str = (File.platform_path p);
     in
      writeln ("using tmpfile " ^ p_str);
      File.write p (t^"\n");
      p
     end;
*}


ML {*
exception ExceptionGraphVizNotFound;
exception ExceptionViewerNotFound;

(* viz is graphiz command, e.g. dot
   viewer is a PDF viewer, e.g. xdg-open
   retuns return code of bash command *)
fun paintGraph (viewer: string) (viz: string) (f: Path.T): int =
  if (Isabelle_System.bash ("which "^viz)) <> 0 then
    raise ExceptionGraphVizNotFound
  else if (Isabelle_System.bash ("which "^viewer)) <> 0 then
    raise ExceptionViewerNotFound
  else
    let val file = (File.platform_path f);
        val filePDF = file^".pdf";
        val cmd = (viz^" -o "^filePDF^" -Tpdf "^file^" && "^viewer^" "^filePDF)
    in
      writeln ("executing: "^cmd);
      Isabelle_System.bash cmd
    end

val paintGraphDotLinux = paintGraph "xdg-open" "dot"

fun ohShitOpenFileInGedit (f: Path.T): int =
    let val file = (File.platform_path f);
        val cmd = ("gedit "^file^" &")
    in
      writeln ("executing: "^cmd);
      Isabelle_System.bash cmd
    end
*}

ML {*
val graph = "digraph graphname { \n a -> b -> c; \n b -> d; \n}";

val file = write_to_tmpfile graph;

(*paintGraphDotLinux file;*)
*}

ML {*
extract_trueprop testlistML
  |> extract_eq_rhs @{typ "(nat \<times> char list) list"} "test_list"
  |> iter_Cons_to_list
  |> map (fn trm => parse_pair @{typ "nat \<Rightarrow> string \<Rightarrow> nat \<times> string"} trm)
  |> format_dot
  |> write_to_tmpfile
  (*|> ohShitOpenFileInGedit*)
  |> paintGraphDotLinux
  (*|> writeln*)
*}

ML{*


let
val term = @{term "[(3::nat, ''asdf''), (4, ''foo'')]"}
val elems = HOLogic.dest_list term |> map HOLogic.dest_prod;

in
Syntax.pretty_term @{context} term |> Pretty.str_of |> ATP_Util.unyxml
end
*}

ML{*

*}

end
