theory MLStuff
imports Main
begin


definition "test_list = [(3::nat, ''asdf''), (4, ''foo'')]"
thm test_list_def


ML {*
Context.theory_name @{theory}
*}


ML {*
fun is_valid_char (c : char) : bool =
    (c <= #"z" andalso c >= #"a") orelse (c <= #"Z" andalso c >= #"A") orelse
    (c <= #"9" andalso c >= #"0");

fun sanitize_string (s: string) : string =
  String.map (fn c => if is_valid_char c then c else #"_") s;

sanitize_string "asdsa sjhsa saklj \"/$(Tnd 098z8    9"
*}


ML {*
fun format_dot_edges (tune_node_format : term -> string -> string) (trm: (term * term) list): string list =
  let
    fun format_node t = t |> Syntax.pretty_term @{context} |> Pretty.string_of |> ATP_Util.unyxml |> tune_node_format t |>  sanitize_string
    fun format_dot_edge (t1, t2) = format_node t1 ^ " -> " ^ format_node t2 ^ ";"
  in
    writeln "TODO: name clashes?"; map format_dot_edge trm
  end;

val default_tune_node_format = (fn _ => I);

fun concat_str (s:string list) : string = 
  fold (fn e => fn a  => a ^ (e^"\n")) s ("")

fun format_dot (tune_node_format : term -> string -> string) (ts: (term * term) list) : string =
  "digraph graphname {\n" ^ concat_str (format_dot_edges tune_node_format ts) ^ "}"


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
fun visualize_graph (tune_node_format : term -> string -> string) (edges: thm) =
  prop_of edges
  |> HOLogic.dest_Trueprop |> HOLogic.dest_eq |> snd
  |> HOLogic.dest_list
  |> map HOLogic.dest_prod
  |> format_dot tune_node_format
  |> write_to_tmpfile
  (*|> ohShitOpenFileInGedit*)
  |> paintGraphDotLinux
  (*|> writeln*);

(*visualize_graph default_tune_node_format @{thm test_list_def}*)
*}


end
