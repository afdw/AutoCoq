theory Acceptor
  imports Main "Nano_JSON.Nano_JSON"
  keywords "accept" :: diag
begin

ML\<open>
open Nano_Json_Type

fun sort_of_json (STRING sort) = sort
  | sort_of_json json = error ("unknown sort: " ^ @{make_string} json)

fun typ_of_json (ARRAY [STRING "Type", STRING name, ARRAY typs_json]) =
      Type (name, typs_json |> List.map typ_of_json)
  | typ_of_json (ARRAY [STRING "TFree", STRING name, ARRAY sorts_json]) =
      TFree (name, sorts_json |> List.map sort_of_json)
  | typ_of_json (ARRAY [STRING "TVar",
                        ARRAY [STRING name, NUMBER (INTEGER index)],
                        ARRAY sorts_json]) =
      TVar ((name, index), sorts_json |> List.map sort_of_json)
  | typ_of_json json = error ("unknown typ: " ^ @{make_string} json)

fun term_of_json (ARRAY [STRING "Const", STRING name, typ_json]) =
      Const (name, typ_json |> typ_of_json)
  | term_of_json (ARRAY [STRING "Free", STRING name, typ_json]) =
      Free (name, typ_json |> typ_of_json)
  | term_of_json (ARRAY [STRING "Var",
                         ARRAY [STRING name, NUMBER (INTEGER index)],
                         typ_json]) =
      Var ((name, index), typ_json |> typ_of_json)
  | term_of_json (ARRAY [STRING "Bound", NUMBER (INTEGER i)]) =
      Bound i
  | term_of_json (ARRAY [STRING "Abs", STRING name, typ_json, term_json]) =
      Abs (name, typ_json |> typ_of_json, term_json |> term_of_json)
  | term_of_json (ARRAY [STRING "op $", fn_json, arg_json]) =
      (term_of_json fn_json) $ (term_of_json arg_json)
  | term_of_json json = error ("unknown term: " ^ @{make_string} json)

fun accept_cmd st input = (
  let
    val ctxt = Toplevel.context_of st;
    val input_json = Nano_Json_Parser.json_of_string input;
    val term = term_of_json input_json
    val term_string = Syntax.string_of_term (Config.put show_types true ctxt) term
  in
    writeln term_string;
    Thm.cterm_of ctxt term |> ignore;
    Output.information (
      Active.sendback_markup_properties
        []
        (cat_lines [
          "lemma \"" ^ term_string ^ "\"",
          "  try",
          "  sorry"
        ])
    )
  end;
  ()
)

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>accept\<close> "accept external goal"
    (Parse.embedded >> (fn input =>
      Toplevel.keep (fn st => accept_cmd st input)))
\<close>

end
