(* Export native kernel terms. No parsing of printed formulas or case-specific rules. *)
(* A compiler-checked bridge, not an unsafe runtime cast. The candidate value is
   supplied through a private lookup namespace; no model identifier is spliced
   into executable text. This structure is loaded only after source execution. *)
structure NativeHOLBindingInspection =
struct
  val captured : Thm.thm option ref = ref NONE
  fun accept (theorem : Thm.thm) = captured := SOME theorem
end;

local
  fun quote s = "\"" ^ String.translate
    (fn #"\"" => "\\\"" | #"\\" => "\\\\" | #"\n" => "\\n"
      | #"\r" => "\\r" | #"\t" => "\\t" | c => str c) s ^ "\"";
  fun array f xs = "[" ^ String.concatWith "," (map f xs) ^ "]";
  fun obj fields = "{" ^ String.concatWith "," (map (fn (k,v) => quote k ^ ":" ^ v) fields) ^ "}";
  fun tyJSON ty =
    if Type.is_vartype ty then
      obj [("kind",quote "type_variable"),("name",quote (Type.dest_vartype ty))]
    else let val {Thy,Tyop,Args} = Type.dest_thy_type ty
         in obj [("kind",quote "type_application"),("theory",quote Thy),
                 ("name",quote Tyop),("arguments",array tyJSON Args)] end;
  fun tmJSON tm =
    if Term.is_var tm then
      let val (name,ty) = Term.dest_var tm
      in obj [("kind",quote "variable"),("name",quote name),("type",tyJSON ty)] end
    else if Term.is_const tm then
      let val {Thy,Name,Ty} = Term.dest_thy_const tm
      in obj [("kind",quote "constant"),("theory",quote Thy),("name",quote Name),("type",tyJSON Ty)] end
    else if Term.is_comb tm then
      let val (f,x) = Term.dest_comb tm
      in obj [("kind",quote "application"),("function",tmJSON f),("argument",tmJSON x)] end
    else let val (v,body) = Term.dest_abs tm
         in obj [("kind",quote "abstraction"),("variable",tmJSON v),("body",tmJSON body)] end;
  fun theoremJSON (name,th) =
    let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
        val location =
          case List.find (fn ((_,nm),_) => nm = name) (DB.thy (current_theory ())) of
            NONE => "null"
          | SOME (_,(_,info)) =>
              (case #loc info of
                 DB.Unknown => "null"
               | DB.Located {scriptpath,linenum,exact} =>
                   obj [("file",quote scriptpath),("line",Int.toString linenum),
                        ("exact",Bool.toString exact)])
    in obj [("name",quote name),("conclusion",tmJSON (Thm.concl th)),
            ("hypotheses",array tmJSON (Thm.hyp th)),
            ("oracles",array quote oracles),("axiom_dependencies",array quote axioms),
            ("source_location",location)] end;
  val namespace = PolyML.globalNameSpace;
  val sourcePath = OS.FileSys.fullPath "source.sml";
  fun declaredAt properties =
    List.mapPartial (fn PolyML.PTdeclaredAt loc => SOME loc | _ => NONE) properties;
  fun fromSource (loc : PolyML.location) =
    #file loc <> "" andalso
    ((OS.FileSys.fullPath (#file loc) = sourcePath) handle OS.SysErr _ => false);
  fun sourceLocation properties = List.find fromSource (declaredAt properties);
  (* Follow source-declared structures too; library structures are not scanned. *)
  fun bindings prefix (ns : PolyML.NameSpace.nameSpace) =
    List.mapPartial (fn (name,value) =>
      case sourceLocation (PolyML.NameSpace.Values.properties value) of
        NONE => NONE | SOME loc => SOME (prefix ^ name,value,loc)) (#allVal ns ())
    @ List.concat (List.mapPartial (fn (name,value) =>
        case sourceLocation (PolyML.NameSpace.Structures.properties value) of
          NONE => NONE
        | SOME _ => SOME (bindings (prefix ^ name ^ ".")
                          (PolyML.NameSpace.Structures.contents value))) (#allStruct ns ()));
  fun asTheorem value =
    let
      val _ = NativeHOLBindingInspection.captured := NONE;
      val ns : PolyML.NameSpace.nameSpace =
        {allFix = #allFix namespace, allFunct = #allFunct namespace,
         allSig = #allSig namespace, allStruct = #allStruct namespace,
         allType = #allType namespace, allVal = #allVal namespace,
         enterFix = fn _ => (), enterFunct = fn _ => (),
         enterSig = fn _ => (), enterStruct = fn _ => (),
         enterType = fn _ => (), enterVal = fn _ => (),
         lookupFix = #lookupFix namespace, lookupFunct = #lookupFunct namespace,
         lookupSig = #lookupSig namespace, lookupStruct = #lookupStruct namespace,
         lookupType = #lookupType namespace,
         lookupVal = fn name => if name = "candidate" then SOME value
                               else #lookupVal namespace name};
      val input = TextIO.openString
        "val _ = NativeHOLBindingInspection.accept (candidate : Thm.thm);";
      val compiled =
        (SOME (PolyML.compiler (fn () => TextIO.input1 input,
           [PolyML.Compiler.CPNameSpace ns,
            PolyML.Compiler.CPOutStream (fn _ => ()),
            PolyML.Compiler.CPErrorMessageProc (fn _ => ())]))
         handle Fail _ => NONE);
      val _ = TextIO.closeIn input;
    in case compiled of
         NONE => NONE
       | SOME run => (run (); !(NativeHOLBindingInspection.captured))
    end;
  val candidates = bindings "" namespace;
  val theoremValues = List.mapPartial (fn (name,value,loc) =>
    case asTheorem value of NONE => NONE | SOME th => SOME (name,th,loc)) candidates;
  fun locationJSON (loc : PolyML.location) =
    obj [("file",quote (#file loc)),("line",Int.toString (#startLine loc)),
         ("exact","true"),("provider",quote "PolyML.PTdeclaredAt")];
  fun valueJSON (name,th,loc) =
    let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
    in obj [("name",quote name),("conclusion",tmJSON (Thm.concl th)),
            ("hypotheses",array tmJSON (Thm.hyp th)),
            ("oracles",array quote oracles),("axiom_dependencies",array quote axioms),
            ("source_location",locationJSON loc),("origin",quote "ML theorem binding")]
    end;
  fun valueReport (name,th,loc) =
    let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
    in obj [("name",quote name),("statement",quote (Parse.thm_to_string th)),
            ("hypotheses",array (quote o Parse.term_to_string) (Thm.hyp th)),
            ("oracles",array quote oracles),("axiom_dependencies",array quote axioms),
            ("source_location",locationJSON loc)]
    end;
  val theory = current_theory ();
  (* Definitions of the library constants the theory uses (and of the library constants those definitions use, up to
     400 definitions), so a checker can give them their meaning instead of treating them as unknown symbols. A
     library definition is one whose conjuncts define the constant: the head of an equation's left side. *)
  val ownThms = map snd (DB.axioms theory) @ map snd (DB.definitions theory) @ map snd (DB.theorems theory)
                @ map (fn (_,th,_) => th) theoremValues;
  val skipThys = [theory, "bool", "min"];
  fun constNames th =
    List.map (fn c => let val {Thy,Name,...} = Term.dest_thy_const c in (Thy,Name) end)
      (HolKernel.find_terms Term.is_const (Thm.concl th));
  fun lhsHeadName t =
    let val t' = snd (boolSyntax.strip_forall t)
    in if boolSyntax.is_eq t' then
         let val h = fst (boolSyntax.strip_comb (boolSyntax.lhs t'))
         in if Term.is_const h then SOME (#Name (Term.dest_thy_const h)) else NONE end
       else NONE end;
  fun defines name th =
    List.exists (fn cj => lhsHeadName cj = SOME name)
      (boolSyntax.strip_conj (snd (boolSyntax.strip_forall (Thm.concl th))));
  fun libDefs (pending, seen, found) =
    case pending of
      [] => found
    | (thy,name)::rest =>
        if length found >= 400 orelse List.exists (fn x => x = (thy,name)) seen
           orelse List.exists (fn x => x = thy) skipThys then libDefs (rest, (thy,name)::seen, found)
        else
          let val ds = (List.filter (fn (_,th) => defines name th) (DB.definitions thy)) handle _ => []
              val newDs = List.filter (fn (dn,_) => not (List.exists (fn (t,n,_) => t = thy andalso n = dn) found)) ds
              val more = List.concat (map (fn (_,th) => constNames th) newDs)
          in libDefs (rest @ more, (thy,name)::seen, found @ map (fn (dn,th) => (thy,dn,th)) newDs) end;
  val libraryDefs = libDefs (List.concat (map constNames ownThms), [], []);
  (* A library built on axioms (such as the deontic library's Carmo-Jones axioms) needs them too; HOL4's own
     theories are definitional and have none. *)
  val libThys = List.foldl (fn (t, acc) => if List.exists (fn x => x = t) acc then acc else t :: acc) []
    (List.filter (fn t => not (List.exists (fn x => x = t) skipThys))
      (map #1 (List.concat (map constNames ownThms)) @ map #1 libraryDefs));
  val libraryAxioms = List.concat (map (fn t => (map (fn (an,th) => (t,an,th)) (DB.axioms t)) handle _ => []) libThys);
  fun libJSON (thy,dn,th) =
    obj [("name",quote (thy ^ "$" ^ dn)),("conclusion",tmJSON (Thm.concl th))];
  val output = TextIO.openOut "kernel_ast.json";
  val bindingOutput = TextIO.openOut "kernel_binding_report.json";
in
  val _ = TextIO.output (output,
    obj [("theory",quote theory),
         ("axioms",array theoremJSON (DB.axioms theory)),
         ("definitions",array theoremJSON (DB.definitions theory)),
         ("theorems",array theoremJSON (DB.theorems theory)),
         ("theorem_values",array valueJSON theoremValues),
         ("library_definitions",array libJSON libraryDefs),
         ("library_axioms",array libJSON libraryAxioms),
         ("binding_inspection",obj [
           ("method",quote "PolyML native namespace, declaration locations, compiler-checked Thm.thm bridge"),
           ("source_value_candidates",Int.toString (length candidates)),
           ("theorem_value_count",Int.toString (length theoremValues)),
           ("scope",quote "Final visible scalar theorem bindings declared in source.sml, including source-declared structures; shadowed, discarded, and container-held values are not captured")])]);
  val _ = TextIO.closeOut output;
  val _ = TextIO.output (bindingOutput,array valueReport theoremValues);
  val _ = TextIO.closeOut bindingOutput;
end;
