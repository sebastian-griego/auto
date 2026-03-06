import Lean

open Lean Elab Command

namespace AutoformalizationEval.Tools

def jsonPrefix : String := "AUTOFORM_JSON:"

def emitJsonLine (payload : Json) : CommandElabM Unit := do
  liftIO <| IO.println s!"{jsonPrefix}{Json.compress payload}"

private def appendNamePart (root : Name) (part : String) : Name :=
  match part.toNat? with
  | some n => Name.num root n
  | none => Name.str root part

def parseDottedName (text : String) : Name :=
  (text.splitOn ".").foldl (init := Name.anonymous) fun acc part =>
    if part.isEmpty then acc else appendNamePart acc part

private def nameParts : Name → List String
  | .anonymous => []
  | .str parent s => nameParts parent ++ [s]
  | .num parent n => nameParts parent ++ [toString n]

def nameHasRootPrefix (name root : Name) : Bool :=
  let nameList := nameParts name
  let rootList := nameParts root
  rootList.length ≤ nameList.length && rootList == nameList.take rootList.length

def relativeToRootString (name root : Name) : String :=
  if !nameHasRootPrefix name root then
    toString name
  else
    let rel := (nameParts name).drop (nameParts root).length
    String.intercalate "." rel

private def appendNameParts (root : Name) (parts : List String) : Name :=
  parts.foldl (init := root) appendNamePart

def replaceRootPrefix (name oldRoot newRoot : Name) : Name :=
  if !nameHasRootPrefix name oldRoot then
    name
  else
    let rel := (nameParts name).drop (nameParts oldRoot).length
    appendNameParts newRoot rel

def isInternalOrAuxName (name : Name) : Bool :=
  name.isInternalDetail || name.isImplementationDetail

private partial def collectConstNamesAux (e : Expr) (acc : Std.HashSet Name) : Std.HashSet Name :=
  match e with
  | .const name _ => acc.insert name
  | .app fn arg => collectConstNamesAux arg (collectConstNamesAux fn acc)
  | .lam _ ty body _ => collectConstNamesAux body (collectConstNamesAux ty acc)
  | .forallE _ ty body _ => collectConstNamesAux body (collectConstNamesAux ty acc)
  | .letE _ ty val body _ =>
      collectConstNamesAux body (collectConstNamesAux val (collectConstNamesAux ty acc))
  | .mdata _ body => collectConstNamesAux body acc
  | .proj _ _ body => collectConstNamesAux body acc
  | _ => acc

def collectConstNames (e : Expr) : Array Name :=
  (collectConstNamesAux e ({} : Std.HashSet Name)).toList.toArray

def containsSorryAx (e : Expr) : Bool :=
  (collectConstNames e).any (fun n => n == ``sorryAx)

def declKindTag : ConstantInfo → String
  | .thmInfo _ => "thmInfo"
  | .defnInfo _ => "defnInfo"
  | .opaqueInfo _ => "opaqueInfo"
  | .axiomInfo _ => "axiomInfo"
  | .quotInfo _ => "quotInfo"
  | .inductInfo _ => "inductInfo"
  | .ctorInfo _ => "ctorInfo"
  | .recInfo _ => "recInfo"

def sortStrings (values : Array String) : Array String :=
  values.qsort (· < ·)

def dedupSortedStrings (values : Array String) : Array String := Id.run do
  let mut out : Array String := #[]
  let mut last : Option String := none
  for value in values do
    if last != some value then
      out := out.push value
      last := some value
  return out

def sortUniqueStrings (values : Array String) : Array String :=
  dedupSortedStrings (sortStrings values)

end AutoformalizationEval.Tools
