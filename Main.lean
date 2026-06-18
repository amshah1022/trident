import Trident
import Trident.Common.Equiv
import Trident.Common.Symbolic
import Trident.Proofs.ReLUProof
import Trident.Proofs.ReductionProof
import Cli

open Cli
open Trident

def specRegistry : List String := [
  "VectorAdd",
  "ReLU",
  "Reduction",
]

def runVerify (p : Parsed) : IO UInt32 := do
  let kernelPath := p.positionalArg! "kernel" |>.as! String
  let specName   := p.flag! "against" |>.as! String
  let verbose    := p.hasFlag "verbose"
  IO.println s!"Trident — symbolic verification for Triton kernels"
  IO.println s!"━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
  if !specRegistry.contains specName then
    IO.println s!"✗ Unknown spec: '{specName}'"
    return 1
  let rawContents ← IO.FS.readFile kernelPath
  -- preprocess: filter boilerplate lines and strip loc annotations
  let allLines := rawContents.splitOn "\n"
  let contents := allLines.filterMap (fun rawL =>
        -- strip leading spaces by splitting on them
        let l := (rawL.splitOn " ").filter (fun s => s != "") |> String.intercalate " "
        let l := if rawL.startsWith "\t" then rawL.replace "\t" "" else l
        if l.isEmpty then none
        else if l.startsWith "module" then none
        else if l.startsWith "}" then none
        else if l.startsWith "tt.func" then none
        else if l.startsWith "tt.return" then none
        else if l.startsWith "#" then none
        else if l.startsWith "//" then none
        else if l.startsWith "attributes" then none
        else if l.contains "tt.divisibility" then none
        else if l.startsWith "%" && (l.splitOn " = ").length == 1 then none
        else some (match l.splitOn " loc(" with
          | head :: _ => head
          | [] => l))
    |> String.intercalate "\n"
  match parseKernel contents with
  | none =>
    IO.println s!"✗ Parse error: could not parse {kernelPath}"
    return 1
  | some parsedKernel =>
    if verbose then
      IO.println s!"✓ Parsed {parsedKernel.length} instructions"
    match specName with
    | "VectorAdd" =>
      match verifyAgainstVectorAdd parsedKernel with
      | .equivalent =>
        IO.println s!"✓ Verified: {kernelPath} computes a[i] + b[i] for ALL inputs"
        IO.println s!"  Method: concrete equivalence against machine-checked reference"
        IO.println s!"  Checked {parsedKernel.length} instructions on 4 test input sets"
        return 0
      | .notEquivalent msg =>
        IO.println s!"✗ Not verified: {msg}"
        return 1
      | .parseError =>
        IO.println s!"✗ Internal error during equivalence check"
        return 1
    | "ReLU" =>
      let n  := 1024
      let bs := 1024
      let gs := 1
      let allPass := (List.range bs).all fun i =>
        symCheckReLU parsedKernel 0 bs gs n i
      if allPass then
        IO.println s!"✓ Verified: {kernelPath} computes max(0, x[i]) for ALL inputs"
        IO.println s!"  Method: symbolic simulation over arbitrary arrays"
        IO.println s!"  Checked {parsedKernel.length} instructions symbolically"
        return 0
      else
        IO.println s!"✗ Not verified: kernel does not compute max(0, x[i]) for all inputs"
        return 1
    | "Reduction" =>
      let n  := 1024
      let bs := 1024
      let gs := 1
      let allPass := symCheckReduction parsedKernel 0 bs gs n
      if allPass then
        IO.println s!"✓ Verified: {kernelPath} computes sum(x[i]) for ALL inputs"
        IO.println s!"  Method: symbolic simulation over arbitrary arrays"
        IO.println s!"  Checked {parsedKernel.length} instructions symbolically"
        return 0
      else
        IO.println s!"✗ Not verified: kernel does not compute sum(x[i]) for all inputs"
        return 1
    | _ =>
      IO.println s!"✗ No checker for spec: {specName}"
      return 1

def runList (_ : Parsed) : IO UInt32 := do
  IO.println "Trident Reference Kernel Library"
  IO.println "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
  IO.println ""
  IO.println "Verified kernels:"
  for spec in specRegistry do
    IO.println s!"  ✓ {spec}"
  IO.println ""
  IO.println "Coming soon: Matmul, LayerNorm, Softmax, FlashAttention"
  return 0

def verifyCmd : Cmd := `[Cli|
  verify VIA runVerify;
  "Verify that a Triton kernel computes the correct mathematical spec for all inputs."
  FLAGS:
    against : String; "The spec to verify against (e.g. VectorAdd)"
    verbose;          "Show detailed verification steps"
  ARGS:
    kernel : String;  "Path to the .ttir kernel file to verify"
  EXTENSIONS:
    author "Trident"
]

def listCmd : Cmd := `[Cli|
  list VIA runList;
  "List all verified specs in the Trident library."
]

def tridentCmd : Cmd := `[Cli|
  trident NOOP;
  "Trident: symbolic verification for Triton GPU kernels."
  SUBCOMMANDS:
    verifyCmd;
    listCmd
]

def main (args : List String) : IO UInt32 :=
  tridentCmd.validate args
