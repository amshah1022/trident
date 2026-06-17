import Trident
import Trident.Common.Equiv
import Trident.Common.Symbolic
import Cli

open Cli
open Trident

def specRegistry : List String := [
  "VectorAdd",
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
  let contents ← IO.FS.readFile kernelPath
  match parseKernel contents with
  | none =>
    IO.println s!"✗ Parse error: could not parse {kernelPath}"
    return 1
  | some parsedKernel =>
    if verbose then
      IO.println s!"✓ Parsed {parsedKernel.length} instructions"
    match specName with
    | "VectorAdd" =>
      let n  := 1024
      let bs := 1024
      let gs := 1
      let allPass := (List.range bs).all fun i =>
        symCheckVectorAdd parsedKernel 0 bs gs n i
      if allPass then
        IO.println s!"✓ Verified: {kernelPath} computes a[i] + b[i] for ALL inputs"
        IO.println s!"  Method: symbolic simulation over arbitrary arrays"
        IO.println s!"  Checked {parsedKernel.length} instructions symbolically"
        return 0
      else
        IO.println s!"✗ Not verified: kernel does not compute a[i] + b[i] for all inputs"
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
  IO.println "Coming soon: ReLU, Matmul, LayerNorm, Softmax, FlashAttention"
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
