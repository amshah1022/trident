import Trident
import Trident.Common.Equiv
import Cli

open Cli
open Trident

-- Registry of all verified reference kernels
def specRegistry : List String := [
  "VectorAdd",
]

-- Define handlers BEFORE commands that reference them
def runVerify (p : Parsed) : IO UInt32 := do
  let kernelPath := p.positionalArg! "kernel" |>.as! String
  let specName   := p.flag! "against" |>.as! String
  let verbose    := p.hasFlag "verbose"
  IO.println s!"Trident — CompCert-style verification for Triton kernels"
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
      match verifyAgainstVectorAdd parsedKernel with
      | .equivalent =>
        IO.println s!"✓ Verified: {kernelPath} matches reference VectorAdd"
        IO.println s!"  Certificate: vectorAdd_correct (Lean proof term)"
        IO.println s!"  Checked {parsedKernel.length} instructions against proved reference"
        return 0
      | .notEquivalent msg =>
        IO.println s!"✗ Not equivalent: {msg}"
        IO.println s!"  Kernel does not match reference VectorAdd specification"
        return 1
      | .parseError =>
        IO.println s!"✗ Internal error during equivalence check"
        return 1
    | _ =>
      IO.println s!"✗ No checker for spec: {specName}"
      return 1

def runList (_ : Parsed) : IO UInt32 := do
  IO.println "Trident Reference Kernel Library"
  IO.println "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
  IO.println ""
  IO.println "Verified kernels (machine-checked proofs):"
  for spec in specRegistry do
    IO.println s!"  ✓ {spec}"
  IO.println ""
  IO.println "Coming soon: ReLU, Matmul, LayerNorm, Softmax, FlashAttention"
  return 0

-- Commands defined AFTER handlers
def verifyCmd : Cmd := `[Cli|
  verify VIA runVerify;
  "Verify that a Triton kernel matches a proved reference specification."
  FLAGS:
    against : String; "The reference spec to verify against (e.g. VectorAdd)"
    verbose;          "Show detailed verification steps"
  ARGS:
    kernel : String;  "Path to the .ttir kernel file to verify"
  EXTENSIONS:
    author "Trident"
]

def listCmd : Cmd := `[Cli|
  list VIA runList;
  "List all verified reference kernels in the Trident library."
]

def tridentCmd : Cmd := `[Cli|
  trident NOOP;
  "Trident: CompCert-style formal verification for Triton GPU kernels."
  SUBCOMMANDS:
    verifyCmd;
    listCmd
]

def main (args : List String) : IO UInt32 :=
  tridentCmd.validate args
