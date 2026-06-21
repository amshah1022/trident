import Trident.Target.Dialect

namespace Trident

def parseOp (opName : String) (rest : List String := []) : Option TritonOp :=
  match opName with
  | "tt.make_range" =>
    let sz := match rest with
      | "{end" :: "=" :: szStr :: _ => szStr.toNat?
      | _ => none
    some (.make_range sz)
  | "tt.splat" =>
    let shapeTok := rest.reverse.find? (fun t => t.startsWith "tensor<") |>.getD ""
    let shape := ((shapeTok.splitOn "<").getD 1 "").splitOn "x"
      |>.takeWhile (fun t => t.toNat?.isSome) |>.filterMap (·.toNat?)
    some (.splat shape)
  | "tt.addptr"         => some .addptr
  | "tt.load" => some .load
  | "tt.store" => some .store
  | "tt.get_program_id" =>
    let axis := match rest with
      | "y" :: _ => 1
      | _        => 0
    some (.get_program_id axis)
  | "tt.expand_dims" =>
    let axis := match rest with
      | _ :: "{axis" :: "=" :: axisStr :: _ => axisStr.toNat?.getD 0
      | _ => 0
    some (.expand_dims axis)
  | "tt.broadcast" =>
    let shapeTok := rest.reverse.find? (fun t => t.startsWith "tensor<") |>.getD ""
    let shape := ((shapeTok.splitOn "<").getD 1 "").splitOn "x"
      |>.takeWhile (fun t => t.toNat?.isSome) |>.filterMap (·.toNat?)
    some (.broadcast shape)
  | "tt.dot"            => some .dot
  | "tt.reduce_sum" => some (.reduce_sum 0)
  | "tt.reduce_max" => some (.reduce_max 0)
  | "arith.constant" =>
    if rest.any (fun t => t.startsWith "dense<") then
      let denseTok := rest.find? (fun t => t.startsWith "dense<") |>.getD ""
      let valStr := ((denseTok.splitOn "<").getD 1 "").splitOn ">" |>.head?.getD ""
      let shapeTok := rest.reverse.find? (fun t => t.startsWith "tensor<") |>.getD ""
      let shape := ((shapeTok.splitOn "<").getD 1 "").splitOn "x"
        |>.takeWhile (fun t => t.toNat?.isSome) |>.filterMap (·.toNat?)
      some (.constant_tensor (valStr.toInt?.getD 0) shape)
    else
      let val := rest.filter (fun t => t.toInt?.isSome) |>.head? |>.bind String.toInt?
      some (.constant (val.getD 0))
  | "arith.cmpi"        =>
      -- extract the predicate (slt, sle, sgt, sge, eq, ne)
      let pred := rest.head? |>.getD ""
      match pred with
      | "slt," => some .cmpi_slt
      | "sle," => some .cmpi_sle
      | "sgt," => some .cmpi_sgt
      | "sge," => some .cmpi_sge
      | "eq,"  => some .cmpi_eq
      | "ne,"  => some .cmpi_ne
      | _      => some .cmpi_slt  -- default
  | "arith.cmpf"        =>
      -- treat all float comparisons as cmpi_sge for now (integer model)
      some .cmpi_sge
  | "arith.select"      => some .select
  | "arith.addi"        => some .addi
  | "arith.subi"        => some .subi
  | "arith.muli"        => some .muli
  | "arith.divsi"       => some .divsi
  | "arith.addf"        => some .addf
  | "arith.mulf"        => some .mulf
  | "arith.minsi" => some .minsi
  | "arith.remsi" => some .remsi
  | "arith.truncf" => some .truncf
  | "arith.andi" => some .andi
  | "arith.subf" => some .subf
  | "arith.divf" => some .divf
  | "math.exp" => some .expf
  | _                   => none

def isSSAVar (s : String) : Bool := s.startsWith "%"
def stripPercent (s : String) : String :=
  let s := if s.endsWith "," then s.dropRight 1 else s
  if s.startsWith "%" then s.drop 1 |>.toString else s

def parseLine (line : String) : Option TritonInstr :=
  let tokens := line.splitOn " " |>.filter (· != "")
  match tokens with
  | [] => none
  | first :: rest =>
    if isSSAVar first then
      match rest with
      | "=" :: opName :: remaining =>
        match parseOp opName remaining with
        | none => none
        | some op =>
          let args := remaining.filter isSSAVar |>.map stripPercent
          some { result := stripPercent first, op := op, args := args }
      | _ => none
    else
      match parseOp first rest with
      | none => none
      | some op =>
        let args := rest.filter isSSAVar |>.map stripPercent
        some { result := "_", op := op, args := args }

def parseKernelVerbose (src : String) : Except String TritonKernel :=
  let lines := src.splitOn "\n"
    |>.map (fun l => l.trim)
    |>.filter (fun l => !l.isEmpty && !l.startsWith "//" &&
                        !l.startsWith "func" && !l.startsWith "}" &&
                        !l.startsWith "module" && !l.startsWith "tt.return" &&
                        !l.startsWith "#" && !l.startsWith "attributes" &&
                        !l.startsWith "tt.func" &&
                        -- skip parameter declaration lines:
                        -- these start with % but have no = (SSA assignments always have =)
                        !(l.startsWith "%" && !l.contains " = "))
  let rec go : List String → Nat → Except String TritonKernel
    | [], _ => .ok []
    | l :: ls, n =>
      match parseLine l with
      | none => .error s!"Parse error on line {n}: {l}"
      | some instr =>
        match go ls (n + 1) with
        | .error e => .error e
        | .ok rest => .ok (instr :: rest)
  go lines 1

def parseKernel (src : String) : Option TritonKernel :=
  match parseKernelVerbose src with
  | .ok k => some k
  | .error _ => none

end Trident
