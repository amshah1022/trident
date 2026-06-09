import Trident.Machine

namespace Trident

-- This fixes the dotted identifier errors completely!
open TritonValue

def evalOp (op : TritonOp) (args : List String) (state : MachineState) : Option TritonValue :=
  match op with

  | .get_program_id _ =>
      some (scalar (Int.ofNat state.pid))

  | .constant v =>
      some (scalar v)

  | .make_range =>
      let rangeList := List.range state.block_size |>.map Int.ofNat
      some (tensor [state.block_size] rangeList)

  | .splat =>
      match args with
      | [scalarVar] =>
          match state.env scalarVar with
          | some (scalar v) =>
              let splatList := List.replicate state.block_size v
              some (tensor [state.block_size] splatList)
          | _ => none
      | _ => none

  | .addptr =>
      match args with
      | [ptrVar, offsetVar] =>
          match state.env ptrVar, state.env offsetVar with
          | some (scalar p), some (scalar o) =>
              some (scalar (p + o))

          | some (scalar p), some (tensor shape offsets) =>
              let newAddresses := offsets.map (fun o => p + o)
              some (tensor shape newAddresses)

          | some (tensor shape1 ptrs), some (tensor shape2 offsets) =>
              if shape1 == shape2 then
                let zipped := List.zip ptrs offsets
                let newAddresses := zipped.map (fun (p, o) => p + o)
                some (tensor shape1 newAddresses)
              else none
          | _, _ => none
      | _ => none
  -- 6. tt.load: Reads values out of virtual memory using pointers
  | .load =>
      match args with
      | [ptrVar] =>
          match state.env ptrVar with
          -- Case A: Loading from a single scalar pointer
          | some (scalar p) =>
              -- Look up the pointer address in our virtual memory mapping
              let fetchedValue := state.memory p.natAbs
              some (scalar fetchedValue)

          -- Case B: Loading an entire tensor block of pointers at once!
          | some (tensor shape ptrs) =>
              -- Read from virtual memory for every single address pointer in the tile
              let fetchedTile := ptrs.map (fun p => state.memory p.natAbs)
              some (tensor shape fetchedTile)

          | _ => none
      | _ => none

  | _ => none

/-
The Memory Safety Specification.
This defines a strict mathematical truth condition (Prop) for Triton loads.
-/
def IsSafeLoad (ptrVar : String) (bufferSize : Nat) (state : MachineState) : Prop :=
  match state.env ptrVar with
  -- Case A: If it's a scalar pointer, its address must be strictly within the buffer bounds
  | some (scalar p) => p.natAbs < bufferSize

  -- Case B: If it's a tensor block of pointers, EVERY SINGLE pointer address
  -- in that tile must be strictly within the buffer bounds!
  | some (tensor _ ptrs) => ∀ p ∈ ptrs, p.natAbs < bufferSize

  -- If the pointer variable doesn't exist in the environment, it's inherently unsafe
  | none => False

end Trident
