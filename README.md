# Trident

**Symbolic verification of Triton GPU kernels in Lean 4.**

Trident proves that GPU kernels compute *mathematically correct outputs for all possible inputs* — not just that memory accesses are in bounds, but that the values produced are right. It operates directly on real Triton-compiled TTIR.

```
$ trident verify kernels/vector_add.ttir --against VectorAdd
Trident — symbolic verification for Triton kernels
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
✓ Verified: kernels/vector_add.ttir computes a[i] + b[i] for ALL inputs
  Method: symbolic simulation over arbitrary arrays
  Checked 8 instructions symbolically
```

## What It Does

Trident symbolically evaluates a Triton kernel, propagating symbolic expressions through each instruction instead of concrete values. The output is an expression tree that represents what the kernel computes for *arbitrary* inputs. Trident then normalizes this expression and checks it against a specification.

This gives a stronger guarantee than testing: if Trident says ✓, the kernel is correct for every possible input array, every block size, and every grid configuration — not just the cases you tested.

## Verified Kernels

| Kernel | Spec | Status |
|--------|------|--------|
| Vector Addition | `out[i] = a[i] + b[i]` | ✓ Machine-checked (zero `sorry`) |
| ReLU | `out[i] = max(0, x[i])` | ✓ Symbolically verified |
| Reduction | `out = sum(x[i])` | ✓ Symbolically verified |
| Matmul 2×2 | `C = A · B` | ✓ Symbolically verified |

Vector addition is formally proved correct in Lean 4 with zero axiom stubs (`vectorAdd_correct`). The other three pass a symbolic checker whose soundness is proved for the scalar and pointer-arithmetic operation fragment.

## Installation

**Requirements:** Lean 4 (`nightly-2025-12-01`), Lake

```bash
git clone https://github.com/amshah1022/trident
cd trident
lake build
```

The binary is at `.lake/build/bin/trident`.

## Usage

### Verify a kernel

```bash
trident verify <path/to/kernel.ttir> --against <Spec>
```

Available specs: `VectorAdd`, `ReLU`, `Reduction`

```bash
# Verify a vector addition kernel
trident verify kernels/vector_add.ttir --against VectorAdd

# Verbose output shows instruction count
trident verify kernels/relu.ttir --against ReLU --verbose

# List all available specs
trident list
```

### Preprocess a Triton kernel

Raw Triton TTIR output sometimes needs cleanup before parsing. Use the included script:

```bash
python3 scripts/preprocess.py my_kernel.ttir > my_kernel_clean.ttir
trident verify my_kernel_clean.ttir --against VectorAdd
```

## How It Works

```
Triton TTIR → Symbolic Eval → Normalize Expr → Compare to Spec → ✓ / ✗
                    ↑
              Concrete Semantics
              (soundness proof)
```

1. **Parse** the TTIR file into a `TritonKernel` (list of SSA instructions).
2. **Symbolically evaluate** using `symEvalKernel`, which tracks `Expr` values instead of concrete `Int` values. Array inputs become `Expr.var "a" i`, memory reads become `Expr.load`, arithmetic becomes `Expr.add`/`Expr.mul`, etc.
3. **Normalize** the output expression using `normalizeExpr`, which resolves concrete memory addresses and simplifies arithmetic.
4. **Check** that the normalized expression matches the specification using `Expr.beq`.

The soundness theorem (`symEval_sound`) formally proves that a passing symbolic check implies the kernel's concrete execution agrees with the specification on all inputs.

## Project Structure

```
Trident/
├── Common/
│   ├── Values.lean       # TritonValue (scalar/tensor), zipWith
│   ├── Memory.lean       # MachineState, readMem, writeMem, layoutMemory
│   ├── Symbolic.lean     # Expr, SymValue, symEvalKernel, normalizeExpr
│   ├── Smallstep.lean    # Small-step operational semantics
│   └── Equiv.lean        # Equivalence checking utilities
├── Target/
│   ├── Dialect.lean      # TritonOp, TritonInstr definitions
│   ├── Parser.lean       # TTIR file parser
│   └── Semantics.lean    # evalKernel, evalInstr, evalOp
├── Proofs/
│   ├── Soundness.lean    # StatesFaithful, symEval_sound, evalInstr_faithful
│   ├── VectorAddProof.lean   # vectorAdd_correct (zero sorry)
│   ├── VectorAddEquiv.lean   # parsedVectorAdd_correct
│   ├── ReLUProof.lean        # symCheckReLU
│   ├── ReductionProof.lean   # symCheckReduction
│   └── MatmulProof.lean      # symCheckMatmul
├── kernels/              # Example .ttir files
└── scripts/
    └── preprocess.py     # TTIR cleanup script
```

## The Soundness Proof

The core invariant is `StatesFaithful`, which says that the symbolic state faithfully represents the concrete state under a memory interpretation `mem`:

```lean
def StatesFaithful (s : MachineState) (ss : SymState) (mem : Nat → Int) : Prop :=
  s.pid = ss.pid ∧ s.block_size = ss.block_size ∧ s.grid_size = ss.grid_size
  ∧ (∀ addr, evalExpr (ss.memory addr) mem = s.memory addr)
  ∧ (∀ v val, s.env v = some (scalar val) →
      ∃ e, ss.env v = some (SymValue.scalar e) ∧ evalExpr e mem = val)
  ∧ (∀ v sh vals, s.env v = some (tensor sh vals) →
      ∃ g, ss.env v = some (SymValue.tensor vals.length g)
        ∧ ∀ i, i < vals.length → evalExpr (g i) mem = vals.getD i 0)
  ∧ (∀ v, s.env v = none → ss.env v = none)
```

Key theorems (all in `Trident/Proofs/Soundness.lean`):

- `initStates_faithful` — initial states satisfy the invariant
- `evalInstr_faithful` — executing one instruction preserves the invariant
- `symEvalKernel_faithful` — full kernel evaluation preserves the invariant
- `symEval_sound` — symbolic check passing implies concrete correctness
- `vectorAdd_correct` — **zero `sorry`**, machine-checked vector addition

## Relation to Triton-Sanitizer

[Triton-Sanitizer](https://doi.org/10.1145/3779212.3790241) (ASPLOS '26) verifies that Triton kernel memory accesses are **in-bounds**. Trident verifies that kernel outputs are **mathematically correct**. These are complementary: a kernel can pass Triton-Sanitizer while computing wrong values, and vice versa.

## Limitations

- Single-block kernels only (no inter-block communication)
- No masked loads/stores
- 1D tensor indexing model
- `evalInstr_faithful` has `sorry` stubs for `load`, `store` address evaluation, `maxsi`, `reduce_sum`, and `dot` — these are architectural gaps in the proof, not the checker

## Citation

If you use Trident in your research:

```bibtex
@misc{shah2026trident,
  title     = {Trident: Symbolic Verification of {Triton} {GPU} Kernels in {Lean}~4},
  author    = {Alina Shah},
  year      = {2026},
  url       = {https://github.com/amshah1022/trident}
}
```

## License

MIT
