# Lean 4 Cyclic Proof System

This is a Lean 4 port of the cyclic proof machinery from `../cyclic` (Coq/Rocq).

## Architecture

```
Scidonia/Cyclic/
├── Graph/FiniteDigraph.lean        # Finite directed graphs with reachability & SCCs
├── Preproof/Preproof.lean          # Graph-shaped derivations with local correctness
├── Progress/Ranking.lean           # Ranking-based global soundness condition
├── Syntax/
│   ├── StrictPos.lean              # Strictly-positive inductive signatures
│   └── Term.lean                   # CIC-like term syntax (de Bruijn indices)
└── Cyclic.lean                     # Root module
```

## Key Concepts

**Cyclic Proofs = Finite Graph + Local Correctness + Global Progress**

1. **FiniteDigraph**: Finite directed graphs over a vertex type V with closure properties
2. **Preproof**: Graph + node labels (judgements) + locally correct rule instances
3. **Ranking Condition**: Well-founded measure ensuring cycles make progress
4. **Term Syntax**: CIC-style terms with Π-types, λ, fixpoints, and inductives

## Building

```bash
lake build
```

## LSP Setup (OpenCode)

The project is configured in `~/.config/opencode/opencode.json` with:
- **Lean LSP**: `lake serve` for `.lean` files
- **lean-lsp-mcp**: MCP server via `uvx lean-lsp-mcp`

## Status

✅ Core graph & preproof structures ported
✅ Ranking-based progress condition
✅ CIC-like term syntax with de Bruijn indices
⚠️  One `sorry` in StrictPos.lookupCtor_lt (proof omitted for now)
🔜 TODO: Typing judgement, bisimulation, fold/refold transformations

## Differences from Coq Version

1. **Lean 4.28 Changes**:
   - `lemma` → `theorem` (keyword removed in 4.28)
   - `List.get?` → array notation `xs[n]?`
   - `deriving DecidableEq` removed from recursive `Tm` type

2. **Representation**:
   - Lists instead of `gset` (stdpp finite sets)
   - Native Lean 4 inductives instead of Coq's `Inductive`

3. **Libraries**:
   - Uses Batteries (std4) instead of stdpp
   - No Autosubst (substitution defined directly)

## Next Steps

1. Port typing judgement from `../cyclic/theories/Judgement/Typing.v`
2. Add bisimulation for proof equivalence
3. Implement fold/refold transformations
4. Connect to semantic interpretation
