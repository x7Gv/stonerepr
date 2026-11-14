# `stonerepr`

```ml
(* Stone's Representation Theorem for Boolean Algebras *)
⊢ Φ : B ≅ Clopen (Ult B)
```

A Lean 4 formalization (`v4.34.0-rc1` + Mathlib) of the algebraic and topological machinery behind Marshall H. Stone's 1936 representation theorem, accompanying my in-progress B.Sc thesis (currently private) (*Stonen esityslause Boolen algebroille*).

---

## Structure

```text
Stonerepr/
├── Ch1/
│   ├── Algebra.lean   -- Posets, duals, order ↔ algebraic lattices, ThesisBooleanAlgebra, BooleanHom
│   ├── Filter.lean    -- ThesisFilter, HasFIP, filtGen, ThesisUltrafilter, ultrafilter characterizations
│   └── Zorn.lean      -- Zorn's lemma ⊢ ultrafilter_exists
└── Ch2/
    └── Topology.lean  -- Ult B, stoneBasis, T2Space, CompactSpace, ult_isStoneSpace, stone_representation
```

### Main Results

| Module | Declaration | Statement |
| :--- | :--- | :--- |
| `Ch1.Algebra` | `orderLatticeToAlgebraicLattice` | `OrderLattice P → AlgebraicLattice P` |
| `Ch1.Algebra` | `complement_unique` | Uniqueness of complements in `ThesisBooleanAlgebra` |
| `Ch1.Filter` | `filtGen_isProper_iff_hasFIP` | `(filtGen L S hS).IsProper ↔ HasFIP L S` |
| `Ch1.Filter` | `ultrafilter_char_1`, `_2` | `a ∈ U.carrier ↔ aᶜ ∉ U.carrier` |
| `Ch1.Zorn` | `ultrafilter_exists` | Every proper filter extends to a `ThesisUltrafilter` |
| `Ch2.Topology` | `ult_isStoneSpace` | `IsStoneSpace (Ult B)` (Hausdorff, compact, clopen basis) |
| `Ch2.Topology` | `stone_representation` | `Function.Bijective (stonePhi B)` |

---

## Build

```sh
lake exe cache get   # fetch prebuilt Mathlib .oleans
lake build
```
