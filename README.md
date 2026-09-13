# Counting Stable Matchings — Lean 4 formalization

**Author:** Huibo Xu  
**Affiliation:** Nanyang Technological University

This repository contains the machine-checked Lean 4 development for two
extremal counting results about strict, complete stable-marriage instances.

## The problem and the result

Let `SM(n)` be the largest number of stable matchings that a single instance
with `n` participants on each side can admit. Determining the exponential
growth of `SM(n)` is a long-standing problem posed by Knuth. The previous
published upper bound was `3.55^n + O(1)`. This development proves, for every
`n >= 1`,

```text
SM(n) < (2078 / 625)^n = 3.3248^n.
```

Thus the repository formally verifies the new upper-bound result addressed by
the project. It does **not** claim to determine the exact exponential growth
rate, which remains open.

The development also proves the sharp stable-pair bound

```text
|Stab(I)|^4 <= 2^m,
```

where `m` is the number of pairs that occur in at least one stable matching.
Equivalently, `|Stab(I)| <= 2^(m/4)`. The intrinsic equality structure is also
formalized: equality is characterized by independent binary blocks covering
the participants, and every subset of blocks is realized by a unique stable
matching.

## What is machine checked

- The strict, complete preference model and stability predicate.
- The one-sided entropy and geometric-window chain.
- The rotation-boundary charging argument and its exact constant certificate.
- Replication, which converts the large-size estimate into the theorem for all
  `n >= 1`.
- The fixed-edge/fixed-coordinate fiber bound.
- The labeled multigraph matching theorem, hypergraph shrinking theorem, and
  omitted-incidence accounting used for the stable-pair result.
- The application of these combinatorial theorems to actual stable-matching
  states, including the intrinsic equality classification and Boolean-block
  realization.

The audited public theorems have no unresolved analytic, probabilistic, or
combinatorial hypotheses. Their axiom dependencies are contained in Lean and
Mathlib's standard logical foundations: `propext`, `Classical.choice`, and
`Quot.sound`.

## Reproduce

The project pins Lean `v4.32.2` and Mathlib commit
`905b95818eb32af7874a58b427f50c1711a5e96c`.

From PowerShell 7:

```powershell
cd lean_e2e
lake update
lake exe cache get
cd ..
./audit/RunAudit.ps1
```

The audit builds the complete dependency graph, checks the headline and
stable-pair endpoints, prints their axiom dependencies, and rejects `sorry`,
`admit`, custom top-level `axiom`, `opaque`, or `implemented_by` declarations
in the published sources. A successful run ends with:

```text
COUNTING_STABLE_MATCHINGS_LEAN_AUDIT_PASS
```

## Repository layout

- `lean_e2e/`: integrated model and proof development.
- `lean/`, `lean_random_reveal/`, `lean_entropy/`, `lean_probability/`:
  foundational local packages used by the integrated development.
- `joint_charging/`: rotation-boundary and global-slack proof modules.
- `constant_optimization/`: exact constant comparison and all-size endpoint.
- `audit/`: reproducible kernel and forbidden-token checks.

## Scope boundary

This repository publishes the Lean formalization only; it does not contain the
paper PDF or LaTeX sources. The penalized stable-pair theorem is checked using
an intrinsic irreducible-support excess parameter; identification with a
separately presented classical rotation encoding is not claimed here. The
external Popular Roommates algorithm and its full running-time transfer are
also outside the end-to-end formalized theorem. These boundaries do not affect
the two counting inequalities stated above.
