# Counting Stable Matchings

**One-Sided Entropy and Sharp Stable-Pair Bounds**

**Huibo Xu**<br>
Nanyang Technological University

This repository contains the paper and Lean 4 formalization for two extremal
counting results about stable marriage.

**[Read the full paper](paper/Counting-Stable-Matchings.pdf)**

## Overview

A stable-marriage instance consists of two equally sized sets of participants,
with every participant strictly ranking everyone on the other side. A perfect
matching is stable if it has no blocking pair: two participants who prefer each
other to their assigned partners.

The Gale-Shapley algorithm finds one stable matching efficiently. A single
preference profile, however, may admit many stable matchings. Let

$$
SM(n)=\max_I |\operatorname{Stab}(I)|,
$$

where the maximum ranges over all strict, complete instances with $n$
participants on each side. Knuth asked for the growth of $SM(n)$ in 1976. The
best known constructions have exponential base about $2.28$, while the previous
published upper bound was $3.55^n+O(1)$. The paper proves, for every $n\ge 1$,

$$
\boxed{SM(n)<\left(\frac{2078}{625}\right)^n=3.3248^n.}
$$

This advances the long-standing extremal counting problem. It does not
determine the exact exponential growth rate of $SM(n)$, which remains open.

## Main results

### An improved bound in the number of participants

The principal theorem improves the worst-case exponential rate from $3.55$ to
$3.3248$. The argument first establishes a universal one-sided rate below
$3.331974$, then proves that its local estimates must lose a linear amount of
entropy on every sufficiently large instance. A replication argument converts
the large-instance estimate into the displayed theorem for all $n\ge 1$.

The same method has a hereditary form. If stable edges incident to $r<n$ men
are prescribed and at least one stable completion exists, then the number of
completions is strictly less than $3.3248^{n-r}$.

### A sharp bound in the number of stable pairs

A stable pair is a pair that occurs in at least one stable matching. If $m$ is
the number of distinct stable pairs in an instance $I$, then

$$
\boxed{|\operatorname{Stab}(I)|^4\le 2^m,}
$$

or equivalently $|\operatorname{Stab}(I)|\le 2^{m/4}$. A refined version gives
an additional exponential penalty for rotations longer than two. The constant
$2^{1/4}$ is optimal. Equality holds precisely when the rotation poset is an
antichain of length-two rotations whose male participant pairs partition the
men; every subset of these rotations produces a distinct stable matching.

The participant bound also improves the running-time base obtained by inserting
a stable-marriage enumeration bound into Kavitha's Popular Roommates algorithm,
giving $O^*(6.9717^N)$ time on $N$ participants.

## Proof architecture

The main obstacle is that local partner choices do not combine independently.
Rotations -- the elementary cyclic exchanges between stable matchings -- obey
precedence constraints and may share participants. Counting the available
partners of each person therefore loses the global compatibility information
that controls the size of the solution space.

The participant-count proof retains this information through three steps.

1. **Fiber-wide oriented cuts.** Sample a stable matching and reveal only the
   men's partners in a random order. A revealed edge fixes both endpoints of a
   matched pair. The woman's comparison between her fixed partner and a target
   man supplies a direction, so the revealed edge cuts the target's ordered
   stable-partner list on the same side throughout the entire conditional fiber
   of stable completions. This is the stable-matching structural input behind
   the encoding.

2. **Geometric-window reduction.** The nearest revealed owners on the two sides
   of the sampled partner enclose every conditionally feasible partner. Given
   target priority $x$, the interval width is dominated by

   $$
   L_x+R_x-1,
   \qquad L_x,R_x\stackrel{\mathrm{iid}}{\sim}\operatorname{Geom}(x).
   $$

   Thus a high-dimensional conditional choice set is reduced to a universal
   one-dimensional random window. Integrating its logarithm gives the baseline
   constant

   $$
   C_*=
   \exp\!\left(\sum_{k\ge1}\frac{2\log k}{(k+1)(k+2)}\right)
   <3.331974.
   $$

3. **Rotation-boundary slack.** The geometric window deliberately forgets
   finite endpoints, infeasible locations inside the bracket, and nonuniformity
   of the conditional distribution. Local endpoint and rotation witnesses
   certify a fixed expected loss whenever they occur. A deletion and
   reconstruction argument on rotation boundaries proves that a uniformly
   random stable matching has linearly many chargeable targets in expectation.
   Consequently, the local window bounds cannot all be nearly tight. The
   resulting linear entropy saving lowers the base from $C_*$ to $3.3248$.

The stable-pair theorem uses a complementary representation. It records the
participant sets of rotations and bounds antichains by matchings in a labeled
multihypergraph. Shrinking hyperedges to ordinary edges preserves every original
matching. The incidences omitted by shrinking pay for the exceptional
double-edge components created in the resulting multigraph. This yields the
sharp $2^{m/4}$ rate and exposes the exact equality structure.

The two proofs share a general principle: retain enough participant information
to measure conflicts between apparently independent choices. The one-sided
encoding is applicable when revealed choices induce oriented cuts valid across
an entire conditional solution family. The incidence-budget argument is
preference-independent and applies to labeled hypergraph matching systems with
the same overlap restrictions.

## Formal verification

The Lean development checks the full proof chain for the two displayed counting
inequalities. In particular, it formalizes:

- strict, complete preference profiles, perfect matchings, and stability;
- the stable-matching lattice and the fixed-edge interval lemma;
- random reveal orders, marker ownership, and the geometric domination;
- the entropy calculation and exact numerical certificates;
- the rotation-boundary deletion and global charging argument;
- replication from the large-size estimate to every $n\ge1$;
- fixed-edge and prescribed-coordinate fiber bounds;
- the labeled multigraph theorem, hypergraph shrinking, and omitted-incidence
  accounting for the stable-pair result; and
- the intrinsic equality classification and Boolean-block realization.

The audited public endpoints contain no `sorry`, `admit`, custom top-level
`axiom`, `opaque`, or `implemented_by` declarations. Their axiom dependencies
are contained in Lean and Mathlib's standard logical foundations:
`propext`, `Classical.choice`, and `Quot.sound`.

The principal all-size Lean theorem is
`StableMatchingsJointCharging.SM_lt_2078_div_625_pow_all_sizes`. The sharp
stable-pair endpoint is
`StableMatchingsE2E.stableCount_fourth_le_two_pow_stablePairs`.

## Reproduce the verification

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

The audit builds the complete dependency graph, evaluates the headline and
stable-pair endpoints, prints their axiom dependencies, runs targeted mutation
counterexamples, and scans the published sources for forbidden declarations. A
successful run ends with:

```text
COUNTING_STABLE_MATCHINGS_LEAN_AUDIT_PASS
```

## Repository layout

- `paper/`: the current public full-version PDF.
- `lean_e2e/`: the integrated stable-matching model and proof development.
- `lean/`, `lean_random_reveal/`, `lean_entropy/`, `lean_probability/`:
  foundational Lean packages used by the integrated development.
- `joint_charging/`: the rotation-boundary and global-slack proof modules.
- `constant_optimization/`: exact constant comparison and the all-size endpoint.
- `audit/`: kernel-dependency, mutation, and forbidden-declaration checks.

## Scope

The repository contains the paper PDF and Lean sources, but not the LaTeX
sources. The exact exponential growth rate of $SM(n)$ remains open. The Lean
development proves the stable-pair penalty using an intrinsic
irreducible-support excess parameter; it does not identify that parameter with
the separately presented classical rotation encoding. The external Popular
Roommates algorithm and the full running-time transfer are discussed in the
paper but lie outside the end-to-end formalized theorem. These boundaries do not
affect the two boxed counting inequalities above.

## Citation

Citation metadata is provided in [`CITATION.cff`](CITATION.cff). GitHub's
**Cite this repository** menu can export BibTeX and APA entries.
