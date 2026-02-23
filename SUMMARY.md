# Formalization of Bohm-Sontacchi 1978

**Paper**: C. Bohm and G. Sontacchi, "On the existence of cycles of given length in
integer sequences like x_{n+1} = x_n/2 if x_n even, and x_{n+1} = 3x_n + 1
otherwise", *Atti Accad. Naz. Lincei*, 1978.

All 7 propositions from the paper have been formally verified in Lean 4 with
**zero `sorry` gaps**.

---

## Build instructions

```bash
# First time only -- fetch the Mathlib cache (avoids rebuilding Mathlib from source):
lake exe cache get

# Build the entire project:
lake build

# Build a single file (e.g. Prop4):
lake build BohmSontacchi.Prop4
```

**Requirements**: Lean 4.28.0 (installed via elan), Mathlib v4.28.0.

---

## Project structure

| File | Lines | Description |
|------|------:|-------------|
| `Defs.lean` | 112 | Core definitions: `collatzU`, `collatzU_iterate`, `listNumSum`, `Schedule`, `cycleFormula`, `collatzIterFormula` |
| `Prop1.lean` | 196 | Compositions of f and g are affine; slope = c^m * a^{sum n_i} |
| `Prop2.lean` | 204 | At most 2^n periodic points (with slope != 1 condition) |
| `Prop3.lean` | 269 | Cycle points lie between fixed points of f and g |
| `Prop4.lean` | 242 | **Iteration formula**: u^n(x) = (3^m x + sum) / 2^n |
| `Prop5.lean` | 326 | **Cycle characterization**: x is a nonzero cycle point iff x = sum / (2^n - 3^m) |
| `Prop6.lean` | 354 | **Cycle bound**: |x| < 3^n for any period-n cycle element |
| `Prop7.lean` | 481 | **Reaching-1 characterization**: x reaches 1 iff x = (2^n - sum) / 3^m |
| `Basic.lean` | 17 | Import hub for all modules |
| **Total** | **2201** | **121 theorems/lemmas, 0 sorry** |

---

## Proposition-by-proposition summary

### Proposition 1 (Prop1.lean) -- Fully proved

The composition f^{n_m} g f^{n_{m-1}} g ... g f^{n_0} is affine with slope
c^m * a^{n_0 + ... + n_m}. Proved by induction on the list of g-applications.

### Proposition 2 (Prop2.lean) -- Fully proved (with added hypothesis)

At most 2^n periodic points of period n. The proof constructs an injection from
the set of fixed points into the set of branch sequences {0,1}^n, using
uniqueness of fixed points for affine maps with slope != 1.

**Caveat**: The theorem required adding a slope hypothesis
(`hslope : forall choices, ... -> alpha != 1`). Without it, the statement is false
in general (slope 1 with intercept 0 gives infinitely many fixed points). The
paper's statement implicitly assumes this via the specific Collatz parameters
(a=1/2, c=3/2), where collatz_slope_ne_one (proved in Prop3) guarantees it.

### Proposition 3 (Prop3.lean) -- Fully proved

Cycle points are bounded by the fixed points of the individual branches
(b/(1-a) and d/(1-c)). Proved using the affine identity f(x) - p = a(x - p).

### Proposition 4 (Prop4.lean) -- Fully proved

The iteration formula: for a schedule compatible with x's trajectory,

    u^n(x) = (3^m * x + sum_{k=0}^{m-1} 3^{m-k-1} * 2^{v_k}) / 2^n

**Key proof technique**: First prove an integer version
(`2^n * u^n(x) = 3^m * x + S`) by induction on n, avoiding rational division
entirely. Then derive the rational formula by dividing both sides by 2^n.
This sidestepped significant difficulties with rational arithmetic in Lean 4.

### Proposition 5 (Prop5.lean) -- Fully proved (with x != 0)

A nonzero integer x is a cycle point of u iff it can be expressed as
x = sum / (2^n - 3^m) for some valid schedule.

**Forward direction**: Construct the schedule from `oddSteps x n`, apply Prop 4,
and rearrange using the cycle condition u^n(x) = x.

**Backward direction** (hardest proof in the formalization): Given
x = sum / (2^n - 3^m), show that x's actual Collatz trajectory matches the
schedule. Proved by induction on step index, using 2-adic valuation arguments
to determine parity: at each step k, the formula forces the parity of u^k(x)
to match the schedule via divisibility of the remaining terms by 2^{k+1}.

**Caveat**: The combined iff theorem requires `x != 0`. The trivial cycle
point x = 0 (where u(0) = 0) has no odd steps, so no Schedule (which requires
nonempty vals) can represent it. The paper's formulation implicitly allows m = 0
(empty sum), but our Schedule structure requires m >= 1.

### Proposition 6 (Prop6.lean) -- Fully proved

For any cycle element x of period n: |x| < 3^n.

**Proof strategy**: Uses Prop 4 directly (not Prop 5). From the integer formula
and the cycle condition, derive x * (2^n - 3^m) = S. Then:
- S >= 0 (each term is nonneg)
- S < 3^n (from the geometric sum bound and element bound on v)
- 2^n != 3^m (parity: even != odd)
- Therefore |x| * |2^n - 3^m| = S < 3^n, and |2^n - 3^m| >= 1, giving |x| < 3^n.

### Proposition 7 (Prop7.lean) -- Fully proved

x reaches 1 under iteration of u iff there exists a witness with
x = (2^n - sum) / 3^m.

**Forward direction**: Given u^n(x) = 1, extend to n' = n+2 to ensure at least
one odd step (since u^n(x) = 1 is odd). Apply the integer formula and rearrange.

**Backward direction**: By strong induction on n, determine parity of x from the
formula at each step. When 0 is in the schedule, x is odd and
u(x) = (3x+1)/2; the formula reduces to one with n-1 steps and a shifted
schedule. When 0 is not in the schedule, x is even and u(x) = x/2. The
singleton schedule [0] base case resolves to x = 2^{n-1}, which reaches 1 by
repeated halving.

---

## Hurdles and gotchas

### 1. Schedule definition design (critical early blocker)

The original `Schedule.n` was defined as `s.vals.getLast` (the last element of
the vals list). This made it impossible to prove Prop 5 forward, because
`oddSteps x n` produces values in {0, ..., n-1}, so `getLast < n`, but we need
`Schedule.n = n` (the total number of iterations).

**Fix**: Redesigned `Schedule` with an explicit `total : N` field and a
`bound : forall i in vals, i < total` proof obligation. Changed `Schedule.n`
to return `s.total`. This was the single most important design change.

### 2. Recursive vs foldl sum representations

The codebase had two representations of the numerator sum:
- `listNumSum` (recursive): `[] -> 0; (v :: rest) -> 3^|rest| * 2^v + listNumSum rest`
- `cycleNumeratorSum` (foldl-based): `List.range.foldl (fun acc k => acc + ...) 0`

These compute the same values but are definitionally different in Lean. Bridging
them required converting both to `Finset.sum` as an intermediate representation.
This equivalence (`listNumSum_eq_cycleNumeratorSum`) was needed in Prop6 to
transfer the bound proofs to the new sum representation.

**Lesson**: Choose one canonical representation early and stick with it.

### 3. Integer vs rational arithmetic

The natural statement of Prop 4 involves division by 2^n in Q. Proving this
directly requires managing Z-to-Q casts, nonzero denominators, and rational
field_simp at every step.

**Solution**: Prove the equivalent integer identity `2^n * u^n(x) = 3^m * x + S`
first, then derive the rational form in one step. This was dramatically simpler
and is the recommended approach for similar formalization efforts.

### 4. The x = 0 edge case

x = 0 is a valid cycle point (u(0) = 0) but cannot be represented via the
cycle formula because `Schedule` requires at least one odd step. The paper's
Prop 5 implicitly handles m = 0, but our `Schedule.nonempty` field forces m >= 1.

**Workaround**: Added `x != 0` hypothesis to `prop5`. Proved separately that
any nonzero cycle point must have at least one odd step (from the integer
formula: if no odd steps, then x * (2^n - 1) = 0, forcing x = 0).

### 5. 2-adic valuation for parity (Prop 5 backward)

The hardest proof was showing that a formula representation forces the
trajectory to match the schedule. The key insight: at each step k, split the
schedule into a prefix (steps < k) and a tail (steps >= k). The integer
formula for the prefix gives `2^k * u^k(x)` in terms of known quantities.
Whether k appears in the schedule determines whether `2^{k+1}` divides the
relevant expression, which in turn determines the parity of `u^k(x)`.

This 2-adic argument required several helper lemmas about divisibility of
`listNumSum` when all positions exceed a threshold.

### 6. Lean 4 / Mathlib API churn

Several Mathlib API names had changed between versions:
- `List.get!` -> `List.getD` (get! doesn't exist in Lean 4.28)
- `List.Chain'` -> `List.Pairwise` (Chain' is deprecated)
- `Mathlib.Data.Rat.Basic` -> `import Mathlib.Tactic` (old imports removed)
- `List.length_eq_zero` -> `List.eq_nil_of_length_eq_zero`

**Lesson**: Pin your Mathlib version and use `import Mathlib.Tactic` as a
catch-all import rather than fine-grained imports that may drift.

### 7. Private lemma visibility

The `private` keyword in Lean 4 restricts visibility to the current file. The
core integer formula (`collatzU_iterate_int_formula`) was initially marked
`private` in Prop4.lean, blocking its use from Prop6 and Prop7.

**Fix**: Made it non-private after realizing downstream files needed it. Design
reusable lemmas as public from the start.

### 8. Namespace collisions

Both Prop4 and Prop5 initially defined `collatzU_even` and `collatzU_odd` in
the `BohmSontacchi` namespace. When `Basic.lean` imported both, the build
failed with duplicate declaration errors.

**Fix**: Moved shared lemmas to `Defs.lean` (the common import).

---

## Dependency graph

```
Defs.lean
  |-- Prop1.lean
  |     |-- Prop3.lean
  |-- Prop2.lean
  |-- Prop4.lean
  |     |-- Prop5.lean
  |     |-- Prop6.lean (also uses Prop4)
  |     |-- Prop7.lean (also uses Prop4, Prop5)
  |
  Basic.lean (imports all)
```

---

## Statistics

- **Lean version**: 4.28.0
- **Mathlib version**: v4.28.0
- **Total lines of code**: 2201
- **Theorems/lemmas**: 121
- **Sorry count**: 0
- **Build time** (warm cache): ~30 seconds
- **Build time** (cold, after `lake exe cache get`): ~2-3 minutes
