# Phase 3 pre-registration: the wall-gluing invariant

**Status: DEFINITION FROZEN AT MERGE OF THIS DOCUMENT. No A-vs-B
comparison may be computed or reported until the validation gates of §5
are implemented and green.** (Discipline: the instrument is defined and
adversarially reviewed before it touches the question it was built to
decide. This document incorporates the findings of the definition-level
adversarial review of 2026-08-12 — one false lemma corrected (F1), one
chart-artifact channel removed from G3 (F2), gates hardened (F10); the
full findings list is recorded in the pre-registration PR.)

## 1. What this decides and why gluing

Report §IV.4 reduces the completeness half of Question 4 (modulo the
flagged reconstruction step, a deliberate trust boundary) to covering
rigidity: *two Keller coverings with the same multiplicity function, up
to the moves, are isomorphic — true or false?* The family-hunt pair
(A, B) is tied through the n₁ and n₂ value sets and is provably not
affinely equivalent (`family_equiv.py`), so it is a genuine test case.
Value-set sampling at higher n_k can pile up ties forever without
deciding anything; the covering data the report identifies as decisive
is the **wall-gluing** — which sheets persist through which wall
strata. This document defines that datum as a hierarchy of finite,
exactly computable, move-invariant objects, and fixes the decision
rules before any data is taken.

## 2. Setting and structural lemmas (machine-checked)

Members are Gallagher weighted-lift Keller maps F = (F₁,F₂,F₃) with
det DF ≡ 1 — everywhere a local diffeomorphism, so fibers are finite
and n(y) := #F⁻¹(y) changes only by preimages escaping to infinity,
never at critical points. Off the wall {C = 0}, fibers biject with the
real roots of the quartic E(w) = −H(w) + w(H′(0) + BC) − AC²
(`family_hunt.py`, three identities certified at import).

All lemmas below are verified mechanically by
`family_gluing_structure.py` (CI-run, failure-loud, both members):

- **L1 (plane reduction).** E depends on the target (A,B,C) only
  through P := BC and R := AC². On {C ≠ 0} the multiplicity function
  factors as n(A,B,C) = N(BC, AC²) with N the real-root count of
  E(w; P, R), and the off-wall landscape is governed by the plane
  discriminant curve D(P,R) := disc_w E = 0. Moreover
  (A,B,C) ↦ (P,R,C) is a diffeomorphism on each half-space {±C > 0},
  so the off-wall landscape is exactly **two copies of
  (plane partition) × ℝ** — the plane census is provably sufficient
  for the 3D census, and every off-wall chamber and Σ-stratum is
  (plane set) × ℝ, hence non-compact (the compactness flag of G1 is
  well-defined but carries no information in this family).
- **L2 (wall limit).** E₀(w) := E|_{P=R=0} = −H(w) + wH′(0) has w = 0
  as a double root (H(0) = 0 and E₀′(0) = 0 identically) and w = 1 as
  a root (the endpoint identity H(1) = H′(0)); the remaining root ρ is
  rational and member-specific (ρ_A = 5, ρ_B = −5/2).
- **L3 (gluing skeleton; corrected by review finding F1).** As C → 0
  at fixed (A,B): the two sheets with w → 0 converge to the γ-branch
  wall points where those exist; the sheet with w → 1 converges to the
  x = 0-branch wall point; the sheet with w → ρ escapes (|y| ~ 1/C)
  unless −ρ = p(ρ), which fails for both members. The near-wall
  pair-reality condition equals the on-wall γ-branch condition (both
  are B² + 4q(0)A > 0, q := E₀/w²). At (A,B) **off** the parabola
  {δ = 0} the wall is a *crack*: n takes equal values on the two sides
  and drops pointwise on the wall itself. **On** {δ = 0} the wall is a
  *jump*: n = 4 on one side, 2 on the other, 1 on the wall, with the
  side selected by the sign of B (exact regression targets in the
  harness: e.g. member A at (5,5): 4 | 1 | 2). Jumps therefore happen
  across Σ := {disc_w E = 0, C ≠ 0} and across the codimension-2 wall
  stratum {δ = 0}; the earlier draft's claim "jumps only across Σ" was
  false and is corrected here.
- **L4 (wall stratification).** The wall fiber count is
  1 + (0 or 2 by the sign of δ(A,B)) — a theorem, not an observation:
  the x = 0 branch solves linearly and **uniquely** for every (A,B),
  and the γ-branch pair count is governed by δ, computed by two
  independent elimination routes that agree. {δ = 0} is a parabola for
  both members (B² = 5A for A, B² = 20A/7 for B).
- **L5 (no ovals ⇒ no base points).** D(P,R) is an irreducible
  quartic, cubic in R with constant leading coefficient, with **no
  smooth vertical tangents** (saturation Gröbner basis = {1}), hence
  no compact ovals: every plane chamber, every 3D chamber (chamber×ℝ
  by L1), and every wall stratum (inside/outside a parabola) is simply
  connected, and the covering over each chamber is trivial. G3's
  matchings are therefore independent of base points and paths — no
  monodromy conventions are needed.
- **L6 (no phantom walls).** Every real point of D = 0 carries a real
  multiple root of E: a non-real double root would force E to be a
  perfect square (lc·(quadratic)²), and the perfect-square locus is
  finite with real double roots at every real point (checked exactly);
  a triple root of a real quartic is automatically real. So every real
  arc of D = 0 is a genuine ±2 jump of N — the computed stratification
  never over-refines the intrinsic one.
- **L7 (wall tangency).** D restricted to the wall-approach path
  (P,R) = (tB, t²A) vanishes to order exactly 2 at generic (A,B), with
  t²-coefficient proportional to the near-wall condition of L3; the t³
  term survives on {δ = 0}. Consequently closure(Σ) ∩ wall = {δ = 0},
  which is where the L3 jump lives.

## 3. The move class, and the invariance theorem

**Moves.** F ↦ ψ ∘ F ∘ φ with φ, ψ polynomial automorphisms of ℝ³
(contains the tame group; every polynomial automorphism is a
homeomorphism of ℝ³). Source moves φ leave n unchanged as a function on
the target; target moves ψ replace n by n ∘ ψ⁻¹.

**Intrinsic stratification (review finding F5).** All strata are
defined from the labeled pair (ℝ³, n) alone: S := the discontinuity
locus of n; S⁽²⁾ := points of S near which S is a topological
2-manifold and the local incidence labels are locally constant; the
remainder is stratified recursively. Homeomorphisms h satisfy
h(S_n) = S_{n∘h⁻¹} and respect this intrinsic stratification;
topological dimension and the labels are homeomorphism-invariant. L6
guarantees the algebraic presentation (Σ, wall, {δ=0}, node, cusps)
realizes the intrinsic stratification rather than refining it.

**Invariance theorem.** Any isomorphism invariant of the labeled
topological pair (ℝ³, n) — any quantity unchanged when n is replaced by
n ∘ h⁻¹ for a homeomorphism h of ℝ³ — is invariant under all moves.
Likewise any invariant of the covering data (total space, F, and
closure-incidence of sheets with stratum fibers) up to homeomorphism
pairs is move-invariant. *Proof:* immediate from the transformation
laws; φ acts upstairs carrying sheets to sheets and preserving closure
incidence. ∎

"Equal up to homeomorphism" is not directly computable; we freeze a
hierarchy of finite combinatorial **shadows**, each a homeomorphism
invariant, each decidable by finite comparison.

## 4. The frozen invariant hierarchy

Chambers and strata carry the (constant) value of n.

- **G0 (value census).** The set of n values on chambers and strata,
  by stratum dimension. *(Measured: chambers {0,2,4}, wall {1,3};
  tied.)*
- **G1 (component census).** For each label (n value, dimension): the
  number of connected components carrying it. Computed exactly via the
  L1 product structure: the (P,R)-plane partition by D = 0 with
  root-count labels (two copies, one per half-space) plus the wall
  partition by δ (L4) and the codimension-2 strata ({δ=0}, node,
  cusps).
- **G2 (labeled incidence graph).** Vertices = chambers and strata
  with G1 labels; edges = topological closure incidence. Compared as
  abstract labeled graphs up to isomorphism. Computation route (review
  finding F8): (a) within each half-space, adjacency = plane adjacency
  × ℝ; (b) wall adjacency: the two origin-local plane chambers attach
  to wall strata along the smooth origin branch of D = 0, whose
  Puiseux data is exact (the t² and t³ coefficients of L7 — the t³
  asymmetry is what pairs C>0 chambers with C<0 chambers across the
  wall); (c) closure(Σ) ∩ wall = {δ = 0} (L7).
- **G3 (sheet-passage decorations; redefined per review finding F2).**
  Each G2 edge between chambers P, Q meeting along a codimension-1
  stratum σ is decorated with: (i) per side, the number of sheets that
  die at σ, **by mechanism** (collide at Σ; escape at the wall); and
  (ii) the matching **of pass-through sheets only**, defined by
  closure incidence with σ-fiber points in the total space. The
  escape-and-return pairing of dying sheets (e.g. the ρ-sheet on the
  two sides of the wall crack) is **chart data, not covering data, and
  is excluded from the frozen invariant**; it may be added later only
  with its own invariance proof. The equivalence on G3 is **global**
  (review finding F3): one relabeling of sheets per chamber, acting
  simultaneously on all edges of that chamber — i.e., isomorphism of
  decorated graphs, equivalently of the covering restricted to a
  neighborhood of the 2-skeleton. By L5 all strata and chambers are
  simply connected, so the matchings are well-defined without base
  points.

**Escalation order:** G0 (done) → G1 → G2 → G3. A tie triggers the
next level; a difference stops escalation (§6). G3 is the only level
carrying data beyond n as a function.

## 5. Validation gates (must pass before any A-vs-B output)

- **V1 (independent-oracle consistency).** The pipeline's n-landscape
  predictions checked pointwise against the independent per-point
  method (Gröbner branch decomposition with substitution verification)
  on a committed grid straddling every predicted stratum of both
  members, including {δ = 0} jump points.
- **V2 (planted difference, G0-level).** The pipeline run on a
  degree-3 Gallagher member must report a difference from A and B.
- **V3 (two-route computation).** D and δ each computed by two
  independent routes; exact agreement required (δ half already in
  L4/CI).
- **V4 (transformation-law spot-check).** For random polynomial
  automorphisms ψ (not only affine): pointwise n of ψ∘F at a committed
  grid equals n∘ψ⁻¹. (This validates the law the invariance theorem
  rests on; it does not require ψ to preserve the wall, and doesn't
  pretend to.)
- **V5 (negative control; blocking for decision rule 2 — review
  finding F10).** The full G0–G3 census computed from the **moved
  presentation** ψ∘A∘φ for a nontrivial affine pair (ψ, φ) — without
  using the (P,R) product shortcut, which the moved form breaks — must
  tie the canonical A census exactly. A pipeline that cannot pass V5
  may not bank any G-level difference.
- **V6 (positive controls; V6a blocking for rule 2).** (a) A synthetic
  same-G0 planted pair (a hand-built labeled plane partition differing
  from A's only at G1/G2, fed to the comparison code) must be detected
  at the correct level. (b) Best effort: a third real moduli member
  with a genuinely different curve topology, if one exists, as an
  end-to-end plant.

## 6. Decision rules (fixed now, before data)

1. **Any Gi difference (i ≤ 2):** anomaly first — assume bug,
   recompute by an independent route, only then bank. A confirmed
   G1/G2 difference means the multiplicity function *as a function up
   to moves* separates the pair (sharper than the value-set ties).
   Banked as **Outcome B evidence, scoped: "separates up to the proved
   move class (polynomial automorphisms; indeed all homeomorphism
   pairs)"**.
2. **G0–G2 tie, G3 differs (confirmed by independent recomputation and
   with V5, V6a green):** two coverings with matching landscape
   shadows but different sheet gluing — the IV.4 configuration. Banked
   as an **Outcome A candidate** with three caveats stated wherever
   quoted (review finding F4): (i) the reconstruction step (deliberate
   trust boundary); (ii) move-class exhaustion beyond the proved
   invariance; (iii) **G0–G2 ties do not prove the n-landscapes
   homeomorphic** — upgrading candidate to claim requires exhibiting a
   labeled-landscape homeomorphism (or an existence proof). Goes to
   external review before any stronger claim.
3. **G0–G3 all tie:** banked as a genuine deep tie; next escalation
   (constructing/excluding an actual covering isomorphism; rigidity
   proof attempt) gets its own pre-registration.
4. Negative and null results bank with the same prominence as
   positives.

## 7. Known limitations

- The shadows are necessary, not sufficient: ties never prove the
  coverings isomorphic (rule 3).
- V6a plants at the comparison layer; only V6b (if a suitable third
  member exists) would plant a G1+-difference end to end.
- The invariance theorem covers polynomial-automorphism moves (and in
  fact all homeomorphism pairs). Measurable-isomorphism moves are NOT
  covered; if the operator-level equivalence ever justifies a larger
  move class, G-level separations need re-examination (rule 1's
  scoping).
- ρ, the w-chart, and every escape-side quantity are presentation
  data; nothing outside the G0–G3 shadows is compared. In particular
  the sign difference ρ_A = 5 vs ρ_B = −5/2 is NOT an invariant and
  must never be quoted as a separation.
- **Erratum 2026-09-09 — continuation method.** The independent
  confirmation `family_gluing_verify.py` previously continued branches
  by nearest-root matching after exact isolation. That can change
  branches silently. Witness: on (R − 64P)(R − 64P − 1) = 0, whose two
  branches never meet, anchored at (P, R) = (0, 1), it returned R = 8
  at P = 1/8 instead of 9. It stepped onto the other branch at its
  *first accepted step*, where the wrong root sat at distance exactly 0
  from the previous value while the correct one sat at distance 1 — and
  the proximity guard read that zero as maximum confidence. Halving the
  step cannot repair it: branch motion scales with the step, the
  inter-branch gap does not. Replaced by order-preserving continuation:
  on a P-interval carrying no critical value the real R-roots never
  collide, so their sorted order is invariant and the k-th root is one
  branch throughout; both the critical-value-free interval and the
  unchanged root count are checked, not assumed. **The G2 separation was
  re-derived under the corrected method and holds unchanged** (A:
  {node, cusp}; B: regular crossing then {cusp, cusp}). The witness is
  `selftest()` in that script, CI-run on every push.
- The corrected script still matches by proximity in exactly one place:
  the re-anchor just past a crossed critical line (member B, left leg),
  where the real-root count genuinely changes and order transport does
  not apply. That step rests on the O(h^(1/2)) ≈ 0.05 cluster-radius
  against O(1) line-root-gap estimate — asserted in prose, not computed.
  A certified enclosure there would close the last gap in this route.

## 8. Provenance

Structural lemmas: `family_gluing_structure.py` (CI-run). Fiber
machinery: `family_hunt.py`. Pair non-triviality: `family_equiv.py`.
Definition-level adversarial review 2026-08-12 (findings F1–F10
recorded in the pre-registration PR): one lemma corrected (F1, the
{δ=0} wall jump), G3 stripped of chart data (F2) and made global (F3),
Outcome A caveat (iii) added (F4), intrinsic stratification added
(F5), plane-census sufficiency proved (F6), no-phantom lemma L6
promoted to machine-checked status (F7), G2 route specified (F8),
harness radical-comparison bug fixed (F9), V5/V6 gates added (F10).
Measurement implementation and data follow in later PRs, gated by §5.

Independent confirmation: `family_gluing_verify.py` (CI-run).
Continuation method corrected 2026-09-09 after review flagged
nearest-root branch matching as unsound: the defect was reproduced on a
two-branch witness, the method was replaced by order transport, and the
separation was re-derived unchanged (§7 erratum). The prior result is
retained in git history rather than deleted; the witness that breaks the
old method is now a permanent regression test.
