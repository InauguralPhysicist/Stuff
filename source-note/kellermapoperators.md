# A Non-Regular Heisenberg System from the Alpöge Keller Map

**Status.** Every algebraic identity below was verified symbolically over ℚ; every
numerical claim was recomputed from scratch. Two claims circulating in an earlier
draft of this analysis were found to be wrong and are corrected in Appendix A.
Section 8 flags the one inference that is expected but *not* established here.

---

## Summary

Alpöge's counterexample to the Jacobian Conjecture yields an explicit triple of
operators on L²(ℝ³) — polynomial coefficients, integer data — satisfying all the
canonical commutation relations of position and momentum, which is nevertheless
**not** unitarily equivalent to any multiple of the Schrödinger representation.
The obstruction is computable in closed form: a single polynomial L(y) whose sign
gives the number of sheets and whose zero set is where a sheet escapes to infinity.

This is a failure of *uniqueness of quantization*, not a spectral gap. See §9.

---

## 1. The map

Let F : ℝ³ → ℝ³ be Alpöge's map (announced 20 July 2026, found with Claude Fable 5):

```
F₁ = (1 + x₁x₂)³x₃ + x₂²(1 + x₁x₂)(4 + 3x₁x₂)
F₂ = x₂ + 3x₁(1 + x₁x₂)²x₃ + 3x₁x₂²(4 + 3x₁x₂)
F₃ = 2x₁ − 3x₁²x₂ − x₁³x₃
```

Verified: **det DF ≡ −2**, identically. Component degrees (7, 6, 4). So F is a
Keller map — a local diffeomorphism everywhere — and it is not injective. The
three colliding points over (−1/4, 0, 0) are all real:

| x₁ | x₂ | x₃ |
|----|----|----|
| −1 | 3/2 | 13/2 |
| 0 | 0 | −1/4 |
| 1 | −3/2 | 13/2 |

## 2. The lifted operators

Because det DF is a nonzero *constant*, the inverse transpose is polynomial:

    A := (DFᵀ)⁻¹ = −adj(DF)ᵀ / 2,     max coefficient degree 11.

Define, with ℏ = 1, on C_c^∞(ℝ³):

    Q′ᵢ = multiplication by Fᵢ(q)
    P′ᵢ = Σₖ Aᵢₖ(q) pₖ,   pₖ = −i ∂ₖ

and the composition operator

    (Cψ)(x) = √2 · ψ(F(x)).

## 3. Verified identities

All four hold exactly as polynomial identities over ℚ:

1. **A · DFᵀ = I** ⟹ [Q′ᵢ, P′ⱼ] = i δᵢⱼ. The Heisenberg CCR hold on the nose.
2. **Piola:** Σₖ ∂ₖAᵢₖ = 0 for each i (all three divergences vanish identically),
   so each P′ᵢ is symmetric as written, with no ordering ambiguity.
3. **Σₖ (Aᵢₖ∂ₖAⱼₗ − Aⱼₖ∂ₖAᵢₗ) = 0** for all i < j and all l, so [P′ᵢ, P′ⱼ] = 0
   exactly. These are first-order operators, so the commutator is i times the
   Poisson bracket with no ℏ² corrections. Equivalently the vector fields
   Xᵢ := row i of A commute.
4. **Intertwining:** P′ᵢC = C pᵢ and Q′ᵢC = C qᵢ, by (1) and the chain rule.

Consequence of (4): for any polynomial Hamiltonian Ĥ(p, q), writing φ(Ĥ) for the
same polynomial in (P′, Q′), we get φ(Ĥ)C = CĤ. So Ĥψ = Eψ implies
φ(Ĥ)(Cψ) = E(Cψ), and eigenvalues transport one way into the new system.

## 4. Fiber structure: the main computation

The lex Gröbner basis of ⟨F − y⟩ with x₃ > x₂ > x₁ has **shape-lemma form**: x₃
and x₂ each appear to degree 1 over x₁. Real roots in x₁ therefore correspond
bijectively to real preimages. The univariate factor is a depressed cubic,

    L(y)·x₁³ + (4 − 3y₂y₃)·x₁ − 2y₃ = 0,

    L(y) = 27y₁²y₃² − 18y₁y₂y₃ + 16y₁ + y₂³y₃ − y₂².

Its discriminant factors:

    Δ(y) = −4 · (27y₁y₃² − 9y₂y₃ + 8)² · L(y).

The squared factor is nonnegative, so **sign Δ = −sign L**. Hence, off the
hypersurface {L = 0}:

| region | Δ | real fiber count n(y) |
|--------|---|------------------------|
| L(y) < 0 | > 0 | **3** |
| L(y) > 0 | < 0 | **1** |

The generic complex fiber has exactly 3 simple points (no ramification, since
det DF never vanishes). Being conjugation-invariant, it always contains a real
point, so **n(y) ≥ 1 off {L = 0}**. By the same parity argument **n(y) = 2 is
impossible.**

**The cubic is an identity, not a genericity statement.** Substituting y = F(x):

    L(F(x))·x₁³ + (4 − 3F₂F₃)·x₁ − 2F₃ = 0   identically in x,

verified by expansion over ℚ. So the eliminant lies in ⟨F − y⟩ as a polynomial
identity and the classification above holds uniformly in y, with no appeal to
genericity of the Gröbner presentation. Two corollaries follow directly.

*Corollary 1 (empty fibers; F is not surjective).* On the curve
y(s) = (4/27s², 4/3s, s) one computes L = 0 **and** 4 − 3y₂y₃ = 0, so at any
preimage the identity would read 0 = −2s ≠ 0. The fiber is empty. Confirmed
independently: ⟨F − (4/27, 4/3, 1)⟩ = ⟨1⟩ and ⟨F − (1/27, 2/3, 2)⟩ = ⟨1⟩.
So n(y) = 0 does occur — necessarily inside {L = 0}, hence on a null set, which
is why the spectral conclusions of §5 are unaffected.

*Corollary 2 (discriminant factorization, second proof).*
(4 − 3y₂y₃)³ + 27y₃²L = (27y₁y₃² − 9y₂y₃ + 8)², verified over ℚ, which is the
displayed factorization of Δ rearranged.

{L = 0} is the *non-properness hypersurface*: where the leading coefficient
degenerates and a root runs off to infinity.

Sampling for orientation only (the classification above is exact): 4000 uniform
points in [−3,3]³ gave n = 1 for 3305 and n = 3 for 695. Both level sets carry
positive measure.

## 5. Consequences for C

Change of variables with |det DF| = 2 gives, for all ψ ∈ L²(ℝ³),

    ‖Cψ‖² = ∫ n(y) |ψ(y)|² dy,    i.e.    **C\*C = M_{n(y)}**.

With n taking only the values 1 and 3, each on a set of positive measure:

- **spec(C\*C) = {1, 3}** — exactly, as a theorem, not as a sampled estimate.
- 1 ≤ C\*C ≤ 3, so ‖C‖ = √3 and C is bounded below by 1.
- C is injective with closed range; ran C is the space of functions constant on
  fibers, which is proper of infinite codimension because n = 3 on an open set.

So the operator-theoretic shadow of "generically 3-to-1" is a defect operator
with two-point spectrum {1, 3}.

## 6. Incompleteness of the flows is forced

The Xᵢ commute (§3.3) and are F-related to the constant fields ∂/∂yᵢ.

**Claim.** Not all Xᵢ can be complete.

*Proof.* If all three were complete, their commuting flows would define a smooth
ℝ³-action Φ on ℝ³ with F(Φ_t(x)) = F(x) + t. Then F is surjective, and
Φ_t maps F⁻¹(y) bijectively onto F⁻¹(y + t), so n(y) is constant. A local
diffeomorphism with constant finite fiber count onto simply connected ℝ³ is a
covering map, forcing n ≡ 1 and F injective — contradicting §1. ∎

So the incompleteness is not an artifact of a bad chart or a stiff integrator.
It is *equivalent in content* to the non-injectivity of F.

**Where it happens.** Along the P′₁ flow, y₂ and y₃ are frozen and y₁ ↦ y₁ + t,
so L restricted to the ray is a quadratic in t:

    L(t) = 27y₃²(y₁+t)² + (16 − 18y₂y₃)(y₁+t) + (y₂³y₃ − y₂²).

Its roots are the escape times. When L(y₀) < 0 — i.e. on the three-sheeted side —
the constant term is negative, so the roots have **negative product: one positive
and one negative real escape time, always** (for y₃ ≠ 0). Near a root t\*, the
leading coefficient vanishes and the escaping root behaves as
±√(−B/L) ~ **|t − t\*|^(−1/2)**: genuine finite-time blowup.

**Crossing a wall is not the same as dying at it.** At each zero of L exactly
two of the three branches run to infinity and one persists, converging to
2y₃/(4 − 3y₂y₃). A trajectory riding the persistent branch crosses {L = 0} and
survives. Example: x₀ = (0.2, 0.1, −0.3) has L(F(x₀)) = −4.2421 < 0 and its
e₁-ray meets {L = 0} at t = 0.2772 and t = −3.7188, yet its x₁ converges to
0.19167 = 2y₃/(4 − 3y₂y₃) while the other two sheets die at the −1/2 rate and
the fiber drops 3 → 1.

The consequence is methodological: no finite set of sampled trajectories can
settle completeness, in either direction. A trajectory that never meets the
escape locus proves nothing, and so does one that meets it and survives. Only
the global argument above decides it.

## 7. Numerical confirmation

Fixed-step RK4 (h = 2×10⁻⁴) launched from preimages over three points with
L < 0, against escape times predicted analytically from L(t) = 0:

| predicted t\* | observed blowup | direction |
|---------------|-----------------|-----------|
| +1.48572 | +1.48600 | forward |
| +0.59492 | +0.59580 | forward |
| +0.28783 | +0.28800 | forward |
| −0.18042 | −0.22120 | backward |
| −0.88750 | −0.93340 | backward |

Forward agreement is 4 digits. Backward agreement is coarser because fixed-step
RK4 loses accuracy approaching an inverse-square-root singularity; the observed
times are late, as expected from overshoot.

## 8. What fails in Stone–von Neumann

The abelian von Neumann algebra generated by (Q′₁, Q′₂, Q′₃) is multiplication by
functions of F. Decomposing L²(ℝ³) over the fibers of F, this algebra acts as
g(y)·Id on ℓ²(F⁻¹(y)), so its **joint spectral multiplicity is exactly n(y)**.

Schrödinger's position triple has multiplicity 1; a direct sum of k copies has
multiplicity k. In every case the multiplicity is *constant* over position space.
Here it is 3 on {L < 0} and 1 on {L > 0}. Multiplicity is a unitary invariant, so:

> (Q′, P′) is not unitarily equivalent to any multiple of the Schrödinger
> representation, and by Stone–von Neumann it cannot integrate to a regular Weyl
> representation. The obstruction is the fiber count itself.

Note the argument needs **non-constancy**, not merely "3 ≠ 1" — three copies of
Schrödinger would give constant multiplicity 3 and be perfectly regular.

*Status of the remaining inference.* Incompleteness (§6) removes the standard
sufficient condition for essential self-adjointness of a divergence-free
first-order operator, which makes it very likely that some P′_v = Σ vᵢP′ᵢ fails
to be essentially self-adjoint on C_c^∞ — the classical model being d/dx on
C_c^∞(0,∞), incomplete in one direction with unequal deficiency indices. This
note does not compute deficiency indices, so that specific claim is expected but
unproven here. The failure of regularity in the displayed statement above does
not depend on it.

The phenomenon is the known one: operators satisfying the Heisenberg relations on
a common dense domain that do not exponentiate to the Weyl relations. The
textbook example is built on L² of a two-sheeted Riemann surface. What is new
here is that the sheeting is supplied by a polynomial self-map of ℝ³ with integer
coefficients, and the whole structure — sheet count, escape locus, escape times —
is decided by the sign and zeros of one explicit polynomial L.

## 9. What this is not

- **Not a mass gap.** spec(C\*C) = {1, 3} is a multiplicity, not an energy. No
  Hamiltonian's spectrum moves. The Yang–Mills mass gap is untouched.
- **Not a new spectrum for a known operator.** The transformed harmonic
  oscillator Σ(P′ᵢ² + Q′ᵢ²) provably contains every level (n₁+n₂+n₃+3/2)ω by the
  transport in §3, but on (ran C)^⊥ its spectrum is uncontrolled and, as far as
  the literature search found, unstudied.
- **Not previously written up.** A search on 31 July 2026 turned up nothing
  connecting the counterexample to Weyl-algebra representation theory, though the
  algebraic consequences (Dixmier, image, vanishing conjectures) are well covered.

## 10. The pullback metric: an incomplete flat 3-manifold

Let g = DFᵀDF be the pullback of the Euclidean metric. Since A = ((DF)⁻¹)ᵀ,

    AᵀA = (DF)⁻¹(DF)⁻ᵀ = (DFᵀDF)⁻¹ = g⁻¹,

so ΣP′ᵢ² has the principal symbol of −Δ_g. Moreover det g = (det DF)² = 4 is
*constant*, so √g drops out of Δ_g = ∂ₖ(g^{kl}∂ₗ), and the first-order terms
agree exactly because the Piola divergences vanish (§3.2). Hence

    Σ(P′ᵢ² + Q′ᵢ²) = −Δ_g + |F|²

on the nose: the transformed oscillator is not merely conjugate to the flat
oscillator, it **is** the flat oscillator pulled back along F.

This gives a cleaner proof of §6. F is a local isometry (ℝ³, g) → ℝ³ flat. A
local isometry from a *complete* Riemannian manifold is a covering map; ℝ³ is
simply connected; so completeness would force F injective. Therefore **g is
incomplete** — the counterexample is an incomplete flat 3-manifold lying étale
over ℝ³. By Hopf–Rinow this is the same statement as §6, since geodesics of g
are exactly the lifts of straight lines, i.e. the integral curves of the X_v.

**The boundary is at finite distance, and measurable.** Because F is a local
isometry and the lift of y = tv (|v| = 1) satisfies |F(x(t))| = t, the parameter
t *is* g-arclength. So escape time equals distance to the metric boundary, and
§6's algebra locates it: the lift from the origin along v dies at the first
positive root of L(tv).

Which directions die is decided by a sign. Near t = 0, L ≈ 16v₁t. For v₁ < 0 the
origin sheet sits on the 3-sheeted side; at the wall −B/L > 0, so two *real*
roots escape and the origin branch is one of them. For v₁ > 0 the escaping pair
is complex, and the origin branch survives into the n = 3 region. Over 4000
random unit directions:

| quantity | value |
|---|---|
| directions reaching the boundary | ≈ 45% (exactly those with v₁ < 0) |
| minimum distance | **1.0732** |
| q10 / median / q90 | 1.147 / 1.670 / 5.78 |
| maximum | 1018 |

A tight cluster just above 1.07 with a long tail. Verified against 60-digit
Newton continuation for v ∝ (−1, 0.3, 0.2): |x| → ∞ at t = 2.30774, matching the
root of L(tv) to five digits.

Two cautions. First, the origin is a degenerate basepoint: L(0) = 0, so y = 0
lies *on* the escape locus, the cubic there degenerates to 4x₁ = 0, and the
fiber over the origin is a single point with two roots at infinity. Second,
K(y) = 27y₁y₃² − 9y₂y₃ + 8 — the common denominator of the shape-lemma
expressions for x₂ and x₃, and the squared factor in Δ — is **not** part of the
boundary. The continuation above passes through K = 0 at t ≈ 1.909 with
|x| ≈ 7. It is a chart singularity of the Gröbner presentation, and tracking x₁
alone across it is unreliable.

## Open questions

1. Deficiency indices of P′_v on C_c^∞(ℝ³), as a function of direction v. Given
   §10 this is a boundary-condition question: does the metric boundary force a
   choice, or is it thin enough to be invisible, as a removed point is in ℝⁿ for
   n ≥ 4? If the indices are nonzero, one classical system admits a family of
   inequivalent quantizations indexed by data on the escape locus.
2. Is {L = 0} smooth? Its singular locus should organize how sheets merge, and
   the empty-fiber curve of §4 lies in it.
3. Spectrum of the Friedrichs extension of −Δ_g + |F|² on (ran C)^⊥ — the
   boundary-localized states, if any. Numerically approachable by finite
   elements in g on a truncated domain, watching for eigenvalues that refuse to
   converge to (n₁+n₂+n₃+3/2)ω as the cutoff grows.
4. The construction generalizes to the whole family of counterexamples. Is the
   fiber-count function — equivalently the joint spectral multiplicity — a
   complete invariant separating them as quantum systems?

*Note on the Weyl algebra.* An earlier draft listed as open whether §3 yields an
explicit non-surjective endomorphism of A₃, via qᵢ ↦ Fᵢ, ∂ᵢ ↦ Σₖ Aᵢₖ∂ₖ. It does,
and the identities of §3 are exactly what makes it well-defined — but this is
the published Bass–Connell–Wright construction, already carried out for this map
in the July 2026 Secret Blogging Seminar discussion, and it is dimension-
preserving rather than the Belov-Kanel–Kontsevich stable equivalence. Injectivity
needs no argument: A₃ is simple, so every nonzero endomorphism is injective.

---

## Appendix A: Errata from the earlier draft

Two claims in a prior write-up of this material did not survive recomputation.

**A.1 — "One sample gave n = 2, on the thin set where a preimage is mid-escape."**
False, and impossible. The complex fiber has 3 simple points off {L = 0} and is
conjugation-invariant, so n is odd. The n = 2 reading came from a resultant-based
sampler that (a) lost roots to float conditioning in a badly scaled elimination,
and (b) contained `if abs(r) < 1e-9: continue`, discarding the x₁ = 0 sheet —
which is a genuine preimage whenever y₃ = 0, including at (−1/4, 0, 0) itself.
The same 28 sample points, run through the exact cubic, give 14 ones and 14
threes.

**A.2 — "Escape times scale as t ~ |x|^(1/2); the flow is complete; the pathology
is strictly joint."** False on all three counts, and this was the load-bearing
error. The true rate is |x| ~ |t − t\*|^(−1/2) — the sign of the exponent is
inverted, and a negative exponent means finite-time blowup rather than
polynomial growth. Completeness fails, necessarily, by §6. The pathology is
therefore not confined to the joint structure.

The numerics behind A.2 were not wrong so much as unrepresentative. The three
tested initial conditions have L = 9.5061, 31.8400, 52.5986 — all strictly
positive, hence all in the one-sheeted region, and their e₁-rays miss {L = 0}
entirely. Those three trajectories really are complete. Two compounding factors
hid the general case: the integrator ran forward in time only, and its adaptive
step h = min(h₀, 0.1/|X|) shrinks as the field grows, so it creeps toward t\*
and never arrives, reporting "no escape" from initial data that does blow up.

**A.3 — Branch-tracking artifacts.** Two further attempts to locate the boundary
by following the origin sheet's x₁-coordinate gave wrong answers before the
algebra settled it. Fixed-step root-matching hopped onto the persistent branch
near the wall, where the roots move fastest, and reported survival; the error is
invisible because the result looks like a clean convergence. A separate
continuation script failed for a different reason — an unguarded linear solve, on
a matrix whose determinant is the constant −2 but which is numerically singular
in float64 at large |x| through cancellation. Both were caught only by exact
elimination and 60-digit continuation. The rate |x₁| ~ |t − t\*|^(−1/2) follows
analytically from L → 0 in the eliminant and needs no fitting.

**Methodological note.** The A.2 passage was fluent, was framed as a measured
result, and explicitly presented itself as a self-correction of an earlier
hypothesis. It was the wrong correction. Confident prose about numerics is worth
nothing until the numerics are rerun — and a *self-correction* is not evidence of
care, since it can be fabricated as easily as the claim it purports to fix. The
same applies to agreement between two methods: corroboration is only as good as
the existence of both instruments. Every number in this note traces to a run
recorded in the session that produced it; where it does not, it has been cut.

## Appendix B: Reproduction

Symbolic checks (SymPy 1.14, exact over ℚ): det DF, identity A·DFᵀ = I, the three
Piola divergences, the 9 commutator coefficients, the lex Gröbner basis and its
shape, the elimination cubic with symbolic y, and the discriminant factorization.
The commutator check is the expensive one (degree-11 coefficients in 3 variables);
using `Poly` arithmetic over `QQ` rather than `expand` on expressions brings it
from minutes to seconds.

Fiber counts should be computed from sign(L(y)) directly. The accompanying
`fiber_and_escape.py` does this, along with escape-time prediction; it replaces
the resultant sampler, which is numerically fragile for this map.
