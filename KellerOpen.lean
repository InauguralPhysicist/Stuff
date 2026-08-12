/-
  Openness layer: the pointwise n₃(y*) ≥ 11 of tower_eleven propagates to a
  neighborhood — the "on an open neighborhood" clause of the exact3
  certificate, closing that trust-ledger row.

  Mechanism: det DF = -2 identically (the inverse Jacobian is exhibited
  explicitly as polynomial entries, both composition identities proved by
  ring), so F has an invertible strict derivative at every point, hence
  map F (𝓝 p) = 𝓝 (F p) (inverse function theorem), hence the same for F³.
  Around each of the eleven preimages take a ball, with radii halved below
  the minimum pairwise distance so the balls are disjoint; the images of
  those balls are neighborhoods of y*, and on their (finite) intersection
  every y has eleven distinct F³-preimages, one in each ball.

  tower_eleven_nhds — ∀ᶠ y in 𝓝 y*, n₃(y) ≥ 11.
-/
import KellerTower

open Filter Topology

namespace KellerOpen
open KellerBridge KellerTower

abbrev E3 := ℝ × ℝ × ℝ

/-! ### The Jacobian of F and its explicit inverse (det DF = -2) -/

noncomputable def J11 (a b c : ℝ) : ℝ := 3*a^2*b^3*c + 6*a*b^4 + 6*a*b^2*c + 7*b^3 + 3*b*c
noncomputable def J12 (a b c : ℝ) : ℝ := 3*a^3*b^2*c + 12*a^2*b^3 + 6*a^2*b*c + 21*a*b^2 + 3*a*c + 8*b
noncomputable def J13 (a b c : ℝ) : ℝ := a^3*b^3 + 3*a^2*b^2 + 3*a*b + 1
noncomputable def J21 (a b c : ℝ) : ℝ := 9*a^2*b^2*c + 18*a*b^3 + 12*a*b*c + 12*b^2 + 3*c
noncomputable def J22 (a b c : ℝ) : ℝ := 6*a^3*b*c + 27*a^2*b^2 + 6*a^2*c + 24*a*b + 1
noncomputable def J23 (a b c : ℝ) : ℝ := 3*a^3*b^2 + 6*a^2*b + 3*a
noncomputable def J31 (a b c : ℝ) : ℝ := -3*a^2*c - 6*a*b + 2
noncomputable def J32 (a b c : ℝ) : ℝ := -3*a^2
noncomputable def J33 (a b c : ℝ) : ℝ := -a^3
noncomputable def Ji11 (a b c : ℝ) : ℝ := 3*a^6*b*c + 9*a^5*b^2 + 3*a^5*c + 3*a^4*b - 4*a^3
noncomputable def Ji12 (a b c : ℝ) : ℝ := -3*a^6*b^2*c/2 - 9*a^5*b^3/2 - 3*a^5*b*c - 6*a^4*b^2 - 3*a^4*c/2 + a^3*b/2 + 3*a^2/2
noncomputable def Ji13 (a b c : ℝ) : ℝ := -3*a^6*b^4*c/2 - 9*a^5*b^5/2 - 6*a^5*b^3*c - 15*a^4*b^4 - 9*a^4*b^2*c - 16*a^3*b^3 - 6*a^3*b*c - 9*a^2*b^2/2 - 3*a^2*c/2 + 3*a*b/2 + 1/2
noncomputable def Ji21 (a b c : ℝ) : ℝ := 3*a^4*b*c + 9*a^3*b^2 + 3*a^3*c + 3*a^2*b - 3*a
noncomputable def Ji22 (a b c : ℝ) : ℝ := -3*a^4*b^2*c/2 - 9*a^3*b^3/2 - 3*a^3*b*c - 6*a^2*b^2 - 3*a^2*c/2 + 1
noncomputable def Ji23 (a b c : ℝ) : ℝ := -3*a^4*b^4*c/2 - 9*a^3*b^5/2 - 6*a^3*b^3*c - 15*a^2*b^4 - 9*a^2*b^2*c - 33*a*b^3/2 - 6*a*b*c - 6*b^2 - 3*c/2
noncomputable def Ji31 (a b c : ℝ) : ℝ := -9*a^5*b*c^2 - 45*a^4*b^2*c - 9*a^4*c^2 - 54*a^3*b^3 - 30*a^3*b*c - 27*a^2*b^2 + 9*a^2*c + 21*a*b + 1
noncomputable def Ji32 (a b c : ℝ) : ℝ := 9*a^5*b^2*c^2/2 + 45*a^4*b^3*c/2 + 9*a^4*b*c^2 + 27*a^3*b^4 + 75*a^3*b^2*c/2 + 9*a^3*c^2/2 + 81*a^2*b^3/2 + 21*a^2*b*c/2 + 3*a*b^2 - 3*a*c - 8*b
noncomputable def Ji33 (a b c : ℝ) : ℝ := 9*a^5*b^4*c^2/2 + 45*a^4*b^5*c/2 + 18*a^4*b^3*c^2 + 27*a^3*b^6 + 165*a^3*b^4*c/2 + 27*a^3*b^2*c^2 + 189*a^2*b^5/2 + 108*a^2*b^3*c + 18*a^2*b*c^2 + 111*a*b^4 + 117*a*b^2*c/2 + 9*a*c^2/2 + 89*b^3/2 + 21*b*c/2

/-! ### Row functionals and a strict-derivative row calculus -/

noncomputable def row (r1 r2 r3 : ℝ) : E3 →L[ℝ] ℝ :=
  r1 • (ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ))
    + r2 • ((ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ)))
    + r3 • ((ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ)))

@[simp] lemma row_apply (r1 r2 r3 : ℝ) (v : E3) :
    row r1 r2 r3 v = r1 * v.1 + r2 * v.2.1 + r3 * v.2.2 := by
  simp [row, smul_eq_mul]

lemma hrow_const (k : ℝ) (p : E3) :
    HasStrictFDerivAt (fun _ : E3 => k) (row 0 0 0) p := by
  have he : (row 0 0 0 : E3 →L[ℝ] ℝ) = 0 := by
    ext v; simp
  rw [he]; exact hasStrictFDerivAt_const k p

lemma hrow_x (p : E3) : HasStrictFDerivAt (fun q : E3 => q.1) (row 1 0 0) p := by
  have he : (row 1 0 0 : E3 →L[ℝ] ℝ) = ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ) := by
    ext v; simp
  rw [he]; exact hasStrictFDerivAt_fst

lemma hrow_y (p : E3) : HasStrictFDerivAt (fun q : E3 => q.2.1) (row 0 1 0) p := by
  have h : HasStrictFDerivAt (fun q : E3 => q.2.1)
      ((ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))) p :=
    hasStrictFDerivAt_fst.comp hasStrictFDerivAt_snd
  have he : (row 0 1 0 : E3 →L[ℝ] ℝ)
      = (ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ)) := by
    ext v; simp
  rw [he]; exact h

lemma hrow_z (p : E3) : HasStrictFDerivAt (fun q : E3 => q.2.2) (row 0 0 1) p := by
  have h : HasStrictFDerivAt (fun q : E3 => q.2.2)
      ((ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))) p :=
    hasStrictFDerivAt_snd.comp hasStrictFDerivAt_snd
  have he : (row 0 0 1 : E3 →L[ℝ] ℝ)
      = (ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ)) := by
    ext v; simp
  rw [he]; exact h

lemma hrow_add {f g : E3 → ℝ} {a1 a2 a3 b1 b2 b3 : ℝ} {p : E3}
    (hf : HasStrictFDerivAt f (row a1 a2 a3) p)
    (hg : HasStrictFDerivAt g (row b1 b2 b3) p) :
    HasStrictFDerivAt (fun q => f q + g q) (row (a1 + b1) (a2 + b2) (a3 + b3)) p := by
  have h : HasStrictFDerivAt (fun q => f q + g q)
      (row a1 a2 a3 + row b1 b2 b3) p := hf.add hg
  have he : (row a1 a2 a3 + row b1 b2 b3 : E3 →L[ℝ] ℝ)
      = row (a1 + b1) (a2 + b2) (a3 + b3) := by
    ext v
    simp only [ContinuousLinearMap.add_apply, row_apply]
    ring
  rw [← he]; exact h

lemma hrow_mul {f g : E3 → ℝ} {a1 a2 a3 b1 b2 b3 : ℝ} {p : E3}
    (hf : HasStrictFDerivAt f (row a1 a2 a3) p)
    (hg : HasStrictFDerivAt g (row b1 b2 b3) p) :
    HasStrictFDerivAt (fun q => f q * g q)
      (row (f p * b1 + g p * a1) (f p * b2 + g p * a2) (f p * b3 + g p * a3)) p := by
  have h : HasStrictFDerivAt (fun q => f q * g q)
      (f p • row b1 b2 b3 + g p • row a1 a2 a3) p := hf.mul hg
  have he : (f p • row b1 b2 b3 + g p • row a1 a2 a3 : E3 →L[ℝ] ℝ)
      = row (f p * b1 + g p * a1) (f p * b2 + g p * a2) (f p * b3 + g p * a3) := by
    ext v
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      row_apply, smul_eq_mul]
    ring
  rw [← he]; exact h

lemma hrow_align {f g : E3 → ℝ} {a1 a2 a3 b1 b2 b3 : ℝ} {p : E3}
    (hf : HasStrictFDerivAt f (row a1 a2 a3) p)
    (hfe : f = g) (h1 : a1 = b1) (h2 : a2 = b2) (h3 : a3 = b3) :
    HasStrictFDerivAt g (row b1 b2 b3) p := by
  rw [← hfe, ← h1, ← h2, ← h3]; exact hf

/-! ### The three rows of DF, by the row calculus -/

lemma hF1row (p : E3) :
    HasStrictFDerivAt (fun q : E3 => F1 q.1 q.2.1 q.2.2)
      (row (J11 p.1 p.2.1 p.2.2) (J12 p.1 p.2.1 p.2.2) (J13 p.1 p.2.1 p.2.2)) p := by
  have hx := hrow_x p
  have hy := hrow_y p
  have hz := hrow_z p
  have hm0c := hrow_const (1 : ℝ) p
  have hm0s0 := hrow_mul hm0c hz
  have hm1c := hrow_const (4 : ℝ) p
  have hm1s0 := hrow_mul hm1c hy
  have hm1s1 := hrow_mul hm1s0 hy
  have hm2c := hrow_const (3 : ℝ) p
  have hm2s0 := hrow_mul hm2c hx
  have hm2s1 := hrow_mul hm2s0 hy
  have hm2s2 := hrow_mul hm2s1 hz
  have hm3c := hrow_const (7 : ℝ) p
  have hm3s0 := hrow_mul hm3c hx
  have hm3s1 := hrow_mul hm3s0 hy
  have hm3s2 := hrow_mul hm3s1 hy
  have hm3s3 := hrow_mul hm3s2 hy
  have hm4c := hrow_const (3 : ℝ) p
  have hm4s0 := hrow_mul hm4c hx
  have hm4s1 := hrow_mul hm4s0 hx
  have hm4s2 := hrow_mul hm4s1 hy
  have hm4s3 := hrow_mul hm4s2 hy
  have hm4s4 := hrow_mul hm4s3 hz
  have hm5c := hrow_const (3 : ℝ) p
  have hm5s0 := hrow_mul hm5c hx
  have hm5s1 := hrow_mul hm5s0 hx
  have hm5s2 := hrow_mul hm5s1 hy
  have hm5s3 := hrow_mul hm5s2 hy
  have hm5s4 := hrow_mul hm5s3 hy
  have hm5s5 := hrow_mul hm5s4 hy
  have hm6c := hrow_const (1 : ℝ) p
  have hm6s0 := hrow_mul hm6c hx
  have hm6s1 := hrow_mul hm6s0 hx
  have hm6s2 := hrow_mul hm6s1 hx
  have hm6s3 := hrow_mul hm6s2 hy
  have hm6s4 := hrow_mul hm6s3 hy
  have hm6s5 := hrow_mul hm6s4 hy
  have hm6s6 := hrow_mul hm6s5 hz
  have ha0 := hrow_add hm0s0 hm1s1
  have ha1 := hrow_add ha0 hm2s2
  have ha2 := hrow_add ha1 hm3s3
  have ha3 := hrow_add ha2 hm4s4
  have ha4 := hrow_add ha3 hm5s5
  have ha5 := hrow_add ha4 hm6s6
  refine hrow_align ha5 ?_ ?_ ?_ ?_
  · funext q; dsimp only; simp only [F1]; ring
  · dsimp only; simp only [J11]; ring
  · dsimp only; simp only [J12]; ring
  · dsimp only; simp only [J13]; ring

lemma hF2row (p : E3) :
    HasStrictFDerivAt (fun q : E3 => F2 q.1 q.2.1 q.2.2)
      (row (J21 p.1 p.2.1 p.2.2) (J22 p.1 p.2.1 p.2.2) (J23 p.1 p.2.1 p.2.2)) p := by
  have hx := hrow_x p
  have hy := hrow_y p
  have hz := hrow_z p
  have hm0c := hrow_const (1 : ℝ) p
  have hm0s0 := hrow_mul hm0c hy
  have hm1c := hrow_const (3 : ℝ) p
  have hm1s0 := hrow_mul hm1c hx
  have hm1s1 := hrow_mul hm1s0 hz
  have hm2c := hrow_const (12 : ℝ) p
  have hm2s0 := hrow_mul hm2c hx
  have hm2s1 := hrow_mul hm2s0 hy
  have hm2s2 := hrow_mul hm2s1 hy
  have hm3c := hrow_const (6 : ℝ) p
  have hm3s0 := hrow_mul hm3c hx
  have hm3s1 := hrow_mul hm3s0 hx
  have hm3s2 := hrow_mul hm3s1 hy
  have hm3s3 := hrow_mul hm3s2 hz
  have hm4c := hrow_const (9 : ℝ) p
  have hm4s0 := hrow_mul hm4c hx
  have hm4s1 := hrow_mul hm4s0 hx
  have hm4s2 := hrow_mul hm4s1 hy
  have hm4s3 := hrow_mul hm4s2 hy
  have hm4s4 := hrow_mul hm4s3 hy
  have hm5c := hrow_const (3 : ℝ) p
  have hm5s0 := hrow_mul hm5c hx
  have hm5s1 := hrow_mul hm5s0 hx
  have hm5s2 := hrow_mul hm5s1 hx
  have hm5s3 := hrow_mul hm5s2 hy
  have hm5s4 := hrow_mul hm5s3 hy
  have hm5s5 := hrow_mul hm5s4 hz
  have ha0 := hrow_add hm0s0 hm1s1
  have ha1 := hrow_add ha0 hm2s2
  have ha2 := hrow_add ha1 hm3s3
  have ha3 := hrow_add ha2 hm4s4
  have ha4 := hrow_add ha3 hm5s5
  refine hrow_align ha4 ?_ ?_ ?_ ?_
  · funext q; dsimp only; simp only [F2]; ring
  · dsimp only; simp only [J21]; ring
  · dsimp only; simp only [J22]; ring
  · dsimp only; simp only [J23]; ring

lemma hF3row (p : E3) :
    HasStrictFDerivAt (fun q : E3 => F3 q.1 q.2.1 q.2.2)
      (row (J31 p.1 p.2.1 p.2.2) (J32 p.1 p.2.1 p.2.2) (J33 p.1 p.2.1 p.2.2)) p := by
  have hx := hrow_x p
  have hy := hrow_y p
  have hz := hrow_z p
  have hm0c := hrow_const (2 : ℝ) p
  have hm0s0 := hrow_mul hm0c hx
  have hm1c := hrow_const (-3 : ℝ) p
  have hm1s0 := hrow_mul hm1c hx
  have hm1s1 := hrow_mul hm1s0 hx
  have hm1s2 := hrow_mul hm1s1 hy
  have hm2c := hrow_const (-1 : ℝ) p
  have hm2s0 := hrow_mul hm2c hx
  have hm2s1 := hrow_mul hm2s0 hx
  have hm2s2 := hrow_mul hm2s1 hx
  have hm2s3 := hrow_mul hm2s2 hz
  have ha0 := hrow_add hm0s0 hm1s2
  have ha1 := hrow_add ha0 hm2s3
  refine hrow_align ha1 ?_ ?_ ?_ ?_
  · funext q; dsimp only; simp only [F3]; ring
  · dsimp only; simp only [J31]; ring
  · dsimp only; simp only [J32]; ring
  · dsimp only; simp only [J33]; ring

/-! ### DF as an explicit continuous linear equivalence -/

noncomputable def Fmap : E3 → E3 :=
  fun q => (F1 q.1 q.2.1 q.2.2, F2 q.1 q.2.1 q.2.2, F3 q.1 q.2.1 q.2.2)

noncomputable def matJ (p : E3) : E3 →L[ℝ] E3 :=
  (row (J11 p.1 p.2.1 p.2.2) (J12 p.1 p.2.1 p.2.2) (J13 p.1 p.2.1 p.2.2)).prod
    ((row (J21 p.1 p.2.1 p.2.2) (J22 p.1 p.2.1 p.2.2) (J23 p.1 p.2.1 p.2.2)).prod
      (row (J31 p.1 p.2.1 p.2.2) (J32 p.1 p.2.1 p.2.2) (J33 p.1 p.2.1 p.2.2)))

noncomputable def matJi (p : E3) : E3 →L[ℝ] E3 :=
  (row (Ji11 p.1 p.2.1 p.2.2) (Ji12 p.1 p.2.1 p.2.2) (Ji13 p.1 p.2.1 p.2.2)).prod
    ((row (Ji21 p.1 p.2.1 p.2.2) (Ji22 p.1 p.2.1 p.2.2) (Ji23 p.1 p.2.1 p.2.2)).prod
      (row (Ji31 p.1 p.2.1 p.2.2) (Ji32 p.1 p.2.1 p.2.2) (Ji33 p.1 p.2.1 p.2.2)))

lemma matJ_left (p : E3) : Function.LeftInverse (matJi p) (matJ p) := by
  intro v
  obtain ⟨v1, v2, v3⟩ := v
  simp only [matJ, matJi, ContinuousLinearMap.prod_apply, row_apply, Prod.ext_iff,
    J11, J12, J13, J21, J22, J23, J31, J32, J33,
    Ji11, Ji12, Ji13, Ji21, Ji22, Ji23, Ji31, Ji32, Ji33]
  refine ⟨?_, ?_, ?_⟩ <;> ring

lemma matJ_right (p : E3) : Function.RightInverse (matJi p) (matJ p) := by
  intro v
  obtain ⟨v1, v2, v3⟩ := v
  simp only [matJ, matJi, ContinuousLinearMap.prod_apply, row_apply, Prod.ext_iff,
    J11, J12, J13, J21, J22, J23, J31, J32, J33,
    Ji11, Ji12, Ji13, Ji21, Ji22, Ji23, Ji31, Ji32, Ji33]
  refine ⟨?_, ?_, ?_⟩ <;> ring

noncomputable def Jequiv (p : E3) : E3 ≃L[ℝ] E3 :=
  ContinuousLinearEquiv.equivOfInverse (matJ p) (matJi p) (matJ_left p) (matJ_right p)

lemma hFmap (p : E3) :
    HasStrictFDerivAt Fmap ((Jequiv p : E3 ≃L[ℝ] E3) : E3 →L[ℝ] E3) p := by
  have h : HasStrictFDerivAt Fmap (matJ p) p :=
    (hF1row p).prodMk ((hF2row p).prodMk (hF3row p))
  exact h

/-! ### Openness of F and F³ -/

lemma fmap_nhds (p : E3) : Filter.map Fmap (𝓝 p) = 𝓝 (Fmap p) :=
  (hFmap p).map_nhds_eq_of_equiv

noncomputable def F3map : E3 → E3 := fun q => Fmap (Fmap (Fmap q))

lemma f3_nhds (p : E3) : Filter.map F3map (𝓝 p) = 𝓝 (F3map p) := by
  have e : Filter.map F3map (𝓝 p)
      = Filter.map Fmap (Filter.map Fmap (Filter.map Fmap (𝓝 p))) := by
    rw [Filter.map_map, Filter.map_map]
    rfl
  rw [e, fmap_nhds, fmap_nhds, fmap_nhds]
  rfl

/-! ### The neighborhood version of the eleven-point count -/

theorem tower_eleven_nhds :
    ∀ᶠ y : E3 in 𝓝 ((yStar1, yStar2, yStar3) : E3),
      ∃ T : Finset E3, T.card = 11 ∧
        ∀ a b c : ℝ, (a, b, c) ∈ T →
          F1 (F1 (F1 a b c) (F2 a b c) (F3 a b c))
             (F2 (F1 a b c) (F2 a b c) (F3 a b c))
             (F3 (F1 a b c) (F2 a b c) (F3 a b c)) = y.1 ∧
          F2 (F1 (F1 a b c) (F2 a b c) (F3 a b c))
             (F2 (F1 a b c) (F2 a b c) (F3 a b c))
             (F3 (F1 a b c) (F2 a b c) (F3 a b c)) = y.2.1 ∧
          F3 (F1 (F1 a b c) (F2 a b c) (F3 a b c))
             (F2 (F1 a b c) (F2 a b c) (F3 a b c))
             (F3 (F1 a b c) (F2 a b c) (F3 a b c)) = y.2.2 := by
  classical
  obtain ⟨S, hScard, hSmem⟩ := tower_eleven
  have hF3mk : ∀ a b c : ℝ, F3map (a, b, c)
      = (F1 (F1 (F1 a b c) (F2 a b c) (F3 a b c))
           (F2 (F1 a b c) (F2 a b c) (F3 a b c))
           (F3 (F1 a b c) (F2 a b c) (F3 a b c)),
         F2 (F1 (F1 a b c) (F2 a b c) (F3 a b c))
           (F2 (F1 a b c) (F2 a b c) (F3 a b c))
           (F3 (F1 a b c) (F2 a b c) (F3 a b c)),
         F3 (F1 (F1 a b c) (F2 a b c) (F3 a b c))
           (F2 (F1 a b c) (F2 a b c) (F3 a b c))
           (F3 (F1 a b c) (F2 a b c) (F3 a b c))) := by
    intro a b c
    simp only [F3map, Fmap]
  have hSm : ∀ p ∈ S, F3map p = ((yStar1, yStar2, yStar3) : E3) := by
    intro p hp
    obtain ⟨a, b, c⟩ := p
    obtain ⟨h1, h2, h3⟩ := hSmem a b c hp
    rw [hF3mk a b c, Prod.ext_iff, Prod.ext_iff]
    exact ⟨h1, h2, h3⟩
  -- radii: half the distance to the nearest other point of S
  have herase : ∀ p ∈ S, ((S.erase p).image (dist p)).Nonempty := by
    intro p hp
    refine Finset.Nonempty.image ?_ _
    rw [← Finset.card_pos, Finset.card_erase_of_mem hp, hScard]
    norm_num
  set r : E3 → ℝ := fun p =>
    if h : ((S.erase p).image (dist p)).Nonempty
    then (((S.erase p).image (dist p)).min' h) / 2 else 1
    with hrdef
  have hrpos : ∀ p ∈ S, 0 < r p := by
    intro p hp
    rw [hrdef]
    simp only [dif_pos (herase p hp)]
    have : ∀ d ∈ (S.erase p).image (dist p), 0 < d := by
      intro d hd
      obtain ⟨q, hq, hdq⟩ := Finset.mem_image.mp hd
      have hqp : q ≠ p := (Finset.mem_erase.mp hq).1
      rw [← hdq]
      exact dist_pos.mpr (Ne.symm hqp)
    have := (Finset.lt_min'_iff _ (herase p hp)).mpr this
    linarith
  have hrle : ∀ p ∈ S, ∀ q ∈ S, q ≠ p → r p ≤ dist p q / 2 := by
    intro p hp q hq hqp
    rw [hrdef]
    simp only [dif_pos (herase p hp)]
    have hmem : dist p q ∈ (S.erase p).image (dist p) :=
      Finset.mem_image.mpr ⟨q, Finset.mem_erase.mpr ⟨hqp, hq⟩, rfl⟩
    have := Finset.min'_le _ _ hmem
    linarith
  -- the finite intersection of the ball images is a neighborhood of y*
  have hU : (⋂ p ∈ S, F3map '' Metric.ball p (r p))
      ∈ 𝓝 ((yStar1, yStar2, yStar3) : E3) := by
    rw [Filter.biInter_finset_mem]
    intro p hp
    rw [← hSm p hp, ← f3_nhds p]
    exact Filter.image_mem_map (Metric.ball_mem_nhds p (hrpos p hp))
  filter_upwards [hU] with y hy
  rw [Set.mem_iInter₂] at hy
  -- choose one preimage of y in each ball
  set g : E3 → E3 := fun p =>
    if h : y ∈ F3map '' Metric.ball p (r p) then h.choose else p with hgdef
  have hgspec : ∀ p ∈ S, g p ∈ Metric.ball p (r p) ∧ F3map (g p) = y := by
    intro p hp
    have hyp := hy p hp
    rw [hgdef]
    simp only [dif_pos hyp]
    exact ⟨hyp.choose_spec.1, hyp.choose_spec.2⟩
  have hinj : Set.InjOn g S := by
    intro p hp p' hp' heq
    by_contra hne
    have h1 := (hgspec p hp).1
    have h2 := (hgspec p' hp').1
    rw [heq] at h1
    rw [Metric.mem_ball] at h1 h2
    have htri : dist p p' ≤ dist (g p') p + dist (g p') p' := by
      rw [dist_comm (g p') p]
      exact dist_triangle p (g p') p'
    have hle1 : r p ≤ dist p p' / 2 := hrle p hp p' hp' (Ne.symm hne)
    have hle2 : r p' ≤ dist p' p / 2 := hrle p' hp' p hp hne
    rw [dist_comm p' p] at hle2
    linarith
  refine ⟨S.image g, ?_, ?_⟩
  · rw [Finset.card_image_of_injOn hinj, hScard]
  · intro a b c hmem
    obtain ⟨p, hp, hpe⟩ := Finset.mem_image.mp hmem
    have hFy := (hgspec p hp).2
    rw [hpe] at hFy
    rw [hF3mk a b c, Prod.ext_iff, Prod.ext_iff] at hFy
    exact ⟨hFy.1, hFy.2.1, hFy.2.2⟩

end KellerOpen
