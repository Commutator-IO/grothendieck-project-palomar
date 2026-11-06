module

public import Mathlib

@[expose] public section


/-!
# Folder 82, pages 77–78: the conic in characteristic 2 and Frobenius, split case

The modernised reading `transcripts/82/82.modern.tex` (« Caractéristique 2 : le Frobenius »,
pages 77 and 78) takes, over a base where `2 = 0`, the module `g̃` of traceless `2 × 2`
matrices with `φ(u, v) = Tr(uv)`. Since `Tr 1 = 2 = 0`, `𝒪_S · 1 ⊂ g̃` and it is the kernel
of `φ` (58). The morphism (59) sends a Borel, that is an isotropic line `L ⊂ g̃` (an element
of square zero), to its `φ`-orthogonal; every such hyperplane contains `1`, so (59) factors
through `P(g̃/𝒪_S)` (60), and the page states that (60) is the relative Frobenius, not a
monomorphism. The edition checks it in the split case (footnote): with `X̃ = E₁₂`,
`Ỹ = E₂₁`, `H̃ = diag(1, −1)`, the conic `xy = z²` is parametrised by `(s : t) ↦ (s², t², st)`
and the orthogonal of `𝒪(s²X̃ + t²Ỹ + stH̃)` is the hyperplane `t²x + s²y = 0`, which
contains `H̃ = 1` and depends only on `(s² : t²)`.

This is finding `82-char2-conic-frobenius` of `src/content/findings.ts`, in the split case,
over any commutative ring `R` with `2 = 0`, for the coordinates `u = xX̃ + yỸ + zH̃`.

* `coord_mul_self`: `u² = (xy + z²) · 1`, so `u` has square zero iff `xy = z²` in
  characteristic 2: the conic.
* `traceless_iff`: `g̃` is the set of the `coord x y z`.
* `tH_eq_one`, `one_mem_traceless`, `ker_phi` (58): `H̃ = 1`, and `1` spans the kernel of
  `φ` on `g̃`.
* `vst_mul_self`: `s²X̃ + t²Ỹ + stH̃` has square zero, a point of the conic.
* `trace_mul_vst`, `orth_iff`: its orthogonal is `t²x + s²y = 0`, which contains `1`
  (`one_mem_orth`).
* `orth_smul`: it depends only on `(s² : t²)`, so (60) is `(s : t) ↦ (s² : t²)`.
* `not_mono`: over `R = 𝔽₂[ε]/(ε²)` the distinct points `(1 : ε)` and `(1 : 0)` of `P¹(R)`
  have the same orthogonal hyperplane: (60) is not a monomorphism.

The canonical isomorphism (61) `P(g̃/𝒪_S) ≃ X^{(2)}` for a twisted conic over an arbitrary
base is not formalised: mathlib has neither conics over a base nor the relative Frobenius.
## Pages 26–27: `sl(2)` in characteristic 2, split case

The reading (« Caractéristique 2 : algèbres couplées et plans affines symplectiques ») says
that over a base with `2 = 0`, `sl(2)` has centre `𝔷 = 𝒪H̃` equal to its derived algebra,
`V = sl(2)/𝔷` of rank 2 and `Λ²V ≅ 𝔷` (the Heisenberg algebra), so that a form of `sl(2)` is
a pair `(V, E)`, `E` an extension of `V` by `det V`; the automorphism group of a form is a
form of `GL(V) ⋉ V`, smooth of relative dimension 6, while that of a symplectic affine plane
is `SL(V) ⋉ V`, of dimension 5. This is finding `82-char2-sl2-forms-affine`, in coordinates
`xX̃ + yỸ + zH̃` (`slMk`) over any commutative ring `R` with `2 = 0`:

* `lie_slMk`, `central_iff`, `slMk_H_eq_lie`: `[u, u'] = (xy' − yx') H̃`; the centre is `R·H̃`,
  and every central element is a bracket.
* `lieHom_eq_autFun`: every Lie endomorphism is `autFun g a b`,
  `u ↦ g(x, y) + (ax + by + det g · z) H̃`, the parameters unique (`autFun_inj`), composing as
  in `GL₂ ⋉ Hom(V, det V)` (`autFun_comp`); `bijective_iff`: it is an automorphism iff
  `det g` is a unit — `Aut(sl(2))(R) ≅ GL₂(R) ⋉ R²`, the automorphisms of the split pair
  `(V, E)`.
* `bijective_fix_iff`: the automorphisms fixing `H̃` (trivial on `det V ≅ 𝒪`) are those with
  `det g = 1`: `SL₂(R) ⋉ R²`, the symplectic affine group.
* `derEquiv`, `finrank_der`: the derivations (the Lie algebra of `Aut`) are `gl₂ × R²`, free of
  rank 6; `derFixEquiv`, `finrank_derFix`: those killing `H̃` are `sl₂ × R²`, rank 5.

Not formalised: forms over a base (descent), `gp(1)`, the coupling of `E` with `E′`, and
smoothness of the automorphism schemes (only their points and Lie algebras are computed).
-/

open Matrix

namespace Folder82

variable {R : Type*} [CommRing R]

/-- `xX̃ + yỸ + zH̃` with `X̃ = E₁₂`, `Ỹ = E₂₁`, `H̃ = diag(1, −1)`. -/
def coord (x y z : R) : Matrix (Fin 2) (Fin 2) R := !![z, x; y, -z]

/-- `H̃ = diag(1, −1)`. -/
def tH : Matrix (Fin 2) (Fin 2) R := !![1, 0; 0, -1]

/-- The generator `s²X̃ + t²Ỹ + stH̃` of the isotropic line of the point `(s : t)`. -/
def vst (s t : R) : Matrix (Fin 2) (Fin 2) R := coord (s ^ 2) (t ^ 2) (s * t)

theorem coord_eq (x y z : R) :
    coord x y z = x • !![0, 1; 0, 0] + y • !![0, 0; 1, 0] + z • tH := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [coord, tH]

/-- `u² = (xy + z²) · 1`: `u` has square zero iff `xy + z² = 0`. -/
theorem coord_mul_self (x y z : R) :
    coord x y z * coord x y z = (x * y + z ^ 2) • (1 : Matrix (Fin 2) (Fin 2) R) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [coord] <;> ring

/-- `g̃`, the traceless matrices, are the `coord x y z`. -/
theorem traceless_iff (u : Matrix (Fin 2) (Fin 2) R) :
    u.trace = 0 ↔ ∃ x y z, u = coord x y z := by
  refine ⟨fun h => ⟨u 0 1, u 1 0, u 0 0, ?_⟩, ?_⟩
  · rw [trace_fin_two] at h
    ext i j; fin_cases i <;> fin_cases j <;> simp [coord]; linear_combination h
  · rintro ⟨x, y, z, rfl⟩
    simp [coord, trace_fin_two]

/-- In characteristic 2, `H̃ = 1`. -/
theorem tH_eq_one (h2 : (2 : R) = 0) : (tH : Matrix (Fin 2) (Fin 2) R) = 1 := by
  have : (-1 : R) = 1 := by linear_combination -h2
  ext i j; fin_cases i <;> fin_cases j <;> simp [tH, this]

/-- (58): in characteristic 2, `1 ∈ g̃`. -/
theorem one_mem_traceless (h2 : (2 : R) = 0) : (1 : Matrix (Fin 2) (Fin 2) R).trace = 0 := by
  simp [h2]

/-- (58): in characteristic 2, the kernel of `φ(u, v) = Tr(uv)` on `g̃` is `R · 1`. -/
theorem ker_phi (h2 : (2 : R) = 0) (x y z : R) :
    (∀ v : Matrix (Fin 2) (Fin 2) R, v.trace = 0 → (coord x y z * v).trace = 0) ↔
      ∃ c : R, coord x y z = c • 1 := by
  constructor
  · intro h
    have h1 : y = 0 := by
      simpa [coord, trace_fin_two] using h (coord 1 0 0) (by simp [coord, trace_fin_two])
    have h2' : x = 0 := by
      simpa [coord, trace_fin_two] using h (coord 0 1 0) (by simp [coord, trace_fin_two])
    refine ⟨z, ?_⟩
    have hz : -z = z := by linear_combination (-z) * h2
    ext i j; fin_cases i <;> fin_cases j <;> simp [coord, h1, h2', hz]
  · rintro ⟨c, hc⟩ v hv
    rw [hc, smul_mul_assoc, one_mul, trace_smul, hv, smul_zero]

/-- The point `(s : t)`: `s²X̃ + t²Ỹ + stH̃` has square zero in characteristic 2. -/
theorem vst_mul_self (h2 : (2 : R) = 0) (s t : R) : vst s t * vst s t = 0 := by
  rw [vst, coord_mul_self, ← mul_pow, ← two_mul, h2, zero_mul, zero_smul]

/-- `φ(u, s²X̃ + t²Ỹ + stH̃) = t²x + s²y` in characteristic 2. -/
theorem trace_mul_vst (h2 : (2 : R) = 0) (x y z s t : R) :
    (coord x y z * vst s t).trace = t ^ 2 * x + s ^ 2 * y := by
  simp only [vst, coord, trace_fin_two, mul_fin_two, of_apply, cons_val', cons_val_zero,
    cons_val_one, empty_val', cons_val_fin_one]
  linear_combination (z * s * t) * h2

/-- The orthogonal of the isotropic line of `(s : t)` is the hyperplane `t²x + s²y = 0`. -/
theorem orth_iff (h2 : (2 : R) = 0) (x y z s t : R) :
    (coord x y z * vst s t).trace = 0 ↔ t ^ 2 * x + s ^ 2 * y = 0 := by
  rw [trace_mul_vst h2]

/-- It contains `1 = H̃`, so (59) factors through `P(g̃/𝒪_S)`. -/
theorem one_mem_orth (h2 : (2 : R) = 0) (s t : R) : ((1 : Matrix (Fin 2) (Fin 2) R) *
    vst s t).trace = 0 := by
  rw [← tH_eq_one h2]
  exact (trace_mul_vst h2 0 0 1 s t).trans (by ring)

/-- It depends only on `(s² : t²)`: (60) is `(s : t) ↦ (s² : t²)`. -/
theorem orth_smul (h2 : (2 : R) = 0) {s t s' t' c : R} (hs : s' ^ 2 = c * s ^ 2)
    (ht : t' ^ 2 = c * t ^ 2) (x y z : R) :
    (coord x y z * vst s' t').trace = c * (coord x y z * vst s t).trace := by
  rw [trace_mul_vst h2, trace_mul_vst h2, hs, ht]
  ring

/-- (60) is not a monomorphism: over `𝔽₂[ε]/(ε²)` the points `(1 : ε)` and `(1 : 0)` of
`P¹` are distinct (no unit carries one pair to the other), and their isotropic lines have
the same orthogonal hyperplane. -/
theorem not_mono :
    (¬ ∃ c : (DualNumber (ZMod 2))ˣ,
        (1 : DualNumber (ZMod 2)) = c * 1 ∧ DualNumber.eps = (c : DualNumber (ZMod 2)) * 0) ∧
      ∀ x y z : DualNumber (ZMod 2),
        (coord x y z * vst 1 DualNumber.eps).trace = (coord x y z * vst 1 0).trace := by
  have h2 : (2 : DualNumber (ZMod 2)) = 0 := by ext <;> simp <;> rfl
  refine ⟨?_, fun x y z => ?_⟩
  · rintro ⟨c, -, h⟩
    simpa using congrArg TrivSqZeroExt.snd h
  · rw [trace_mul_vst h2, trace_mul_vst h2, sq, DualNumber.eps_mul_eps]
    ring

/-! ### Pages 26–27: sl(2) in characteristic 2, its automorphisms and derivations -/

open LieAlgebra.SpecialLinear in
/-- `sl(2)` over `R`. -/
abbrev Sl2 (R : Type*) [CommRing R] := sl (Fin 2) R

/-- The element `xX̃ + yỸ + zH̃` of `sl(2)`. -/
def slMk (x y z : R) : Sl2 R :=
  ⟨coord x y z, by simp [LieAlgebra.SpecialLinear.sl, coord, trace_fin_two]⟩

@[simp] theorem slMk_val (x y z : R) : (slMk x y z).val = coord x y z := rfl

theorem slMk_eta (u : Sl2 R) : u = slMk (u.val 0 1) (u.val 1 0) (u.val 0 0) := by
  have h : u.val.trace = 0 := u.2
  rw [trace_fin_two] at h
  apply Subtype.ext
  ext i j; fin_cases i <;> fin_cases j <;> simp [coord]; linear_combination h

theorem slMk_inj {x y z x' y' z' : R} (h : slMk x y z = slMk x' y' z') :
    x = x' ∧ y = y' ∧ z = z' := by
  have := congrArg Subtype.val h
  exact ⟨by simpa [coord] using congrFun (congrFun this 0) 1,
    by simpa [coord] using congrFun (congrFun this 1) 0,
    by simpa [coord] using congrFun (congrFun this 0) 0⟩

theorem slMk_add (x y z x' y' z' : R) :
    slMk x y z + slMk x' y' z' = slMk (x + x') (y + y') (z + z') := by
  apply Subtype.ext
  ext i j; fin_cases i <;> fin_cases j <;> simp [coord]; ring

theorem slMk_sub (x y z x' y' z' : R) :
    slMk x y z - slMk x' y' z' = slMk (x - x') (y - y') (z - z') := by
  apply Subtype.ext
  ext i j; fin_cases i <;> fin_cases j <;> simp [coord]; ring

theorem slMk_smul (c x y z : R) : c • slMk x y z = slMk (c * x) (c * y) (c * z) := by
  apply Subtype.ext
  ext i j; fin_cases i <;> fin_cases j <;> simp [coord]

theorem slMk_zero : slMk 0 0 0 = (0 : Sl2 R) := by
  apply Subtype.ext
  ext i j; fin_cases i <;> fin_cases j <;> simp [coord]

/-- In characteristic 2, `sl(2)` is the Heisenberg algebra: `[u, u'] = (xy' − yx') H̃`. -/
theorem lie_slMk (h2 : (2 : R) = 0) (x y z x' y' z' : R) :
    ⁅slMk x y z, slMk x' y' z'⁆ = slMk 0 0 (x * y' - y * x') := by
  apply Subtype.ext
  rw [LieAlgebra.SpecialLinear.sl_bracket]
  ext i j; fin_cases i <;> fin_cases j <;> simp [coord]
  · ring
  · linear_combination (z * x' - x * z') * h2
  · linear_combination (y * z' - z * y') * h2
  · ring

/-- The centre of `sl(2)` in characteristic 2 is `R · H̃`, and every central element is a
bracket: centre = derived algebra, `V = sl(2)/R·H̃` free of rank 2, `Λ²V ≅ R·H̃`. -/
theorem central_iff (h2 : (2 : R) = 0) (u : Sl2 R) :
    (∀ v : Sl2 R, ⁅u, v⁆ = 0) ↔ ∃ z : R, u = slMk 0 0 z := by
  refine ⟨fun h => ⟨u.val 0 0, ?_⟩, ?_⟩
  · rw [slMk_eta u] at h ⊢
    have h1 := h (slMk 1 0 0)
    have h2' := h (slMk 0 1 0)
    rw [lie_slMk h2, ← slMk_zero] at h1 h2'
    obtain ⟨-, -, h1⟩ := slMk_inj h1
    obtain ⟨-, -, h2'⟩ := slMk_inj h2'
    simp only [mul_zero, mul_one, zero_sub, neg_eq_zero, sub_zero] at h1 h2'
    simp [h1, h2', coord]
  · rintro ⟨z, rfl⟩ v
    rw [slMk_eta v, lie_slMk h2, ← slMk_zero]
    simp

theorem slMk_H_eq_lie (h2 : (2 : R) = 0) (z : R) :
    slMk 0 0 z = ⁅(slMk 1 0 0 : Sl2 R), slMk 0 z 0⁆ := by
  rw [lie_slMk h2]; simp

/-- The Lie endomorphism `xX̃ + yỸ + zH̃ ↦ g(x, y) + (ax + by + det g · z) H̃`, for a `2 × 2`
matrix `g` and `a, b ∈ R`: the pair `(g, (a, b))` of `GL(V) ⋉ Hom(V, det V)`. -/
def autFun (h2 : (2 : R) = 0) (g : Matrix (Fin 2) (Fin 2) R) (a b : R) : Sl2 R →ₗ⁅R⁆ Sl2 R where
  toFun u := slMk (g 0 0 * u.val 0 1 + g 0 1 * u.val 1 0) (g 1 0 * u.val 0 1 + g 1 1 * u.val 1 0)
    (a * u.val 0 1 + b * u.val 1 0 + g.det * u.val 0 0)
  map_add' u v := by
    rw [slMk_add]; congr 1 <;> simp <;> ring
  map_smul' c u := by
    rw [RingHom.id_apply, slMk_smul]; congr 1 <;> simp <;> ring
  map_lie' {u v} := by
    conv_lhs => rw [slMk_eta u, slMk_eta v, lie_slMk h2]
    rw [lie_slMk h2]
    simp only [slMk_val, coord, of_apply, cons_val', cons_val_zero, cons_val_one,
      empty_val', cons_val_fin_one, det_fin_two]
    congr 1 <;> ring

theorem autFun_slMk (h2 : (2 : R) = 0) (g : Matrix (Fin 2) (Fin 2) R) (a b x y z : R) :
    autFun h2 g a b (slMk x y z) =
      slMk (g 0 0 * x + g 0 1 * y) (g 1 0 * x + g 1 1 * y) (a * x + b * y + g.det * z) := by
  simp [autFun, coord]

/-- **Every Lie endomorphism of `sl(2)` is an `autFun`** (characteristic 2): it sends the
centre `R · H̃` into itself, and `H̃ = [X̃, Ỹ]` to `det g · H̃`. -/
theorem lieHom_eq_autFun (h2 : (2 : R) = 0) (φ : Sl2 R →ₗ⁅R⁆ Sl2 R) :
    φ = autFun h2 !![(φ (slMk 1 0 0)).val 0 1, (φ (slMk 0 1 0)).val 0 1;
      (φ (slMk 1 0 0)).val 1 0, (φ (slMk 0 1 0)).val 1 0]
      ((φ (slMk 1 0 0)).val 0 0) ((φ (slMk 0 1 0)).val 0 0) := by
  ext1 u
  have hH : φ (slMk 0 0 1) = ⁅φ (slMk 1 0 0), φ (slMk 0 1 0)⁆ := by
    rw [← LieHom.map_lie, lie_slMk h2]; simp
  have hu : u = u.val 0 1 • slMk 1 0 0 + u.val 1 0 • slMk 0 1 0 + u.val 0 0 • slMk 0 0 1 := by
    conv_lhs => rw [slMk_eta u]
    simp only [slMk_smul, slMk_add]; congr 1 <;> ring
  conv_lhs => rw [hu, map_add, map_add, map_smul, map_smul, map_smul, hH]
  conv_rhs => rw [slMk_eta u, autFun_slMk]
  rw [slMk_eta (φ (slMk 1 0 0)), slMk_eta (φ (slMk 0 1 0)), lie_slMk h2]
  simp only [slMk_smul, slMk_add, slMk_val, coord, of_apply, cons_val', cons_val_zero,
    cons_val_one, empty_val', cons_val_fin_one, det_fin_two]
  congr 1 <;> ring

/-- `autFun` determines its parameters. -/
theorem autFun_inj (h2 : (2 : R) = 0) {g g' : Matrix (Fin 2) (Fin 2) R} {a b a' b' : R}
    (h : autFun h2 g a b = autFun h2 g' a' b') : g = g' ∧ a = a' ∧ b = b' := by
  have hX := congrArg (· (slMk 1 0 0)) h
  have hY := congrArg (· (slMk 0 1 0)) h
  simp only [autFun_slMk, mul_one, mul_zero, add_zero, zero_add] at hX hY
  obtain ⟨h1, h2', h3⟩ := slMk_inj hX
  obtain ⟨h4, h5, h6⟩ := slMk_inj hY
  refine ⟨?_, h3, h6⟩
  ext i j; fin_cases i <;> fin_cases j <;> simp [h1, h2', h4, h5]

/-- The composition law of `GL(V) ⋉ Hom(V, det V)`. -/
theorem autFun_comp (h2 : (2 : R) = 0) (g g' : Matrix (Fin 2) (Fin 2) R) (a b a' b' : R) :
    (autFun h2 g a b).comp (autFun h2 g' a' b') = autFun h2 (g * g')
      (a * g' 0 0 + b * g' 1 0 + g.det * a') (a * g' 0 1 + b * g' 1 1 + g.det * b') := by
  ext1 u
  rw [LieHom.comp_apply, slMk_eta u, autFun_slMk, autFun_slMk, autFun_slMk, det_mul]
  simp only [mul_apply, Fin.sum_univ_two]
  congr 1 <;> ring

/-- `autFun g a b` is bijective iff `det g` is a unit. -/
theorem bijective_autFun_iff (h2 : (2 : R) = 0) (g : Matrix (Fin 2) (Fin 2) R) (a b : R) :
    Function.Bijective (autFun h2 g a b) ↔ IsUnit g.det := by
  constructor
  · intro hφ
    obtain ⟨u, hu⟩ := hφ.2 (slMk 1 0 0)
    obtain ⟨v, hv⟩ := hφ.2 (slMk 0 1 0)
    rw [slMk_eta u, autFun_slMk] at hu
    rw [slMk_eta v, autFun_slMk] at hv
    obtain ⟨e1, e2, -⟩ := slMk_inj hu
    obtain ⟨e3, e4, -⟩ := slMk_inj hv
    refine isUnit_iff_exists_inv.2 ⟨u.val 0 1 * v.val 1 0 - u.val 1 0 * v.val 0 1, ?_⟩
    rw [det_fin_two]
    linear_combination (g 1 0 * v.val 0 1 + g 1 1 * v.val 1 0) * e1 + e4 -
      (g 0 0 * v.val 0 1 + g 0 1 * v.val 1 0) * e2
  · rintro ⟨d, hd⟩
    have hde : g.det * ↑d⁻¹ = 1 := by rw [← hd, Units.mul_inv]
    let ψ : Sl2 R → Sl2 R := fun w =>
      slMk (↑d⁻¹ * (g 1 1 * w.val 0 1 - g 0 1 * w.val 1 0))
        (↑d⁻¹ * (g 0 0 * w.val 1 0 - g 1 0 * w.val 0 1))
        (↑d⁻¹ * (w.val 0 0 - a * (↑d⁻¹ * (g 1 1 * w.val 0 1 - g 0 1 * w.val 1 0)) -
          b * (↑d⁻¹ * (g 0 0 * w.val 1 0 - g 1 0 * w.val 0 1))))
    rw [det_fin_two] at hde
    refine Function.bijective_iff_has_inverse.2 ⟨ψ, fun w => ?_, fun w => ?_⟩ <;>
      obtain ⟨x, y, z, rfl⟩ : ∃ x y z, w = slMk x y z := ⟨_, _, _, slMk_eta w⟩
    · simp only [ψ, autFun_slMk, slMk_val, coord, of_apply, cons_val', cons_val_zero,
        cons_val_one, empty_val', cons_val_fin_one, det_fin_two]
      congr 1
      · linear_combination x * hde
      · linear_combination y * hde
      · linear_combination (z - ↑d⁻¹ * a * x - ↑d⁻¹ * b * y) * hde
    · simp only [ψ, autFun_slMk, slMk_val, coord, of_apply, cons_val', cons_val_zero,
        cons_val_one, empty_val', cons_val_fin_one, det_fin_two]
      congr 1
      · linear_combination x * hde
      · linear_combination y * hde
      · linear_combination (z - a * (↑d⁻¹ * (g 1 1 * x - g 0 1 * y)) -
          b * (↑d⁻¹ * (g 0 0 * y - g 1 0 * x))) * hde

/-- **Automorphisms of `sl(2)` in characteristic 2**: a Lie endomorphism is bijective iff it is
`autFun g a b` with `det g` a unit, the parameters being unique. So `Aut(sl(2))(R)` is
`GL₂(R) ⋉ R²` (`autFun_comp`), the automorphisms of the split pair `(V, E)`, `E` an extension
of `V` by `det V`: an affine group of dimension 6. -/
theorem bijective_iff (h2 : (2 : R) = 0) (φ : Sl2 R →ₗ⁅R⁆ Sl2 R) :
    Function.Bijective φ ↔ ∃ (g : Matrix (Fin 2) (Fin 2) R) (a b : R),
      IsUnit g.det ∧ φ = autFun h2 g a b := by
  refine ⟨fun h => ⟨_, _, _, ?_, lieHom_eq_autFun h2 φ⟩, ?_⟩
  · rw [← bijective_autFun_iff h2, ← lieHom_eq_autFun h2 φ]; exact h
  · rintro ⟨g, a, b, hg, rfl⟩
    exact (bijective_autFun_iff h2 g a b).2 hg

/-- The automorphisms fixing `H̃`, i.e. acting trivially on `det V ≅ 𝒪`: those of a
symplectic affine plane, `SL₂(R) ⋉ R²`, of dimension 5. -/
theorem bijective_fix_iff (h2 : (2 : R) = 0) (φ : Sl2 R →ₗ⁅R⁆ Sl2 R) :
    (Function.Bijective φ ∧ φ (slMk 0 0 1) = slMk 0 0 1) ↔
      ∃ (g : Matrix (Fin 2) (Fin 2) R) (a b : R), g.det = 1 ∧ φ = autFun h2 g a b := by
  rw [bijective_iff h2]
  constructor
  · rintro ⟨⟨g, a, b, -, rfl⟩, hH⟩
    rw [autFun_slMk] at hH
    exact ⟨g, a, b, by simpa using (slMk_inj hH).2.2, rfl⟩
  · rintro ⟨g, a, b, hg, rfl⟩
    refine ⟨⟨g, a, b, hg ▸ isUnit_one, rfl⟩, ?_⟩
    rw [autFun_slMk, hg]; simp

/-- The derivation `xX̃ + yỸ + zH̃ ↦ G(x, y) + (ax + by + tr G · z) H̃`. -/
def derFun (h2 : (2 : R) = 0) (G : Matrix (Fin 2) (Fin 2) R) (a b : R) :
    LieDerivation R (Sl2 R) (Sl2 R) where
  toFun u := slMk (G 0 0 * u.val 0 1 + G 0 1 * u.val 1 0) (G 1 0 * u.val 0 1 + G 1 1 * u.val 1 0)
    (a * u.val 0 1 + b * u.val 1 0 + G.trace * u.val 0 0)
  map_add' u v := by
    rw [slMk_add]; congr 1 <;> simp <;> ring
  map_smul' c u := by
    rw [RingHom.id_apply, slMk_smul]; congr 1 <;> simp <;> ring
  leibniz' u v := by
    simp only [LinearMap.coe_mk, AddHom.coe_mk]
    conv_lhs => rw [slMk_eta u, slMk_eta v, lie_slMk h2]
    conv_rhs => rw [slMk_eta u, slMk_eta v]
    rw [lie_slMk h2, lie_slMk h2]
    simp only [slMk_val, coord, of_apply, cons_val', cons_val_zero, cons_val_one,
      empty_val', cons_val_fin_one, trace_fin_two]
    rw [slMk_sub]
    congr 1 <;> ring

theorem derFun_slMk (h2 : (2 : R) = 0) (G : Matrix (Fin 2) (Fin 2) R) (a b x y z : R) :
    derFun h2 G a b (slMk x y z) =
      slMk (G 0 0 * x + G 0 1 * y) (G 1 0 * x + G 1 1 * y) (a * x + b * y + G.trace * z) := by
  simp [derFun, coord]

/-- The parameters `(G, a, b)` of a derivation, read on `X̃` and `Ỹ`. -/
def derParams (D : LieDerivation R (Sl2 R) (Sl2 R)) : Matrix (Fin 2) (Fin 2) R × R × R :=
  (!![(D (slMk 1 0 0)).val 0 1, (D (slMk 0 1 0)).val 0 1;
    (D (slMk 1 0 0)).val 1 0, (D (slMk 0 1 0)).val 1 0],
    (D (slMk 1 0 0)).val 0 0, (D (slMk 0 1 0)).val 0 0)

/-- Every derivation of `sl(2)` is a `derFun` (characteristic 2). -/
theorem der_eq_derFun (h2 : (2 : R) = 0) (D : LieDerivation R (Sl2 R) (Sl2 R)) :
    D = derFun h2 (derParams D).1 (derParams D).2.1 (derParams D).2.2 := by
  ext1 u
  have hH : D (slMk 0 0 1) = ⁅(slMk 1 0 0 : Sl2 R), D (slMk 0 1 0)⁆ -
      ⁅(slMk 0 1 0 : Sl2 R), D (slMk 1 0 0)⁆ := by
    rw [← LieDerivation.apply_lie_eq_sub, lie_slMk h2]; simp
  have hu : u = u.val 0 1 • (slMk 1 0 0 : Sl2 R) + u.val 1 0 • slMk 0 1 0 +
      u.val 0 0 • slMk 0 0 1 := by
    conv_lhs => rw [slMk_eta u]
    simp only [slMk_smul, slMk_add]; congr 1 <;> ring
  conv_lhs => rw [hu, map_add, map_add, map_smul, map_smul, map_smul, hH]
  conv_rhs => rw [slMk_eta u, derFun_slMk]
  rw [slMk_eta (D (slMk 1 0 0)), slMk_eta (D (slMk 0 1 0)), lie_slMk h2, lie_slMk h2]
  simp only [derParams, slMk_smul, slMk_add, slMk_sub, of_apply, cons_val',
    cons_val_zero, cons_val_one, empty_val', cons_val_fin_one, trace_fin_two]
  congr 1 <;> ring

/-- **The Lie algebra of `Aut(sl(2))`**: in characteristic 2 the derivations of `sl(2)` form a
free module of rank 6, `gl₂ × R²`. -/
def derEquiv (h2 : (2 : R) = 0) :
    LieDerivation R (Sl2 R) (Sl2 R) ≃ₗ[R] Matrix (Fin 2) (Fin 2) R × R × R where
  toFun := derParams
  map_add' D D' := by
    refine Prod.ext ?_ (Prod.ext ?_ ?_)
    · ext i j; fin_cases i <;> fin_cases j <;> simp [derParams]
    all_goals simp [derParams]
  map_smul' c D := by
    refine Prod.ext ?_ (Prod.ext ?_ ?_)
    · ext i j; fin_cases i <;> fin_cases j <;> simp [derParams]
    all_goals simp [derParams]
  invFun p := derFun h2 p.1 p.2.1 p.2.2
  left_inv D := (der_eq_derFun h2 D).symm
  right_inv p := by
    obtain ⟨G, a, b⟩ := p
    simp only [derParams, derFun_slMk]
    ext i j <;> try fin_cases i <;> fin_cases j
    all_goals simp [coord]

theorem finrank_der {K : Type*} [Field K] (h2 : (2 : K) = 0) :
    Module.finrank K (LieDerivation K (Sl2 K) (Sl2 K)) = 6 := by
  rw [(derEquiv h2).finrank_eq]
  simp [Module.finrank_matrix]

variable (R) in
/-- The derivations killing `H̃`: the Lie algebra of the automorphisms of a symplectic affine
plane. -/
def derFix : Submodule R (LieDerivation R (Sl2 R) (Sl2 R)) where
  carrier := {D | D (slMk 0 0 1) = 0}
  add_mem' {D D'} hD hD' := by simp_all
  zero_mem' := by simp
  smul_mem' c D hD := by simp_all

theorem mem_derFix_iff (h2 : (2 : R) = 0) (D : LieDerivation R (Sl2 R) (Sl2 R)) :
    D ∈ derFix R ↔ (derParams D).1.trace = 0 := by
  change D (slMk 0 0 1) = 0 ↔ _
  conv_lhs => rw [der_eq_derFun h2 D, derFun_slMk, ← slMk_zero]
  constructor
  · intro h; simpa using (slMk_inj h).2.2
  · intro h; simp only [h]; simp

/-- In characteristic 2 the derivations killing `H̃` form a free module of rank 5,
`sl₂ × R²`. -/
def derFixEquiv (h2 : (2 : R) = 0) : derFix R ≃ₗ[R] (R × R × R) × R × R where
  toFun D := (((derParams D.1).1 0 0, (derParams D.1).1 0 1, (derParams D.1).1 1 0),
    (derParams D.1).2)
  map_add' D D' := by
    have := (derEquiv h2).map_add D.1 D'.1
    simp only [derEquiv, LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk] at this
    simp [this]
  map_smul' c D := by
    have := (derEquiv h2).map_smul c D.1
    simp only [derEquiv, LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk] at this
    simp [this]
  invFun p := ⟨derFun h2 !![p.1.1, p.1.2.1; p.1.2.2, -p.1.1] p.2.1 p.2.2, by
    change _ = _
    rw [derFun_slMk, ← slMk_zero]; simp [trace_fin_two]⟩
  left_inv D := by
    obtain ⟨D, hD⟩ := D
    have ht := (mem_derFix_iff h2 D).1 hD
    rw [trace_fin_two] at ht
    apply Subtype.ext
    change _ = D
    conv_rhs => rw [der_eq_derFun h2 D]
    refine congrArg (fun G => derFun h2 G _ _) ?_
    ext i j; fin_cases i <;> fin_cases j <;> simp [derParams] at ht ⊢
    linear_combination -ht
  right_inv p := by
    obtain ⟨⟨p, q, r⟩, a, b⟩ := p
    simp [derParams, derFun_slMk, coord]

theorem finrank_derFix {K : Type*} [Field K] (h2 : (2 : K) = 0) :
    Module.finrank K (derFix K) = 5 := by
  rw [(derFixEquiv h2).finrank_eq]
  simp

end Folder82
