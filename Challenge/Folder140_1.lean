module

public import Mathlib
public import Challenge.Folder146

@[expose] public section

namespace Grothendieck.Folder140_1

open groupCohomology

section General

variable {G : Type} [Group G]

/-- The `ℤ`-linear representation of `G` on an abelian group with a distributive action. -/
abbrev R (G M : Type) [Group G] [AddCommGroup M] [DistribMulAction G M] : Rep ℤ G :=
  Rep.ofDistribMulAction ℤ G M

variable {M N : Type} [AddCommGroup M] [DistribMulAction G M] [AddCommGroup N]
  [DistribMulAction G N]

variable (G M) in
/-- The 1-cocycles `f(gh) = g f(h) + f(g)`. -/
def Z1 : AddSubgroup (G → M) where
  carrier := {f | IsCocycle₁ f}
  add_mem' {f f'} hf hf' g h := by
    simp only [Pi.add_apply, hf g h, hf' g h, smul_add]; abel
  zero_mem' g h := by simp
  neg_mem' {f} hf g h := by simp only [Pi.neg_apply, hf g h, smul_neg]; abel

variable (G M) in
/-- The 1-coboundaries `g ↦ g m - m`, inside the cocycles. -/
def B1 : AddSubgroup (Z1 G M) where
  carrier := {f | IsCoboundary₁ (f : G → M)}
  add_mem' {f f'} := fun ⟨x, hx⟩ ⟨x', hx'⟩ => ⟨x + x', fun g => by
    change g • (x + x') - (x + x') = (f : G → M) g + (f' : G → M) g
    rw [smul_add, ← hx, ← hx']
    abel⟩
  zero_mem' := ⟨0, fun g => by simp⟩
  neg_mem' {f} := fun ⟨x, hx⟩ => ⟨-x, fun g => by
    change g • (-x) - (-x) = -(f : G → M) g
    rw [smul_neg, ← hx]
    abel⟩

variable (G M) in
/-- `Z¹ / B¹`. -/
abbrev Q := Z1 G M ⧸ B1 G M

/-- Mathlib's cocycles are these cocycles. -/
def cocyclesEquiv : cocycles₁ (R G M) ≃+ Z1 G M where
  toFun f := ⟨f.1, isCocycle₁_of_mem_cocycles₁ _ f.2⟩
  invFun f := ⟨f.1, (cocyclesOfIsCocycle₁ (k := ℤ) f.2).2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

variable (G M) in
/-- `H¹(G, M)` (Mathlib's, for the representation on `M`) is cocycles modulo coboundaries. -/
noncomputable def H1Equiv : Q G M ≃+ H1 (R G M) :=
  let ψ : Z1 G M →+ H1 (R G M) :=
    (H1π (R G M)).hom.toAddMonoidHom.comp (cocyclesEquiv (G := G) (M := M)).symm.toAddMonoidHom
  have hψ : Function.Surjective ψ := fun y => by
    obtain ⟨x, hx⟩ := (ModuleCat.epi_iff_surjective (H1π (R G M))).1 inferInstance y
    exact ⟨cocyclesEquiv x, by simpa [ψ] using hx⟩
  have hk : ψ.ker = B1 G M := by
    ext f
    change (H1π (R G M)) (cocyclesEquiv.symm f) = 0 ↔ IsCoboundary₁ (f : G → M)
    rw [H1π_eq_zero_iff]
    exact ⟨isCoboundary₁_of_mem_coboundaries₁ _,
      fun h => (coboundariesOfIsCoboundary₁ (k := ℤ) h).2⟩
  (QuotientAddGroup.quotientAddEquivOfEq hk.symm).trans
    (QuotientAddGroup.quotientKerEquivOfSurjective ψ hψ)

variable {A : Type} [AddCommGroup A] [DistribMulAction G A]

end General

/-- `𝔖₃ = 𝔖_J`, `J = {0, 1, 2}`. -/
abbrev G3 := Equiv.Perm (Fin 3)

/-- `V(J) = Ker(ℤ^J → ℤ)`, the divisors of the units of `U_{0,3}`. -/
def VJ : AddSubgroup (Fin 3 → ℤ) where
  carrier := {x | ∑ j, x j = 0}
  add_mem' {x y} hx hy := by simp_all [Finset.sum_add_distrib]
  zero_mem' := by simp
  neg_mem' {x} hx := by simp_all

lemma sum_perm (σ : G3) (x : Fin 3 → ℤ) : ∑ j, x (σ⁻¹ j) = ∑ j, x j :=
  Equiv.sum_comp σ⁻¹ x

/-- `𝔖₃` permutes the coordinates: `(σ x)_j = x_{σ⁻¹ j}`. -/
instance : DistribMulAction G3 VJ where
  smul σ x := ⟨fun j => (x : Fin 3 → ℤ) (σ⁻¹ j), (sum_perm σ x).trans x.2⟩
  one_smul x := rfl
  mul_smul σ τ x := by ext j; rfl
  smul_zero σ := rfl
  smul_add σ x y := rfl

@[simp] lemma smul_VJ (σ : G3) (x : VJ) (j : Fin 3) :
    ((σ • x : VJ) : Fin 3 → ℤ) j = (x : Fin 3 → ℤ) (σ⁻¹ j) := rfl

/-- The units of a ring `k` (the units of the base `S`), written additively, with the trivial
action of `𝔖₃`. -/
def Triv (k : Type) [CommRing k] := Additive kˣ

instance (k : Type) [CommRing k] : AddCommGroup (Triv k) :=
  inferInstanceAs (AddCommGroup (Additive kˣ))

variable {k : Type} [CommRing k]

/-- The coefficients of `sgnExp σ`: `1` at `0` when `σ⁻¹(∞) = 1`, at `1` when `σ⁻¹(∞) = 0`. -/
def wt (σ : G3) (j : Fin 3) : ℤ := if σ⁻¹ 2 = 1 ∧ j = 0 ∨ σ⁻¹ 2 = 0 ∧ j = 1 then 1 else 0

/-- The parity of the constant that appears when `λ^a (1 − λ)^b`, `v = (a, b, −a − b)`, is
composed with the substitution `h` inducing `σ⁻¹` on `0, 1, ∞`: `hλ` carries a sign when
`h(∞) = 1`, and `1 − hλ` when `h(∞) = 0`. -/
def sgnExp (σ : G3) (v : VJ) : ℤ := ∑ j, wt σ j * (v : Fin 3 → ℤ) j

lemma sgnExp_add (σ : G3) (v w : VJ) : sgnExp σ (v + w) = sgnExp σ v + sgnExp σ w := by
  simp [sgnExp, mul_add, Finset.sum_add_distrib]

lemma wt_key : ∀ σ τ : G3, ∀ j, (wt (σ * τ) j - wt τ j - wt σ (τ j) -
    (wt (σ * τ) 0 - wt τ 0 - wt σ (τ 0))) % 2 = 0 := by decide

lemma sgnExp_mul (σ τ : G3) (v : VJ) :
    2 ∣ sgnExp (σ * τ) v - (sgnExp τ v + sgnExp σ (τ • v)) := by
  have hv : ∑ j, (v : Fin 3 → ℤ) j = 0 := v.2
  have e : sgnExp σ (τ • v) = ∑ j, wt σ (τ j) * (v : Fin 3 → ℤ) j := by
    simp only [sgnExp, smul_VJ]
    rw [← Equiv.sum_comp τ]
    simp
  obtain ⟨t1, h1⟩ := Int.dvd_of_emod_eq_zero (wt_key σ τ 1)
  obtain ⟨t2, h2⟩ := Int.dvd_of_emod_eq_zero (wt_key σ τ 2)
  rw [e]
  simp only [sgnExp, Fin.sum_univ_three] at hv ⊢
  exact ⟨t1 * (v : Fin 3 → ℤ) 1 + t2 * (v : Fin 3 → ℤ) 2, by
    linear_combination (v : Fin 3 → ℤ) 1 * h1 + (v : Fin 3 → ℤ) 2 * h2 +
      (wt (σ * τ) 0 - wt τ 0 - wt σ (τ 0)) * hv⟩

@[simp] lemma sgnExp_zero (σ : G3) : sgnExp σ 0 = 0 := by simp [sgnExp]

@[simp] lemma sgnExp_one (v : VJ) : sgnExp 1 v = 0 := by simp [sgnExp, wt]

/-- The units of `U_{0,3} = Spec k[λ, 1/λ, 1/(1 − λ)]`, written additively: `c λ^a (1 − λ)^b`
is `(c, (a, b, −a − b))`, the second component its divisor on `0, 1, ∞`. -/
def Units3 (k : Type) [CommRing k] := Triv k × VJ

instance : AddCommGroup (Units3 k) := inferInstanceAs (AddCommGroup (Triv k × VJ))

namespace Units3

/-- The unit `c λ^a (1 − λ)^b`, `v = (a, b, −a − b)`. -/
def mk (c : Triv k) (v : VJ) : Units3 k := (c, v)

/-- The constant. -/
def cst (x : Units3 k) : Triv k := Prod.fst (β := VJ) x

/-- The divisor. -/
def dv (x : Units3 k) : VJ := Prod.snd (α := Triv k) x

@[ext] lemma ext {x y : Units3 k} (h1 : x.cst = y.cst) (h2 : x.dv = y.dv) : x = y :=
  Prod.ext h1 h2

@[simp] lemma cst_mk (c : Triv k) (v : VJ) : (mk c v).cst = c := rfl

@[simp] lemma dv_mk (c : Triv k) (v : VJ) : (mk c v).dv = v := rfl

@[simp] lemma cst_add (x y : Units3 k) : (x + y).cst = x.cst + y.cst := rfl

@[simp] lemma dv_add (x y : Units3 k) : (x + y).dv = x.dv + y.dv := rfl

@[simp] lemma cst_sub (x y : Units3 k) : (x - y).cst = x.cst - y.cst := rfl

@[simp] lemma dv_sub (x y : Units3 k) : (x - y).dv = x.dv - y.dv := rfl

@[simp] lemma cst_zero : (0 : Units3 k).cst = 0 := rfl

@[simp] lemma dv_zero : (0 : Units3 k).dv = 0 := rfl

@[simp] lemma cst_zsmul (m : ℤ) (x : Units3 k) : (m • x).cst = m • x.cst := rfl

@[simp] lemma dv_zsmul (m : ℤ) (x : Units3 k) : (m • x).dv = m • x.dv := rfl

end Units3

open Units3

/-- `(-1)^s`, in `k^*` written additively. -/
def negPow (s : ℤ) : Triv k := Additive.ofMul ((-1 : kˣ) ^ s)

lemma negPow_add (s t : ℤ) : negPow (k := k) (s + t) = negPow s + negPow t := by
  rw [negPow, zpow_add]; rfl

@[simp] lemma negPow_zero : negPow (k := k) 0 = 0 := by rw [negPow, zpow_zero]; rfl

lemma negPow_eq_zero {s : ℤ} (h : 2 ∣ s) : negPow (k := k) s = 0 := by
  obtain ⟨u, rfl⟩ := h
  rw [negPow, zpow_mul, show ((-1 : kˣ) ^ (2 : ℤ)) = 1 by norm_num, one_zpow]; rfl

lemma negPow_congr {s t : ℤ} (h : 2 ∣ s - t) : negPow (k := k) s = negPow t := by
  rw [show s = s - t + t by ring, negPow_add, negPow_eq_zero h, zero_add]

/-- The anharmonic action: `σ` sends `f` to `f ∘ h`, `h` the substitution inducing `σ⁻¹` on
`0, 1, ∞`; on the divisor it permutes the coordinates, on the constant it multiplies by
`(-1)^{sgnExp σ v}` (`ev_smul`). -/
instance : DistribMulAction G3 (Units3 k) where
  smul σ x := mk (x.cst + negPow (sgnExp σ x.dv)) (σ • x.dv)
  one_smul x := Units3.ext (show x.cst + negPow (sgnExp 1 x.dv) = x.cst by simp)
    (one_smul G3 x.dv)
  mul_smul σ τ x := Units3.ext (by
    change x.cst + _ = x.cst + _ + _
    rw [add_assoc, ← negPow_add, negPow_congr (sgnExp_mul σ τ x.dv)]; rfl) (mul_smul σ τ x.dv)
  smul_zero σ := Units3.ext (show (0 : Units3 k).cst + negPow (sgnExp σ 0) = 0 by simp)
    (smul_zero σ)
  smul_add σ x y := Units3.ext (by
    change x.cst + y.cst + negPow (sgnExp σ (x.dv + y.dv)) = x.cst + _ + (y.cst + _)
    rw [sgnExp_add, negPow_add]; abel) (smul_add σ x.dv y.dv)

@[simp] lemma cst_smul (σ : G3) (x : Units3 k) :
    (σ • x).cst = x.cst + negPow (sgnExp σ x.dv) := rfl

@[simp] lemma dv_smul (σ : G3) (x : Units3 k) : (σ • x).dv = σ • x.dv := rfl

/-- The sign of a permutation, in `k^*`. -/
def sgnK (σ : G3) : Triv k :=
  Additive.ofMul (Units.map (Int.castRingHom k).toMonoidHom (Equiv.Perm.sign σ))

/-- The point `∞`. -/
def e2 : Fin 3 → ℤ := fun j => if j = 2 then 1 else 0

/-- The divisor `2[∞] − 2[σ(∞)]`. -/
def tanV (σ : G3) : VJ := ⟨fun j => 2 * (e2 j - e2 (σ⁻¹ j)), by
  change ∑ j, 2 * (e2 j - e2 (σ⁻¹ j)) = 0
  rw [← Finset.mul_sum, Finset.sum_sub_distrib, sum_perm σ e2, sub_self, mul_zero]⟩

lemma sgnExp_tanV (σ τ : G3) : 2 ∣ sgnExp σ (tanV τ) :=
  Finset.dvd_sum fun _ _ => Dvd.dvd.mul_left (dvd_mul_right 2 _) _

/-- The tangent cocycle `σ ↦ (h⁻¹)′(λ)`, `h` inducing `σ` on `0, 1, ∞`: its constant is the
sign of `σ` and its divisor `2[∞] − 2[σ(∞)]` (`ev_tan`). -/
def tan : Z1 G3 (Units3 k) :=
  ⟨fun σ => mk (sgnK σ) (tanV σ), fun σ τ => Units3.ext (by
    simp only [cst_add, cst_smul, cst_mk, dv_mk, negPow_eq_zero (sgnExp_tanV σ τ), add_zero]
    rw [add_comm, sgnK, map_mul, map_mul]; rfl)
    (by ext j; simp [tanV, mul_inv_rev]; ring)⟩

/-- The lower bound of page 24, with the bound of page 22: for a domain `k` with `2 ≠ 0`,
`H¹(𝔖₃, O(U_{0,3})^*) ≃ ℤ/6`, generated by the tangent class. -/
theorem H1_units [IsDomain k] (h2 : (2 : k) ≠ 0) :
    Nat.card (H1 (R G3 (Units3 k))) = 6 ∧
      addOrderOf (H1Equiv G3 (Units3 k) (QuotientAddGroup.mk tan)) = 6 ∧
      Nonempty (H1 (R G3 (Units3 k)) ≃+ ZMod 6) := by
  sorry

end Grothendieck.Folder140_1
