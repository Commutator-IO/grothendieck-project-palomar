module

public import Mathlib

@[expose] public section


/-!
# Folder 72: regular polytopes and pseudo-reflections in any dimension

## The group `𝒰_ρ` and the automorphisms of a realisation (pages 37–38, 87–88)

Finding `72-automorphisms-deform-gm-to-ga` (`src/content/findings.ts`), on the
reading `transcripts/72/72.modern.tex`, section IX and section XV D). Page 37
defines `𝒰_ρ = Spec 𝒪_S[T]_{(1+ρT)}` with the law `λ * λ' = λ + λ' + ρλλ'`, and
its action `u_λ = id + λ π ⊗ c̃` on `E`; the « Théorème » of page 38 says that
`𝔾_m × 𝒰_ρ → Aut(E, (τᵢ))` and `𝒰_ρ → Aut(X, (τᵢ))` are isomorphisms and that
`D₀ ∖ {c, d}` is a torsor under `𝒰_ρ`, trivialised by `s₀`. No proof is on the
pages.

**The coordinates.** Over a commutative ring `R`, take `E = R^{n+2}` with basis
`e₀ = s₀, e₁ = a₀, …, e_{n+1} = aₙ` (the basis `(s₀, a₀, …, aₙ)` of condition
(12) of page 96), and the pseudo-reflections `τᵢ = id + a'ᵢ ⊗ aᵢ` with
`⟨a_{i−1}, a'ᵢ⟩ = 1`, `⟨aᵢ, a'ᵢ⟩ = μᵢ`, `⟨a_{i+1}, a'ᵢ⟩ = βᵢ`, all other
pairings `0` (the conventions of the reading). Here `a'ᵢ = F i`, so
`F i x = x_i + μᵢ x_{i+1} + βᵢ x_{i+2}`, and `π` is the coordinate `x₀`. By the theorem
of pages 96–100 (`pinned_classification` below), every pinned non-degenerate
realisation is isomorphic to this one.

* `U ρ`: the `R`-points of `𝒰_ρ`, a commutative group; `toUnits : λ ↦ 1 + ρλ`
  is an isomorphism onto `Rˣ` when `ρ` is a unit (`toUnitsEquiv`), and
  `U 0 ≃* Multiplicative R` (`U_zero`). `forall_surjective_iff`: `λ ↦ 1 + ρλ`
  is surjective over every `R`-algebra iff `ρ` is a unit (test algebra: the dual
  numbers, unit `1 + ε`).
* `ct` is `c̃` (back-substitution, `F_ct`, `co_ct_top`), `ρ = π(c̃)`;
  `ρ_one`: for `n = 1`, `ρ = μ₀μ₁ − β₀`, `4 − β₀` for reflections, as page 41.
* `u_mul`: `u_λ u_λ' = u_{λ * λ'}`; `τ_mul_P`, `P_mul_τ`: `u_λ` commutes with the
  `τᵢ`; `det_u`: `det u_λ = 1 + ρλ`.
* `commute_iff` (the computation under the « Théorème »): an endomorphism of `E`
  commutes with all `τᵢ` iff it is `c + t π ⊗ c̃`, with `(c, t)` unique
  (`coeff_unique`); `isUnit_iff`: it is invertible iff `c` and `c + tρ` are units.
  `centraliserEquiv : Rˣ × U ρ ≃* centraliser`: the linear form of the theorem,
  `𝔾_m × 𝒰_ρ ≅ Aut(E, (τᵢ))`, on `R`-points.
* `mem_D0_iff`, `mem_startPoints_iff`, `u_e0_injective`, `u_u_e0`: the points of
  `D₀ = H₁ ∩ ⋯ ∩ Hₙ` are the `a s₀ + t c̃`; the start points off `c` and `d`,
  normalised by `⟨s, a'₀⟩ = 1`, are exactly the `u_λ s₀ = s₀ + λ c̃`, each
  for one `λ`, and `u_μ (u_λ s₀) = u_{λ * μ} s₀`: a trivial torsor under `𝒰_ρ`.

Not formalised: the group scheme, its smoothness, the projective statement over
a base (automorphisms of `X` commuting with the projective `τᵢ`), the torsor of
flags itself (page 87 C, the bijection flags ↔ start points).
-/

namespace Grothendieck.Folder72

universe u

variable {R : Type u} [CommRing R]

/-! ### The group `𝒰_ρ` -/

/-- The `R`-points of `𝒰_ρ = Spec R[T]_{(1+ρT)}`. -/
@[ext]
structure U (ρ : R) where
  /-- the coordinate `λ` -/
  val : R
  isUnit : IsUnit (1 + ρ * val)

namespace U

variable {ρ : R}

instance : One (U ρ) := ⟨⟨0, by simp⟩⟩

instance : Mul (U ρ) :=
  ⟨fun x y => ⟨x.val + y.val + ρ * x.val * y.val, by
    have : 1 + ρ * (x.val + y.val + ρ * x.val * y.val) = (1 + ρ * x.val) * (1 + ρ * y.val) := by
      ring
    rw [this]; exact x.isUnit.mul y.isUnit⟩⟩

lemma inv_isUnit (x : U ρ) : IsUnit (1 + ρ * (-x.val * ↑x.isUnit.unit⁻¹)) := by
  have h := x.isUnit.mul_val_inv
  have : 1 + ρ * (-x.val * ↑x.isUnit.unit⁻¹) = ↑x.isUnit.unit⁻¹ := by
    linear_combination (-1 : R) * h
  rw [this]; exact Units.isUnit _

noncomputable instance : Inv (U ρ) := ⟨fun x => ⟨-x.val * ↑x.isUnit.unit⁻¹, inv_isUnit x⟩⟩

@[simp] lemma one_val : (1 : U ρ).val = 0 := rfl
@[simp] lemma mul_val (x y : U ρ) : (x * y).val = x.val + y.val + ρ * x.val * y.val := rfl
lemma inv_val (x : U ρ) : (x⁻¹).val = -x.val * ↑x.isUnit.unit⁻¹ := rfl

noncomputable instance : CommGroup (U ρ) where
  mul_assoc x y z := by ext; simp; ring
  one_mul x := by ext; simp
  mul_one x := by ext; simp
  inv_mul_cancel x := by
    ext; simp only [mul_val, inv_val, one_val]
    linear_combination (-x.val) * x.isUnit.mul_val_inv
  mul_comm x y := by ext; simp; ring

/-- `λ ↦ 1 + ρλ`, the homomorphism `𝒰_ρ → 𝔾_m`. -/
noncomputable def toGm : U ρ →* Rˣ where
  toFun x := x.isUnit.unit
  map_one' := by ext; simp
  map_mul' x y := by ext; simp; ring

@[simp] lemma toGm_val (x : U ρ) : (toGm x : R) = 1 + ρ * x.val := rfl

end U

open U

theorem toGm_bijective {ρ : R} (hρ : IsUnit ρ) : Function.Bijective (toGm (ρ := ρ)) :=
    ⟨fun x y h => by
      have h' : 1 + ρ * x.val = 1 + ρ * y.val := by
        simpa using congrArg (fun v : Rˣ => (v : R)) h
      ext; exact hρ.mul_left_cancel (by linear_combination h'),
     fun v => ⟨⟨↑hρ.unit⁻¹ * ((v : R) - 1), by
        have : 1 + ρ * (↑hρ.unit⁻¹ * ((v : R) - 1)) = v := by
          linear_combination ((v : R) - 1) * hρ.mul_val_inv
        rw [this]; exact v.isUnit⟩, by
        ext; simp only [toGm_val]; linear_combination ((v : R) - 1) * hρ.mul_val_inv⟩⟩

/-- Where `ρ` is invertible, `𝒰_ρ ≅ 𝔾_m` (the centre at finite distance). -/
noncomputable def toUnitsEquiv {ρ : R} (hρ : IsUnit ρ) : U ρ ≃* Rˣ :=
  MulEquiv.ofBijective toGm (toGm_bijective hρ)

/-- For `ρ = 0`, `𝒰₀ = 𝔾_a` (the centre at infinity). -/
def U_zero : U (0 : R) ≃* Multiplicative R where
  toFun x := Multiplicative.ofAdd x.val
  invFun a := ⟨a.toAdd, by simp⟩
  left_inv x := by ext; simp
  right_inv a := by simp
  map_mul' x y := by simp [← ofAdd_add]

/-- `λ ↦ 1 + ρλ` is onto the units over every `R`-algebra iff `ρ` is a unit: the
morphism `𝒰_ρ → 𝔾_m` is an isomorphism exactly where the centre is at finite
distance. -/
theorem forall_surjective_iff (ρ : R) :
    (∀ (A : Type u) [CommRing A] [Algebra R A],
        Function.Surjective (toGm (ρ := algebraMap R A ρ))) ↔ IsUnit ρ := by
  constructor
  · intro h
    let ε : DualNumber R := DualNumber.eps
    have hu : IsUnit (1 + ε) :=
      IsUnit.of_mul_eq_one (1 - ε) (by
        have : ε * ε = 0 := DualNumber.eps_mul_eps
        linear_combination (-1 : DualNumber R) * this)
    obtain ⟨x, hx⟩ := h (DualNumber R) hu.unit
    have h1 : 1 + algebraMap R (DualNumber R) ρ * x.val = 1 + ε := by
      simpa using congrArg (fun v : (DualNumber R)ˣ => (v : DualNumber R)) hx
    have h2 : algebraMap R (DualNumber R) ρ * x.val = ε := add_left_cancel h1
    have h3 : ρ * x.val.snd = 1 := by
      simpa [ε, TrivSqZeroExt.algebraMap_eq_inl] using congrArg TrivSqZeroExt.snd h2
    exact IsUnit.of_mul_eq_one _ h3
  · intro hρ A _ _
    exact (toGm_bijective (hρ.map (algebraMap R A))).2

/-! ### The realisation in coordinates -/

variable (n : ℕ) (μ β : ℕ → R)

/-- The coordinate of index `k`, zero beyond `n + 1`. -/
def co (k : ℕ) : (Fin (n + 2) → R) →ₗ[R] R :=
  if h : k < n + 2 then LinearMap.proj (⟨k, h⟩ : Fin (n + 2)) else 0

/-- The basis vector `e_k` (`e₀ = s₀`, `e_{i+1} = aᵢ`). -/
def e (k : ℕ) : Fin (n + 2) → R := fun j => if (j : ℕ) = k then 1 else 0

/-- The form `a'ᵢ`: `⟨a_{i−1}, a'ᵢ⟩ = 1`, `⟨aᵢ, a'ᵢ⟩ = μᵢ`, `⟨a_{i+1}, a'ᵢ⟩ = βᵢ`. -/
def F (i : ℕ) : (Fin (n + 2) → R) →ₗ[R] R :=
  co n i + μ i • co n (i + 1) + β i • co n (i + 2)

/-- The pseudo-reflection `τᵢ = id + a'ᵢ ⊗ aᵢ`. -/
def τ (i : ℕ) : Module.End R (Fin (n + 2) → R) :=
  1 + (F n μ β i).smulRight (e n (i + 1))

variable {n}

lemma co_of_lt {k : ℕ} (h : k < n + 2) (x : Fin (n + 2) → R) :
    co n k x = x ⟨k, h⟩ := by simp [co, h]

lemma co_of_le {k : ℕ} (h : n + 2 ≤ k) (x : Fin (n + 2) → R) : co n k x = 0 := by
  simp [co, show ¬ k < n + 2 by omega]

lemma co_e (j k : ℕ) (hk : k < n + 2) :
    co n j (e n k : Fin (n + 2) → R) = if j = k then 1 else 0 := by
  by_cases hj : j < n + 2
  · simp [co_of_lt hj, e]
  · rw [co_of_le (by omega)]; simp [show j ≠ k by omega]

lemma co_zero_apply (x : Fin (n + 2) → R) : co n 0 x = x 0 := by
  rw [co_of_lt (by omega)]; rfl

lemma co_e_self (k : ℕ) (hk : k < n + 2) : co n k (e n k : Fin (n + 2) → R) = 1 := by
  simp [co_of_lt hk, e]

lemma co_e_ne {j k : ℕ} (h : j ≠ k) : co n j (e n k : Fin (n + 2) → R) = 0 := by
  by_cases hj : j < n + 2
  · simp [co_of_lt hj, e, h]
  · exact co_of_le (by omega) _

lemma e_val (j : Fin (n + 2)) (r : R) : Pi.single j r = r • (e n j : Fin (n + 2) → R) := by
  funext k; simp [e, Pi.single_apply, Fin.ext_iff]

lemma τ_apply (i : ℕ) (x : Fin (n + 2) → R) :
    τ n μ β i x = x + F n μ β i x • e n (i + 1) := rfl

lemma co_τ_zero (i : ℕ) (x : Fin (n + 2) → R) : co n 0 (τ n μ β i x) = co n 0 x := by
  simp [τ_apply, co_e_ne (show 0 ≠ i + 1 by omega)]

lemma F_e_far {i k : ℕ} (h0 : k ≠ i) (h1 : k ≠ i + 1) (h2 : k ≠ i + 2) :
    F n μ β i (e n k) = 0 := by
  simp [F, co_e_ne (Ne.symm h0), co_e_ne (Ne.symm h1), co_e_ne (Ne.symm h2)]

/-- The non-consecutive `τᵢ` commute (relation (7) of page 96). -/
theorem τ_comm {i j : ℕ} (hij : i + 2 ≤ j) :
    τ n μ β i * τ n μ β j = τ n μ β j * τ n μ β i := by
  refine LinearMap.ext fun x => ?_
  simp only [Module.End.mul_apply, τ_apply, map_add, map_smul, F_e_far μ β (show j + 1 ≠ i by omega)
    (show j + 1 ≠ i + 1 by omega) (show j + 1 ≠ i + 2 by omega),
    F_e_far μ β (show i + 1 ≠ j by omega) (show i + 1 ≠ j + 1 by omega)
      (show i + 1 ≠ j + 2 by omega),
    zero_smul, add_zero]
  abel

/-! ### Back-substitution: the vector `c̃` -/

/-- `(y_{top−m}, y_{top−m+1})` for the solution of `F_k y = 0` (`k < top`) with
`y_top = 1`, `y_k = 0` for `k > top`. -/
def cc (top : ℕ) : ℕ → R × R
  | 0 => (1, 0)
  | m + 1 => (-(μ (top - 1 - m) * (cc top m).1 + β (top - 1 - m) * (cc top m).2), (cc top m).1)

/-- The coordinates of the back-substituted vector with top index `top`. -/
def y (top k : ℕ) : R := if k ≤ top then (cc μ β top (top - k)).1 else 0

variable {μ β}

lemma y_top (top : ℕ) : y μ β top top = 1 := by simp [y, cc]

lemma y_of_lt {top k : ℕ} (h : top < k) : y μ β top k = 0 := by
  simp [y, show ¬ k ≤ top by omega]

lemma y_rec {top k : ℕ} (h : k < top) :
    y μ β top k = -(μ k * y μ β top (k + 1) + β k * y μ β top (k + 2)) := by
  obtain ⟨m, rfl⟩ : ∃ m, top = k + 1 + m := ⟨top - k - 1, by omega⟩
  have hA : y μ β (k + 1 + m) k =
      -(μ k * (cc μ β (k + 1 + m) m).1 + β k * (cc μ β (k + 1 + m) m).2) := by
    simp only [y, show k ≤ k + 1 + m by omega, ↓reduceIte, show k + 1 + m - k = m + 1 by omega, cc,
      show k + 1 + m - 1 - m = k by omega]
  have hB : y μ β (k + 1 + m) (k + 1) = (cc μ β (k + 1 + m) m).1 := by
    simp only [y, show k + 1 ≤ k + 1 + m by omega, ↓reduceIte,
      show k + 1 + m - (k + 1) = m by omega]
  have hC : y μ β (k + 1 + m) (k + 2) = (cc μ β (k + 1 + m) m).2 := by
    rcases m with _ | m
    · simp [y, cc]
    · simp only [y, show k + 2 ≤ k + 1 + (m + 1) by omega, ↓reduceIte,
        show k + 1 + (m + 1) - (k + 2) = m by omega, cc]
  rw [hA, hB, hC]

variable (μ β) in
/-- The vector with coordinates `y top`. -/
def vec (top : ℕ) : Fin (n + 2) → R := fun j => y μ β top j

lemma co_vec {top : ℕ} (htop : top ≤ n + 1) (k : ℕ) :
    co n k (vec μ β top) = y μ β top k := by
  by_cases hk : k < n + 2
  · rw [co_of_lt hk]; rfl
  · rw [co_of_le (by omega), y_of_lt (by omega)]

lemma F_apply (i : ℕ) (x : Fin (n + 2) → R) :
    F n μ β i x = co n i x + μ i * co n (i + 1) x + β i * co n (i + 2) x := rfl

lemma F_vec {top i : ℕ} (htop : top ≤ n + 1) (hi : i < top) : F n μ β i (vec μ β top) = 0 := by
  rw [F_apply, co_vec htop, co_vec htop, co_vec htop, y_rec hi]; ring

/-- The kernel of `F₀, …, F_{top−1}` among the vectors supported in `[0, top]` is the
line of `vec top`. -/
theorem eq_smul_vec {top : ℕ} (htop : top ≤ n + 1) (v : Fin (n + 2) → R)
    (hsupp : ∀ k, top < k → co n k v = 0) (hF : ∀ i < top, F n μ β i v = 0) :
    v = co n top v • vec μ β top := by
  set w := v - co n top v • vec μ β top with hw
  have hco : ∀ k, co n k w = co n k v - co n top v * y μ β top k := by
    intro k; simp [hw, co_vec htop]
  have hFw : ∀ i < top, F n μ β i w = 0 := by
    intro i hi; simp [hw, hF i hi, F_vec htop hi]
  have key : ∀ m k, top ≤ k + m → co n k w = 0 := by
    intro m
    induction m with
    | zero =>
      intro k hk
      rcases (show top < k ∨ k = top by omega) with h | rfl
      · rw [hco, hsupp k h, y_of_lt h]; ring
      · rw [hco, y_top]; ring
    | succ m ih =>
      intro k hk
      by_cases h : top ≤ k + m
      · exact ih k h
      · have hkt : k < top := by omega
        have h1 := ih (k + 1) (by omega)
        have h2 := ih (k + 2) (by omega)
        have := hFw k hkt
        rw [F_apply, h1, h2] at this
        simpa using this
  have hw0 : w = 0 := by
    funext j
    have := key top j (by omega)
    rwa [co_of_lt j.isLt] at this
  exact sub_eq_zero.mp hw0

/-! ### `c̃`, `ρ` and the action `u_λ` -/

variable (n μ β)

/-- `c̃`: killed by every `a'ᵢ`, coordinate `1` on `aₙ`. -/
def ct : Fin (n + 2) → R := vec μ β (n + 1)

/-- `ρ = π(c̃)`. -/
def ρ : R := y μ β (n + 1) 0

/-- `π ⊗ c̃`. -/
def P : Module.End R (Fin (n + 2) → R) := (co n 0).smulRight (ct n μ β)

/-- `u_λ = id + λ π ⊗ c̃`. -/
def u (t : R) : Module.End R (Fin (n + 2) → R) := 1 + t • P n μ β

variable {n μ β}

lemma F_ct {i : ℕ} (hi : i ≤ n) : F n μ β i (ct n μ β) = 0 := F_vec le_rfl (by omega)

lemma co_ct_top : co n (n + 1) (ct n μ β) = 1 := by rw [ct, co_vec le_rfl, y_top]

lemma co_ct_zero : co n 0 (ct n μ β) = ρ n μ β := by rw [ct, co_vec le_rfl]; rfl

/-- For `n = 1`, `ρ = μ₀μ₁ − β₀`; for reflections (`μᵢ = −2`), `4 − β₀`. -/
theorem ρ_one : ρ 1 μ β = μ 0 * μ 1 - β 0 := by
  simp [ρ, y, cc]; ring

lemma P_apply (x : Fin (n + 2) → R) : P n μ β x = co n 0 x • ct n μ β := rfl

lemma P_mul_P : P n μ β * P n μ β = ρ n μ β • P n μ β := by
  refine LinearMap.ext fun x => ?_
  simp only [Module.End.mul_apply, P_apply, LinearMap.smul_apply, map_smul, co_ct_zero, smul_smul]
  rw [mul_comm]

lemma u_apply (t : R) (x : Fin (n + 2) → R) :
    u n μ β t x = x + (t * co n 0 x) • ct n μ β := by
  simp [u, P_apply, smul_smul]

/-- `u_λ u_λ' = u_{λ + λ' + ρλλ'}`. -/
theorem u_mul (s t : R) : u n μ β s * u n μ β t = u n μ β (s + t + ρ n μ β * s * t) := by
  simp only [u, add_mul, mul_add, one_mul, mul_one, smul_mul_smul_comm, P_mul_P, smul_smul,
    add_smul]
  rw [show s * t * ρ n μ β = ρ n μ β * s * t by ring]; abel

lemma τ_mul_P {i : ℕ} (hi : i ≤ n) : τ n μ β i * P n μ β = P n μ β := by
  refine LinearMap.ext fun x => ?_
  simp [P_apply, τ_apply, F_ct hi]

lemma P_mul_τ (i : ℕ) : P n μ β * τ n μ β i = P n μ β := by
  refine LinearMap.ext fun x => ?_
  simp [P_apply, co_τ_zero]

/-- `u_λ` commutes with the `τᵢ`. -/
theorem u_comm {i : ℕ} (hi : i ≤ n) (t : R) : u n μ β t * τ n μ β i = τ n μ β i * u n μ β t := by
  simp [u, add_mul, mul_add, P_mul_τ, τ_mul_P hi]

/-- `det u_λ = 1 + ρλ`. -/
theorem det_u (t : R) : LinearMap.det (u n μ β t) = 1 + ρ n μ β * t := by
  have hm : LinearMap.toMatrix' (u n μ β t) =
      1 + Matrix.replicateCol Unit (t • ct n μ β) *
        Matrix.replicateRow Unit (Pi.single 0 1 : Fin (n + 2) → R) := by
    ext i j
    rw [LinearMap.toMatrix'_apply, u_apply, co_zero_apply]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Matrix.add_apply, Matrix.one_apply,
      Matrix.mul_apply, Matrix.replicateCol_apply, Matrix.replicateRow_apply, Finset.univ_unique,
      Finset.sum_singleton, Pi.single_apply]
    by_cases hj : j = 0
    · simp only [hj, ↓reduceIte]; ring
    · simp only [hj, Ne.symm hj, ↓reduceIte]; ring
  rw [← LinearMap.det_toMatrix', hm, Matrix.det_one_add_replicateCol_mul_replicateRow,
    single_dotProduct]
  simp only [Pi.smul_apply, smul_eq_mul, one_mul, ct, vec, ρ, Fin.val_zero]
  ring

/-! ### The automorphisms of the realisation -/

lemma comm_iff_apply (g : Module.End R (Fin (n + 2) → R)) (i : ℕ) :
    g * τ n μ β i = τ n μ β i * g ↔
      ∀ x, F n μ β i x • g (e n (i + 1)) = F n μ β i (g x) • e n (i + 1) := by
  constructor
  · intro h x
    have := congrArg (fun f => f x) h
    simpa [τ_apply] using this
  · intro h; refine LinearMap.ext fun x => ?_; simp [τ_apply, h x]

lemma F_e_self (i : ℕ) (hi : i ≤ n) : F n μ β i (e n i) = 1 := by
  simp [F_apply, co_e _ i (show i < n + 2 by omega)]

lemma F_e_zero {i : ℕ} (hi : 1 ≤ i) : F n μ β i (e n 0) = 0 := by
  simp [F_apply, co_e _ 0 (show 0 < n + 2 by omega), show i ≠ 0 by omega]

/-- The commutant of the `τᵢ`: an endomorphism commutes with all of them iff it is
`c + t π ⊗ c̃`. -/
theorem commute_iff (g : Module.End R (Fin (n + 2) → R)) :
    (∀ i ≤ n, g * τ n μ β i = τ n μ β i * g) ↔
      ∃ c t : R, g = c • 1 + t • P n μ β := by
  constructor
  · intro h
    -- `g aᵢ = cᵢ aᵢ` and `a'ᵢ ∘ g = cᵢ a'ᵢ`, with `cᵢ = a'ᵢ(g e_i)`
    have hga : ∀ i ≤ n, g (e n (i + 1)) = F n μ β i (g (e n i)) • e n (i + 1) := by
      intro i hi
      have := (comm_iff_apply g i).1 (h i hi) (e n i)
      rwa [F_e_self i hi, one_smul] at this
    have hFg : ∀ i ≤ n, ∀ x, F n μ β i (g x) = F n μ β i (g (e n i)) * F n μ β i x := by
      intro i hi x
      have h1 := (comm_iff_apply g i).1 (h i hi) x
      rw [hga i hi, smul_smul] at h1
      have h2 := congrArg (co n (i + 1)) h1
      simp only [map_smul, co_e _ _ (show i + 1 < n + 2 by omega), ↓reduceIte,
        smul_eq_mul, mul_one] at h2
      rw [← h2, mul_comm]
    set c := F n μ β 0 (g (e n 0)) with hc
    have hci : ∀ i ≤ n, F n μ β i (g (e n i)) = c := by
      intro i hi
      induction i with
      | zero => rfl
      | succ i ih =>
        rw [hga i (by omega), map_smul, F_e_self _ hi, ih (by omega), smul_eq_mul, mul_one]
    have hgk : ∀ k, 1 ≤ k → k ≤ n + 1 → g (e n k) = c • e n k := by
      intro k hk1 hk2
      obtain ⟨i, rfl⟩ : ∃ i, k = i + 1 := ⟨k - 1, by omega⟩
      rw [hga i (by omega), hci i (by omega)]
    set w := g (e n 0) - c • e n 0 with hw
    have hFw : ∀ i < n + 1, F n μ β i w = 0 := by
      intro i hi
      rw [hw, map_sub, map_smul, hFg i (by omega), hci i (by omega), smul_eq_mul, sub_self]
    have hwct : w = co n (n + 1) w • ct n μ β :=
      eq_smul_vec le_rfl w (fun k hk => co_of_le (by omega) w) hFw
    refine ⟨c, co n (n + 1) w, ?_⟩
    apply LinearMap.pi_ext
    intro j r
    rw [e_val, map_smul, map_smul]
    congr 1
    rcases Nat.eq_zero_or_pos (j : ℕ) with h0 | hpos
    · rw [h0, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.smul_apply,
        Module.End.one_apply, P_apply, co_e_self 0 (by omega), one_smul, ← hwct, hw]
      abel
    · rw [hgk j hpos (by omega)]
      simp [P_apply, co_e 0 (j : ℕ) j.isLt, show (0 : ℕ) ≠ j by omega]
  · rintro ⟨c, t, rfl⟩ i hi
    simp [add_mul, mul_add, P_mul_τ, τ_mul_P hi]

/-- The pair `(c, t)` is unique. -/
theorem coeff_unique {c t c' t' : R}
    (h : c • (1 : Module.End R (Fin (n + 2) → R)) + t • P n μ β = c' • 1 + t' • P n μ β) :
    c = c' ∧ t = t' := by
  have h1 : c = c' := by
    simpa [P_apply, co_e 0 1 (show 1 < n + 2 by omega), co_e 1 1 (show 1 < n + 2 by omega)]
      using congrArg (fun f => co n 1 (f (e n 1))) h
  subst h1
  have h2 : t = t' := by
    simpa [P_apply, co_e 0 0 (show 0 < n + 2 by omega), co_e (n + 1) 0 (show 0 < n + 2 by omega),
      co_ct_top] using congrArg (fun f => co n (n + 1) (f (e n 0))) h
  exact ⟨rfl, h2⟩

lemma smul_one_add_mul (c t c' t' : R) :
    (c • (1 : Module.End R (Fin (n + 2) → R)) + t • P n μ β) * (c' • 1 + t' • P n μ β) =
      (c * c') • 1 + (c * t' + t * c' + t * t' * ρ n μ β) • P n μ β := by
  simp only [add_mul, mul_add, smul_mul_smul_comm, one_mul, mul_one, P_mul_P, smul_smul, add_smul]
  abel

/-- `c + t π ⊗ c̃` is invertible iff `c` and `c + tρ` are units. -/
theorem isUnit_iff (c t : R) :
    IsUnit (c • (1 : Module.End R (Fin (n + 2) → R)) + t • P n μ β) ↔
      IsUnit c ∧ IsUnit (c + t * ρ n μ β) := by
  constructor
  · intro hg
    obtain ⟨g, hg⟩ := hg
    have hcomm : ∀ i ≤ n, (↑g⁻¹ : Module.End R (Fin (n + 2) → R)) * τ n μ β i =
        τ n μ β i * ↑g⁻¹ := by
      intro i hi
      have h1 : (↑g : Module.End R (Fin (n + 2) → R)) * τ n μ β i = τ n μ β i * ↑g := by
        rw [hg]; exact (commute_iff _).2 ⟨c, t, rfl⟩ i hi
      exact (Commute.units_inv_left h1).eq
    obtain ⟨c', t', hinv⟩ := (commute_iff _).1 hcomm
    have hmul : (c • (1 : Module.End R (Fin (n + 2) → R)) + t • P n μ β) *
        (c' • 1 + t' • P n μ β) = 1 := by rw [← hg, ← hinv]; simp
    rw [smul_one_add_mul] at hmul
    obtain ⟨h1, h2⟩ := coeff_unique (n := n) (μ := μ) (β := β) (c := c * c')
      (t := c * t' + t * c' + t * t' * ρ n μ β) (c' := (1 : R)) (t' := 0) (by rw [hmul]; simp)
    refine ⟨IsUnit.of_mul_eq_one _ h1, IsUnit.of_mul_eq_one (c' + t' * ρ n μ β) ?_⟩
    linear_combination h1 + ρ n μ β * h2
  · rintro ⟨hc, hd⟩
    set a : R := ↑hc.unit⁻¹
    set b : R := ↑hd.unit⁻¹
    have e1 : c * a = 1 := hc.mul_val_inv
    have e2 : (c + t * ρ n μ β) * b = 1 := hd.mul_val_inv
    have key : ∀ c₁ t₁ c₂ t₂ : R, c₁ * c₂ = 1 → c₁ * t₂ + t₁ * c₂ + t₁ * t₂ * ρ n μ β = 0 →
        (c₁ • (1 : Module.End R (Fin (n + 2) → R)) + t₁ • P n μ β) *
          (c₂ • 1 + t₂ • P n μ β) = 1 := by
      intro c₁ t₁ c₂ t₂ h1 h2; rw [smul_one_add_mul, h1, h2]; simp
    have h0 : c * (-t * a * b) + t * a + t * (-t * a * b) * ρ n μ β = 0 := by
      linear_combination (-(t * a)) * e2
    exact ⟨⟨_, a • 1 + (-t * a * b) • P n μ β, key _ _ _ _ e1 h0,
      key _ _ _ _ (by rw [mul_comm]; exact e1) (by linear_combination (-(t * a)) * e2)⟩, rfl⟩

/-- The automorphisms of `(E, (τᵢ))`. -/
def centraliser (n : ℕ) (μ β : ℕ → R) : Subgroup (Module.End R (Fin (n + 2) → R))ˣ where
  carrier := {g | ∀ i ≤ n, (↑g : Module.End R (Fin (n + 2) → R)) * τ n μ β i = τ n μ β i * ↑g}
  one_mem' := by intro i _; simp
  mul_mem' := by
    intro a b ha hb i hi
    exact (Commute.mul_left (ha i hi) (hb i hi)).eq
  inv_mem' := by
    intro a ha i hi
    exact (Commute.units_inv_left (ha i hi)).eq

lemma u_zero : u n μ β 0 = 1 := by simp [u]

/-- `c • u_λ`, as a unit. -/
noncomputable def cu (p : Rˣ × U (ρ n μ β)) : (Module.End R (Fin (n + 2) → R))ˣ where
  val := (p.1 : R) • u n μ β p.2.val
  inv := (↑p.1⁻¹ : R) • u n μ β (p.2⁻¹).val
  val_inv := by
    rw [smul_mul_smul_comm, u_mul, ← U.mul_val, mul_inv_cancel, U.one_val, u_zero]; simp
  inv_val := by
    rw [smul_mul_smul_comm, u_mul, ← U.mul_val, inv_mul_cancel, U.one_val, u_zero]; simp

lemma cu_val (p : Rˣ × U (ρ n μ β)) :
    (cu p : Module.End R _) = (p.1 : R) • 1 + ((p.1 : R) * p.2.val) • P n μ β := by
  simp [cu, u, smul_add, smul_smul]

lemma cu_mem (p : Rˣ × U (ρ n μ β)) : cu p ∈ centraliser n μ β := by
  intro i hi
  rw [cu_val]; exact (commute_iff _).2 ⟨_, _, rfl⟩ i hi

/-- `(c, λ) ↦ c u_λ`. -/
noncomputable def cuHom : Rˣ × U (ρ n μ β) →* centraliser n μ β where
  toFun p := ⟨cu p, cu_mem p⟩
  map_one' := by
    apply Subtype.ext; apply Units.ext
    change ((1 : Rˣ) : R) • u n μ β (1 : U (ρ n μ β)).val = 1
    simp [u_zero]
  map_mul' p q := by
    apply Subtype.ext; apply Units.ext
    change ((p * q).1 : R) • u n μ β (p * q).2.val =
      ((p.1 : R) • u n μ β p.2.val) * ((q.1 : R) • u n μ β q.2.val)
    rw [smul_mul_smul_comm, u_mul]
    simp

/-- **`𝔾_m × 𝒰_ρ ≅ Aut(E, (τᵢ))`** on `R`-points: `(c, λ) ↦ c u_λ`. -/
noncomputable def centraliserEquiv : Rˣ × U (ρ n μ β) ≃* centraliser n μ β :=
  MulEquiv.ofBijective cuHom
    ⟨by
      intro p q h
      have h' := congrArg (fun g : centraliser n μ β =>
        ((g : (Module.End R (Fin (n + 2) → R))ˣ) : Module.End R (Fin (n + 2) → R))) h
      change (↑(cu p) : Module.End R (Fin (n + 2) → R)) = ↑(cu q) at h'
      rw [cu_val, cu_val] at h'
      obtain ⟨h1, h2⟩ := coeff_unique h'
      have h1' : p.1 = q.1 := Units.ext h1
      rw [h1] at h2
      exact Prod.ext h1' (U.ext (q.1.isUnit.mul_left_cancel h2)),
     by
      rintro ⟨g, hg⟩
      have hg' : ∀ i ≤ n, (↑g : Module.End R (Fin (n + 2) → R)) * τ n μ β i = τ n μ β i * ↑g := hg
      obtain ⟨c, t, hct⟩ := (commute_iff (↑g : Module.End R (Fin (n + 2) → R))).1 hg'
      obtain ⟨hc, hd⟩ := (isUnit_iff c t).1 (hct ▸ g.isUnit)
      refine ⟨(hc.unit, ⟨↑hc.unit⁻¹ * t, ?_⟩), ?_⟩
      · have : 1 + ρ n μ β * (↑hc.unit⁻¹ * t) = ↑hc.unit⁻¹ * (c + t * ρ n μ β) := by
          linear_combination (-1 : R) * hc.val_inv_mul
        rw [this]; exact (Units.isUnit _).mul hd
      · apply Subtype.ext; apply Units.ext
        change (hc.unit : R) • u n μ β (↑hc.unit⁻¹ * t) = ↑g
        rw [hct]
        simp only [u, IsUnit.unit_spec, smul_add, smul_smul]
        rw [← mul_assoc, hc.mul_val_inv, one_mul]⟩

/-! ### The start points: a torsor under `𝒰_ρ` -/

/-- The points of `D₀ = H₁ ∩ ⋯ ∩ Hₙ` are the `a s₀ + t c̃`. -/
theorem mem_D0_iff (s : Fin (n + 2) → R) :
    (∀ i, 1 ≤ i → i ≤ n → F n μ β i s = 0) ↔ ∃ a t : R, s = a • e n 0 + t • ct n μ β := by
  constructor
  · intro h
    set v := s - F n μ β 0 s • e n 0 with hv
    have hFv : ∀ i < n + 1, F n μ β i v = 0 := by
      intro i hi
      rcases Nat.eq_zero_or_pos i with rfl | hpos
      · simp [hv, F_e_self 0 (by omega)]
      · simp [hv, h i hpos (by omega), F_e_zero hpos]
    have hv' : v = co n (n + 1) v • ct n μ β :=
      eq_smul_vec le_rfl v (fun k hk => co_of_le (by omega) v) hFv
    refine ⟨F n μ β 0 s, co n (n + 1) v, ?_⟩
    rw [← hv', hv]; abel
  · rintro ⟨a, t, rfl⟩ i hi1 hi2
    simp [F_e_zero hi1, F_ct hi2]

lemma u_e0 (t : R) : u n μ β t (e n 0) = e n 0 + t • ct n μ β := by
  simp [u_apply, co_e 0 0 (show 0 < n + 2 by omega)]

/-- The start points off `c` (`⟨s, a'₀⟩` a unit, normalised to `1`) and off `d`
(`π(s)` a unit), in `D₀`. -/
def startPoints : Set (Fin (n + 2) → R) :=
  {s | (∀ i, 1 ≤ i → i ≤ n → F n μ β i s = 0) ∧ F n μ β 0 s = 1 ∧ IsUnit (co n 0 s)}

/-- `D₀ ∖ {c, d} = 𝒰_ρ · s₀`. -/
theorem mem_startPoints_iff (s : Fin (n + 2) → R) :
    s ∈ startPoints (n := n) (μ := μ) (β := β) ↔ ∃ x : U (ρ n μ β), s = u n μ β x.val (e n 0) := by
  constructor
  · rintro ⟨hD, hF0, hπ⟩
    obtain ⟨a, t, rfl⟩ := (mem_D0_iff s).1 hD
    have ha : a = 1 := by simpa [F_e_self 0 (by omega), F_ct (show 0 ≤ n by omega)] using hF0
    subst ha
    refine ⟨⟨t, ?_⟩, by rw [u_e0, one_smul]⟩
    have : co n 0 ((1 : R) • e n 0 + t • ct n μ β) = 1 + ρ n μ β * t := by
      simp [co_e 0 0 (show 0 < n + 2 by omega), co_ct_zero, mul_comm]
    convert hπ using 1; exact this.symm
  · rintro ⟨x, rfl⟩
    rw [u_e0]
    refine ⟨fun i hi1 hi2 => by simp [F_e_zero hi1, F_ct hi2], ?_, ?_⟩
    · simp [F_e_self 0 (by omega), F_ct (show 0 ≤ n by omega)]
    · have : co n 0 (e n 0 + x.val • ct n μ β) = 1 + ρ n μ β * x.val := by
        simp [co_e 0 0 (show 0 < n + 2 by omega), co_ct_zero, mul_comm]
      rw [this]; exact x.isUnit

/-- The orbit map `λ ↦ u_λ s₀` is injective: the action is free. -/
theorem u_e0_injective {x y : U (ρ n μ β)}
    (h : u n μ β x.val (e n 0) = u n μ β y.val (e n 0)) : x = y := by
  exact U.ext (by
    simpa [u_e0, co_e (n + 1) 0 (show 0 < n + 2 by omega), co_ct_top]
      using congrArg (co n (n + 1)) h)

/-- The action: `u_μ (u_λ s₀) = u_{λ * μ} s₀`. -/
theorem u_u_e0 (x y : U (ρ n μ β)) :
    u n μ β y.val (u n μ β x.val (e n 0)) = u n μ β (x * y).val (e n 0) := by
  rw [← Module.End.mul_apply, u_mul, U.mul_val]
  congr 2; ring

/-! ## Invariant subspaces (pages 79–82)

Finding `72-invariant-subspaces-string`, reading section XIV. Over a field, in the
coordinates above (any `μᵢ`, characteristic 2 allowed), with `Z'ᵢ = H₀ ∩ ⋯ ∩ Hᵢ`
(`Zp i`), `Z*ᵢ = Lin(h_{i+1}, …, hₙ)` (`Zs i`, the vectors whose coordinates
`0, …, i+1` vanish), `C` the hyperplane `π = 0` (`Vh`) and `c` the line of `c̃`:

* `invariant_iff` (the theorem of page 79): a subspace is stable under all `τᵢ` iff
  it is `0`, `E`, `K c̃`, `Vh`, or `Z'ᵢ` or `Z*ᵢ` for some `i < n` with `βᵢ = 0`.
* `Zs_le_Zp_iff`: `Z*ᵢ ⊂ Z'ᵢ` iff `βᵢ = 0` (with the « ∈ » of the margin of
  page 79, not the « ∉ » of page 81).
* `invariant_iff_of_ne_zero`: if all `βᵢ ≠ 0`, only the four.
-/

section Invariant

/-- `Z'ᵢ = H₀ ∩ ⋯ ∩ Hᵢ`. -/
def Zp (n : ℕ) (μ β : ℕ → R) (i : ℕ) : Submodule R (Fin (n + 2) → R) where
  carrier := {x | ∀ k ≤ i, F n μ β k x = 0}
  add_mem' := by intro a b ha hb k hk; simp [ha k hk, hb k hk]
  zero_mem' := by intro k _; simp
  smul_mem' := by intro c x hx k hk; simp [hx k hk]

/-- `Z*ᵢ = Lin(h_{i+1}, …, hₙ) = Lin(e_{i+2}, …, e_{n+1})`. -/
def Zs (n : ℕ) (i : ℕ) : Submodule R (Fin (n + 2) → R) where
  carrier := {x | ∀ k ≤ i + 1, co n k x = 0}
  add_mem' := by intro a b ha hb k hk; simp [ha k hk, hb k hk]
  zero_mem' := by intro k _; simp
  smul_mem' := by intro c x hx k hk; simp [hx k hk]

/-- The hyperplane at infinity `C`, `π = 0`. -/
def Vh (n : ℕ) : Submodule R (Fin (n + 2) → R) := LinearMap.ker (co n 0)

/-- Stability under all the `τᵢ`. -/
def Invariant (n : ℕ) (μ β : ℕ → R) (W : Submodule R (Fin (n + 2) → R)) : Prop :=
  ∀ i ≤ n, ∀ w ∈ W, τ n μ β i w ∈ W

lemma sum_e (x : Fin (n + 2) → R) : x = ∑ j : Fin (n + 2), x j • e n j := by
  conv_lhs => rw [pi_eq_sum_univ x]
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1; funext k; simp [e, Fin.ext_iff, eq_comm]

lemma mem_of_coords (W : Submodule R (Fin (n + 2) → R)) (x : Fin (n + 2) → R)
    (h : ∀ j : Fin (n + 2), x j = 0 ∨ e n j ∈ W) : x ∈ W := by
  rw [sum_e x]
  refine Submodule.sum_mem _ fun j _ => ?_
  rcases h j with h | h
  · simp [h]
  · exact W.smul_mem _ h

lemma F_e_succ_succ (i : ℕ) : F n μ β i (e n (i + 2)) = if i + 2 < n + 2 then β i else 0 := by
  by_cases h : i + 2 < n + 2
  · simp [F_apply, co_e _ _ h, h]
  · have he : (e n (i + 2) : Fin (n + 2) → R) = 0 := by
      funext j; simp [e]; omega
    simp [he, h]

theorem Zp_invariant {i : ℕ} (hi : i < n) (hβ : β i = 0) : Invariant n μ β (Zp n μ β i) := by
  intro j hj w hw
  by_cases hji : j ≤ i
  · rw [τ_apply, hw j hji, zero_smul, add_zero]; exact hw
  · refine (Zp n μ β i).add_mem hw ((Zp n μ β i).smul_mem _ ?_)
    intro k hk
    by_cases hk' : k = i ∧ j = i + 1
    · obtain ⟨rfl, rfl⟩ := hk'
      rw [F_e_succ_succ]; simp [hβ]
    · exact F_e_far μ β (by omega) (by omega) (by omega)

theorem Zs_invariant {i : ℕ} (hβ : β i = 0) : Invariant n μ β (Zs n i) := by
  intro j hj w hw
  by_cases hji : j ≤ i
  · have hF : F n μ β j w = 0 := by
      rw [F_apply, hw j (by omega), hw (j + 1) (by omega)]
      rcases (show j + 2 ≤ i + 1 ∨ j = i by omega) with h | rfl
      · rw [hw (j + 2) h]; ring
      · rw [hβ]; ring
    rw [τ_apply, hF, zero_smul, add_zero]; exact hw
  · refine (Zs n i).add_mem hw ((Zs n i).smul_mem _ ?_)
    intro k hk
    exact co_e_ne (by omega)

theorem Zs_le_Zp_iff {i : ℕ} (hi : i < n) : Zs n i ≤ Zp n μ β i ↔ β i = 0 := by
  constructor
  · intro h
    have hm : (e n (i + 2) : Fin (n + 2) → R) ∈ Zs n i := fun k hk => co_e_ne (by omega)
    have := h hm i le_rfl
    rw [F_e_succ_succ] at this
    simpa [show i + 2 < n + 2 by omega] using this
  · intro hβ x hx k hk
    rw [F_apply, hx k (by omega), hx (k + 1) (by omega)]
    rcases (show k + 2 ≤ i + 1 ∨ k = i by omega) with h | rfl
    · rw [hx (k + 2) h]; ring
    · rw [hβ]; ring

variable {K : Type u} [Field K] {μ' β' : ℕ → K}

lemma stable_iff_of_field (W : Submodule K (Fin (n + 2) → K)) (i : ℕ) :
    (∀ w ∈ W, τ n μ' β' i w ∈ W) ↔ e n (i + 1) ∈ W ∨ ∀ w ∈ W, F n μ' β' i w = 0 := by
  constructor
  · intro h
    by_cases hall : ∀ w ∈ W, F n μ' β' i w = 0
    · exact Or.inr hall
    · push Not at hall
      obtain ⟨w, hw, hne⟩ := hall
      left
      have h1 : F n μ' β' i w • e n (i + 1) ∈ W := by
        have := W.sub_mem (h w hw) hw
        rwa [τ_apply, add_sub_cancel_left] at this
      have := W.smul_mem (F n μ' β' i w)⁻¹ h1
      rwa [smul_smul, inv_mul_cancel₀ hne, one_smul] at this
  · rintro (h | h) w hw
    · rw [τ_apply]; exact W.add_mem hw (W.smul_mem _ h)
    · rw [τ_apply, h w hw, zero_smul, add_zero]; exact hw

/-- The low part `Σ_{k ≤ m} x_k e_k`. -/
def low (m : ℕ) (x : Fin (n + 2) → K) : Fin (n + 2) → K := fun j => if (j : ℕ) ≤ m then x j else 0

lemma co_low (m k : ℕ) (x : Fin (n + 2) → K) :
    co n k (low m x) = if k ≤ m then co n k x else 0 := by
  by_cases hk : k < n + 2
  · simp [co_of_lt hk, low]
  · simp [co_of_le (show n + 2 ≤ k by omega)]

lemma sub_low_mem_Zs (i : ℕ) (x : Fin (n + 2) → K) : x - low (i + 1) x ∈ Zs n i := by
  intro k hk; simp [co_low, hk]

/-- **Page 79.** The subspaces stable under all the `τᵢ`. -/
theorem invariant_iff (W : Submodule K (Fin (n + 2) → K)) :
    Invariant n μ' β' W ↔
      W = ⊥ ∨ W = ⊤ ∨ W = K ∙ ct n μ' β' ∨ W = Vh n ∨
        ∃ i < n, β' i = 0 ∧ (W = Zp n μ' β' i ∨ W = Zs n i) := by
  constructor
  · intro hW
    have hst : ∀ i ≤ n, e n (i + 1) ∈ W ∨ ∀ w ∈ W, F n μ' β' i w = 0 :=
      fun i hi => (stable_iff_of_field W i).1 (hW i hi)
    -- (a) the `i` with `W ⊂ Hᵢ` form an initial segment
    have ha : ∀ i, 1 ≤ i → i ≤ n → (∀ w ∈ W, F n μ' β' i w = 0) →
        ∀ w ∈ W, F n μ' β' (i - 1) w = 0 := by
      intro i h1 h2 hI
      rcases hst (i - 1) (by omega) with h | h
      · have := hI _ h
        rw [show i - 1 + 1 = i by omega, F_e_self i h2] at this
        exact absurd this one_ne_zero
      · exact h
    -- (b) the `j` with `hⱼ ∈ W` form a final segment
    have hb : ∀ j < n, e n (j + 1) ∈ W → e n (j + 2) ∈ W := by
      intro j hj he
      rcases hst (j + 1) (by omega) with h | h
      · exact h
      · have := h _ he
        rw [F_e_self (j + 1) (by omega)] at this
        exact absurd this one_ne_zero
    by_cases hIn : ∀ w ∈ W, F n μ' β' n w = 0
    · -- `W ⊂ H₀ ∩ ⋯ ∩ Hₙ = K c̃`
      have hall : ∀ i ≤ n, ∀ w ∈ W, F n μ' β' i w = 0 := by
        intro i hi
        induction h : n - i generalizing i with
        | zero => rwa [show i = n by omega]
        | succ m ih =>
          have := ha (i + 1) (by omega) (by omega) (ih (i + 1) (by omega) (by omega))
          simpa using this
      have hle : W ≤ K ∙ ct n μ' β' := by
        intro w hw
        rw [eq_smul_vec le_rfl w (fun k hk => co_of_le (by omega) w)
          (fun i hi => hall i (by omega) w hw)]
        exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
      by_cases hct : ct n μ' β' ∈ W
      · exact Or.inr (Or.inr (Or.inl (le_antisymm hle
          ((Submodule.span_singleton_le_iff_mem _ _).2 hct))))
      · left
        rw [Submodule.eq_bot_iff]
        intro w hw
        obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 (hle hw)
        by_cases hc0 : c = 0
        · rw [← hc, hc0, zero_smul]
        · exact absurd (by
            have := W.smul_mem c⁻¹ hw
            rwa [← hc, smul_smul, inv_mul_cancel₀ hc0, one_smul] at this) hct
    · have hen : e n (n + 1) ∈ W := (hst n le_rfl).resolve_right hIn
      have hex : ∃ j, e n (j + 1) ∈ W := ⟨n, hen⟩
      classical
      set j0 := Nat.find hex with hj0def
      have hj0 : e n (j0 + 1) ∈ W := Nat.find_spec hex
      have hj0n : j0 ≤ n := Nat.find_min' hex hen
      have hbelow : ∀ k < j0, ∀ w ∈ W, F n μ' β' k w = 0 :=
        fun k hk => (hst k (by omega)).resolve_left (Nat.find_min hex hk)
      have habove : ∀ k, j0 ≤ k → k ≤ n → e n (k + 1) ∈ W := by
        intro k hk1 hk2
        induction k with
        | zero => rwa [show j0 = 0 by omega] at hj0
        | succ k ih =>
          rcases (show j0 = k + 1 ∨ j0 ≤ k by omega) with h | h
          · rwa [h] at hj0
          · exact hb k (by omega) (ih h (by omega))
      have hej : ∀ j : Fin (n + 2), j0 + 1 ≤ (j : ℕ) → e n j ∈ W := by
        intro j hj
        have := habove ((j : ℕ) - 1) (by omega) (by omega)
        rwa [show (j : ℕ) - 1 + 1 = j by omega] at this
      rcases Nat.eq_zero_or_pos j0 with h0 | hpos
      · -- `C ⊂ W`
        have hV : Vh n ≤ W := by
          intro x hx
          refine mem_of_coords W x fun j => ?_
          rcases Nat.eq_zero_or_pos (j : ℕ) with hj | hj
          · left
            have : co n 0 x = 0 := hx
            rwa [co_of_lt (by omega), show (⟨0, by omega⟩ : Fin (n + 2)) = j from Fin.ext hj.symm]
              at this
          · exact Or.inr (hej j (by omega))
        by_cases hw : ∃ w ∈ W, co n 0 w ≠ 0
        · obtain ⟨w, hw, hne⟩ := hw
          right; left
          rw [eq_top_iff]
          intro x _
          have hm : x - (co n 0 x / co n 0 w) • w ∈ Vh n := by
            change co n 0 _ = 0
            rw [map_sub, map_smul, smul_eq_mul, div_mul_cancel₀ _ hne, sub_self]
          have := W.add_mem (hV hm) (W.smul_mem (co n 0 x / co n 0 w) hw)
          rwa [sub_add_cancel] at this
        · push Not at hw
          exact Or.inr (Or.inr (Or.inr (Or.inl (le_antisymm (fun w h => hw w h) hV))))
      · obtain ⟨i, hi⟩ : ∃ i, j0 = i + 1 := ⟨j0 - 1, by omega⟩
        have hin : i < n := by omega
        have hβ : β' i = 0 := by
          have := hbelow i (by omega) _
            (show e n (i + 2) ∈ W by have h := hj0; rw [hi] at h; exact h)
          rw [F_e_succ_succ] at this
          simpa [show i + 2 < n + 2 by omega] using this
        have hZsW : Zs n i ≤ W := by
          intro x hx
          refine mem_of_coords W x fun j => ?_
          by_cases hj : (j : ℕ) ≤ i + 1
          · left
            have := hx j hj
            rwa [co_of_lt j.isLt] at this
          · exact Or.inr (hej j (by omega))
        have hWZp : W ≤ Zp n μ' β' i := fun w hw k hk => hbelow k (by omega) w hw
        have hlow : ∀ x ∈ Zp n μ' β' i, low (i + 1) x = co n (i + 1) x • vec μ' β' (i + 1) := by
          intro x hx
          have hhigh := (Zs_le_Zp_iff (μ := μ') hin).2 hβ (sub_low_mem_Zs i x)
          have h := eq_smul_vec (μ := μ') (β := β') (show i + 1 ≤ n + 1 by omega) (low (i + 1) x)
            (fun k hk => by rw [co_low]; simp [show ¬ k ≤ i + 1 by omega])
            (fun k hk => by
              have h1 := hhigh k (by omega)
              rw [map_sub, hx k (by omega), zero_sub, neg_eq_zero] at h1
              exact h1)
          simp only [co_low, le_refl, ↓reduceIte] at h
          exact h
        right; right; right; right
        refine ⟨i, hin, hβ, ?_⟩
        by_cases hw : ∃ w ∈ W, co n (i + 1) w ≠ 0
        · obtain ⟨w, hw, hne⟩ := hw
          left
          have hlw : low (i + 1) w ∈ W := by
            have := W.sub_mem hw (hZsW (sub_low_mem_Zs i w))
            rwa [sub_sub_cancel] at this
          have hvec : vec μ' β' (i + 1) ∈ W := by
            have := W.smul_mem (co n (i + 1) w)⁻¹ hlw
            rwa [hlow w (hWZp hw), smul_smul, inv_mul_cancel₀ hne, one_smul] at this
          refine le_antisymm hWZp fun x hx => ?_
          have := W.add_mem (hZsW (sub_low_mem_Zs i x)) (W.smul_mem (co n (i + 1) x) hvec)
          rwa [← hlow x hx, sub_add_cancel] at this
        · push Not at hw
          right
          refine le_antisymm (fun w h => ?_) hZsW
          have h1 := sub_low_mem_Zs i w
          rwa [hlow w (hWZp h), hw w h, zero_smul, sub_zero] at h1
  · rintro (rfl | rfl | rfl | rfl | ⟨i, hi, hβ, rfl | rfl⟩)
    · intro i _ w hw; rw [Submodule.mem_bot] at hw ⊢; simp [hw]
    · intro i _ w _; trivial
    · intro i hi w hw
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hw
      rw [map_smul, τ_apply, F_ct hi, zero_smul, add_zero]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
    · intro i _ w hw
      change co n 0 _ = 0
      rw [co_τ_zero]; exact hw
    · exact Zp_invariant hi hβ
    · exact Zs_invariant hβ

/-- Corollary (c) of page 80: if all `βᵢ` are nonzero, the four are the only ones. -/
theorem invariant_iff_of_ne_zero (hβ : ∀ i < n, β' i ≠ 0) (W : Submodule K (Fin (n + 2) → K)) :
    Invariant n μ' β' W ↔ W = ⊥ ∨ W = ⊤ ∨ W = K ∙ ct n μ' β' ∨ W = Vh n := by
  rw [invariant_iff]
  constructor
  · rintro (h | h | h | h | ⟨i, hi, h0, _⟩)
    exacts [Or.inl h, Or.inr (Or.inl h), Or.inr (Or.inr (Or.inl h)), Or.inr (Or.inr (Or.inr h)),
      absurd h0 (hβ i hi)]
  · rintro (h | h | h | h)
    exacts [Or.inl h, Or.inr (Or.inl h), Or.inr (Or.inr (Or.inl h)),
      Or.inr (Or.inr (Or.inr (Or.inl h)))]

end Invariant

/-! ## Pinned realisations over a ring (pages 91–105)

Finding `72-pinned-realisations-over-base`, reading sections XV–XVI. Over a
commutative ring `k`, for a `k`-module `M`, pseudo-reflections
`τᵢ = id + a'ᵢ ⊗ aᵢ` (`ps`), a start vector `s₀`, `s_{i+1} = τᵢ sᵢ` (`sv`) and
`νᵢ = ⟨s₀, a'₀⟩⟨a₀, a'₁⟩⋯⟨a_{i−1}, a'ᵢ⟩`:

* `condA_iff_condB` (the theorem of pages 96–100, in the form (Ā) ⇔ (B̄) of the
  remark of page 102): « non-consecutive `τᵢ` commute, `τᵢ s₀ = s₀` for `i ≥ 1`,
  `(s₀, …, s_{n+1})` a basis » iff « `⟨aᵢ, a'ⱼ⟩ = 0` for `i, j` non-consecutive,
  `⟨s₀, a'ᵢ⟩ = 0` for `i ≥ 1`, `(s₀, a₀, …, aₙ)` a basis, `νₙ` a unit ». No
  strictness of the `a'ᵢ` is assumed: the basis condition forces `⟨sᵢ, a'ᵢ⟩`
  to be a unit.
* `pinned_classification`: a realisation satisfying (B̄), normalised by
  `⟨s₀, a'₀⟩ = 1` and `⟨a_{i−1}, a'ᵢ⟩ = 1`, is isomorphic, by a linear
  isomorphism sending `s₀` to `e₀` and conjugating the `τᵢ`, to the coordinate
  model `τ n μ β` above with `μᵢ = ⟨aᵢ, a'ᵢ⟩`, `βᵢ = ⟨a_{i+1}, a'ᵢ⟩`;
  `pinned_rigid`: the isomorphism is unique.
* `invariants_eq`: a linear map compatible with `s₀` and the `τᵢ` between two
  normalised realisations forces equal `(μᵢ, βᵢ)`.
* `model_condB`: the model satisfies (B̄), normalised, for all `μ`, `β`;
  `model_isUnit_iff`: `τᵢ` is invertible iff `λᵢ = 1 + μᵢ` is a unit. Hence the
  classification by the `2n + 1` parameters `(λ₀, β₀, …, β_{n−1}, λₙ)`,
  `λᵢ` units, `βᵢ` arbitrary (margin of page 13).

Not formalised: the local existence of the start vector (pages 102–105), the
locally free (non-free) case, the projective version.
-/

section Pinned

open Module

variable {k : Type*} [CommRing k] {M : Type*} [AddCommGroup M] [Module k M]

/-- The pseudo-reflection `τᵢ = id + a'ᵢ ⊗ aᵢ`. -/
def ps (a : ℕ → M) (a' : ℕ → Module.Dual k M) (i : ℕ) : Module.End k M :=
  1 + (a' i).smulRight (a i)

/-- `s₀`, `s_{i+1} = τᵢ sᵢ`. -/
def sv (a : ℕ → M) (a' : ℕ → Module.Dual k M) (s0 : M) : ℕ → M
  | 0 => s0
  | i + 1 => ps a a' i (sv a a' s0 i)

/-- `νᵢ = ⟨s₀, a'₀⟩⟨a₀, a'₁⟩⋯⟨a_{i−1}, a'ᵢ⟩`. -/
def ν (a : ℕ → M) (a' : ℕ → Module.Dual k M) (s0 : M) : ℕ → k
  | 0 => a' 0 s0
  | i + 1 => ν a a' s0 i * a' (i + 1) (a i)

/-- The family `(s₀, a₀, a₁, …)`. -/
def av (a : ℕ → M) (s0 : M) : ℕ → M
  | 0 => s0
  | i + 1 => a i

variable (k) in
/-- A family indexed by `Fin m` is a basis. -/
def IsBasisFam {m : ℕ} (f : Fin m → M) : Prop :=
  LinearIndependent k f ∧ Submodule.span k (Set.range f) = ⊤

/-- Conditions (Ā): (7), (8) and `(s₀, …, s_{n+1})` a basis. -/
def CondA (n : ℕ) (a : ℕ → M) (a' : ℕ → Module.Dual k M) (s0 : M) : Prop :=
  (∀ i j, i + 2 ≤ j → j ≤ n → ps a a' i * ps a a' j = ps a a' j * ps a a' i) ∧
  (∀ i, 1 ≤ i → i ≤ n → ps a a' i s0 = s0) ∧
  IsBasisFam k (fun j : Fin (n + 2) => sv a a' s0 j)

/-- Conditions (B̄): (10), (11), `(s₀, a₀, …, aₙ)` a basis, (13). -/
def CondB (n : ℕ) (a : ℕ → M) (a' : ℕ → Module.Dual k M) (s0 : M) : Prop :=
  (∀ i j, i + 2 ≤ j → j ≤ n → a' j (a i) = 0 ∧ a' i (a j) = 0) ∧
  (∀ i, 1 ≤ i → i ≤ n → a' i s0 = 0) ∧
  IsBasisFam k (fun j : Fin (n + 2) => av a s0 j) ∧
  IsUnit (ν a a' s0 n)

variable {a : ℕ → M} {a' : ℕ → Module.Dual k M} {s0 : M}

lemma ps_apply (i : ℕ) (x : M) : ps a a' i x = x + a' i x • a i := rfl

lemma sv_succ (i : ℕ) : sv a a' s0 (i + 1) = sv a a' s0 i + a' i (sv a a' s0 i) • a i := rfl

lemma sv_eq_sum (j : ℕ) :
    sv a a' s0 j = s0 + ∑ m ∈ Finset.range j, a' m (sv a a' s0 m) • a m := by
  induction j with
  | zero => simp [sv]
  | succ j ih => rw [sv_succ, Finset.sum_range_succ, ← add_assoc, ← ih]

/-- Under (10) and (11), `⟨sⱼ, a'ⱼ⟩ = νⱼ` (part 1° of the theorem). -/
lemma d_eq_ν {n : ℕ} (h10 : ∀ i j, i + 2 ≤ j → j ≤ n → a' j (a i) = 0)
    (h11 : ∀ i, 1 ≤ i → i ≤ n → a' i s0 = 0) : ∀ j ≤ n, a' j (sv a a' s0 j) = ν a a' s0 j := by
  intro j
  induction j with
  | zero => intro _; rfl
  | succ j ih =>
    intro hj
    rw [sv_eq_sum, map_add, map_sum, h11 (j + 1) (by omega) hj, zero_add, Finset.sum_range_succ,
      Finset.sum_eq_zero (fun m hm => by
        rw [map_smul, h10 m (j + 1) (by simp at hm; omega) hj, smul_zero]),
      zero_add, map_smul, ih (by omega), smul_eq_mul, ν]

lemma isUnit_ν_of_le {n : ℕ} (h : IsUnit (ν a a' s0 n)) : ∀ j ≤ n, IsUnit (ν a a' s0 j) := by
  intro j hj
  induction h' : n - j generalizing j with
  | zero => rwa [show j = n by omega]
  | succ m ih =>
    have := ih (j + 1) (by omega) (by omega)
    rw [ν] at this
    exact isUnit_of_mul_isUnit_left this

/-- The basis attached to a family that is one. -/
noncomputable def bas {m : ℕ} {f : Fin m → M} (hf : IsBasisFam k f) : Basis (Fin m) k M :=
  Basis.mk hf.1 hf.2.ge

lemma bas_apply {m : ℕ} {f : Fin m → M} (hf : IsBasisFam k f) (j : Fin m) : bas hf j = f j :=
  Basis.mk_apply hf.1 hf.2.ge j

lemma bas_repr {m : ℕ} {f : Fin m → M} (hf : IsBasisFam k f) (j : Fin m) :
    (bas hf).repr (f j) = Finsupp.single j 1 := by
  rw [← bas_apply hf j, Basis.repr_self]

/-- A family upper triangular in a basis, with invertible diagonal, is a basis. -/
lemma isBasisFam_of_tri {m : ℕ} (b : Basis (Fin m) k M) (v : Fin m → M)
    (hlow : ∀ i j : Fin m, j < i → b.repr (v j) i = 0) (hdiag : ∀ j, IsUnit (b.repr (v j) j)) :
    IsBasisFam k v := by
  refine b.is_basis_iff_det.2 ?_
  rw [b.det_apply, Matrix.det_of_isUpperTriangular (by
    intro i j h; rw [Basis.toMatrix_apply]; exact hlow i j h)]
  have : (∏ i, b.toMatrix v i i) = ↑(∏ i, (hdiag i).unit) := by
    simp [Units.coe_prod, Basis.toMatrix_apply]
  rw [this]; exact Units.isUnit _

lemma single_apply_fin {m : ℕ} (i j : Fin m) (c : k) :
    Finsupp.single i c j = if (i : ℕ) = j then c else 0 := by
  simp [Finsupp.single_apply, Fin.ext_iff]

/-- (B̄) ⇒ (Ā). -/
theorem condA_of_condB {n : ℕ} (hB : CondB n a a' s0) : CondA n a a' s0 := by
  obtain ⟨h10, h11, hbas, hν⟩ := hB
  have hd := d_eq_ν (fun i j h1 h2 => (h10 i j h1 h2).1) h11
  refine ⟨fun i j hij hj => ?_, fun i h1 h2 => ?_, ?_⟩
  · refine LinearMap.ext fun x => ?_
    simp only [Module.End.mul_apply, ps_apply, map_add, map_smul, (h10 i j hij hj).1,
      (h10 i j hij hj).2, zero_smul, add_zero]
    abel
  · rw [ps_apply, h11 i h1 h2, zero_smul, add_zero]
  · set b := bas hbas
    have hra : ∀ i (hi : i ≤ n), b.repr (a i) = Finsupp.single ⟨i + 1, by omega⟩ 1 :=
      fun i hi => bas_repr hbas ⟨i + 1, by omega⟩
    have hlow : ∀ j (hj : j < n + 2) (i : Fin (n + 2)), j < (i : ℕ) →
        b.repr (sv a a' s0 j) i = 0 := by
      intro j
      induction j with
      | zero =>
        intro _ i hi
        rw [show sv a a' s0 0 = av a s0 ((⟨0, by omega⟩ : Fin (n + 2)) : ℕ) from rfl,
          bas_repr hbas, single_apply_fin]
        simp only [ite_eq_right_iff]; omega
      | succ j ih =>
        intro hj i hi
        rw [sv_succ, map_add, map_smul, hra j (by omega), Finsupp.add_apply,
          ih (by omega) i (by omega), Finsupp.smul_apply, single_apply_fin]
        split_ifs with h
        · simp at h; omega
        · simp
    refine isBasisFam_of_tri b _ (fun i j h => hlow j j.isLt i h) (fun j => ?_)
    obtain ⟨j, hj⟩ := j
    rcases j with _ | j
    · rw [show sv a a' s0 ((⟨0, hj⟩ : Fin (n + 2)) : ℕ) = av a s0 ((⟨0, hj⟩ : Fin (n + 2)) : ℕ)
        from rfl, bas_repr hbas]
      simp
    · simp only
      rw [sv_succ, map_add, map_smul, hra j (by omega), Finsupp.add_apply,
        hlow j (by omega) ⟨j + 1, hj⟩ (by simp), Finsupp.smul_apply, Finsupp.single_eq_same,
        zero_add, smul_eq_mul, mul_one, hd j (by omega)]
      exact isUnit_ν_of_le hν j (by omega)

/-- (Ā) ⇒ (B̄). -/
theorem condB_of_condA {n : ℕ} (hA : CondA n a a' s0) : CondB n a a' s0 := by
  obtain ⟨h7, h8, hbas⟩ := hA
  set b := bas hbas
  have hsv : ∀ j (hj : j < n + 2), b.repr (sv a a' s0 j) = Finsupp.single ⟨j, hj⟩ 1 :=
    fun j hj => bas_repr hbas ⟨j, hj⟩
  -- `dᵢ • aᵢ = s_{i+1} − sᵢ`
  have hda : ∀ i (hi : i ≤ n) (l : Fin (n + 2)), a' i (sv a a' s0 i) * b.repr (a i) l =
      (if (l : ℕ) = i + 1 then 1 else 0) - (if (l : ℕ) = i then 1 else 0) := by
    intro i hi l
    have h := congrArg (fun x => b.repr x l) (show a' i (sv a a' s0 i) • a i =
      sv a a' s0 (i + 1) - sv a a' s0 i by rw [sv_succ]; abel)
    simp only [map_smul, Finsupp.smul_apply, smul_eq_mul, map_sub, Finsupp.sub_apply,
      hsv (i + 1) (by omega), hsv i (by omega), single_apply_fin] at h
    rw [h]; simp [eq_comm]
  have hdu : ∀ i ≤ n, IsUnit (a' i (sv a a' s0 i)) := by
    intro i hi
    have := hda i hi ⟨i + 1, by omega⟩
    simp only [↓reduceIte, show i + 1 ≠ i by omega, sub_zero] at this
    exact IsUnit.of_mul_eq_one _ this
  have hdiag : ∀ i (hi : i ≤ n), IsUnit (b.repr (a i) ⟨i + 1, by omega⟩) := by
    intro i hi
    have := hda i hi ⟨i + 1, by omega⟩
    simp only [↓reduceIte, show i + 1 ≠ i by omega, sub_zero] at this
    exact IsUnit.of_mul_eq_one_right _ this
  have hoff : ∀ i (hi : i ≤ n) (l : Fin (n + 2)), (l : ℕ) ≠ i → (l : ℕ) ≠ i + 1 →
      b.repr (a i) l = 0 := by
    intro i hi l h1 h2
    have := hda i hi l
    simp only [h1, h2, ↓reduceIte, sub_zero] at this
    exact (hdu i hi).mul_right_eq_zero.1 this
  -- smul-cancellation on `aᵢ` through the coordinate `i + 1`
  have hcancel : ∀ i (hi : i ≤ n) (c : k), c • a i = 0 → c = 0 := by
    intro i hi c h
    have := congrArg (fun x => b.repr x ⟨i + 1, by omega⟩) h
    simp only [map_smul, Finsupp.smul_apply, smul_eq_mul, map_zero, Finsupp.coe_zero,
      Pi.zero_apply] at this
    exact (hdiag i hi).mul_left_eq_zero.1 this
  have h11 : ∀ i, 1 ≤ i → i ≤ n → a' i s0 = 0 := by
    intro i h1 h2
    have h := h8 i h1 h2
    rw [ps_apply, add_eq_left] at h
    exact hcancel i h2 _ h
  have hcomm : ∀ i j, i + 2 ≤ j → j ≤ n → ∀ x,
      (a' j x * a' i (a j)) • a i = (a' i x * a' j (a i)) • a j := by
    intro i j hij hj x
    have h := congrArg (fun f : Module.End k M => f x) (h7 i j hij hj)
    simp only [Module.End.mul_apply, ps_apply, map_add, map_smul] at h
    rw [mul_smul, mul_smul]
    linear_combination (norm := module) h
  have h10 : ∀ i j, i + 2 ≤ j → j ≤ n → a' j (a i) = 0 ∧ a' i (a j) = 0 := by
    intro i j hij hj
    constructor
    · have h := congrArg (fun x => b.repr x ⟨j + 1, by omega⟩) (hcomm i j hij hj (sv a a' s0 i))
      simp only [map_smul, Finsupp.smul_apply, smul_eq_mul,
        hoff i (by omega) ⟨j + 1, by omega⟩ (by simp; omega) (by simp; omega), mul_zero] at h
      have h' := h.symm
      rw [mul_assoc] at h'
      exact (hdiag j hj).mul_left_eq_zero.1 ((hdu i (by omega)).mul_right_eq_zero.1 h')
    · have h := congrArg (fun x => b.repr x ⟨i + 1, by omega⟩) (hcomm i j hij hj (sv a a' s0 j))
      simp only [map_smul, Finsupp.smul_apply, smul_eq_mul,
        hoff j hj ⟨i + 1, by omega⟩ (by simp; omega) (by simp; omega), mul_zero] at h
      rw [mul_assoc] at h
      exact (hdiag i (by omega)).mul_left_eq_zero.1 ((hdu j hj).mul_right_eq_zero.1 h)
  have hd := d_eq_ν (fun i j h1 h2 => (h10 i j h1 h2).1) h11
  refine ⟨h10, h11, ?_, by rw [← hd n le_rfl]; exact hdu n le_rfl⟩
  refine isBasisFam_of_tri b _ (fun l j hjl => ?_) (fun j => ?_)
  · obtain ⟨j, hj⟩ := j
    rcases j with _ | j
    · change b.repr (sv a a' s0 0) l = 0
      rw [hsv 0 hj, single_apply_fin]
      simp only [ite_eq_right_iff]
      intro h; exact absurd hjl (by rw [Fin.lt_def]; simp; omega)
    · change b.repr (a j) l = 0
      rw [Fin.lt_def] at hjl
      exact hoff j (by omega) l (by simp at hjl; omega) (by simp at hjl; omega)
  · obtain ⟨j, hj⟩ := j
    rcases j with _ | j
    · change IsUnit (b.repr (sv a a' s0 0) ⟨0, hj⟩)
      rw [hsv 0 hj]; simp
    · exact hdiag j (by omega)

/-- **Pages 96–100.** (Ā) ⇔ (B̄). -/
theorem condA_iff_condB (n : ℕ) : CondA n a a' s0 ↔ CondB n a a' s0 :=
  ⟨condB_of_condA, condA_of_condB⟩

/-! ### The classification -/

lemma model_ps (n : ℕ) (μ β : ℕ → k) (i : ℕ) :
    ps (fun i => e n (i + 1)) (F n μ β) i = τ n μ β i := rfl

lemma av_model (n : ℕ) (j : Fin (n + 2)) :
    av (fun i => (e n (i + 1) : Fin (n + 2) → k)) (e n 0) j = Pi.basisFun k (Fin (n + 2)) j := by
  rw [Pi.basisFun_apply, e_val, one_smul]
  obtain ⟨j, hj⟩ := j
  rcases j with _ | j <;> rfl

lemma ν_model (n : ℕ) (μ β : ℕ → k) (j : ℕ) (hj : j ≤ n) :
    ν (fun i => (e n (i + 1) : Fin (n + 2) → k)) (F n μ β) (e n 0) j = 1 := by
  induction j with
  | zero => exact F_e_self 0 (by omega)
  | succ j ih => rw [ν, ih (by omega), F_e_self (j + 1) hj, one_mul]

/-- The model satisfies (B̄), normalised, for all parameters. -/
theorem model_condB (n : ℕ) (μ β : ℕ → k) :
    CondB n (fun i => (e n (i + 1) : Fin (n + 2) → k)) (F n μ β) (e n 0) ∧
      F n μ β 0 (e n 0) = 1 ∧ ∀ i < n, F n μ β (i + 1) (e n (i + 1)) = 1 := by
  refine ⟨⟨fun i j hij hj => ⟨F_e_far μ β (by omega) (by omega) (by omega),
      F_e_far μ β (by omega) (by omega) (by omega)⟩, fun i h1 _ => F_e_zero h1, ?_, ?_⟩,
    F_e_self 0 (by omega), fun i hi => F_e_self (i + 1) (by omega)⟩
  · have : (fun j : Fin (n + 2) => av (fun i => (e n (i + 1) : Fin (n + 2) → k)) (e n 0) j) =
        Pi.basisFun k (Fin (n + 2)) := funext (av_model n)
    rw [this]
    exact ⟨(Pi.basisFun k (Fin (n + 2))).linearIndependent, (Pi.basisFun k _).span_eq⟩
  · rw [ν_model n μ β n le_rfl]; exact isUnit_one

/-- In the model, `τᵢ` is invertible iff `λᵢ = 1 + μᵢ` is a unit. -/
theorem model_isUnit_iff (n : ℕ) (μ β : ℕ → k) {i : ℕ} (hi : i ≤ n) :
    IsUnit (τ n μ β i) ↔ IsUnit (1 + μ i) := by
  have hτe : τ n μ β i (e n (i + 1)) = (1 + μ i) • e n (i + 1) := by
    rw [τ_apply, add_smul, one_smul]
    congr 2
    simp [F_apply, co_e _ (i + 1) (show i + 1 < n + 2 by omega)]
  have hF : F n μ β i (e n (i + 1)) = μ i := by
    simp [F_apply, co_e _ (i + 1) (show i + 1 < n + 2 by omega)]
  constructor
  · rintro ⟨σ, hσ⟩
    have h := congrArg (fun x => co n (i + 1) ((↑σ⁻¹ : Module.End k _) x)) hτe
    rw [← hσ, ← Module.End.mul_apply, Units.inv_mul, Module.End.one_apply,
      co_e_self (i + 1) (by omega)] at h
    simp only [map_smul, smul_eq_mul] at h
    exact IsUnit.of_mul_eq_one _ h.symm
  · intro hl
    have hu : (1 + μ i) * ↑hl.unit⁻¹ = 1 := hl.mul_val_inv
    refine ⟨⟨τ n μ β i, 1 - (↑hl.unit⁻¹ : k) • (F n μ β i).smulRight (e n (i + 1)), ?_, ?_⟩, rfl⟩
    all_goals
      refine LinearMap.ext fun x => ?_
      simp only [τ, Module.End.mul_apply, LinearMap.sub_apply, LinearMap.add_apply,
        Module.End.one_apply, LinearMap.smul_apply, LinearMap.smulRight_apply, map_add, map_sub,
        map_smul, hF]
      linear_combination (norm := module) hu • ((-F n μ β i x) • (e n (i + 1) : Fin (n + 2) → k))

/-- **The classification** (margin of page 13, with the coordinates of page 91): a
normalised pinned realisation is isomorphic to the model with `μᵢ = ⟨aᵢ, a'ᵢ⟩`,
`βᵢ = ⟨a_{i+1}, a'ᵢ⟩`. -/
theorem pinned_classification {n : ℕ} (hB : CondB n a a' s0) (h0 : a' 0 s0 = 1)
    (h1 : ∀ i < n, a' (i + 1) (a i) = 1) :
    ∃ φ : M ≃ₗ[k] (Fin (n + 2) → k), φ s0 = e n 0 ∧ ∀ i ≤ n,
      φ.toLinearMap ∘ₗ ps a a' i =
        τ n (fun i => a' i (a i)) (fun i => a' i (a (i + 1))) i ∘ₗ φ.toLinearMap := by
  obtain ⟨h10, h11, hbas, _⟩ := hB
  set b := bas hbas
  have hφ : ∀ j : Fin (n + 2), b.equivFun (av a s0 j) = (e n j : Fin (n + 2) → k) := by
    intro j
    change (bas hbas).equivFun (av a s0 j) = _
    rw [← bas_apply hbas j]
    funext l
    rw [Basis.equivFun_self]
    by_cases h : j = l
    · subst h; simp [e]
    · have h' : (l : ℕ) ≠ j := fun h'' => h (Fin.ext h''.symm)
      simp [e, h, h']
  refine ⟨b.equivFun, hφ ⟨0, by omega⟩, fun i hi => b.ext fun j => ?_⟩
  have hai : b.equivFun (a i) = (e n (i + 1) : Fin (n + 2) → k) := hφ ⟨i + 1, by omega⟩
  rw [show b j = av a s0 j from bas_apply hbas j]
  simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply]
  rw [ps_apply, map_add, map_smul, hφ, hai, τ_apply]
  congr 2
  obtain ⟨j, hj⟩ := j
  simp only [F_apply, co_e _ j hj]
  -- `F i (e j) = ⟨av j, a'ᵢ⟩`
  rcases (show j = i ∨ j = i + 1 ∨ j = i + 2 ∨ (j ≠ i ∧ j ≠ i + 1 ∧ j ≠ i + 2) by omega) with
    rfl | rfl | rfl | ⟨hj1, hj2, hj3⟩
  · rcases j with _ | j
    · simp [av, h0]
    · simp [av, h1 j (by omega)]
  · simp [av]
  · simp [av]
  · simp only [Ne.symm hj1, Ne.symm hj2, Ne.symm hj3, ↓reduceIte, mul_zero, add_zero]
    rcases j with _ | j
    · exact h11 i (by omega) hi
    · rcases (show j + 2 ≤ i ∨ i + 2 ≤ j by omega) with h | h
      · exact (h10 j i h hi).1
      · exact (h10 i j h (by omega)).2

/-- A linear map compatible with `s₀` and the `τᵢ` agrees with any other on the `sⱼ`. -/
lemma map_sv {M₂ : Type*} [AddCommGroup M₂] [Module k M₂] {b : ℕ → M₂}
    {b' : ℕ → Module.Dual k M₂} {t0 : M₂} {n : ℕ} (φ : M →ₗ[k] M₂) (h0 : φ s0 = t0)
    (hφ : ∀ i ≤ n, φ ∘ₗ ps a a' i = ps b b' i ∘ₗ φ) :
    ∀ j ≤ n + 1, φ (sv a a' s0 j) = sv b b' t0 j := by
  intro j hj
  induction j with
  | zero => exact h0
  | succ j ih =>
    have := congrArg (fun f => f (sv a a' s0 j)) (hφ j (by omega))
    simp only [LinearMap.coe_comp, Function.comp_apply] at this
    rw [sv, this, ih (by omega)]; rfl

/-- Rigidity: the isomorphism with the model is unique. -/
theorem pinned_rigid {n : ℕ} (hB : CondB n a a' s0) (μ β : ℕ → k)
    (φ ψ : M →ₗ[k] (Fin (n + 2) → k)) (hφ0 : φ s0 = e n 0) (hψ0 : ψ s0 = e n 0)
    (hφ : ∀ i ≤ n, φ ∘ₗ ps a a' i = τ n μ β i ∘ₗ φ)
    (hψ : ∀ i ≤ n, ψ ∘ₗ ps a a' i = τ n μ β i ∘ₗ ψ) : φ = ψ := by
  have hA := condA_of_condB hB
  refine (bas hA.2.2).ext fun j => ?_
  simp only [bas, Basis.mk_apply]
  rw [map_sv (b := fun i => e n (i + 1)) (b' := F n μ β) φ hφ0 hφ j (by omega),
    map_sv (b := fun i => e n (i + 1)) (b' := F n μ β) ψ hψ0 hψ j (by omega)]

/-- Normalised, `aᵢ = s_{i+1} − sᵢ`. -/
lemma a_eq_sub {n : ℕ} (hB : CondB n a a' s0) (h0 : a' 0 s0 = 1)
    (h1 : ∀ i < n, a' (i + 1) (a i) = 1) : ∀ i ≤ n, a i = sv a a' s0 (i + 1) - sv a a' s0 i := by
  intro i hi
  have hν : ∀ j ≤ n, ν a a' s0 j = 1 := by
    intro j hj
    induction j with
    | zero => exact h0
    | succ j ih => rw [ν, ih (by omega), h1 j (by omega), one_mul]
  rw [sv_succ, d_eq_ν (fun i j h h' => (hB.1 i j h h').1) hB.2.1 i hi, hν i hi, one_smul,
    add_sub_cancel_left]

/-- **The invariants**: a linear map compatible with `s₀` and the `τᵢ` between two
normalised realisations forces the same `(μᵢ, βᵢ)`. -/
theorem invariants_eq {M₂ : Type*} [AddCommGroup M₂] [Module k M₂] {b : ℕ → M₂}
    {b' : ℕ → Module.Dual k M₂} {t0 : M₂} {n : ℕ}
    (hB : CondB n a a' s0) (h0 : a' 0 s0 = 1) (h1 : ∀ i < n, a' (i + 1) (a i) = 1)
    (hB₂ : CondB n b b' t0) (h0₂ : b' 0 t0 = 1) (h1₂ : ∀ i < n, b' (i + 1) (b i) = 1)
    (φ : M →ₗ[k] M₂) (hφ0 : φ s0 = t0) (hφ : ∀ i ≤ n, φ ∘ₗ ps a a' i = ps b b' i ∘ₗ φ) :
    (∀ i ≤ n, a' i (a i) = b' i (b i)) ∧ (∀ i < n, a' i (a (i + 1)) = b' i (b (i + 1))) := by
  have hφa : ∀ i ≤ n, φ (a i) = b i := by
    intro i hi
    rw [a_eq_sub hB h0 h1 i hi, map_sub, map_sv φ hφ0 hφ (i + 1) (by omega),
      map_sv φ hφ0 hφ i (by omega), a_eq_sub hB₂ h0₂ h1₂ i hi]
  have hcancel : ∀ i ≤ n, ∀ c c' : k, c • b i = c' • b i → c = c' := by
    intro i hi c c' h
    have := congrArg (fun x => (bas hB₂.2.2.1).repr x ⟨i + 1, by omega⟩) h
    simp only [map_smul, Finsupp.smul_apply, smul_eq_mul] at this
    rwa [show b i = av b t0 ((⟨i + 1, by omega⟩ : Fin (n + 2)) : ℕ) from rfl, bas_repr,
      Finsupp.single_eq_same, mul_one, mul_one] at this
  have hτ : ∀ i ≤ n, ∀ x, φ (ps a a' i x) = ps b b' i (φ x) := fun i hi x =>
    congrArg (fun f => f x) (hφ i hi)
  constructor
  · intro i hi
    have h := hτ i hi (a i)
    rw [ps_apply, ps_apply, map_add, map_smul, hφa i hi] at h
    have h' : (a' i (a i)) • b i = (b' i (b i)) • b i := add_left_cancel h
    exact hcancel i hi _ _ h'
  · intro i hi
    have h := hτ i (by omega) (a (i + 1))
    rw [ps_apply, ps_apply, map_add, map_smul, hφa (i + 1) hi, hφa i (by omega)] at h
    exact hcancel i (by omega) _ _ (add_left_cancel h)

end Pinned

/-! ## Irreducibility on `C` (pages 80–82)

Finding `72-invariant-subspaces-string`, reading section XIV, « Irréductibilité sur
`C` ». Over a field, in the coordinates above, the subspaces of the hyperplane
`C = Vh` (`π = 0`) stable under all `τᵢ`:

* `invariant_le_Vh_iff`: in general, `0`, `C`, the line `K c̃` when `ρ = 0`
  (`c ∈ C`), and, for `i < n` with `βᵢ = 0`, `Z*ᵢ` (always in `C`, `Zs_le_Vh`)
  and `Z'ᵢ` when `Z'ᵢ ⊂ C`.
* `invariant_le_Vh_iff_of_ne_zero`: if all `βᵢ ≠ 0`, only `0`, `C`, and `K c̃` when
  `ρ = 0`.
* `irreducible_on_C_iff`: the representation on `C` is irreducible iff all
  `βᵢ ≠ 0` and (`n = 0` or `ρ ≠ 0`). So « all `βᵢ ≠ 0` » alone (page 82, c)) does
  not suffice for `n ≥ 1`: `ρ = 0` gives the invariant line `K c̃ ⊂ C`, as the
  struck-out d) of page 80 says. For `n = 0`, `C` is a line.
-/

section Irreducible

variable {K : Type u} [Field K] {μ' β' : ℕ → K}

lemma e_mem_Vh {k : ℕ} (hk : k ≠ 0) : (e n k : Fin (n + 2) → K) ∈ Vh n :=
  co_e_ne (Ne.symm hk)

lemma e_zero_not_mem_Vh : (e n 0 : Fin (n + 2) → K) ∉ Vh n := by
  intro h
  have h1 := co_e_self (R := K) (n := n) 0 (by omega)
  change co n 0 _ = 0 at h
  exact zero_ne_one (h ▸ h1)

lemma ct_mem_Vh_iff : ct n μ' β' ∈ Vh n ↔ ρ n μ' β' = 0 := by
  change co n 0 _ = 0 ↔ _; rw [co_ct_zero]

lemma Zs_le_Vh (i : ℕ) : Zs n i ≤ (Vh n : Submodule K (Fin (n + 2) → K)) :=
  fun _ hx => hx 0 (Nat.zero_le _)

lemma ct_ne_zero : ct n μ' β' ≠ 0 := by
  intro h
  simpa [h] using co_ct_top (n := n) (μ := μ') (β := β')

/-- **Pages 80–82.** The invariant subspaces contained in `C`, in general. -/
theorem invariant_le_Vh_iff (W : Submodule K (Fin (n + 2) → K)) :
    (Invariant n μ' β' W ∧ W ≤ Vh n) ↔
      W = ⊥ ∨ W = Vh n ∨ (ρ n μ' β' = 0 ∧ W = K ∙ ct n μ' β') ∨
        ∃ i < n, β' i = 0 ∧ (W = Zs n i ∨ (W = Zp n μ' β' i ∧ Zp n μ' β' i ≤ Vh n)) := by
  constructor
  · rintro ⟨hW, hle⟩
    rcases (invariant_iff W).1 hW with h | h | h | h | ⟨i, hi, hβ, h | h⟩
    · exact Or.inl h
    · subst h; exact absurd (hle Submodule.mem_top) e_zero_not_mem_Vh
    · refine Or.inr (Or.inr (Or.inl ⟨ct_mem_Vh_iff.1 (hle ?_), h⟩))
      rw [h]; exact Submodule.mem_span_singleton_self _
    · exact Or.inr (Or.inl h)
    · subst h; exact Or.inr (Or.inr (Or.inr ⟨i, hi, hβ, Or.inr ⟨rfl, hle⟩⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨i, hi, hβ, Or.inl h⟩))
  · rintro (rfl | rfl | ⟨h0, rfl⟩ | ⟨i, hi, hβ, rfl | ⟨rfl, hle⟩⟩)
    · exact ⟨(invariant_iff _).2 (Or.inl rfl), bot_le⟩
    · exact ⟨(invariant_iff _).2 (Or.inr (Or.inr (Or.inr (Or.inl rfl)))), le_rfl⟩
    · exact ⟨(invariant_iff _).2 (Or.inr (Or.inr (Or.inl rfl))),
        (Submodule.span_singleton_le_iff_mem _ _).2 (ct_mem_Vh_iff.2 h0)⟩
    · exact ⟨Zs_invariant hβ, Zs_le_Vh i⟩
    · exact ⟨Zp_invariant hi hβ, hle⟩

/-- If all `βᵢ ≠ 0`, the invariant subspaces of `C` are `0`, `C`, and `K c̃` when `ρ = 0`. -/
theorem invariant_le_Vh_iff_of_ne_zero (hβ : ∀ i < n, β' i ≠ 0)
    (W : Submodule K (Fin (n + 2) → K)) :
    (Invariant n μ' β' W ∧ W ≤ Vh n) ↔
      W = ⊥ ∨ W = Vh n ∨ (ρ n μ' β' = 0 ∧ W = K ∙ ct n μ' β') := by
  rw [invariant_le_Vh_iff]
  constructor
  · rintro (h | h | h | ⟨i, hi, h0, _⟩)
    exacts [Or.inl h, Or.inr (Or.inl h), Or.inr (Or.inr h), absurd h0 (hβ i hi)]
  · tauto

/-- For `n = 0`, `ρ = 0` makes `c̃` span `C`. -/
lemma span_ct_eq_Vh_of_zero {μ'' β'' : ℕ → K} (h0 : ρ 0 μ'' β'' = 0) :
    K ∙ ct 0 μ'' β'' = Vh 0 := by
  refine le_antisymm ((Submodule.span_singleton_le_iff_mem _ _).2 (ct_mem_Vh_iff.2 h0)) ?_
  intro x hx
  refine Submodule.mem_span_singleton.2 ⟨x 1, ?_⟩
  have hc0 := co_ct_zero (n := 0) (μ := μ'') (β := β'')
  have hc1 := co_ct_top (n := 0) (μ := μ'') (β := β'')
  change co 0 0 x = 0 at hx
  rw [co_zero_apply] at hx hc0
  rw [co_of_lt (by omega)] at hc1
  funext j
  fin_cases j
  · simp [hx, hc0, h0]
  · have h1 : ct 0 μ'' β'' 1 = 1 := hc1
    simp [h1]

/-- **Irreducibility on `C`** (pages 80–82): no subspace of `C` other than `0` and `C`
is stable under all `τᵢ` iff all `βᵢ ≠ 0` and, for `n ≥ 1`, `ρ ≠ 0`. -/
theorem irreducible_on_C_iff :
    (∀ W : Submodule K (Fin (n + 2) → K), W ≤ Vh n → Invariant n μ' β' W →
        W = ⊥ ∨ W = Vh n) ↔
      (∀ i < n, β' i ≠ 0) ∧ (n = 0 ∨ ρ n μ' β' ≠ 0) := by
  constructor
  · intro h
    refine ⟨fun i hi hβ => ?_, ?_⟩
    · have hm : (e n (i + 2) : Fin (n + 2) → K) ∈ Zs n i := fun k hk => co_e_ne (by omega)
      rcases h (Zs n i) (Zs_le_Vh i) (Zs_invariant hβ) with h1 | h1
      · rw [h1, Submodule.mem_bot] at hm
        simpa [hm] using co_e_self (R := K) (n := n) (i + 2) (by omega)
      · have h1' : (e n 1 : Fin (n + 2) → K) ∈ Zs n i := h1 ▸ e_mem_Vh one_ne_zero
        have h2 := co_e_self (R := K) (n := n) 1 (by omega)
        exact zero_ne_one (h1' 1 (by omega) ▸ h2)
    · by_contra hc
      push Not at hc
      obtain ⟨hn, hρ⟩ := hc
      rcases h (K ∙ ct n μ' β') ((Submodule.span_singleton_le_iff_mem _ _).2 (ct_mem_Vh_iff.2 hρ))
          ((invariant_iff _).2 (Or.inr (Or.inr (Or.inl rfl)))) with h1 | h1
      · rw [Submodule.span_singleton_eq_bot] at h1; exact ct_ne_zero h1
      · have hm : (e n 1 : Fin (n + 2) → K) ∈ K ∙ ct n μ' β' := h1 ▸ e_mem_Vh one_ne_zero
        obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.1 hm
        have h2 := congrArg (co n (n + 1)) ha
        rw [map_smul, co_ct_top, smul_eq_mul, mul_one, co_e_ne (by omega)] at h2
        rw [h2, zero_smul] at ha
        simpa [← ha] using co_e_self (R := K) (n := n) 1 (by omega)
  · rintro ⟨hβ, hρ⟩ W hW hinv
    rcases (invariant_le_Vh_iff_of_ne_zero hβ W).1 ⟨hinv, hW⟩ with h | h | ⟨h0, h⟩
    · exact Or.inl h
    · exact Or.inr h
    · rcases hρ with rfl | hρ
      · exact Or.inr (h.trans (span_ct_eq_Vh_of_zero h0))
      · exact (hρ h0).elim

end Irreducible


/-! ## The start vector (pages 102–105)

Finding `72-pinned-realisations-over-base`, the proposition of pages 102–105. Its
condition b) is the triangular half of (10) only, so it concerns the conditions (B̄′)
of the corollary of pages 97–98 (`CondB'`); (B̄) is (B̄′) plus the other half of (10),
which does not involve `s₀` (`condB_iff_condB'`).

* `condB'_iff_of_basis` (pages 104–105, over any ring): if `(v, a₀, …, aₙ)` is a basis,
  `φ` the coordinate on `v`, and b), c) hold, then `s₀` satisfies (B̄′) iff
  `⟨s₀, a'ᵢ⟩ = 0` for `1 ≤ i ≤ n` (`s₀ ∈ F`), `⟨s₀, a'₀⟩` is a unit (`s₀ ∉ D`) and
  `φ(s₀)` is a unit (`s₀ ∉ Δ`).
* `exists_condB'_iff` (pages 102–105, over a local ring): a start vector with (B̄′)
  exists iff a) `(a₀, …, aₙ)` extends to a basis by one vector, a′) `x ↦ (⟨x, a'ᵢ⟩)ᵢ`
  maps onto `kⁿ⁺¹`, b) `⟨aᵢ, a'ⱼ⟩ = 0` for `i + 2 ≤ j`, c) `⟨aᵢ, a'ᵢ₊₁⟩` units. The
  residue field may be `𝔽₂`: `s₀` is one of `t`, `s`, `s + t`.
-/

section StartVector

open Module

variable {k : Type*} [CommRing k] {M : Type*} [AddCommGroup M] [Module k M]
  {a : ℕ → M} {a' : ℕ → Module.Dual k M} {s0 : M} {n : ℕ}

/-- Conditions (B̄′) of the corollary of pages 97–98: (17), `(s₀, a₀, …, aₙ)` a basis,
(19). -/
def CondB' (n : ℕ) (a : ℕ → M) (a' : ℕ → Module.Dual k M) (s0 : M) : Prop :=
  (∀ i j, i + 2 ≤ j → j ≤ n → a' j (a i) = 0) ∧ (∀ i, 1 ≤ i → i ≤ n → a' i s0 = 0) ∧
    IsBasisFam k (fun j : Fin (n + 2) => av a s0 j) ∧ IsUnit (ν a a' s0 n)

theorem condB_iff_condB' :
    CondB n a a' s0 ↔ CondB' n a a' s0 ∧ ∀ i j, i + 2 ≤ j → j ≤ n → a' i (a j) = 0 := by
  simp only [CondB, CondB', forall_and]; tauto

lemma isUnit_ν_iff (n : ℕ) :
    IsUnit (ν a a' s0 n) ↔ IsUnit (a' 0 s0) ∧ ∀ i < n, IsUnit (a' (i + 1) (a i)) := by
  induction n with
  | zero => simp [ν]
  | succ n ih =>
    simp only [ν, IsUnit.mul_iff, ih, Nat.lt_succ_iff_lt_or_eq, or_imp, forall_and,
      forall_eq, and_assoc]

/-- A family lower triangular in a basis, with invertible diagonal, is a basis. -/
lemma isBasisFam_of_lowtri {m : ℕ} (b : Basis (Fin m) k M) (v : Fin m → M)
    (hup : ∀ i j : Fin m, i < j → b.repr (v j) i = 0) (hdiag : ∀ j, IsUnit (b.repr (v j) j)) :
    IsBasisFam k v :=
  b.is_basis_iff_det.2 <| by
    rw [b.det_apply, Matrix.det_of_isLowerTriangular (b.toMatrix v) hup]
    exact IsUnit.prod_univ_iff.2 hdiag

/-- **The start vectors** (pages 104–105): with `(v, a₀, …, aₙ)` a basis and `φ` the
coordinate on `v`, `s₀` satisfies (B̄′) iff it lies in `F`, off `D` and off `Δ`. -/
theorem condB'_iff_of_basis {v : M} (hv : IsBasisFam k (fun j : Fin (n + 2) => av a v j))
    (hb : ∀ i j, i + 2 ≤ j → j ≤ n → a' j (a i) = 0) (hc : ∀ i < n, IsUnit (a' (i + 1) (a i))) :
    CondB' n a a' s0 ↔ (∀ i, 1 ≤ i → i ≤ n → a' i s0 = 0) ∧ IsUnit (a' 0 s0) ∧
      IsUnit ((bas hv).coord 0 s0) := by
  have hφa : ∀ i (hi : i ≤ n), (bas hv).repr (a i) = Finsupp.single ⟨i + 1, by omega⟩ 1 :=
    fun i hi => bas_repr hv ⟨i + 1, by omega⟩
  constructor
  · rintro ⟨-, h11, hbas, hν⟩
    refine ⟨h11, ((isUnit_ν_iff n).1 hν).1, ?_⟩
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun k).1
      (hbas.2.ge (Submodule.mem_top (x := v)))
    have h := congrArg ((bas hv).coord 0) hc
    have hv0 : (bas hv).repr v = Finsupp.single 0 1 := bas_repr hv 0
    rw [map_sum, Fin.sum_univ_succ, Finset.sum_eq_zero fun i _ => by
      rw [map_smul, show av a s0 (i.succ : ℕ) = a i from rfl, Basis.coord_apply,
        hφa i (by omega), Finsupp.single_eq_of_ne' (Fin.ne_of_val_ne (by simp)), smul_zero]] at h
    rw [Basis.coord_apply, Basis.coord_apply, hv0, add_zero, map_smul, Finsupp.smul_apply,
      smul_eq_mul, Finsupp.single_eq_same, Fin.val_zero] at h
    exact .of_mul_eq_one_right _ h
  · rintro ⟨h11, h0, hφ⟩
    refine ⟨hb, h11, isBasisFam_of_lowtri (bas hv) _ (fun i j hij => ?_) (fun j => ?_),
      (isUnit_ν_iff n).2 ⟨h0, hc⟩⟩ <;> obtain ⟨_ | j, hj⟩ := j
    · simp at hij
    · rw [show av a s0 (j + 1) = a j from rfl, hφa j (by omega),
        Finsupp.single_eq_of_ne' hij.ne']
    · exact hφ
    · simp [show av a s0 (j + 1) = a j from rfl, hφa j (by omega)]

/-- Back-substitution (page 104): by b) and c), every `x` has the same image as some
`s ∈ F` under any form vanishing on `a₀, …, a_{n−1}`. -/
lemma exists_mem_F (hb : ∀ i j, i + 2 ≤ j → j ≤ n → a' j (a i) = 0)
    (hc : ∀ i < n, IsUnit (a' (i + 1) (a i))) (f : Module.Dual k M) (hf : ∀ i < n, f (a i) = 0)
    (x : M) : ∃ s, f s = f x ∧ ∀ i, 1 ≤ i → i ≤ n → a' i s = 0 := by
  suffices ∀ m ≤ n, ∃ s, f s = f x ∧ ∀ i, n - m < i → i ≤ n → a' i s = 0 by
    obtain ⟨s, h1, h2⟩ := this n le_rfl
    exact ⟨s, h1, fun i hi hin => h2 i (by omega) hin⟩
  intro m
  induction m with
  | zero => exact fun _ => ⟨x, rfl, fun i h1 h2 => by omega⟩
  | succ m ih =>
    intro hm
    obtain ⟨s, h1, h2⟩ := ih (by omega)
    obtain ⟨p, hp⟩ : ∃ p, n - m = p + 1 := ⟨n - m - 1, by omega⟩
    have hu := (hc p (by omega)).mul_val_inv
    refine ⟨s - (↑(hc p (by omega)).unit⁻¹ * a' (p + 1) s) • a p, ?_, fun i hi hin => ?_⟩
    · rw [map_sub, map_smul, hf p (by omega), smul_zero, sub_zero, h1]
    · rw [map_sub, map_smul, smul_eq_mul]
      rcases (show i = p + 1 ∨ n - m < i by omega) with rfl | hi'
      · linear_combination (-a' (p + 1) s) * hu
      · rw [h2 i hi' hin, hb p i (by omega) hin, mul_zero, sub_zero]

/-- **Local existence of the start vector** (pages 102–105): over a local ring, a start
vector satisfying (B̄′) exists iff a), a′), b), c) hold. -/
theorem exists_condB'_iff [IsLocalRing k] :
    (∃ s0, CondB' n a a' s0) ↔ (∃ v, IsBasisFam k (fun j : Fin (n + 2) => av a v j)) ∧
      Function.Surjective (fun x : M => fun i : Fin (n + 1) => a' i x) ∧
      (∀ i j, i + 2 ≤ j → j ≤ n → a' j (a i) = 0) ∧ ∀ i < n, IsUnit (a' (i + 1) (a i)) := by
  constructor
  · rintro ⟨s0, hb, h11, hbas, hν⟩
    obtain ⟨h0, hc⟩ := (isUnit_ν_iff n).1 hν
    refine ⟨⟨s0, hbas⟩, fun y => ?_, hb, hc⟩
    -- the matrix `(⟨av i, a'ⱼ⟩)` is upper triangular with diagonal `⟨s₀, a'₀⟩, c₀, …`
    set N : Matrix (Fin (n + 1)) (Fin (n + 1)) k := fun j i => a' j (av a s0 i)
    have hN : IsUnit N := by
      rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_of_isUpperTriangular fun j i (h : i < j) => by
        obtain ⟨_ | i, hi⟩ := i
        · exact h11 j (Fin.lt_def.1 h) (by omega)
        · exact hb i j (show i + 1 < (j : ℕ) from h) (by omega)]
      exact IsUnit.prod_univ_iff.2 fun ⟨j, hj⟩ => match j with
        | 0 => h0
        | j + 1 => hc j (by omega)
    obtain ⟨z, hz⟩ := Matrix.mulVec_surjective_iff_isUnit.2 hN y
    exact ⟨∑ i, z i • av a s0 i, funext fun j => by simp [← hz, Matrix.mulVec, dotProduct, N, mul_comm]⟩
  · rintro ⟨⟨v, hv⟩, ha', hb, hc⟩
    set φ := (bas hv).coord 0
    have hφ : ∀ i ≤ n, φ (a i) = 0 := fun i hi => by
      rw [Basis.coord_apply, show a i = av a v ((⟨i + 1, by omega⟩ : Fin (n + 2)) : ℕ) from rfl,
        bas_repr, Finsupp.single_eq_of_ne (by simp [Fin.ext_iff])]
    obtain ⟨s, hs1, hs⟩ := exists_mem_F hb hc φ (fun i hi => hφ i hi.le) v
    have hv0 : (bas hv).repr v = Finsupp.single 0 1 := bas_repr hv 0
    have hs1 : IsUnit (φ s) := by
      rw [hs1, Basis.coord_apply, hv0, Finsupp.single_eq_same]; exact isUnit_one
    obtain ⟨t, ht⟩ := ha' (Pi.single 0 1)
    have ht0 : a' 0 t = 1 := by simpa using congrFun ht 0
    have ht : ∀ i, 1 ≤ i → i ≤ n → a' i t = 0 := fun i h1 h2 => by
      simpa [Fin.ext_iff, show i ≠ 0 by omega, Nat.mod_eq_of_lt (show i < n + 1 by omega)]
        using congrFun ht ⟨i, by omega⟩
    have key : ∀ x y : k, IsUnit x → ¬IsUnit y → IsUnit (x + y) := fun x y hx hy =>
      (IsLocalRing.isUnit_or_isUnit_of_isUnit_add (b := -y) (by simpa using hx)).resolve_right
        (by simpa using hy)
    by_cases h1 : IsUnit (φ t)
    · exact ⟨t, (condB'_iff_of_basis hv hb hc).2 ⟨ht, by simp [ht0], h1⟩⟩
    by_cases h2 : IsUnit (a' 0 s)
    · exact ⟨s, (condB'_iff_of_basis hv hb hc).2 ⟨hs, h2, hs1⟩⟩
    refine ⟨s + t, (condB'_iff_of_basis hv hb hc).2
      ⟨fun i h h' => by simp [hs i h h', ht i h h'], ?_,
        by rw [map_add]; exact key _ _ hs1 h1⟩⟩
    rw [map_add, add_comm]; exact key _ _ (by simp [ht0]) h2

/-- With the other half of (10), the start vector of `exists_condB'_iff` satisfies (B̄),
hence (Ā). -/
theorem exists_condA_iff [IsLocalRing k] :
    (∃ s0, CondA n a a' s0) ↔ (∃ v, IsBasisFam k (fun j : Fin (n + 2) => av a v j)) ∧
      Function.Surjective (fun x : M => fun i : Fin (n + 1) => a' i x) ∧
      (∀ i j, i + 2 ≤ j → j ≤ n → a' j (a i) = 0 ∧ a' i (a j) = 0) ∧
      ∀ i < n, IsUnit (a' (i + 1) (a i)) := by
  simp only [condA_iff_condB, condB_iff_condB', exists_and_right, exists_condB'_iff, forall_and]
  tauto

/-- Over a local ring, on `M` free of rank `n + 2`, condition a) of the page —
`(a₀, …, aₙ)` strictly free, i.e. independent with a complementary submodule — gives the
vector `v` completing it to a basis. -/
theorem exists_completion [IsLocalRing k] [Module.Free k M] [Module.Finite k M]
    (hM : finrank k M = n + 2) (hli : LinearIndependent k (fun i : Fin (n + 1) => a i))
    {Q : Submodule k M}
    (hQ : IsCompl (Submodule.span k (Set.range fun i : Fin (n + 1) => a i)) Q) :
    ∃ v, IsBasisFam k (fun j : Fin (n + 2) => av a v j) := by
  set P := Submodule.span k (Set.range fun i : Fin (n + 1) => a i)
  have : Module.Finite k Q := Module.Finite.equiv (P.quotientEquivOfIsCompl Q hQ)
  have : Module.Projective k Q :=
    .of_split Q.subtype _ (Submodule.projectionOnto_comp_subtype hQ.symm)
  have : Module.Free k Q := Module.free_of_flat_of_isLocalRing
  have : Module.Free k P := .of_basis (Basis.span hli)
  have : Module.Finite k P := .of_basis (Basis.span hli)
  have hQ1 : finrank k Q = 1 := by
    have h := (P.prodEquivOfIsCompl Q hQ).finrank_eq
    rw [Module.finrank_prod, hM, finrank_span_eq_card hli, Fintype.card_fin] at h
    omega
  set bQ := Module.finBasisOfFinrankEq k Q hQ1
  have hsp : ⊤ ≤ Submodule.span k (Set.range fun j : Fin (n + 2) => av a (bQ 0 : M) j) := by
    rw [← hQ.sup_eq_top, sup_le_iff]
    refine ⟨Submodule.span_le.2 ?_, fun x hx => ?_⟩
    · rintro _ ⟨i, rfl⟩
      exact Submodule.subset_span ⟨i.succ, rfl⟩
    · have h := congrArg Subtype.val (bQ.sum_repr ⟨x, hx⟩)
      rw [Fin.sum_univ_one, Submodule.coe_smul] at h
      rw [show x = _ from h.symm]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩)
  exact ⟨bQ 0, linearIndependent_of_top_le_span_of_card_eq_finrank hsp (by simp [hM]),
    top_le_iff.1 hsp⟩

/-- On a reflexive `M` (for instance free of finite rank), condition a′) of the page —
`(a'₀, …, a'ₙ)` strictly free in `M^∨` — makes `x ↦ (⟨x, a'ᵢ⟩)ᵢ` surjective. -/
theorem surjective_of_strict [Module.IsReflexive k M]
    (hli : LinearIndependent k (fun i : Fin (n + 1) => a' i)) {Q : Submodule k (Module.Dual k M)}
    (hQ : IsCompl (Submodule.span k (Set.range fun i : Fin (n + 1) => a' i)) Q) :
    Function.Surjective (fun x : M => fun i : Fin (n + 1) => a' i x) := by
  set b := Basis.span hli
  set x : Fin (n + 1) → M := fun i =>
    (Module.evalEquiv k M).symm ((b.coord i).comp (Submodule.projectionOnto _ Q hQ))
  have hx : ∀ i j : Fin (n + 1), a' j (x i) = if j = i then 1 else 0 := fun i j => by
    rw [Module.apply_evalEquiv_symm_apply, LinearMap.comp_apply,
      show a' j = (b j : Module.Dual k M) by simp [b, Basis.span_apply],
      Submodule.projectionOnto_apply_left, Basis.coord_apply, Basis.repr_self,
      Finsupp.single_apply]
  exact fun y => ⟨∑ i, y i • x i, funext fun j => by simp [hx]⟩

/-- **Local existence of the start vector, with the page's « strictement libre »**: over a
local ring, on `M` free of rank `n + 2`, under a) and a′) in the strict sense, b) and c),
there is a start vector satisfying (B̄′). -/
theorem exists_condB'_of_strict [IsLocalRing k] [Module.Free k M] [Module.Finite k M]
    (hM : finrank k M = n + 2) (ha : LinearIndependent k (fun i : Fin (n + 1) => a i))
    {Q : Submodule k M} (hQ : IsCompl (Submodule.span k (Set.range fun i : Fin (n + 1) => a i)) Q)
    (ha' : LinearIndependent k (fun i : Fin (n + 1) => a' i)) {Q' : Submodule k (Dual k M)}
    (hQ' : IsCompl (Submodule.span k (Set.range fun i : Fin (n + 1) => a' i)) Q')
    (hb : ∀ i j, i + 2 ≤ j → j ≤ n → a' j (a i) = 0) (hc : ∀ i < n, IsUnit (a' (i + 1) (a i))) :
    ∃ s0, CondB' n a a' s0 :=
  exists_condB'_iff.2 ⟨exists_completion hM ha hQ, surjective_of_strict ha' hQ', hb, hc⟩

end StartVector

/-! ## The theorem in the « libre » (direct summand) sense (pages 96–100, 103)

Finding `72-pinned-realisations-over-base`. For `E` an arbitrary module (locally free and
not free, for instance), « libre » read as on page 103: a family is strictly free if it
is independent and its span has a complementary submodule (`IsStrictFam`).

* `condAs_iff_condBs`: (A) ⇔ (B) with (9) and (12) in this sense, over any commutative
  ring and any module. The proof restricts everything to the span of the family, where
  it is the theorem with bases (`condA_iff_condB`); under (A), `⟨sᵢ, a'ᵢ⟩` is a unit, read
  off a coordinate of the projection along the complement, so `aᵢ` lies in the span.
* `not_condAw_imp`: in the weak sense (independence only), (A) does not imply (13):
  `k = ℤ`, `n = 0`, `s₀ = e₀`, `a₀ = e₁`, `a'₀ = 2e₀*`.
* `free_of_condA`: (Ā) forces `E` free, so on a locally free non-free `E` there is no
  global start vector; the existence of pages 102–105 is local (`exists_condB'_iff`).
-/

section Strict

open Module

variable {k : Type*} [CommRing k] {M : Type*} [AddCommGroup M] [Module k M]
  {a : ℕ → M} {a' : ℕ → Module.Dual k M} {s0 : M} {n : ℕ}

variable (k) in
/-- A family is strictly free: independent, with a span that is a direct summand. -/
def IsStrictFam {m : ℕ} (f : Fin m → M) : Prop :=
  LinearIndependent k f ∧ ∃ Q : Submodule k M, IsCompl (Submodule.span k (Set.range f)) Q

/-- Conditions (A): (7), (8), (9) with « libre » in the strict sense. -/
def CondAs (n : ℕ) (a : ℕ → M) (a' : ℕ → Module.Dual k M) (s0 : M) : Prop :=
  (∀ i j, i + 2 ≤ j → j ≤ n → ps a a' i * ps a a' j = ps a a' j * ps a a' i) ∧
    (∀ i, 1 ≤ i → i ≤ n → ps a a' i s0 = s0) ∧
    IsStrictFam k (fun j : Fin (n + 2) => sv a a' s0 j)

/-- Conditions (B): (10), (11), (12) with « libre » in the strict sense, (13). -/
def CondBs (n : ℕ) (a : ℕ → M) (a' : ℕ → Module.Dual k M) (s0 : M) : Prop :=
  (∀ i j, i + 2 ≤ j → j ≤ n → a' j (a i) = 0 ∧ a' i (a j) = 0) ∧
    (∀ i, 1 ≤ i → i ≤ n → a' i s0 = 0) ∧
    IsStrictFam k (fun j : Fin (n + 2) => av a s0 j) ∧ IsUnit (ν a a' s0 n)

/-- `aᵢ` seen in a submodule containing it (`0` otherwise). -/
noncomputable def resA (N : Submodule k M) (a : ℕ → M) (i : ℕ) : N := by
  classical exact if h : a i ∈ N then ⟨a i, h⟩ else 0

/-- `a'ᵢ` restricted to a submodule. -/
def resA' (N : Submodule k M) (a' : ℕ → Module.Dual k M) (i : ℕ) : Module.Dual k N :=
  (a' i).domRestrict N

variable {N : Submodule k M}

lemma coe_resA {i : ℕ} (h : a i ∈ N) : (resA N a i : M) = a i := by simp [resA, h]

lemma coe_ps_res (hN : ∀ i ≤ n, a i ∈ N) {i : ℕ} (hi : i ≤ n) (x : N) :
    (ps (resA N a) (resA' N a') i x : M) = ps a a' i x := by
  simp [ps_apply, resA', coe_resA (hN i hi)]

lemma coe_sv_res (hN : ∀ i ≤ n, a i ∈ N) (hs : s0 ∈ N) :
    ∀ j ≤ n + 1, ((sv (resA N a) (resA' N a') ⟨s0, hs⟩ j : N) : M) = sv a a' s0 j := by
  intro j hj
  induction j with
  | zero => rfl
  | succ j ih => rw [sv, coe_ps_res hN (by omega), ih (by omega), sv]

lemma ν_res (hN : ∀ i ≤ n, a i ∈ N) (hs : s0 ∈ N) :
    ∀ j ≤ n, ν (resA N a) (resA' N a') ⟨s0, hs⟩ j = ν a a' s0 j := by
  intro j hj
  induction j with
  | zero => rfl
  | succ j ih => simp [ν, ih (by omega), resA', coe_resA (hN j (by omega))]

lemma coe_av_res (hN : ∀ i ≤ n, a i ∈ N) (hs : s0 ∈ N) (j : Fin (n + 2)) :
    ((av (resA N a) ⟨s0, hs⟩ j : N) : M) = av a s0 j := by
  obtain ⟨_ | j, hj⟩ := j
  · rfl
  · exact coe_resA (hN j (by omega))

/-- A family of `N` is a basis of `N` iff, in `M`, it is independent and spans `N`. -/
lemma isBasisFam_res {m : ℕ} {f : Fin m → M} {g : Fin m → N} (hg : ∀ j, (g j : M) = f j) :
    IsBasisFam k g ↔ LinearIndependent k f ∧ Submodule.span k (Set.range f) = N := by
  have hf : f = N.subtype ∘ g := funext fun j => (hg j).symm
  subst hf
  refine and_congr (LinearMap.linearIndependent_iff _ N.ker_subtype).symm ?_
  rw [Set.range_comp, Submodule.span_image]
  exact ⟨fun h => by rw [h, Submodule.map_subtype_top], fun h =>
    Submodule.map_injective_of_injective N.injective_subtype (h.trans N.map_subtype_top.symm)⟩

/-- (A) ⇔ (B) in the strict sense, for any module. -/
theorem condAs_iff_condBs : CondAs n a a' s0 ↔ CondBs n a a' s0 := by
  constructor
  · rintro ⟨h7, h8, hli, Q, hQ⟩
    set N := Submodule.span k (Set.range fun j : Fin (n + 2) => sv a a' s0 j)
    have hsN : ∀ j ≤ n + 1, sv a a' s0 j ∈ N := fun j hj =>
      Submodule.subset_span ⟨⟨j, by omega⟩, rfl⟩
    -- `⟨sᵢ, a'ᵢ⟩ aᵢ = s_{i+1} − sᵢ`, and the coordinate on `s_{i+1}` is `1`
    have hN : ∀ i ≤ n, a i ∈ N := by
      intro i hi
      set g := ((Basis.span hli).coord ⟨i + 1, by omega⟩).comp (N.projectionOnto Q hQ)
      have hg : ∀ j : Fin (n + 2), g (sv a a' s0 j) = if (j : ℕ) = i + 1 then 1 else 0 := by
        intro j
        rw [LinearMap.comp_apply, show sv a a' s0 j = ((Basis.span hli j : N) : M) by
          simp [Basis.span_apply], Submodule.projectionOnto_apply_left, Basis.coord_apply,
          Basis.repr_self, single_apply_fin, eq_comm]
      have h := congrArg g (sv_succ (a := a) (a' := a') (s0 := s0) i)
      rw [map_add, map_smul, hg ⟨i + 1, by omega⟩, show sv a a' s0 i = sv a a' s0
        ((⟨i, by omega⟩ : Fin (n + 2)) : ℕ) from rfl, hg ⟨i, by omega⟩] at h
      simp only [ite_true, show i ≠ i + 1 by omega, ite_false, zero_add, smul_eq_mul] at h
      have hu := IsUnit.of_mul_eq_one _ h.symm
      have := N.sub_mem (hsN (i + 1) (by omega)) (hsN i (by omega))
      rwa [sv_succ, add_sub_cancel_left, Submodule.smul_mem_iff_of_isUnit _ hu] at this
    have hs : s0 ∈ N := hsN 0 (by omega)
    obtain ⟨h10, h11, hbas, hν⟩ := condB_of_condA (n := n) (a := resA N a) (a' := resA' N a')
      (s0 := ⟨s0, hs⟩) ⟨fun i j hij hj => LinearMap.ext fun x => Subtype.ext (by
        simpa only [Module.End.mul_apply, coe_ps_res hN (show i ≤ n by omega), coe_ps_res hN hj]
          using congrArg (· (x : M)) (h7 i j hij hj)),
        fun i h1 h2 => Subtype.ext (by rw [coe_ps_res hN h2]; exact h8 i h1 h2),
        (isBasisFam_res fun j => coe_sv_res hN hs j (by omega)).2 ⟨hli, rfl⟩⟩
    obtain ⟨hli', hspan⟩ := (isBasisFam_res (coe_av_res hN hs)).1 hbas
    refine ⟨fun i j hij hj => ?_, fun i h1 h2 => ?_, ⟨hli', Q, hspan ▸ hQ⟩,
      ν_res hN hs n le_rfl ▸ hν⟩
    · simpa [resA', coe_resA (hN i (by omega)), coe_resA (hN j hj)] using h10 i j hij hj
    · simpa [resA'] using h11 i h1 h2
  · rintro ⟨h10, h11, ⟨hli, Q, hQ⟩, hν⟩
    set N := Submodule.span k (Set.range fun j : Fin (n + 2) => av a s0 j)
    have hN : ∀ i ≤ n, a i ∈ N := fun i hi => Submodule.subset_span ⟨⟨i + 1, by omega⟩, rfl⟩
    have hs : s0 ∈ N := Submodule.subset_span ⟨⟨0, by omega⟩, rfl⟩
    obtain ⟨-, -, hbas⟩ := condA_of_condB (n := n) (a := resA N a) (a' := resA' N a')
      (s0 := ⟨s0, hs⟩) ⟨fun i j hij hj => by
        simpa [resA', coe_resA (hN i (by omega)), coe_resA (hN j hj)] using h10 i j hij hj,
        fun i h1 h2 => by simpa [resA'] using h11 i h1 h2,
        (isBasisFam_res (coe_av_res hN hs)).2 ⟨hli, rfl⟩, (ν_res hN hs n le_rfl).symm ▸ hν⟩
    obtain ⟨hli', hspan⟩ := (isBasisFam_res fun j => coe_sv_res hN hs j (by omega)).1 hbas
    refine ⟨fun i j hij hj => LinearMap.ext fun x => ?_, fun i h1 h2 => by
      rw [ps_apply, h11 i h1 h2, zero_smul, add_zero], hli', Q, hspan ▸ hQ⟩
    simp only [Module.End.mul_apply, ps_apply, map_add, map_smul, (h10 i j hij hj).1,
      (h10 i j hij hj).2, zero_smul, add_zero]
    abel

/-- In the weak sense (independence only), (A) does not give (13): over `ℤ`, `n = 0`,
`s₀ = e₀`, `a₀ = e₁`, `a'₀ = 2e₀*`, `(s₀, s₁) = (e₀, e₀ + 2e₁)` is independent and
`ν₀ = 2`. -/
theorem not_condAw_imp : ∃ (a : ℕ → Fin 2 → ℤ) (a' : ℕ → Module.Dual ℤ (Fin 2 → ℤ)) (s0 : _),
    LinearIndependent ℤ (fun j : Fin 2 => sv a a' s0 j) ∧ ¬IsUnit (ν a a' s0 0) := by
  refine ⟨fun _ => Pi.single 1 1, fun _ => 2 • LinearMap.proj 0, Pi.single 0 1, ?_, ?_⟩
  · rw [Fintype.linearIndependent_iff]
    intro g hg
    simp [Fin.sum_univ_two, sv, ps_apply, funext_iff, Fin.forall_fin_two] at hg
    exact Fin.forall_fin_two.2 ⟨by omega, hg.2⟩
  · simp [ν, Int.isUnit_iff]

/-- (Ā) forces `E` to be free. -/
theorem free_of_condA (h : CondA n a a' s0) : Module.Free k M := .of_basis (bas h.2.2)

end Strict
end Grothendieck.Folder72
