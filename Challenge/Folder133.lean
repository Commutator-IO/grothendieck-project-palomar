module

public import Mathlib

@[expose] public section

namespace Grothendieck.Folder133

open Subgroup

open scoped commutatorElement

variable {G : Type*} [Group G] (N N' : Subgroup G) [N.Normal] [N'.Normal]

/-- The inverse image in `G` of `ℨ = [Cent(K)/(N′/π₁)] ∩ Ker Θ`, `K = G/π₁`,
`π₁ = N ∩ N′` (page 46): the elements central modulo `π₁` that centralise `N`. -/
def zbar : Subgroup G :=
  (center (G ⧸ (N ⊓ N'))).comap (QuotientGroup.mk' (N ⊓ N')) ⊓ centralizer (N : Set G)

/-- `ℨ = zbar ⧸ N′` (page 46). -/
abbrev Zfrak := zbar N N' ⧸ N'.subgroupOf (zbar N N')

variable {N N'}

theorem mem_zbar {z : G} :
    z ∈ zbar N N' ↔ (∀ g : G, ⁅g, z⁆ ∈ N ⊓ N') ∧ ∀ n ∈ N, n * z = z * n := by
  rw [zbar, mem_inf, mem_comap, mem_centralizer_iff]
  refine and_congr ⟨fun h g => ?_, fun h => mem_center_iff.mpr fun x => ?_⟩ Iff.rfl
  · exact (QuotientGroup.eq_one_iff _).mp <| (map_commutatorElement (QuotientGroup.mk' _) g z).trans
      (commutatorElement_eq_one_iff_mul_comm.mpr (mem_center_iff.mp h _))
  · obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
    exact commutatorElement_eq_one_iff_mul_comm.mp <|
      (map_commutatorElement (QuotientGroup.mk' _) g z).symm.trans
        ((QuotientGroup.eq_one_iff _).mpr (h g))

/-- A central element commutes with everything, written in the order used below. -/
theorem central_comm {H : Type*} [Group H] {c : H} (hc : c ∈ center H) (x : H) :
    c * x = x * c :=
  (mem_center_iff.mp hc x).symm

/-- Multiplying the second argument of a commutator by a central element does not change it. -/
theorem comm_mul_central {H : Type*} [Group H] {c : H} (hc : c ∈ center H) (g z : H) :
    ⁅g, z * c⁆ = ⁅g, z⁆ := by
  simp only [commutatorElement_def]
  calc g * (z * c) * g⁻¹ * (z * c)⁻¹ = g * z * (c * g⁻¹) * c⁻¹ * z⁻¹ := by group
    _ = g * z * (g⁻¹ * c) * c⁻¹ * z⁻¹ := by rw [central_comm hc]
    _ = g * z * g⁻¹ * z⁻¹ := by group

section Centre

variable (hN' : N' ≤ center G)

include hN'

theorem comm_mem_center {z : G} (hz : z ∈ zbar N N') (g : G) : ⁅g, z⁆ ∈ center G :=
  hN' (mem_inf.mp ((mem_zbar.mp hz).1 g)).2

theorem comm_mul_left {z : G} (hz : z ∈ zbar N N') (g h : G) :
    ⁅g * h, z⁆ = ⁅g, z⁆ * ⁅h, z⁆ := by
  have hc := comm_mem_center hN' hz h
  calc ⁅g * h, z⁆ = g * (⁅h, z⁆ * (z * g⁻¹ * z⁻¹)) := by
        simp only [commutatorElement_def]; group
    _ = ⁅h, z⁆ * (g * z * g⁻¹ * z⁻¹) := by
        rw [← mul_assoc, ← central_comm hc g]; group
    _ = ⁅h, z⁆ * ⁅g, z⁆ := by rw [commutatorElement_def g z]
    _ = ⁅g, z⁆ * ⁅h, z⁆ := central_comm hc _

/-- For `z ∈ zbar`, `g ↦ ⁅g, z⁆` as a homomorphism `G →* π₁`. -/
def commHom (z : zbar N N') : G →* ↥(N ⊓ N') where
  toFun g := ⟨⁅g, z⁆, (mem_zbar.mp z.2).1 g⟩
  map_one' := by ext; simp
  map_mul' g h := by ext; exact comm_mul_left hN' z.2 g h

theorem le_ker_commHom (z : zbar N N') : N ⊔ N' ≤ (commHom hN' z).ker := by
  refine sup_le (fun n hn => ?_) (fun n hn => ?_) <;> rw [MonoidHom.mem_ker] <;>
    apply Subtype.ext <;> show ⁅n, (z : G)⁆ = 1 <;> rw [commutatorElement_eq_one_iff_mul_comm]
  · exact (mem_zbar.mp z.2).2 n hn
  · exact (mem_center_iff.mp (hN' hn) z).symm

/-- `φ_G(z) : π₀ → π₁`, `π₀ = G/NN′`: the commutator with `z`, on `π₀`. -/
def phi (z : zbar N N') : G ⧸ (N ⊔ N') →* ↥(N ⊓ N') :=
  QuotientGroup.lift _ (commHom hN' z) (le_ker_commHom hN' z)

theorem phi_eq_of_rel {z w : zbar N N'} (h : z⁻¹ * w ∈ N'.subgroupOf (zbar N N')) :
    phi hN' z = phi hN' w := by
  refine QuotientGroup.monoidHom_ext _ (MonoidHom.ext fun g => Subtype.ext ?_)
  show ⁅g, (z : G)⁆ = ⁅g, (w : G)⁆
  have hc : (z : G)⁻¹ * w ∈ center G := hN' (by simpa [mem_subgroupOf] using h)
  rw [show (w : G) = z * ((z : G)⁻¹ * w) by group, comm_mul_central hc]

/-- `Ψ_G : ℨ → Hom(π₀, π₁)` (page 46). -/
def Psi : Zfrak N N' → (G ⧸ (N ⊔ N') →* ↥(N ⊓ N')) :=
  fun a => Quotient.liftOn' a (phi hN') fun _ _ h =>
    phi_eq_of_rel hN' (QuotientGroup.leftRel_apply.mp h)

/-- **Page 46.** `N′ = Cent(G)` if and only if `Ψ_G` is injective. -/
theorem injective_Psi_iff : Function.Injective (Psi (N := N) hN') ↔ N' = center G := by
  sorry

end Centre

end Grothendieck.Folder133
