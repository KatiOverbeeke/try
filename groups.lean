import Mathlib.Algebra.Group.Defs
import Mathlib.Tactic
import Mathlib.Order.BoundedOrder
import Mathlib.SetTheory.Cardinal.Finite


example {G : Type*} [Group G] (x : G) : x * x⁻¹ = 1 := mul_inv_cancel x

example {G : Type*} [Group G] (x y z : G) : x * (y * z) * (x * z)⁻¹ * (x * y * x⁻¹)⁻¹ = 1 := by
  group

variables (a b : G)

set_option diagnostics true



def conjugate {G : Type*} [Group G] (x : G) (H : Subgroup G) : Subgroup G where
  carrier := {a : G | ∃ h, h ∈ H ∧ a = x * h * x⁻¹}
  one_mem' := by
    dsimp
    use 1
    simp; exact Subgroup.one_mem H
  inv_mem' := by
    dsimp
    intro h; intro h1
    ring_nf
    cases h1  with
    | intro w h2 => use w⁻¹; ring_nf; constructor; apply Subgroup.inv_mem; exact h2.left; rw[h2.right]; group

  mul_mem' := by
    dsimp
    intro a; intro b; intro h; intro h1
    cases h  with
    | intro w h => cases h1 with
      | intro w1 h1 => use (w * w1); constructor; apply Subgroup.mul_mem; exact h.left; exact h1.left; rw[h.right, h1.right]; group

section exercises
variable {G H : Type*} [Group G] [Group H]

open Subgroup

example (φ : G →* H) (S T : Subgroup H) (hST : S ≤ T) : comap φ S ≤ comap φ T := by
  intro x
  intro h
  exact hST h

example (φ : G →* H) (S T : Subgroup G) (hST : S ≤ T) : map φ S ≤ map φ T := by
  intro x
  intro h
  rw[Subgroup.mem_map] at h
  rw[Subgroup.mem_map]
  cases h  with
    | intro w h => use w; constructor; apply hST;exact h.left; exact h.right

variable {K : Type*} [Group K]

-- Remember you can use the `ext` tactic to prove an equality of subgroups.
example (φ : G →* H) (ψ : H →* K) (U : Subgroup K) :
    comap (ψ.comp φ) U = comap φ (comap ψ U) := by
    ext
    constructor
    intro h
    exact h
    intro h
    exact h



-- Pushing a subgroup along one homomorphism and then another is equal to
-- pushing it forward along the composite of the homomorphisms.
example (φ : G →* H) (ψ : H →* K) (S : Subgroup G) :
    map (ψ.comp φ) S = map ψ (S.map φ) := by
    ext
    constructor
    intro h
    sorry
    intro h
    sorry

end exercises

variable {G : Type*} [Group G]

lemma conjugate_one (H : Subgroup G) : conjugate 1 H = H := by
  ext
  constructor
  intro h
  sorry
  intro h


  sorry

instance : MulAction G (Subgroup G) where
  smul := conjugate
  one_smul := by
    intro b
    rw[]

    apply?
    rw[]

    constructor
    intro h

    exact?

    sorry
  mul_smul := by
    sorry


section
variable {G : Type*} [Group G] {H K : Subgroup G}

open MonoidHom

#check Nat.card_pos -- The nonempty argument will be automatically inferred for subgroups
#check Subgroup.index_eq_card
#check Subgroup.index_mul_card
#check Nat.eq_of_mul_eq_mul_right

lemma aux_card_eq [Finite G] (h' : Nat.card G = Nat.card H * Nat.card K) :
    Nat.card (G ⧸ H) = Nat.card K := by
    rw[]
    rw[<- Subgroup.index_eq_card]
    rw[]
    apply?
    rw[Subgroup.index_]
