import Mathlib.GroupTheory.Perm.Cycle.Concrete
import Mathlib.Control.Random
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Tactic
import Init.System.IO



structure Point where
  x : Float
  y : Float
deriving Repr

def origin : Point := { x := 0.0, y := 0.0 }

#eval origin

def addPoints (p1 : Point) (p2 : Point) : Point :=
  { x := p1.x + p2.x, y := p1.y + p2.y }

def distance (p1 : Point) (p2 : Point) : Float :=
  Float.sqrt (((p2.x - p1.x) ^ 2.0) + ((p2.y - p1.y) ^ 2.0))

#eval distance { x := 1.0, y := 2.0 } { x := 5.0, y := -1.0 }

#check 5


def α : Equiv.Perm Int := (1)

#check α

structure Cards where
  b : Bool


def col : Bool → ℕ
  | false => 0
  | true => 1

def d := [false, true, true]

#eval col d[0]

def e := [col d[0], col d[1], col d[2]]

#eval e

def g := [0,0,1,1,1,0,1,1,1]

#eval g[3]

def h: String := "0010010101"

#eval List.splitAt 2 g

def split_g := List.splitAt 5 g

#eval split_g.1

#eval List.sum g

#eval List.sum split_g.1

#eval List.sum split_g.2

#eval List.length g

#eval List.length split_g.1

#eval List.length split_g.2

#eval (List.sum split_g.1) = (List.length split_g.2- List.sum split_g.2)

def cb := (List.sum (List.splitAt 5 g).1) = (List.length (List.splitAt 5 g).2- List.sum (List.splitAt 5 g).2)

#eval (List.sum (List.splitAt 5 g).1) = (List.length (List.splitAt 5 g).2- List.sum (List.splitAt 5 g).2)

def color: ℕ -> Bool :=
 fun n => (List.sum (List.splitAt n g).1) = (List.length (List.splitAt n g).2- List.sum (List.splitAt n g).2)

#eval color 3

universe u
variable {α : Type*} [CommRing α]

def SumOfSquares (x : α) :=
  ∃ a b, x = a ^ 2 + b ^ 2

theorem sumOfSquares_mul {x y : α} (sosx : SumOfSquares x) (sosy : SumOfSquares y) :
    SumOfSquares (x * y) := by
  rcases sosx with ⟨a, b, xeq⟩
  rcases sosy with ⟨c, d, yeq⟩
  rw [xeq, yeq]
  use a * c - b * d, a * d + b * c
  ring

variable {a: α}
variable {b: α}
variable {c: α}



example (divab : a ∣ b) (divbc : b ∣ c) : a ∣ c := by
  rcases divab with ⟨d, beq⟩
  rcases divbc with ⟨e, ceq⟩
  rw [ceq, beq]
  use d * e; ring

example (divab : a ∣ b) (divac : a ∣ c) : a ∣ b + c := by
  rcases divab with ⟨d, beq⟩
  rcases divac with ⟨e, ceq⟩
  rw[beq,ceq]
  use d + e; ring



example (x y : ℝ) (h : x - y ≠ 0) : (x ^ 2 - y ^ 2) / (x - y) = x + y := by
  field_simp [h]
  ring

example {f : ℝ → ℝ} (h : Function.Surjective f) : ∃ x, f x ^ 2 = 4 := by
  rcases h 2 with ⟨x, hx⟩
  use x
  rw [hx]
  norm_num

  variable {α : Type*} {β : Type*} {γ : Type*}
variable {g : β → γ} {f : α → β}

example (surjg : Function.Surjective g) (surjf : Function.Surjective f) : Function.Surjective fun x ↦ g (f x) := by
  intro h
  rcases surjg h with ⟨y, hy⟩
  rcases surjf y with ⟨z, hz⟩
  use z; simp; rw[ hz, hy]

variable {α β : Type*}
variable (f : α → β)
variable (s t : Set α)
variable (u v : Set β)

open Function
open Set

example : f '' s ⊆ v ↔ s ⊆ f ⁻¹' v := by
  constructor
  intro h
  exact image_subset_iff.mp h
  intro h
  exact image_subset_iff.mpr h

example (h : Injective f) : f ⁻¹' (f '' s) ⊆ s := by
  intro x
  intro h1
  exact (Injective.mem_set_image h).mp h1

example : f '' (f ⁻¹' u) ⊆ u := by
  intro x
  intro h
  simp at h
  cases h  with
    | intro w h => rw[<-h.right]; exact h.left


example (h : Surjective f) : u ⊆ f '' (f ⁻¹' u) := by
  intro x
  intro h

  sorry

example (h : s ⊆ t) : f '' s ⊆ f '' t := by
  intro x
  intro h
  sorry

example (h : u ⊆ v) : f ⁻¹' u ⊆ f ⁻¹' v := by
  intro x
  intro h1
  apply h at h1
  exact h1

example : f ⁻¹' (u ∪ v) = f ⁻¹' u ∪ f ⁻¹' v := by
  ext
  constructor
  intro h
  exact h
  intro h
  exact h


example : f '' (s ∩ t) ⊆ f '' s ∩ f '' t := by
  intro x
  intro h
  rcases h with ⟨a, ⟨ha_s, ha_t⟩, rfl⟩
  constructor
  exact mem_image_of_mem f ha_s
  exact mem_image_of_mem f ha_t


example (h : Injective f) : f '' s ∩ f '' t ⊆ f '' (s ∩ t) := by
  intro x h1
  -- By definition of intersection, `x ∈ f '' s` and `x ∈ f '' t`
  rcases h1 with ⟨⟨a1, ha1_s, rfl⟩, ⟨a2, ha2_t, rfl⟩⟩
  -- Use injectivity of `f` to deduce `a1 = a2`
  have : a1 = a2 := h rfl
  rw [this] at ha1_s
  -- Now `a1 ∈ s ∩ t` since `a1 ∈ s` and `a1 ∈ t`
  use a1
  exact ⟨ha1_s, ha2_t⟩
  sorry

set_option trace.split.failure true

example : f '' s \ f '' t ⊆ f '' (s \ t) := by
  intro x
  intro h
  rcases h with ⟨⟨a, ha_s, rfl⟩, h_not_t⟩
  use a
  split
  · exact ha_s
  · intro ha_t
     exact h_not_t ⟨a, ha_t, rfl⟩
  apply?

  sorry

example : f ⁻¹' u \ f ⁻¹' v ⊆ f ⁻¹' (u \ v) := by
  intro x
  intro h
  exact h


example : f '' s ∩ v = f '' (s ∩ f ⁻¹' v) := by
  ext
  constructor
  intro h

  apply?
  sorry

example : f '' (s ∩ f ⁻¹' u) ⊆ f '' s ∩ u := by
  intro x
  intro h
  apply?
  sorry

example : s ∩ f ⁻¹' u ⊆ f ⁻¹' (f '' s ∩ u) := by
  intro x
  intro h

  sorry

example : s ∪ f ⁻¹' u ⊆ f ⁻¹' (f '' s ∪ u) := by
  intro x
  intro h
  right

  sorry

def f1 (x : ℝ) :=
  x

theorem f1_bijective: f1.Bijective := by
  rw[Function.Bijective]
  constructor
  rw[Function.Injective]
  intro a b
  intro h
  rw[f1] at h; rw[f1] at h
  exact h
  rw[Function.Surjective]
  intro b
  use b
  rw[f1]
