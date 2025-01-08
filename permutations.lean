import Init.Prelude
import Init.Data.List.Basic
import Mathlib.Tactic
--import Init.Data.List.Defs
import Mathlib.Data.Finset.Range
import Mathlib.Data.Finset.Defs


set_option diagnostics true

#eval [1, 2, 3].permutations

variable (p1 : List ℕ)


def fac : ℕ → ℕ
  | 0 => 1
  | n + 1 => (n + 1) * fac n

variable (n : ℕ)

def bool_to_int (b : Bool) : ℕ :=
if b then 1 else 0

variable (i : Finset ℕ)

--def H := (Finset n \ {i, i+1})

def neighbour_swap1 (n: ℕ) (p1: (List (Finset ℕ))) (p2: List (Finset ℕ) ) : Prop :=
  --∃ i: Finset (length.p1),  (p1[i] = p2[i+1])
  sorry

def neighbour_swap (n: ℕ) (p1: (List (Finset ℕ))) (p2: List (Finset ℕ) ) (i: Finset ℕ): Bool :=
    ∀ j:
    |(j= i ∧ p1[j] ≠ p2[j+1]) false


--if (p1[i]=p2[i+1]) ∧ (p1[i+1] = p2[i]) ∧ ∀ j : (Finset n \ {i, i+1}) p1[j]=p2[j] then true else false




--theorem perm: ∃ L: Finset -> List.permutations, L.Bijective ∧ ∀ (i: Finset n), ∃ i : Finset
