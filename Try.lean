-- This module serves as the root of the `Try` library.
-- Import modules here that should be built as part of the library.
import Try.Basic

/- Define some constants. -/

def m : Nat := 1       -- m is a natural number
def n : Nat := 0
def b1 : Bool := true  -- b1 is a Boolean
def b2 : Bool := false

/- Check their types. -/

#check m            -- output: Nat
#check n
#check n + 0        -- Nat
#check m * (n + 0)  -- Nat
#check b1           -- Bool
#check b1 && b2     -- "&&" is the Boolean and
#check b1 || b2     -- Boolean or
#check true         -- Boolean "true"

/- Evaluate -/

#eval 5 * 4         -- 20
#eval m + 2         -- 3
#eval b1 && b2      -- false

/- Own examples-/

def k: Nat := 3

#check k -- Nat
#check k-1 -- Nat
#check k*(m+1)*(n+3) -- Nat
#check b1 -> b2 -- Prop

#eval k * (m+1) -- 6
#eval k-1 -- 2
#eval b1 -> b2 -- false
#eval b1 -> (b1 || b2) -- true

#eval Nat.succ 5
#eval Nat.pred 8
#eval Nat.add 5 8
#eval Nat.mul 3 9

#eval (8,6).1
#eval (8,6).2


#check fun (x : Nat) => x + 5   -- Nat → Nat
#check λ (x : Nat) => x + 5     -- λ and fun mean the same thing
#check fun x => x + 5     -- Nat inferred
#check λ x => x + 5       -- Nat inferred

/- own examples-/
#check fun (x: Nat) => x*x +5*x + 2
#check λ (x: Nat) => x*x +5*x + 2
#check fun x => x*x +5*x + 2
#check λ x => x*x +5*x + 2

#eval (λ x : Nat => x*x +5*x + 2) 3    -- 26

def f (n : Nat) : String := toString n
def g (s : String) : Bool := s.length > 0

#check fun x : Nat => x        -- Nat → Nat
#check fun x : Nat => true     -- Nat → Bool
#check fun x : Nat => g (f x)  -- Nat → Bool
#check fun x => g (f x)        -- Nat → Bool

#check fun (g : String → Bool) (f : Nat → String) (x : Nat) => g (f x)
-- (String → Bool) → (Nat → String) → Nat → Bool

#check let y := 2 + 2; y * y   -- Nat
#eval  let y := 2 + 2; y * y   -- 16

def twice_double (x : Nat) : Nat :=
  let y := x + x; y * y

#eval twice_double 2   -- 16

variable (α β γ : Type)
variable (g : β → γ) (f : α → β) (h : α → α)
variable (x : α)

def compose := g (f x)
def doTwice := h (h x)
def doThrice := h (h (h x))

#print compose
#print doTwice
#print doThrice


/-own examples-/
variable (p q : Bool)
def prop1 := (p || q) -> (p  && q)

#print prop1
