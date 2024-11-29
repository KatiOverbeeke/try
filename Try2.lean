import Try.Basic

def Implies (p q : Prop) : Prop := p → q
#check And     -- Prop → Prop → Prop
#check Or      -- Prop → Prop → Prop
#check Not     -- Prop → Prop
#check Implies -- Prop → Prop → Prop

variable (p q r : Prop)
#check And p q                      -- Prop
#check Or (And p q) r               -- Prop
#check Implies (And p q) (And q p)  -- Prop


structure Proof (p : Prop) : Type where
  proof : p
#check Proof   -- Proof : Prop → Type

axiom modus_ponens : (p q : Prop) → Proof (Implies p q) → Proof p → Proof q

axiom implies_intro : (p q : Prop) → (Proof p → Proof q) → Proof (Implies p q)
