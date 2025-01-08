import Init.Prelude
import Init.Data.List.Basic
import Mathlib.Tactic

set_option diagnostics true

--rewrites a boolean to an int such that a false is mapped to a 0 and a True to 1
def bool_to_int (b : Bool) : ℕ :=
if b then 1 else 0

--rewrites a boolean list to an int list such that a false is mapped to a 0 and a True to 1
--uses bool_to_int as a mapping
def bool_to_int_list (l : List Bool) : List ℕ :=
l.map bool_to_int

-- gives the left list for the list of Booleans
def list_left (g: List Bool)(n: ℕ) : List ℕ:=
  (List.splitAt n (bool_to_int_list g)).1

-- gives the right list for the list of Booleans
def list_right (g: List Bool)(n: ℕ) : List ℕ:=
  (List.splitAt n (bool_to_int_list g)).2

-- the amount of red cards on the left
def count_left (g: List ℕ): ℕ:=
  List.length g - List.sum g

-- the amount of black cards on the right
def count_right (g: List ℕ):ℕ:=
  List.sum g

--theorem giving that the length of the left split for the first n is n,
--we can only split for n≤ g.length
theorem split_length: ∀ g: List ℕ, ∀ n, n≤ g.length ->
List.length ((List.splitAt n g).1)= n := by
  intro g n h
  simp
  exact h

-- this is the proof for the assumption that the n we choose is ≤ g.length
theorem cards_assumption: ∀ g : List Bool, List.sum (bool_to_int_list g) ≤ g.length := by
  intro g
  rw[bool_to_int_list]
  induction' g with m im ih
  simp
  rcases m
  rw[List.map, bool_to_int]; simp; exact Nat.le_add_right_of_le ih
  rw[List.map, bool_to_int]; simp; rw[add_comm 1 ((List.map bool_to_int im).sum)];
   apply Nat.add_le_add_right; exact ih

--this is the proof that for this chosen n, the length of the left split for the first n is n
theorem len:  ∀ g : List Bool, (List.splitAt (bool_to_int_list (g)).sum
(bool_to_int_list (g))).1.length = (List.map bool_to_int (g)).sum := by
  intro g
  rw[bool_to_int_list]
  have h : List.splitAt (1 + (List.map bool_to_int g).sum) (1 :: List.map bool_to_int g) =
           (List.take (1 + (List.map bool_to_int g).sum) (1 :: List.map bool_to_int g),
            List.drop (1 + (List.map bool_to_int g).sum) (1 :: List.map bool_to_int g)) := by
    exact List.splitAt_eq (1 + (List.map bool_to_int g).sum) (1 :: List.map bool_to_int g)
  apply split_length
  simp
  apply cards_assumption

--this is a helper part, used in the proof for cards
theorem cards_part1: ∀ im : List Bool, (List.map bool_to_int im).sum =
(List.map bool_to_int (false :: im)).sum := by
  intro g
  rw[List.map, bool_to_int]; simp

--this is a helper part, used in the proof for cards_part2
theorem cards_part2_part1: ∀ g: List Bool, (List.drop (List.map bool_to_int g).sum
(List.map bool_to_int g)).sum +(List.take (List.map bool_to_int g).sum
(List.map bool_to_int g)).sum = (List.map bool_to_int g).sum := by
  intro g
  let n := (List.map bool_to_int g).sum
  -- Decompose `List.map bool_to_int g` using `List.take` and `List.drop`
  nth_rewrite 5[← List.take_append_drop (List.map bool_to_int g).sum (List.map bool_to_int g)]
  -- The sum of the appended lists is the sum of their individual sums
  rw[List.sum_append]
  -- Simplify to show that the sum is equal to `n`
  exact Nat.add_comm (List.drop (List.map bool_to_int g).sum (List.map bool_to_int g)).sum
      (List.take (List.map bool_to_int g).sum (List.map bool_to_int g)).sum

--this is a helper part, used in the proof for cards_part2
theorem cards_part2_part2: ∀ g: List Bool, ∀ n: ℕ, (List.drop n
(0::List.map bool_to_int g)).sum +(List.take n (0::List.map bool_to_int g)).sum
 = (0::List.map bool_to_int g).sum := by
  intro g
  intro n
  -- Decompose `List.map bool_to_int g` using `List.take` and `List.drop`
  nth_rewrite 3[← List.take_append_drop n (0::List.map bool_to_int g)]
  -- The sum of the appended lists is the sum of their individual sums
  rw[List.sum_append]
  -- Simplify to show that the sum is equal to `n`
  exact
    Nat.add_comm (List.drop n (0 :: List.map bool_to_int g)).sum
      (List.take n (0 :: List.map bool_to_int g)).sum

--this is a helper part, used in the proof for cards
theorem cards_part2: ∀ im : List Bool, (List.splitAt (List.map bool_to_int im).sum
(List.map bool_to_int im)).2.sum +(List.splitAt (List.map bool_to_int im).sum
(List.map bool_to_int im)).1.sum = (List.splitAt (List.map bool_to_int (false :: im)).sum
(List.map bool_to_int (false :: im))).2.sum +(List.splitAt (List.map bool_to_int
(false :: im)).sum (List.map bool_to_int (false :: im))).1.sum := by
  intro g
  rw[List.map, bool_to_int]; simp
  rw[cards_part2_part1, cards_part2_part2]
  simp

--this is a helper part, used in the proof for cards
theorem cards_part3: ∀ im: List Bool, (List.map bool_to_int (true :: im)).sum =
(List.map bool_to_int (im)).sum +1 := by
  intro g
  rw[List.map, bool_to_int]; simp
  exact Nat.add_comm 1 (List.map bool_to_int g).sum

--this is a helper part, used in the proof for cards_part4
theorem cards_part4_part1: ∀ g: List Bool, (List.drop (1 + (List.map bool_to_int g).sum)
(1 :: List.map bool_to_int g)).sum= (List.drop (bool_to_int_list g).sum
(bool_to_int_list g)).sum := by
  intro g
  -- Step 1: Substitute `bool_to_int_list g` with its definition
  rw [bool_to_int_list]
  rw[Nat.add_comm 1 (List.map bool_to_int g).sum]
  rw[List.drop_succ_cons]

--this is a helper part, used in the proof for cards_part4
theorem cards_part4_part2: ∀ g: List Bool, (List.take (1 + (List.map bool_to_int g).sum)
(1 :: List.map bool_to_int g)).sum=
      (List.take (bool_to_int_list g).sum (bool_to_int_list g)).sum +
    1 := by
  intro g
  rw[bool_to_int_list]
  have h : List.take (1 + (List.map bool_to_int g).sum) (1 :: List.map bool_to_int g) =
           1 :: List.take (List.map bool_to_int g).sum (List.map bool_to_int g) := by
    rw[Nat.add_comm 1 (List.map bool_to_int g).sum]
    rw[List.take_succ_cons]
  rw[h]
  rw[List.sum_cons]
  rw[Nat.add_comm]

--this is a helper part, used in the proof for cards
 theorem cards_part4: ∀ im: List Bool, (List.splitAt (List.map bool_to_int
 (true :: im)).sum (List.map bool_to_int (true :: im))).2.sum +(List.splitAt
 (List.map bool_to_int (true :: im)).sum (List.map bool_to_int (true :: im))).1.sum
 = (List.splitAt (bool_to_int_list im).sum (bool_to_int_list im)).2.sum +
    (List.splitAt (bool_to_int_list im).sum (bool_to_int_list im)).1.sum + 1 := by
    intro g
    rw[List.map, bool_to_int]; simp; rw[cards_part4_part1]
    rw[cards_part4_part2]
    rfl

--this is the theorem that we want to proof, namely to show that for any n
-- there exists a split so that the black cards on the right of the split
-- equal the red cards on the left of the split
theorem cards: ∀ g : List Bool, ∃ n, count_left (list_left g n) = count_right
(list_right g n) := by
  intro g
  use List.sum (bool_to_int_list g)
  rw[count_left, count_right]
  rw[list_left, list_right]
  apply Nat.sub_eq_of_eq_add;
  rw[len]
  induction' g with m im ih
  simp; rw[bool_to_int_list, List.map]; simp
  rcases m
  rw[<- cards_part1]; rw[bool_to_int_list,<- cards_part2]; exact ih
  rw[cards_part3]; rw[bool_to_int_list]; rw[cards_part4]; rw[ih]
