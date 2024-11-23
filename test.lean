import Mathlib.ALgebra.Ring.Defs

def isEven (n : Int) : Prop := ∃ k, n = 2 * k

theorem sum_of_evens (a b : Int) (ha : isEven a) (hb : isEven b) :
  isEven (a + b) := by
  cases ha with | intro k hk =>
  cases hb with | intro m hm =>
  exists k + m
  rw [hk, hm]
  rw [mul_add]
