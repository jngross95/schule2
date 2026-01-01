inductive MyNat where
  | zero : MyNat
  | succ : MyNat → MyNat

open MyNat

instance : Zero MyNat where
  zero := zero

--axiom1
theorem zero_mynat : zero = (0: MyNat) := by
  rfl

--axiom2
theorem succ_my_nat (n : MyNat) : ∃m, m = succ n := by
 exact ⟨succ n, rfl⟩

--axiom3
theorem zero_not_succ (n : MyNat) : succ n ≠ zero := by
  intro h
  cases h

--axiom4
theorem succ_injective (m n : MyNat) :
     succ m = succ n → m = n := by
  intro h
  cases h
  rfl

--axiom5
theorem mynat_induction
  {P : MyNat → Prop}
  (h0 : P 0)
  (hs : ∀ n, P n → P (succ n))
  : ∀ n, P n := by
  intro n
  induction n with
    | zero => exact h0             -- Basisfall: 0
    | succ d hd => exact hs d hd   -- Induktionsschritt

def add : MyNat → MyNat → MyNat
  | m, zero => m
  | m, succ n => succ (add m n)

instance : HAdd MyNat MyNat MyNat where
  hAdd := add


theorem add_zero (m : MyNat) : m + 0 = m := by
  rfl

theorem add_succ (m n : MyNat) : m + succ n = succ (m + n) := by
  rfl

theorem zero_add (m : MyNat) : 0 + m = m := by
  apply mynat_induction (P := fun m => 0 + m = m)
  · rfl
  · intro m ia
    rw [add_succ]
    rw [ia]

theorem succ_add (m n : MyNat) : succ m + n = succ (m + n) := by
  apply mynat_induction (P := fun n => succ m + n = succ (m + n))
  · repeat rw [add_zero]
  · intro d hd
    rw [add_succ]
    rw [hd]
    rw [add_succ]


theorem add_comm (m n : MyNat) : m + n = n + m := by
  apply mynat_induction (P := fun n => m + n = n + m)
  · rw [add_zero m]
    rw [zero_add m]
  · intro d ih
    rw [add_succ]
    rw [ih]
    rw [<-succ_add]

theorem add_assoc (a b c : MyNat) : (a + b) + c = a + (b + c) := by
induction c with
  | zero =>
      rfl
  | succ d hd =>
      repeat rw [add_succ]
      rw [hd]


instance : Std.Associative (α := MyNat) (· + ·) where
  assoc := add_assoc

instance : Std.Commutative (α := MyNat) (· + ·) where
  comm := add_comm


example (a b c : MyNat) : a + (b + c) = (c + b) + a := by
  ac_rfl

def mul : MyNat → MyNat → MyNat
  | _, 0 => 0
  | m, succ n => add m (mul m n)

instance : HMul MyNat MyNat MyNat where
  hMul := mul

theorem mul_zero (m : MyNat) : m * 0 = 0 := by
  rfl

theorem mul_succ (m n : MyNat) : m * succ n = m + m * n := by
  rfl

theorem add_succ2 (m n : MyNat) :  succ n + m = n + succ m := by
  calc succ n + m = succ (n + m) := by rw [succ_add]
                _ = n + succ m := by rw [add_succ]




theorem succ_mul (m n : MyNat) : (succ n) * m = n * m + m := by
  apply mynat_induction (P := fun m => (succ n) * m = n * m + m)
  · rfl
  · intro m ia
    calc (succ n) * (succ m) = (succ n) + (succ n) * m := by rw [mul_succ]
                           _ = (succ n) + (n * m + m) := by rw [ia]
                           _ = (succ n) + n * m + m := by ac_rfl
                           _ = ((succ n) + m) + n*m := by ac_rfl
                           _ = n + (succ m) + n*m := by rw [add_succ2]
                           _ = n + n*m + (succ m) := by ac_rfl
                           _ = n * (succ m) + (succ m) := by rw [mul_succ]




theorem zero_mul (m : MyNat) : 0 * m = 0 := by
  apply mynat_induction (P := fun m => 0 * m = 0)
  · rfl
  · intro m ia
    rw [mul_succ]
    rw [ia]
    rw [add_zero]

theorem mul_comm (m n : MyNat) : m * n = n * m := by
  apply mynat_induction (P := fun n => m * n = n * m)
  · rw [mul_zero m]
    rw [zero_mul m]
  · intro d ih
    rw [mul_succ]
    rw [ih]
    rw [add_comm]
    rw [succ_mul]
