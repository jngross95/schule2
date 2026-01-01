

inductive MyNat where
  | zero : MyNat
  | succ : MyNat → MyNat

open MyNat

def axiom1 : MyNat := zero

def axiom2 (n : MyNat) : MyNat := succ n

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

instance : Zero MyNat where
  zero := zero

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
  induction m with
    | zero =>
      rfl
    | succ d hd =>
      rw [add_succ]
      rw [hd]


theorem succ_add (m n : MyNat) : succ m + n = succ (m + n) := by
  apply mynat_induction (P := fun n => succ m + n = succ (m + n))
  · simp [add_zero]
  · intro d hd
    rw [add_succ]
    rw [hd]
    rw [add_succ]


theorem add_comm (m n : MyNat) : m + n = n + m := by
  induction n with
    | zero =>
      rw [add_zero m]
      rw [zero_add m]
    | succ d ih=>
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



instance : Std.Associative MyNat add where
  assoc := add_assoc

instance : Std.Commutative MyNat add where
  comm := add_comm



example (a b c : MyNat) : (a + (b + c)) = ((a + b) + c) := by
  ac_rfl[add]
