import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic.Ring

#check CommSemiring

inductive MyNat where
  | zero : MyNat
  | succ : MyNat → MyNat


namespace MyNat
--open MyNat


instance : Zero MyNat where
  zero := zero


--axiom1
theorem zero_mynat : zero = (0: MyNat) := by
  rfl

--axiom2
theorem succ_my_nat (n : MyNat) : ∃m, m = succ n := by
 exact ⟨succ n, rfl⟩

--axiom3
--theorem zero_not_succ (n : MyNat) : succ n ≠ zero := by
--  intro h
--  cases h

--axiom4
--theorem succ_injective (m n : MyNat) :
--     succ m = succ n → m = n := by
--  intro h
--  cases h
--  rfl

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

instance : Add MyNat  where
  add := add

theorem add_zero (m : MyNat) : m + 0 = m := by
  rfl

theorem add_succ (m n : MyNat) : m + succ n = succ (m + n) := by
  rfl

theorem zero_add (m : MyNat) : 0 + m = m := by
  apply mynat_induction (P := fun m => 0 + m = m)
  · rfl
  · intro m ia
    rw [add_succ, ia]

theorem succ_add (m n : MyNat) : succ m + n = succ (m + n) := by
  apply mynat_induction (P := fun n => succ m + n = succ (m + n))
  · repeat rw [add_zero]
  · intro d hd
    rw [add_succ, hd, add_succ]

--add kommutativgesetz
theorem add_comm (m n : MyNat) : m + n = n + m := by
  apply mynat_induction (P := fun n => m + n = n + m)
  · rw [add_zero m, zero_add m]
  · intro d ih
    rw [add_succ, ih, <-succ_add]

--add assoziativgesetz
theorem add_assoc (a b c : MyNat) : (a + b) + c = a + (b + c) := by
induction c with
  | zero =>
      rfl
  | succ d hd =>
      repeat rw [add_succ]
      rw [hd]


instance : Std.Commutative (α := MyNat) (· + ·) where
  comm := add_comm
instance : Std.Associative (α := MyNat) (· + ·) where
  assoc := add_assoc




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
    rw [mul_succ, ia, add_zero]

--mult. kommutativgesetz
theorem mul_comm (m n : MyNat) : m * n = n * m := by
  apply mynat_induction (P := fun n => m * n = n * m)
  · rw [mul_zero m, zero_mul m]
  · intro d ih
    rw [mul_succ, ih, add_comm, succ_mul]


--mult. distributivgesetz
theorem left_distrib (a b c : MyNat) : a * (b + c) = a*b + a*c := by
  apply mynat_induction (P := fun a => a * (b + c) = a*b + a*c)
  · rw [zero_mul (b+c), zero_mul b, zero_mul c, add_zero]
  · intro aa ih
    calc aa.succ * (b + c) = aa * (b + c) + (b + c)       := by rw [succ_mul]
                      _ = (aa*b + aa*c) + (b + c)     := by rw [ih]
                      _ = (aa*b + b) + (aa*c + c)     := by ac_rfl
                      _ = aa.succ * b + aa.succ * c   := by rw [succ_mul, succ_mul]


theorem right_distrib (a b c : MyNat) : (a + b) * c  = a*c + b*c := by
  rw [mul_comm (a + b) c, mul_comm a c, mul_comm b c]
  rw [left_distrib c a b]


--mult. assoziativgesetz
theorem mul_assoc (a b c : MyNat) : a * b * c = a * (b * c) := by
  apply mynat_induction (P := fun c => a * b * c = a * (b * c))
  · rw [mul_zero b]
    rw [mul_zero (a*b)]
    rw [mul_zero a]
  · intro d ih
    calc a * b * d.succ = a * b + a * b * d      := by rw [mul_succ]
                      _ = a * b + a * (b * d)    := by rw [ih]
                      _ = a * (b + b*d)          := by rw [<-left_distrib a b (b*d)]
                      _ = a * (b * d.succ)       := by rw [mul_succ]




theorem mul_one (m : MyNat) : m * succ 0 = m := by
  rfl

theorem one_mul (m : MyNat) : succ 0 * m = m := by
  rw[mul_comm]
  rfl

instance : Std.Commutative (α := MyNat) (· * ·) where
  comm := mul_comm

instance : Std.Associative (α := MyNat) (· * ·) where
  assoc := mul_assoc

example (a b c : MyNat) : a * (b * c) = (c * b) * a := by
  ac_rfl


instance : CommSemiring MyNat := {
  zero := 0
  one := succ 0
  add := (· + ·)
  mul := (· * ·)
  add_comm := add_comm
  add_assoc := add_assoc
  zero_add := zero_add
  add_zero := add_zero
  mul_comm := mul_comm
  mul_assoc := mul_assoc
  zero_mul := zero_mul
  mul_zero := mul_zero
  one_mul := one_mul
  mul_one := mul_one
  left_distrib := left_distrib
  right_distrib := right_distrib
  nsmul := nsmulRec
  }


example (a b c : MyNat) : a + a * (b + c)+ c+c  = a *(b+c+ 1) + c*2 := by
  ring


end MyNat
