import SatinStress.U1.Radix

/-!
# Certificate polynomial interpreter

Evaluate the (93) test polynomials after Radix.encode. No sortedness/in-range assumptions
needed of any sparse-polynomial operations; prove correct denotation even if the zero
recognizer were to fail to recognize some identities. Checks over ℤ+iℤ.
-/
namespace SatinStress.U1
namespace Radix

open MvPolynomial
open scoped Polynomial

structure GI where
  re : ℤ
  im : ℤ
  deriving DecidableEq, Repr
namespace GI
instance : Zero GI := ⟨⟨0,0⟩⟩
instance : One GI := ⟨⟨1,0⟩⟩
instance : Add GI := ⟨fun a b => ⟨a.re+b.re, a.im+b.im⟩⟩
instance : Neg GI := ⟨fun a => ⟨-a.re,-a.im⟩⟩
instance : Mul GI := ⟨fun a b => ⟨a.re*b.re - a.im*b.im, a.re*b.im + a.im*b.re⟩⟩

noncomputable def c (a : GI) : ℂ := ⟨a.re, a.im⟩
@[simp] theorem c_add (a b : GI) : (a+b).c = a.c + b.c := by
  apply Complex.ext
  · change (((a.re+b.re : ℤ) : ℝ)) = (a.re : ℝ) + b.re; simp
  · change (((a.im+b.im : ℤ) : ℝ)) = (a.im : ℝ) + b.im; simp
@[simp] theorem c_mul (a b : GI) : (a*b).c = a.c * b.c := by
  apply Complex.ext
  · change ((a.re*b.re-a.im*b.im : ℤ) : ℝ) = (a.re : ℝ)*b.re-(a.im : ℝ)*b.im; simp
  · change ((a.re*b.im+a.im*b.re : ℤ) : ℝ) = (a.re : ℝ)*b.im+(a.im : ℝ)*b.re; simp
@[simp] theorem c_neg (a : GI) : (-a).c = -a.c := by
  apply Complex.ext
  · change (((-a.re : ℤ) : ℝ)) = -(a.re : ℝ); simp
  · change (((-a.im : ℤ) : ℝ)) = -(a.im : ℝ); simp
@[simp] theorem c_zero : c 0 = 0 := by change c ⟨0,0⟩ = _; apply Complex.ext <;> simp [c]
@[simp] theorem c_one : c 1 = 1 := by change c ⟨1,0⟩ = _; apply Complex.ext <;> simp [c]
lemma c_inj (a b : GI) : a.c = b.c ↔ a = b := by rcases a with ⟨_,_⟩; rcases b with ⟨_,_⟩; simp [GI.c]
end GI

abbrev Term := ℕ × GI
abbrev Tape := List Term
namespace Tape
noncomputable def poly : Tape → ℂ[X]
  | [] => 0
  | x::xs => Polynomial.monomial x.1 x.2.c + poly xs
@[simp] lemma poly_nil : poly [] = 0 := rfl
@[simp] lemma poly_cons (x : Term) (xs : Tape) : poly (x::xs) = Polynomial.monomial x.1 x.2.c + poly xs := rfl
lemma poly_append (xs ys : Tape) : poly (xs++ys) = poly xs + poly ys := by
  induction xs with
  | nil => simp
  | cons a as ih => simp [ih, add_assoc]

def omitZero (d : ℕ) (x : GI) (xs : Tape) := if x.re == 0 && x.im == 0 then xs else (d,x)::xs
lemma poly_omit (d : ℕ) (x : GI) (xs : Tape) : poly (omitZero d x xs) = Polynomial.monomial d x.c + poly xs := by
  rcases x with ⟨a,b⟩
  unfold omitZero; split
  next h => simp at h; rw [h.1,h.2]; change _ = Polynomial.monomial d (GI.c 0) + _; simp
  rfl

def neg (xs : Tape) : Tape := xs.map (fun x => (x.1,-x.2))
lemma poly_neg (xs : Tape) : poly (neg xs) = -poly xs := by
  induction xs with
  | nil => simp [neg]
  | cons a as ih => simpa [neg,add_comm] using congrArg (fun y => Polynomial.monomial a.1 (-a.2.c)+y) ih

def mix (fuel : ℕ) (xs ys : Tape) : Tape := match fuel with
  | 0 => xs ++ ys
  | n+1 =>
    match xs, ys with
    | [], _ => ys
    | _, [] => xs
    | x::rx, y::ry =>
      if x.1 == y.1 then omitZero x.1 (x.2+y.2) (mix n rx ry) else
      if x.1 < y.1 then x :: mix n rx ys else y :: mix n xs ry
lemma poly_mix (n : ℕ) (xs ys : Tape) : poly (mix n xs ys) = poly xs + poly ys := by
  induction n generalizing xs ys with
  | zero => exact poly_append ..
  | succ n ih =>
    cases xs with
    | nil => simp [mix]
    | cons x xs =>
      cases ys with
      | nil => simp [mix]
      | cons y ys =>
        simp only [mix,poly_cons]
        split
        next h => simp [poly_omit,ih,beq_iff_eq.mp h]; abel
        split <;> simp [ih] <;> abel

def plus (xs ys : Tape) : Tape :=
  if xs.isEmpty then ys else
  if ys.isEmpty then xs else
  mix (xs.length + ys.length) xs ys
lemma poly_plus (xs ys : Tape) : poly (plus xs ys) = poly xs + poly ys := by cases xs <;> cases ys <;> simp only [plus,List.isEmpty_cons,List.isEmpty_nil,↓reduceIte,Bool.false_eq_true,poly_mix,poly_nil,add_zero,zero_add]

def timesOne (x : Term) (ys : Tape) : Tape := ys.map fun y => (x.1+y.1,x.2*y.2)
lemma poly_timesOne (x : Term) (ys : Tape) :
    poly (timesOne x ys) = Polynomial.monomial x.1 x.2.c * poly ys := by
  induction ys with
  | nil => simp [timesOne]
  | cons a as ih => change poly ((_,_) :: timesOne x as) = _; simp [ih,mul_add,Polynomial.monomial_mul_monomial]

def times : Tape → Tape → Tape
  | [], _ => []
  | x::xs, ys => plus (timesOne x ys) (times xs ys)
lemma poly_times (xs ys : Tape) : poly (times xs ys) = poly xs * poly ys := by
  induction xs with
  | nil => simp [times]
  | cons a as ih => simp [add_mul,times,poly_timesOne,poly_plus,ih]

def look (n : ℕ) : Tape → GI
  | [] => 0
  | x::xs => if x.1 == n then x.2 + look n xs else look n xs
lemma look_eq (n : ℕ) (xs : Tape) : (look n xs).c = (poly xs).coeff n := by
  induction xs with
  | nil => simp [look]
  | cons a as ih =>
    rw [look]
    split
    next he => simp [ih,beq_iff_eq.mp he]
    next he => simp [Polynomial.coeff_monomial,ih, (show a.1 ≠ n by simpa using he)]
end Tape

/-- Arithmetic circuits with literals in ℤ+iℤ. Variables identified later. -/
inductive Expr where
  | var (i : Fin 9)
  | con (k : GI)
  | opp (x : Expr)
  | add (x y : Expr)
  | mul (x y : Expr)
namespace Expr
open Tape

instance : Zero Expr := ⟨con 0⟩
instance : One Expr := ⟨con 1⟩
instance : Add Expr := ⟨Expr.add⟩
instance : Mul Expr := ⟨Expr.mul⟩
instance : Neg Expr := ⟨opp⟩
-- no AddGroup inference
instance : Sub Expr := ⟨fun a b => a + -b⟩

def conZ (x : ℤ) := con ⟨x,0⟩
noncomputable def den : Expr → Many
  | var i => X i
  | con k => C k.c
  | opp x => -den x
  | add x y => den x + den y
  | mul x y => den x * den y
@[simp] lemma den_add (x y : Expr) : den (x+y) = den x + den y := rfl
@[simp] lemma den_mul (x y : Expr) : den (x*y) = den x * den y := rfl
@[simp] lemma den_neg (x : Expr) : den (-x) = -den x := rfl
@[simp] lemma den_sub (x y : Expr) : den (x-y) = den x - den y := by change den (x + -y) = _; rw [sub_eq_add_neg, ←den_neg, ←den_add]
@[simp] lemma den_zero : den 0 = 0 := by change den (con 0) = _; simp [den]
@[simp] lemma den_one : den 1 = 1 := by change den (con 1) = _; simp [den]
@[simp] lemma den_conZ (n : ℤ) : den (conZ n) = n := by
  have h : GI.c ⟨n,0⟩ = n := by apply Complex.ext <;> simp [GI.c]
  simp [conZ,den,h]

def bound : Expr → ℕ
  | var _ => 1
  | con _ => 0
  | opp x => bound x
  | add x y => max (bound x) (bound y)
  | mul x y => bound x + bound y

lemma bounded (x : Expr) : x.den.totalDegree ≤ bound x := by
  induction x with
  | var i => simp [den,bound]
  | con c => simp [den,bound]
  | opp x ih =>
    simp only [den, bound]
    -- totalDegree_neg
    rw [← neg_one_mul, ← map_one (M:=ℂ) C, ← map_neg C]
    exact (totalDegree_mul ..).trans (by simpa only [totalDegree_C,zero_add] using ih)
  | add x y ix iy => exact (totalDegree_add ..).trans (max_le_max ix iy)
  | mul x y ix iy => exact (totalDegree_mul ..).trans (add_le_add ix iy)

def sparse : Expr → Tape
  | var i => [(wt i,1)]
  | con k => omitZero 0 k []
  | opp x => Tape.neg x.sparse
  | add x y => plus x.sparse y.sparse
  | mul x y => times x.sparse y.sparse
lemma sparse_eq (x : Expr) : poly x.sparse = encode x.den := by
  induction x with
  | var i => simp [den,sparse, Polynomial.monomial_one_right_eq_X_pow]
  | con c => rw [sparse,den,poly_omit,encode_C,poly_nil,add_zero]; rfl
  | opp x ix => simp [den,sparse,poly_neg,ix]
  | add x y ix iy => simp [den,sparse,poly_plus,ix,iy]
  | mul x y ix iy => simp [den,sparse,poly_times,ix,iy]
/-- Check a **zero polynomial**, not just a relation on sample points. -/
def spends (x : Expr) : Bool := x.sparse.isEmpty && x.bound < base
lemma spend_zero (x : Expr) (h : x.spends) : den x = 0 := by
  rw [spends] at h
  simp only [Bool.and_eq_true, List.isEmpty_iff,decide_eq_true_eq] at h
  exact encode_detect ((bounded x).trans_lt h.2) (by rw [← sparse_eq,h.1,poly_nil])
lemma micro (x : Expr) (n : ℕ) : test n (den x) = GI.c (look n x.sparse) := by rw [look_eq,sparse_eq,test_at]
lemma row_zero (x : Expr) (n : ℕ) : test n (den x) = 0 ↔ look n x.sparse = 0 := by rw [micro,← GI.c_zero,GI.c_inj]
end Expr
end Radix
end SatinStress.U1
