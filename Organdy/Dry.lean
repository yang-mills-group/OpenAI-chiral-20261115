import Organdy.Stylus
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 500000
noncomputable section
namespace YM.CF.Organdy.Larva
open Filter Topology Metric Lattice Exterior Precision 
open Tulip Branch Cube Lat Tenant Drapes _root_.Zephyr.Chern

open scoped Matrix.Norms.L2Operator Matrix
attribute [local instance] opCStarAlgebra
local notation "G" => SU.group
variable {N m:Side}{d r:ℝ}


open Payne
namespace Dry
def Fine (f:ℕ→ℝ) : Prop := ∀ {a:ℝ},0<a→ ∃ M,0<M∧∀ k, |f k|≤M*Real.exp (a*k)
variable {f g:ℕ→ℝ}
lemma cons (c:ℝ):Fine (fun _=> c):=
 fun {_} p=> ⟨|c|+1,by positivity, fun k=>by
     have e:1≤Real.exp (_ * k):= Real.one_le_exp (mul_nonneg p.le (Nat.cast_nonneg _))
     exact le_trans (le_add_of_nonneg_right zero_le_one) (le_mul_of_one_le_right (by positivity) e)⟩
lemma atom : Fine (fun k=>k):=
 fun {a} p=>⟨a⁻¹,inv_pos_of_pos p, fun k=> by
    rw [abs_of_nonneg (Nat.cast_nonneg _)]
    apply (le_inv_mul_iff₀ p).mpr
    exact (le_add_of_nonneg_right zero_le_one).trans (Real.add_one_le_exp _)
 ⟩
lemma sum (h: Fine f)(j:Fine g) : Fine (fun k=>f k+g k):=by
    intro a p
    obtain ⟨c,e,b⟩:=h p; obtain ⟨l,t,v⟩:=j p
    exact ⟨_,add_pos e t,fun k=> (abs_add_le ..).trans ((add_le_add (b _) (v _)).trans_eq (add_mul ..).symm)⟩

lemma mult (h: Fine f)(j:Fine g) : Fine (fun k=>f k*g k):=by
    intro a p; obtain ⟨c,e,b⟩:=h (half_pos p);obtain ⟨l,t,v⟩:=j (half_pos p)
    refine ⟨_,mul_pos e t,fun k=>?_⟩
    rw [abs_mul]; apply (mul_le_mul (b k) (v k) (abs_nonneg _) (by positivity)).trans_eq
    rw [mul_mul_mul_comm, ←Real.exp_add, ←add_mul, add_halves]
lemma raised (n:ℕ)(h: Fine f): Fine (fun k=>f k^n):=by
    induction n with
    | zero=> simp_rw [pow_zero];exact cons 1
    | succ n v=>simp_rw [pow_succ];exact mult v h
lemma strung: Fine stretch:=by
    unfold stretch;push_cast
    exact mult (mult (mult (cons _) (raised 5 (sum (mult (cons _) (sum atom (cons _))) (cons _)))) (cons _)) (cons _)
lemma bead:Fine (fun k=>locale (k+1)):=by
    unfold locale;push_cast
    exact mult (mult (cons _) (raised 4 (sum (sum atom (cons _)) (cons _)))) (cons _)
lemma bs:Fine (fun k=>scale k r 1):=mult (cons _) (raised _ strung)
end Dry

-- common coupon
abbrev dust (r:ℝ)(k:ℕ):ℝ:=(locale (k+1))^2*(2*scale k r 1) +scale k r 1+sweets r
open Dry in lemma scarf {a:ℝ}(p:0<a): ∃ D,0<D ∧ ∀ k,dust r k ≤ D * Real.exp (a*k):= by
    obtain ⟨c,h,u⟩:= (show Dry.Fine (dust r) from Dry.sum (Dry.sum (mult (raised 2 bead) (mult (cons 2) bs)) bs) (cons _)) p

    exact ⟨c,h,fun k=>(le_abs_self _).trans (u k)⟩
