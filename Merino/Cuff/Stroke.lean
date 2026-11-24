import Merino.Cuff.Suede
import Merino.Cuff.Gauge
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 600000
set_option synthInstance.maxSize 24000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Merino.Cuff
open Function Filter Topology NormedSpace Lattice Wilson Fock Pastry Scree Sault Sour Stax Skye Jet NormedSpace Scroll Finset Palot Cadre Vow
open RG Mew Rive Nor Hake MeasureTheory Bake Rue Salt
open Metric Drapes Tulip Lat Branch Cube Tenant
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Classical
attribute [local instance] opCStarAlgebra
open Rush SU Prism Nacre Laic Tap Levier Thera Moto Oath Font Haro Spire Swell

variable {n:Side}
local notation "I"=> Single n

open Push.Uniform Planned.JetPort Peaks
open scoped ContDiff

section
variable {V:Type}[NormedAddCommGroup V][NormedSpace ℝ V]
abbrev Afford (f:V→ℝ)(r C:ℝ):Prop:=
   ∀ {x},‖x‖≤r → Jet.Allows 3 f x C

/-- Symmetric ticket, including the 2!. -/
def round (f:V→ℝ): V→ₗ[ℝ]V→ₗ[ℝ]ℝ:=
 LinearMap.mk₂ ℝ (fun u v=>fderiv ℝ (fderiv ℝ f) 0 u v/2)
   (by intro; simp [add_div])
   (by intro; simp [div_eq_mul_inv,mul_assoc])
   (by intro; simp [add_div])
   (by intro; simp [div_eq_mul_inv,mul_assoc])
lemma roundV (f:V→ℝ)(u v:V):
 round f u v=(iteratedFDeriv ℝ 2 f 0 ![u,v])/2:=by rw [iteratedFDeriv_two_apply]; rfl

lemma round_symm {f:V→ℝ}(h:ContDiffAt ℝ 2 f 0)(u v:V):
 round f u v= round f v u:=by rw [roundV,Work.F03.hessian_symmetric h,←roundV]

lemma round_le {f:V→ℝ}{C:ℝ} (h:Jet.Allows 3 f 0 C)(u v:V):
  |round f u v| ≤ C*(‖u‖*‖v‖):=by
 rw [roundV,abs_div,abs_of_pos (show (0:ℝ)<2 by norm_num)]
 apply le_trans (half_le_self (abs_nonneg _))
 exact ((iteratedFDeriv ℝ 2 f 0).le_opNorm ![u,v]).trans
   (by simp [Fin.prod_univ_two]; gcongr; exact h.norm_le 2 (by decide))


def bolt (X:V):ℝ→L[ℝ] V:= (ContinuousLinearMap.id ℝ ℝ).smulRight X
lemma round_line (X:V){t:ℝ}{f:V→ℝ} {k:ℕ}
   (h:ContDiffAt ℝ k f (bolt X t)):
   iteratedDeriv k (f ∘ bolt X) t=iteratedFDeriv ℝ k f (bolt X t) (fun _=>X):=by
 rw [iteratedDeriv,Push.Uniform.iter_lin_at h,ContinuousMultilinearMap.compContinuousLinearMap_apply]
 simp [bolt]

lemma Afford.cubic {f:V→ℝ}{r C:ℝ}(h:Afford f r C)(hg:fderiv ℝ f 0 = 0)(X:V)(t:‖X‖ ≤ r):
   |f X - (f 0 + round f X X)| ≤ C*‖X‖^3:=by
 let L:=bolt X
 let U:=f ∘ L
 let S:=Set.Icc (0:ℝ) 1
 have hh (x:ℝ)(hx:x∈S):‖L x‖≤r:=by
    change ‖x • X‖≤r; rw [norm_smul,Real.norm_of_nonneg hx.1]
    exact (mul_le_of_le_one_left (norm_nonneg _) hx.2).trans t
 have h0(i:ℕ)(hv:i≤3)(x:ℝ)(hx:x∈S) :=(h (hh x hx)).smooth.of_le (show (i:WithTop ℕ∞)≤(3:ℕ) by exact_mod_cast hv)
 have he(i:ℕ)(hv:i≤3)(x:ℝ)(hx:x∈S): ContDiffAt ℝ i U x:= (h0 i hv x hx).comp _ L.contDiff.contDiffAt


 have hs:0∈S:=Set.left_mem_Icc.mpr zero_le_one
 have hu : (0:ℝ)<1:=zero_lt_one
 have hw (i:ℕ)(hv:i≤3)(x:ℝ)(hx:x∈S): iteratedDerivWithin i U S x = iteratedDeriv i U x:=
     iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc hu) (he i hv x hx) hx
 have hk (x:ℝ)(hx:x∈S): ‖iteratedDeriv 3 U x‖≤ C*‖X‖^3:=by
   rw [show iteratedDeriv 3 U x=_ from round_line X (h0 3 le_rfl x hx)]
   apply (ContinuousMultilinearMap.le_opNorm ..).trans
   simp; gcongr; exact (h (hh x hx)).norm_le 3 le_rfl
 have hl := taylor_mean_remainder_bound (C:=C*‖X‖^3) (n:=2) (f:=U)
     hu.le (fun x hx=>
       (he 3 le_rfl x hx).contDiffWithinAt.of_le (by norm_num))
     (Set.right_mem_Icc.mpr hu.le)
     (fun x hx=>by rw [hw _ le_rfl _ hx]; exact hk x hx)
 have hx: iteratedDeriv 1 U 0=0:=by
     unfold U; rw [iteratedDeriv_one,deriv,fderiv_comp 0 ((h0 1 (by decide) 0 hs).differentiableAt (by norm_num)) L.differentiableAt,map_zero,hg,ContinuousLinearMap.zero_comp]; rfl
 have hy: iteratedDeriv 2 U 0=fderiv ℝ (fderiv ℝ f) 0 X X:=by
     rw [show iteratedDeriv 2 U 0=_ from round_line X (h0 2 (by decide) 0 hs), map_zero,iteratedFDeriv_two_apply]


 rw [taylor_within_apply,sum_range_succ,sum_range_succ,sum_range_one,
   hw 0 (by norm_num) _ hs,hw 1 (by norm_num) _ hs,hw 2 (by norm_num) _ hs,
   hx,hy] at hl
 norm_num [U,L,bolt,Nat.factorial,←div_eq_inv_mul] at hl
 have hg:= (h (hh 0 hs)).nonneg
 rw [roundV,iteratedFDeriv_two_apply,show ∀ v:ℝ,v/2=1/2*v by intro; ring]
 exact hl.trans (half_le_self (mul_nonneg hg (pow_nonneg (norm_nonneg _) _)))

end


-- aside on locality
section
variable {V:Type}[NormedAddCommGroup V][NormedSpace ℝ V]

lemma round_diag {f:V→ℝ}(h:ContDiffAt ℝ 2 f 0){u v:V}
    (g:(f∘bolt u) =ᶠ[𝓝 0] (f∘bolt v)) :
    round f u u = round f v v:=by
 have t(x:V):iteratedDeriv 2 (f∘bolt x) 0/2=round f x x:=by
    rw [round_line x (by rw [map_zero]; exact h),map_zero,roundV,iteratedFDeriv_two_apply,iteratedFDeriv_two_apply]
    rfl
 rw [←t,←t,g.iteratedDeriv_eq]
end
end YM.CF.Merino.Cuff
