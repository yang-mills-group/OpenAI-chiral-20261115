import YM.SU5.Relativistic.Schist
import YM.SU5.Relativistic.Raspa
import YM.CF.Continuum.Extensive
/-! # pinpoint charge. On clean ORBIT. (For unrepaired dirty count by t.) -/
set_option autoImplicit false
set_option maxHeartbeats 420000
noncomputable section
namespace YM.CF.Papyrus.Franc
open Function Filter NormedSpace Metric Fock Finset Lattice Lat Fir Ember Thera BPress.Spin.Blank Rush SU Scroll Tulip Dial Cube Skye Pannier Pannier.Chancel Buffered Pastry
open Crest.Sleet Pannier.Damask
open scoped Topology Matrix MatrixOrder InnerProductSpace Matrix.Norms.L2Operator BigOperators ComplexOrder Kronecker
attribute [local instance] opCStarAlgebra
set_option linter.unusedSectionVars false
set_option linter.flexible false
open CF.Window Matrix
namespace Verses
variable {I:Type}[LinearOrder I][Fintype I]{h C t:ℝ}
abbrev condor (P:Op I)(c:ℝ):Prop:=∀ j, ∑ i:I, ‖P i j‖≤ c
structure fiber (T:Shaft I)(c:ℝ):Prop where
   fst (i:I) : ‖acts T.sell (basisKet i)‖≤c
   snd (i:I) : ‖acts (star T.buy) (basisKet i)‖≤c
lemma column_action (P A:Op I){c d:ℝ}(h:∀ i:I,‖acts P (basisKet i)‖≤c)(p:condor A d)(t:0≤c)(i:I): ‖acts (P*A) (basisKet i)‖ ≤ c*d:=by
 rw [act_mul]; let v:=acts A (basisKet i); have he:v=∑ j:I,A j i • basisKet j:=by nth_rw 1 [←basis_expand v]; unfold v; simp_rw [basis_act]
 change ‖acts P v‖ ≤ _
 rw [he,map_sum, mul_comm c d]; apply (norm_sum_le ..).trans; apply le_trans (b:=(∑ j,‖A j i‖)*c) ?_ (mul_le_mul_of_nonneg_right (p i) t); rw [Finset.sum_mul]; apply sum_le_sum; intro j _; rw [map_smul,norm_smul]; exact mul_le_mul_of_nonneg_left (h j) (norm_nonneg _)
lemma condor_budget (A B:Op I)(v:condor A C) : entryBudget (A*B)≤C*entryBudget B:=by
 unfold entryBudget; simp only [mul_apply]; apply (sum_le_sum (s:=univ) (fun i _=> sum_le_sum (s:=univ) (fun j _ => norm_sum_le ..))).trans
 rw [show (∑ i:I,∑ j:I,∑ k:I, ‖A i k*B k j‖)=∑ k:I,∑ j:I, (∑ i:I, ‖A i k‖)*‖B k j‖ from ?_,mul_sum]; swap
 · simp_rw [sum_mul,norm_mul]; rw [sum_comm]; nth_rw 2 [sum_comm]; apply sum_congr rfl; intro j _; rw [sum_comm]
 apply sum_le_sum; intro i _; rw [mul_sum]; apply sum_le_sum; intro j _; exact mul_le_mul_of_nonneg_right (v i) (norm_nonneg _)
lemma condor_right (A B:Op I)(v:condor (star A) C) : entryBudget (B*A) ≤ C*entryBudget B:=by
 rw [←entryBudget_adjoint B,←entryBudget_adjoint (B*A),star_mul]; exact condor_budget _ _ v
lemma condor_one_sub (A:Op I)(p:condor A C): condor (1-A) (1+C) :=by
 intro j; apply ((sum_le_sum (s:=univ) (fun i _=> norm_sub_le ((1:Op I) i j) (A i j))).trans ?_) -- cast wrong
 rw [sum_add_distrib]; refine add_le_add ?_ (p j)
 simp [Matrix.one_apply, apply_ite norm]
lemma glow_dg (T:Shaft I)(hp:fiber T C)(h:0≤C)(A:Op I) : ‖T.glow (dg A)‖≤ C^2*entryBudget A:=by
 have hv (d:Finset I)(F:I→FC I) : T.glow (∑ i∈d,F i)= ∑ i∈d,T.glow (F i):=by induction d using Finset.induction_on with| empty=> simp [T.glow_zero]| insert i d h ih=> rw [sum_insert h,sum_insert h,T.glow_sum,ih]
 unfold dg dyad entryBudget
 simp_rw [hv,T.glow_free,T.glow_mult, mul_sum]
 refine (norm_sum_le ..).trans (sum_le_sum (s:=univ) (fun i _=> (norm_sum_le ..).trans (sum_le_sum (s:=univ) (fun j _=>?_))))
 change ‖A i j • (T.glow (put i)*T.glow (takeF j))‖≤_
 have hf:‖T.glow (put i)‖≤ C:=by
    rw [show put i=create (basisKet i) from ?_,T.glow_up]
    exact (Flare.cost_pe false _).trans (hp.fst _)
    -- basis equation?
    exact (create_put ..).symm
 have hq:‖T.glow (takeF j)‖≤ C:=by
    rw [show takeF j=Fock.remove (basisKet j) from ?_,T.glow_down]; exact (Flare.cost_pe true _).trans (hp.snd _); unfold Fock.remove takeF; rw [create_put]
 rw [norm_smul,sq,mul_comm (C*C)]; exact mul_le_mul_of_nonneg_left ((norm_mul_le ..).trans (mul_le_mul hf hq (norm_nonneg _) h)) (norm_nonneg _)

-- conjugate through exp . commute log
lemma glow_thermal (T:Shaft I)(A:FC I): T.glow (exp A)=exp (T.glow A):=by
 let f:FC I→ₐ[ℂ] FC I:={
  toFun:=T.glow
  map_one':=T.glow_nil
  map_zero':=T.glow_zero
  map_add':=T.glow_sum
  map_mul':=T.glow_mult
  commutes':=fun r=> by rw [Algebra.algebraMap_eq_smul_one,T.glow_free,T.glow_nil] }
 -- map theorem
 exact NormedSpace.map_exp_of_mem_ball (𝕂:=ℂ) f (f.toLinearMap.continuous_of_finiteDimensional) A ((expSeries_radius_eq_top ℂ (FC I)).symm ▸ edist_lt_top _ _)
end Verses
end YM.CF.Papyrus.Franc
