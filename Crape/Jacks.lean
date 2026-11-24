import Crape.Oblivion
import Nankin.Bern
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4500
set_option maxHeartbeats 220000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance
namespace Spine
namespace PledgeT
open Calico
open Asymptotics
variable{X:Type*}[NormedAddCommGroup X][NormedSpace ℂ X]
    (x:ℕ→X)
-- summability crude with factor 3 exp, relative coefficients. avoids buying uniform in s separately.
lemma eventual_domino (B:ℝ)(p:0<B)(h:∀ᶠ i:ℕ in atTop,‖x (i+1)‖ ≤ B+2*‖x i‖):∃ t:ℝ,0<t ∧∀ i:ℕ, ‖x i‖ ≤ t*3^i:=by
 obtain ⟨n,h⟩:= Filter.eventually_atTop.mp h
 let v:= ∑ i ∈ Finset.range (n+1),‖x i‖
 let t:= v+B; have H:0≤v:=Finset.sum_nonneg (fun _ _=>norm_nonneg _); have y:0<t:=add_pos_of_nonneg_of_pos H p; have e:B≤t:=le_add_of_nonneg_left H
 have he(i:ℕ): 1≤ (3:ℝ)^i:=one_le_pow₀ (by norm_num)
 have g(i:ℕ): t≤ t*3^i:=le_mul_of_one_le_right y.le (he i)
 have u(i:ℕ)(p:i<n+1):‖x i‖≤ v:=single_le_sum (fun _ _=>norm_nonneg _) (mem_range.mpr p)
 refine ⟨t,y,fun i=>?_⟩; induction i with
 |zero=> exact (u 0 (by omega)).trans ((le_add_of_nonneg_right p.le).trans (g 0))
 |succ i ih=>
   rcases lt_or_ge i n with z|z
   · exact (u (i+1) (by omega)).trans ((le_add_of_nonneg_right p.le).trans (g (i+1)))
   rw [pow_succ,←mul_assoc]; have l:= h i z; have w:=g i; linarith only [e,l,w,ih]
#check Asymptotics.isBigOWith_iff
#check summable_of_isBigO_nat
lemma splat{θ:ℝ}(h:0< θ)(t:θ<1){u:ℕ→ℝ}(P:∀ i,0≤ u i)(C:ℝ)(hv:∀ᶠ i:ℕ in atTop, u i ≤C*θ^i):Summable u:=by
 apply summable_of_isBigO_nat (summable_geometric_of_lt_one h.le t)
 exact (isBigOWith_iff.mpr (hv.mono fun i p=> by simpa only [Real.norm_eq_abs,abs_of_nonneg (P i),abs_of_nonneg (pow_nonneg h.le i)] using p):IsBigOWith C atTop u (fun i=>θ^i)).isBigO

lemma excur (Y:ℝ)(H₀:0<Y)(u:∀ᶠ i:ℕ in atTop, ‖x (i+1)-x i‖ ≤ Y*16⁻¹^i+ Y*16⁻¹^i*‖x i‖):CauchySeq x:=by
 let θ:ℝ:=16⁻¹; have ht:0<θ:=by unfold θ; norm_num
 have ht':θ<1:=by unfold θ; norm_num
 have he:Tendsto (fun n:ℕ=>Y*θ^n) atTop (𝓝 (0:ℝ)):=by simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one ht.le ht'|>.const_mul Y)
 have arm:∀ᶠ i:ℕ in atTop,Y*θ^i≤1:=he.eventually (ge_mem_nhds zero_lt_one)
 obtain ⟨C,y,t⟩:=eventual_domino x 1 zero_lt_one (u.and arm |>.mono fun i ⟨p,q⟩=>by
   exact (calc ‖x (i+1)‖ ≤ ‖x (i+1)-x i‖+‖x i‖:=by simpa using norm_add_le (x (i+1)-x i) (x i)
               _ ≤1+2*‖x i‖:=by change Y*16⁻¹^i ≤1 at q; nlinarith [norm_nonneg (x i)]))
 apply cauchySeq_of_summable_dist
 refine splat (θ:=3*θ) (by positivity) (by norm_num [θ]) (fun _=>dist_nonneg) (Y+Y*C) (u.mono fun i h=>?_)
 rw [dist_comm,dist_eq_norm]
 apply h.trans; rw [add_mul]; have e':θ^i ≤ (3*θ)^i:=pow_le_pow_left₀ ht.le (by unfold θ; norm_num) _
 refine add_le_add (mul_le_mul_of_nonneg_left e' H₀.le) ?_
 rw [mul_pow]; exact (mul_le_mul_of_nonneg_left (t i) (by positivity)).trans_eq (by unfold θ; ring)
#print axioms excur
end PledgeT
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
