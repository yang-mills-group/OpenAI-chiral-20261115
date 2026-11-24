import GaugeFieldConstruction.WaltsQuotaNX
import GaugeFieldConstruction.Solvent
-- hs via operator bloc equivalent explicit.Entry sheets.
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 3600
set_option linter.unusedSectionVars false
set_option maxHeartbeats 100000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Ballad
open Function Filter Metric Fock Finset Fir Jill Lat Lattice Cube Sods Tulip Scroll Spire Pastry RP Branch Wilson Phase SU Rush Mir Reflect Lifted Bilinear Window Skye
open scoped Matrix MatrixOrder BigOperators Kronecker InnerProductSpace Topology Classical
variable {R:ℕ}{B N:Side}
open YM.CF.Lamour.Bridge.Celeste
open Py.Rate.LocalLimit.Papal (Weaver household)
open Kea
open Flare
open scoped Matrix.Norms.Frobenius in
lemma lipCrestFNX (u:SU.E)(i j:SU.F): ‖fund u i j-(1:Op SU.F) i j‖ ≤ Real.sqrt group.repDim * group.chord u:=by
  let A:=SU.fund u-1
  unfold Gauge.chord; rw [mul_div_cancel₀ _ (show Real.sqrt (group.repDim:ℝ) ≠ 0 from group.colorScale_pos.ne')] -- tune
  change ‖A i j‖ ≤ ‖A‖
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp -- tune direction
  rw [Gauge.frob_sq]; unfold Matrix.trace; simp_rw [Complex.re_sum,Matrix.diag_apply,Matrix.mul_apply,Complex.re_sum]
  have hp(i j:SU.F):(A i j * star A j i).re=‖A i j‖^2:= inner_self_eq_norm_sq (𝕜:=ℂ) (A i j)
  simp_rw [hp]
  exact le_trans (single_le_sum (f:=fun k=>‖A i k‖^2) (fun k _ =>sq_nonneg _) (mem_univ j)) (single_le_sum (f:=fun k:SU.F=>∑ j,‖A k j‖^2) (fun k _=>sum_nonneg (fun k _=>sq_nonneg _)) (mem_univ i))
open scoped Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
lemma majorFundFNX : ∃ C:ℝ,0≤ C ∧ ∀ U:SU.E,‖SU.fund U-1‖≤C*group.chord U:=by
   let f(k l:SU.F):Op SU.F:=Matrix.single k l 1
   have h(A:Op SU.F): A= ∑ i,∑ j,A i j • f i j:=by ext y z; simp [f,Matrix.sum_apply,Matrix.single,ite_and, Finset.sum_ite_irrel, eq_comm] -- tune
   let C:=Real.sqrt group.repDim
   let L:=∑ i, ∑ j,C*‖f i j‖
   refine ⟨L, Finset.sum_nonneg (fun i _=>Finset.sum_nonneg (fun j _=>by unfold C; positivity)),fun u=>?_⟩
   let A:= SU.fund u-1
   change ‖A‖≤ _
   nth_rw 1[h A]
   refine (norm_sum_le ..).trans ?_
   unfold L; rw [sum_mul]; refine sum_le_sum fun i _=>?_; rw [sum_mul]; refine (norm_sum_le ..).trans (sum_le_sum fun j _=>?_); rw[norm_smul]; exact (mul_le_mul_of_nonneg_right (lipCrestFNX u i j) (norm_nonneg _)).trans_eq (by unfold C; ring)
lemma lipsMinorFNX : ∃ C:ℝ,0≤C ∧∀ U:SU.E, ‖(matter U).val-1‖≤ C* group.chord U:=by
 obtain ⟨b,h,hb⟩:= Pic.gulf
 obtain ⟨c,hc,g⟩:= majorFundFNX
 refine ⟨b*c,mul_nonneg (by linarith) hc,fun U=>?_⟩
 have ht:=hb U 1
 change ‖(matter U).val-(matter (1:SU.E)).val‖≤ b*‖(firstF U).val-(firstF (1:SU.E)).val‖ at ht
 rw [map_one, map_one] at ht
 change ‖(matter U).val-1‖≤ b*‖SU.fund U-1‖ at ht
 refine le_trans ht ?_
 exact (_root_.mul_assoc ..).ge.trans' (mul_le_mul_of_nonneg_left (g U) (by linarith))
open Py.Rate.LocalLimit.Papal
open Afterglow
lemma walkingFNX{S:Finset Cover}{T:Support (More N)} {U:Pane N}{a:ℝ}(p:FrameP.chordK T U a)(h:Satin.region S N⊆ T)(x:Cover)(W:Walk)(t:x∈ S)(e:∀ i∈visits x W,i∈S): group.chord (travel (onC N U) x W) ≤ W.length*a:=by
 induction W generalizing x with
 | nil=> simp [travel]
 | cons g W ih=>
    obtain ⟨g,b⟩:=g
    let Y:Step:=⟨g,b⟩
    have hx(v:Cover)(u:v∈visits (x+Y.vec) W):v∈S:= e v (List.Mem.tail _ u)
    have hp : x+Y.vec∈ S:= hx _ (by cases W<;>simp [visits])
    have he: group.chord (Y.read (onC N U) x)≤ a:=by
       cases b
       · change group.chord (onC N U (x,g))≤a
         rw[onC_spec]; apply p
         · exact h (mem_image_of_mem _ t)
         have g':x+step g∈ S:=hp
         have he:=h (show wrap (More N) (x+ step g)∈ Afterglow.Satin.region S N from mem_image_of_mem _ g'); rw [map_add,wrap_step] at he; exact he -- tune region namespace
       · change group.chord (onC N U (x-step g,g))⁻¹ ≤ a
         rw [onC_spec,group.chord_inv]; apply p
         · exact h (mem_image_of_mem _ (show x-step g∈ S from by simpa [Y,Step.vec,sub_eq_add_neg] using hp))
         change (wrap _ (x-step g))+ step g∈ T; rw[map_sub,wrap_step, sub_add_cancel]; exact h (mem_image_of_mem _ t)
    rw [travel,List.length_cons]; push_cast
    exact (group.chord_triangle _ _).trans ((add_le_add he (ih _ hp hx)).trans_eq (by ring))
#print axioms walkingFNX
end YM.CF.Buffered.Ballad
end
