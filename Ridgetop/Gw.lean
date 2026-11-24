import YM.SU5.Circuit.Lark
import Ridgetop.Origin
import Risa.Warehouse
import Preen.Chey
-- pilot price exactly zero, all. 
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 5000
set_option maxHeartbeats 360000
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
open Aria Casting Set
open scoped Pointwise
namespace MiterT
open _root_.YM.Gleam.Luster.Risa CF.BProof AnalyticBridge.VerifiedReset
open Py.Rate.LocalLimit Py Py.Dyad Papal _root_.YM.CF.Pannier.Chancel Cliplet Precision
variable (P:Spine) (s A:ℕ)(o:Bool→ Cover)(b:Bool)
noncomputable abbrev needleL(d:ℕ)(w:Cover):ℝ:= (pollN P:ℝ)* (4*(girder P d:ℝ))+ 2*↑(nodeC w 3)
local notation "R0" d w=>needleL P d w
local notation "R1" d:max=> ((girder P d):ℝ)
lemma paneLED (d:ℕ)(w:Cover):
 let X:=nodeC (outlookT P d w false)-nodeC (outlookT P d w true);
 ∀ i:Axis, (((X i):ℤ):ℝ) = if i=3 then -needleL P d w else -(pollN P:ℝ)*(4*(idleCar P:ℝ)):=by
 intro X i
 unfold X outlookT; rw [Pi.sub_apply,Int.cast_sub]
 change (nodeC (shuffleT P 0 (swapW w)) i:ℝ) - (nodeC (shuffleT P (spindle P d ( _ )) w) i:ℝ) =_
 rw [cruise_price,cruise_price,fling_price]
 by_cases p:i=3
 · subst i; rw [if_pos rfl,if_pos rfl]; simp only [spindle,if_pos rfl,Pi.zero_apply]; unfold needleL girder; push_cast; ring
 rw [if_neg p,if_neg (Ne.symm p)]; simp only [spindle,if_neg p,Pi.zero_apply]; push_cast; ring
variable {d:ℕ}{w:Cover}(p:Enrolled P d (stairW d) w)
lemma pollN_pos:0<pollN P:=Nat.mul_pos (by decide) P.par.block.property
lemma measure_min(d:ℕ):1≤girder P d:=by unfold girder trailerH; omega
include p
-- L ~ const P * r
lemma needle_span : R1 d ≤ needleL P d w ∧ needleL P d w ≤ (4*(pollN P:ℝ)+2)*(R1 d):=by
 let l:ℤ:=nodeC w 3; obtain ⟨hp,hq⟩:=p.clock; change _≤l at hp; change l≤_ at hq
 have hL: l ≤ (girder P d:ℤ):=by
   refine hq.trans ?_
   unfold girder trailerH; push_cast; have hK : (0:ℤ) ≤ (P.par.R.L.val:ℤ)^P.par.b:=by positivity
   linarith only [hK,Nat.cast_nonneg (α:=ℤ) P.calibration.ℓ] -- nat_int cast nonlinear; try exact by moved.LE
 have hQ:0 ≤l:=by omega
 unfold needleL; change _≤ _ + 2*(l:ℝ) ∧ _ +2*(l:ℝ) ≤_
 have hr : 0 ≤ R1 d:=Nat.cast_nonneg _
 have hd:1≤(pollN P:ℝ):= by exact_mod_cast (pollN_pos P)
 constructor <;> nlinarith only [mul_le_mul_of_nonneg_right hd hr,hr,show (0:ℝ)≤(l:ℝ) by exact_mod_cast hQ, show (l:ℝ) ≤ R1 d by exact_mod_cast hL]
omit p
open CF.Onyx Stationary
-- pointwise gaia convergence
variable {D:ℕ→ℕ}(sD:Tendsto D atTop atTop)(W:ℕ→ Cover)(V:∀ d,Enrolled P (D d) (stairW (D d)) (W d))
include V
lemma needle_pos (q:ℕ):0<needleL P (D q) (W q):=lt_of_lt_of_le (by exact_mod_cast (show 0<girder P (D q) from measure_min P (D q))) (needle_span P (V q)).1
include sD
lemma goWaist:Tendsto (fun q=>needleL P (D q) (W q)) atTop atTop:= tendsto_atTop_mono (f:=fun d=>R1 (D d)) (fun d=>(needle_span P (V d)).1) (tendsto_natCast_atTop_atTop.comp ((measuring_up P).comp sD))
local notation "Oq" d=>outlookT P (D d) (W d)
lemma sewer : Tendsto (fun q=> riseX (needleL P (D q) (W q)) (nodeC (outlookT P (D q) (W q) false)-nodeC (outlookT P (D q) (W q) true))) atTop (𝓝 (-YM.basis 3)):=by
 -- EuclideanSpace homeomorph
 rw [show (𝓝 (-YM.basis 3)) = Filter.comap (@WithLp.ofLp 2 (Axis→ℝ)) (𝓝 (WithLp.ofLp (-YM.basis 3))) from ?_]
 rw [tendsto_comap_iff,tendsto_pi_nhds]; intro a
 let x:=-(pollN P:ℝ)*(4*(idleCar P:ℝ))
 have he:Tendsto (fun q=>x/(needleL P (D q) (W q))) atTop (𝓝 0):=by simpa only [Function.comp_def, ← div_eq_mul_inv,mul_zero] using (tendsto_inv_atTop_zero (𝕜:=ℝ) |>.comp (goWaist P sD W V)).const_mul x
 change Tendsto (fun q=> ((↑((nodeC (outlookT P (D q) (W q) false)-nodeC (outlookT P (D q) (W q) true)) a)):ℝ) / needleL P (D q) (W q)) atTop (𝓝 (- ((YM.basis 3) a)))
 have hv(q):= paneLED P (D q) (W q) a; simp_rw [hv]; by_cases g:a=(3:Axis)
 · subst a; change Tendsto (fun q=> -(needleL P (D q) (W q))/ needleL P (D q) (W q)) atTop _
   have hj : ∀ q,-(needleL P (D q) (W q))/needleL P (D q) (W q)= -(1:ℝ):=fun q=> by rw [neg_div,div_self (needle_pos P W V q|>.ne')]
   simp_rw [hj]; rw [basis_eq]; simpa using tendsto_const_nhds (x:=(-1:ℝ)) -- basis_eq rfl rhs?
 simp_rw [if_neg g]; rw [basis_eq]; simpa [g,x] using he
 exact (PiLp.homeomorph 2 (fun _:Axis=>ℝ)).isInducing.nhds_eq_comap _
#check PiLp.continuous_apply
#check PiLp.homeomorph
#print axioms paneLED
end MiterT
end PledgeT
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
