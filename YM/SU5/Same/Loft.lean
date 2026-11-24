import YM.SU5.Same.PhasePrice
/-!
# Identification in the relative-time complex variable. Prospect costs
-/
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 30000
set_option quotPrecheck false
noncomputable section
namespace YM.SatinEdge.RealSheet
open Function Set Filter Metric Finset MeasureTheory Measure Spectral Analysis Boundary Probe Complex
open OS Semigroup
open scoped Topology NNReal ENNReal ComplexOrder InnerProductSpace BigOperators Classical ComplexConjugate
open Multiplier Roy
open CF.Buffered.Afterglow.Tower.VacuumSelection Spine
variable {H:Hilbert}{a:Axis}(S:OS.Semigroup H a)(X Y:ℝ→ H)
local notation "P" => S.ℚmeasure
local notation "θ" => S.ℚmeasure.diagonal
local notation "μ₀" => homeMeasure S X
abbrev paintedFrom (b:E4)(z:ℂ):ℂ:= separationPrice S X Y (b+ z.re • basis a) z.im
lemma at_paint (b:E4)(t:ℝ) : paintedFrom S X Y b ((t:ℂ)*Complex.I)=separationPrice S X Y b t:=by simp [paintedFrom]
abbrev offset (r:ℝ)(z:ℂ) : ℂ:= -Complex.I * z - ↑(r+r)
lemma realtime_shift (x:ℝ)(t:ℂ) : (offset x t).re= t.im-x-x:= by simp [offset]; ring -- z unused
lemma moment_rise (b:E4)(t:ℝ)(u:H): planks S (b+t • basis a) u=(planks S b) (S.edge t u):= by rw [planks, ← S.unit.sends]; exact congrArg (fun y:H=> planks S b y) (DFunLike.congr_fun (Picket.trans_time t S) u)
variable (hX:SatinJets.Positive S X) (hY:SatinJets.Positive S Y)
include hX hY
lemma shade_price(b:E4)(r:ℝ)(v:0<r) {z:ℂ}(t:r+r<z.im):
 paintedFrom S X Y b z= inner ℂ (X r) (planks S b (S.F (offset r z) (Y r))):=by
 let x:= b+z.re • basis a; let s:= z.im/2; have hs:r<s:= by unfold s; linarith only [t]
 let k:=s-r; let d:= k.toNNReal
 have ht:(d:ℝ)=k:= Real.coe_toNNReal _ (sub_pos.mpr hs|>.le)
 let Xr:= X r; let Yr:= Y r
 have he: 0<d:= Real.toNNReal_pos.mpr (sub_pos.mpr hs)
 have hp:Commute (S.E d) (planks S x):=(costT S d).jointly (Picket.story S x)
 calc
    paintedFrom S X Y b z= inner ℂ (S.E d Xr) (planks S x (S.E d Yr)):= congrArg₂ (fun v w:H=> inner ℂ v (planks S x w)) (hX _ _ v hs.le) (hY _ _ v hs.le)
    _= inner ℂ Xr (planks S x (S.E (d+d) Yr)):=by
       rw [S.swing, show S.E d (planks S x (S.E d Yr))= _ from DFunLike.congr_fun hp.eq (S.E d Yr),S.time]; rfl
    _= _:= by
       apply congrArg (inner ℂ Xr); unfold x; rw [moment_rise S b z.re -- unused r
            _, ← S.roots_heat (add_pos he he), ← ContinuousLinearMap.comp_apply (S.edge z.re) , S.along (dur.mpr (add_pos he he)), show duration (d+d)+sideways z.re= offset r z from ?_] -- adjust comp
       apply Complex.ext; · simp only [realtime_shift r,side,add_re]; change ((d+d:ℝ≥0):ℝ)+0=_; rw [NNReal.coe_add, ht]; unfold k s; ring
       simp [offset,sideways,duration] -- tune
lemma shade_holo (b:E4) : AnalyticOnNhd ℂ (paintedFrom S X Y b) {z:ℂ|0<z.im}:=by
 intro z f; let r:= z.im/4; have h:= show 0<z.im from f; have v:0<r:=by unfold r; linarith only [h]
 have t:r+r < z.im:=by unfold r; linarith only [h]
 let F: H.Op→L[ℂ] ℂ:= (innerSL ℂ (X r)).comp ((planks S b).comp (ContinuousLinearMap.apply ℂ _ (Y r)))
 have he: AnalyticAt ℂ (offset r) z:=by unfold offset; exact (analyticAt_const.mul analyticAt_id).sub analyticAt_const
 have hf: offset r z∈ inside:=by change 0<(offset r z).re; rw [realtime_shift r]; linarith only [t]
 refine (((F.analyticAt (S.F (offset r z))).comp (f:=S.F ∘ offset r) ((S.localHeat _ hf).comp he))).congr ?_
 filter_upwards [(Complex.continuous_im.tendsto z).eventually (lt_mem_nhds t)] with i u; exact (shade_price S X Y hX hY b r v u).symm
end YM.SatinEdge.RealSheet
open YM.SatinEdge.RealSheet
#print axioms shade_holo
