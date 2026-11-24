import SatinFixedContrastNovember4

import SatinThinCanvas
import SatinThinMaze

/-! # CP12 Coalition: applying the metering -/
set_option autoImplicit false
set_option maxHeartbeats 350000
set_option synthInstance.maxSize 28000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance Lamour.Bridge.Celeste Designs Twah Prototype
open Lamour.Bridge.Celeste.Morn
namespace Spine
open Aria Casting Six OS.Semigroup.Balloon


open MacroGrid SatinNucleus
variable (P:Spine)(x:P.Spectrum0 3)(j:Axis)
local notation "ξ"=> P.advocate 3 x j
variable (f r n:ℕ) (A:Coalition) (v:ℕ→ℕ)(u:StrictMono v)(a:ℕ→ℝ)
local notation "V" k:max=>v (n+k)
local notation "F" i:max=> P.basePlay x f i
-- sum with max and base n
abbrev parliament (A:Coalition)(v:ℕ→ℕ) := max (v n) (A.voters.sup (fun k=>v (n+k)))
local notation "s₀"=> parliament n A v
local notation "U"=> (F (v n)).zoom P s₀
local notation "Fh"=> fun k:ℕ=> P.basePlay x f (V k)
private lemma admissible_wh (k:ℕ)(h:k∈ A.voters): (F (V k)).s ≤ s₀:= le_trans (le_sup (f:=fun k=>v (n+k)) h) (le_max_right ..)
lemma base_wg : bell (timeMesh P.par) s₀ ((U) j) = P.roomy * P.macroStep (v n):= ((F (v n)).zoom_bell P j s₀ (le_max_left ..)).trans (P.play_width x f (v n) j)
private lemma base_wf (p q:ℕ)(h:p≤ q) : P.macroStep q ≤ P.macroStep p:= by
 have he: (1:ℝ) ≤ (P.par.R.L.val:ℝ):=by exact_mod_cast P.par.R.L.property
 rw [← P.daysF q p h]; exact le_mul_of_one_le_left (P.macroStep_pos _|>.le) (one_le_pow₀ he)
local notation "A'"=> fun (k:ℕ) => A.w k * (P.rewardK f r * a (n+k))
include u in
private lemma admissible_zoom(k:ℕ)(h:k∈ A.voters)(d:Axis): (F (V k)).zoom P s₀ d≤ (U) d:=by
 rw [P.zoom_check _ _ _ _ (admissible_wh P x f n A v k h),P.base_wg,P.play_width]; gcongr; exact P.base_wf _ _ (u.monotone (by omega)) -- gcongr may require 0
noncomputable def pleading (u:StrictMono v): P.Apron:= P.canvas Fh A.voters U s₀ (fun j=> (F (v n)).zoomP P j s₀) (admissible_wh P x f n A v) (admissible_zoom P x f n A v u) (fun i=>( (A.w i * (P.rewardK f r * a (n+i)) : ℝ) :ℂ))
local notation "B" A:max=> P.pleading x f r n A v a u -- check order
lemma pleading_p(p:ℝ)(l:List Axis)(h:P.roomy * P.macroStep (v n) ≤ p): P.beamRaw j x ((B A).pivot P l) p= ∑ i∈ A.voters, (((A.w i * (P.rewardK f r * a (n+i)) : ℝ) : ℂ)) • P.beamRaw j x ((F (V i)).pivot P l) p:= P.pivot_exact j x Fh A.voters (U) (s₀) _ _ _ (A') l p ((P.base_wg x j f n A v).le.trans h) -- check args!
lemma pleading_w : (B A).realWidth P j= P.roomy * P.macroStep (v n):= P.base_wg x j .. -- check
lemma pleading_g : P.singleState 3 (B A).s x (B A).F=0:=by
 let s:= parliament n A v; change P.singleState 3 s _ (canvas ..).F=_; rw [P.canvas_gain]; exact sum_eq_zero fun i _=> mul_eq_zero_of_right _ (P.origin_act x f (V i)) -- change canvas notation unresolved
lemma pleading_b : P.birthF 3 (B A).s (B A).F:=by
 let s:= parliament n A v; let f'(i:ℕ):= (((A') i:ℝ):ℂ); have he(i:ℕ)(y:i∈ A.voters): P.birthF 3 s (f' i • (F (V i)).full P s):= P.birthScaleJ 3 s (f' i) (P.rig 3 (V i) s (P.base_birth x f (V i)) (admissible_wh P x f n A v i y))
 choose! Y ht hx using (show ∀ i,∀ y:i∈ A.voters, ∃ Y:P.ColorHil 3 x,∃ z:P.birthF 3 s (f' i • (F (V i)).full P s), P.viewF 3 x s z=Y from fun i y=> ⟨_,he i y,rfl⟩) -- hx outside
 exact (P.birthSumJ 3 x s A.voters (fun i=>_) Y (fun i y=>⟨ht _ y,hx _ y⟩)).choose
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.pleading_p
