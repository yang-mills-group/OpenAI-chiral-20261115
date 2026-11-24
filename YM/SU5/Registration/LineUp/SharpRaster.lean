import YM.SU5.Registration.Ink.RegEu
import YM.SU5.Registration.Affine.Egret
import YM.SU5.Registration.LineUp.Diversion
import YM.Analysis.Multilinear
/-!
 # Raster estimate. Only on truly priced charge stencils & the same sector / height. 
 This is a physical cost equivalent to establishing the angular invariance on generic answers for
 these M10 charges on this x. We did not obtain this estimate here. No estimates on after-rotation
 coarse seams. Recover invariance of those points for THIS Eu price even through ties (no order fixed
 across a rotation). Then can progress with the support/use. This is presently conditional. All quantities are
 real regulator questions before analytic continuation in C.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 3000
set_option maxHeartbeats 700000
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
open Spine
open CF.Velvet CF.Pannier.Chancel
open QuadClock
open Aria Casting MacroGrid Preparation.Yoke Yoke.Travel
open SatinNucleus Six DoseTravel Set

namespace Spine
open _root_.YM.CF.Buffered.Afterglow.Hierarchy
open _root_.YM.CF.Buffered.Afterglow.Hierarchy.LyraBill.Chiffon.Sesame.FlakeNight
open FirstWindows FirstWindows.Chambers FirstWindows.LightBudget

open Aria Casting Six OS.Semigroup OS.Semigroup.Balloon
open MacroGrid SatinNucleus SatinJets DoseTravel Set

open _root_.YM.SatinEdge.RealSheet Boundary Probe
open SatinRegistration
-- Seld valise etc.
open scoped CF.Buffered.Afterglow.Hierarchy.Seld
variable (P : Spine) (x : P.Spectrum0 3)
local notation "ξ" => P.advocate 3 x 3
local notation "H" => P.ManyF 3 ξ
local notation "S" => P.seasons 3 ξ
local notation "D" => radial (P.seasons 3 ξ)
local notation "G" => bands (P.seasons 3 ξ)
local notation "Ω" => P.vacuumEntry x
local notation "ζ" => P.heaven 3 ξ
local notation "κ" => Lead.Clan
open Swatch SatinWFixed
open _root_.YM.Boundary.Probe

open _root_.YM.SatinWFixed Carton
open _root_.YM.SatinWFixed Courts
open Seld.Poin (Each)
universe ν
variable {I:Type ν}{n:ℕ}(Q:I→P.Swatch)(u:∀ i,(Q i).WPermit x 3)
local notation "Λ"=> epaulets I
variable (F:InkWaves (epaulets I))(W:WView (epaulets I))(Hf:InkPort (P.store x Q u) F W) (X:P.Ellis 3 x) (R: Courts (epaulets I))
lemma star_sited {x:Points n}(p:x∈generic n) : StarCluster (Each n) (qua x):=by
 -- Poin.SortApp copied here
 intro a; let k:Fin n→ℝ:= fun i=> x i a; have h:Injective k:=p a
 let R(i j:Fin n):= k i ≤ k j; letI : Std.Total R:= ⟨fun i j=> le_total ..⟩; letI : IsTrans (Fin n) R:= ⟨fun _ _ _ => le_trans⟩; letI : DecidableRel R:= Classical.decRel R; let M:= (Each n).insertionSort R; have u:M.Perm (Each n):= List.perm_insertionSort ..; have he:= u.nodup_iff.mpr ( List.nodup_finRange _); refine ⟨M,u.symm, ?_⟩; apply List.pairwise_iff_get.mpr; intro i j z; exact lt_of_le_of_ne ((List.pairwise_iff_get.mp (show M.Pairwise R from List.pairwise_insertionSort ..)) i j z) (h.ne (( List.pairwise_iff_get.mp he) i j z))
lemma sweep_entrant (q:Points n)(v:Fin n→Λ): axisSweep F v q=F.entrance q v:= by
 have he: Boundary.trace (mon q 0)=Boundary.trace q:=trace_place' ..; unfold axisSweep InkWaves.restricted; rw [he]; change F.F n (Boundary.shift _ _) _ v=F.F n _ _ v
 congr 2; ext1 i; simp [mon, Boundary.shift, YM.Boundary.place,flightTimes]

-- at SAME widths & heights even across both pictures (not legal to do same heights if stencils budget less than asked). charges v as actual LINEAR COMBINATION of school members, with the very same real placements on every summand, so can estimate joint from Hart program in this sector. 
noncomputable abbrev seatPlan (v:Fin n→Λ):= Fintype.piFinset (fun i=>(v i).support)
noncomputable def sigVisit (v:Fin n→Λ) (σ:Fin n→ℕ) (r:Fin n→ Cover) (w:ℕ): P.Test:= ∑ A∈ seatPlan v, (∏ i:Fin n, (v i) (A i)) • P.fullVisit (Each n) (P.school Q ∘ A) σ r w
lemma earn_sig (v:Fin n→Λ) (σ:Fin n→ℕ) (r:Fin n→ Cover) (w:ℕ) : P.sigVisit Q v σ r w∈ enclave P.calibration:= Subalgebra.sum_mem _ fun i _=>Subalgebra.smul_mem _ (P.color_permit (Each n) _ _ _ w) _ -- maybe args/order
-- Ratios. Extra canon common *one* w. x & proper portrait placements.
structure SigReach (v:Fin n→Λ) (q:Points n) (σ:ℕ→Fin n→ℕ) (r:ℕ→Fin n→ Cover) (w:ℕ→ℕ): Prop where
 time3 (i): Tendsto (fun k=>P.laysM (P.vtile (w k) (r k i))) atTop (𝓝 (qua q i))
 prices : ∀ᶠ k:ℕ in atTop, ∀ (A:Fin n→I×Bool), A∈ seatPlan v→ ∀ i:Fin n, ((P.school Q (A i)).fieldA (σ k i)).s ≤ w k

local notation "L"=> Each n
include Hf X
lemma sig_tends (q:Points n)(g:q∈generic n)(h:q∈Wheeled n)(v:Fin n→Λ) {σ:ℕ→Fin n→ℕ} {r:ℕ→Fin n→ Cover} {w:ℕ→ℕ}(t:∀ i,Tendsto (fun k=>σ k i) atTop atTop) (f:P.SigReach Q v q σ r w) :
 Tendsto (fun k=> P.singleState 3 (w k) x (P.sigVisit Q v (σ k) (r k) (w k))) atTop (𝓝 (F.entrance q v)):=by
 let B(i:Fin n): Module.Basis (I×Bool) ℂ (epaulets I):=Finsupp.basisSingleOne; let FD:= F.entrance q; rw [show F.entrance q v =∑ A∈seatPlan v, ((∏ i,(v i) (A i)) • FD (pupil ∘ A)) from ?_]; swap
 · exact Multilabel.expansion B FD v -- defeq?
 simp_rw [sigVisit,map_sum,map_smul]; apply tendsto_finsetSum; intro A hA
 apply Tendsto.const_smul; unfold FD; rw [← sweep_entrant F q]; apply P.stencil_wick x q F W Q u Hf A X h (star_sited g) t (f.time3) (f.prices.mono (fun k u=> u _ hA)) -- args
omit Hf X
open Filter TopologicalSpace
lemma sig_join (v v':Fin n→Λ) (p q:Points n) (σ:ℕ→Fin n→ℕ) (ψ:ℕ→Fin n→ℕ) : ∃ (r r':ℕ→Fin n→ Cover)(w:ℕ→ℕ), Tendsto w atTop atTop ∧ P.SigReach Q v p σ r w ∧ P.SigReach Q v' q ψ r' w:=by
 choose X hX using fun (x:Points n)(i:Fin n)=>P.vantage_approach (qua x i); -- notation?
 let rates (v:Fin n→Λ)(σ:Fin n→ℕ)(w:ℕ):= ∀ A∈seatPlan v,∀ i,((P.school Q (A i)).fieldA (σ i)).s ≤ w; let alongX (r:Points n)(k w:ℕ):= ∀ i:Fin n,∃ q:Cover,P.vtile w q=X r i k; have h₀(x:Points n) (k:ℕ):∀ᶠ w in atTop, alongX x k w:=by
    refine Filter.eventually_all.mpr fun i:Fin n=>?_; filter_upwards [Filter.eventually_all.mpr (fun a:Axis=>P.vwhere («g»:=X x i k) 0 a)] with y p; choose j hj using p; exact ⟨j,funext hj⟩
 have ht(v:Fin n→Λ)(σ:Fin n→ℕ) : ∀ᶠ w in atTop, rates v σ w:= ((seatPlan v).eventually_all).mpr fun i t=> Filter.eventually_all.mpr fun j=> eventually_ge_atTop _
 choose w hw hW₀ hW₁ t t' using fun k=> ((eventually_ge_atTop k).and ((ht v (σ k)).and ((ht v' (ψ k)).and ((h₀ p k).and (h₀ q k))))).exists
 choose r hr using fun k i=> t k i; choose z hz using fun k i=> t' k i; refine ⟨r,z,w,tendsto_atTop_mono hw tendsto_id,⟨fun i=> (hX p i).congr fun k=> congrArg _ (hr k i).symm, Eventually.of_forall hW₀⟩,⟨fun i=> (hX q i).congr fun k=>congrArg _ (hz k i).symm,Eventually.of_forall hW₁⟩⟩

/-- Proposed estimate on *actual normalized prices*. q positions in the same physical units Vantage with clock block convention. Use whole (width, height, pose) vector on this election. Includes estimates even across
 ANY fixed angle/r; ask no uniformity in angle. Does need ALL arity even repeated labels.
 May request simultaneously every γ, only need at x.
-/
def RasterPrice : Prop := ∀ n:ℕ, ∀ (v:Fin n→Λ) (U:SatinWFixed.Frames n) (q:Points n), fairFrame U →
 q∈generic n → q∈Wheeled n → reFrame U q∈generic n → reFrame U q∈Wheeled n →
 ∀ (σ:ℕ→Fin n→ℕ)(r r':ℕ→Fin n→ Cover)(w:ℕ→ℕ), (∀ i,Tendsto (fun k=>σ k i) atTop atTop) → Tendsto w atTop atTop → P.SigReach Q v q σ r w → P.SigReach Q (reSup U R v) (reFrame U q) σ r' w → ∀ ε>0,
 ∀ᶠ k in atTop, ‖P.singleState 3 (w k) x (P.sigVisit Q (reSup U R v) (σ k) (r' k) (w k)-P.sigVisit Q v (σ k) (r k) (w k))‖ < ε
include Hf X
lemma raster_carriages : P.RasterPrice x Q R ↔ R.Carriage F:=by
 constructor
 · intro h n U hU q qg hq xg ph v; let x':=reFrame U q; let v':=reSup U R v; let σ(k:ℕ)(i:Fin n):= k;
   have ht(i:Fin n): Tendsto (fun k=>σ k i) atTop atTop:=tendsto_id; obtain ⟨r,r',w,hw,u₀,u₁⟩:= P.sig_join Q v v' q x' σ σ; let t:= P.sig_tends x Q u F W Hf X q qg hq v ht u₀; let t':= P.sig_tends x Q u F W Hf X x' xg ph v' ht u₁
   let Y:=fun k=> P.singleState 3 (w k) x (P.sigVisit Q v' (σ k) (r' k) (w k)- P.sigVisit Q v (σ k) (r k) (w k)); have hx: Tendsto Y atTop (𝓝 0):=by
      refine Metric.tendsto_nhds.mpr fun ε hε=>?_ ; simp_rw[dist_zero_right]; exact h n v U q hU qg hq xg ph _ _ _ _ ht hw u₀ u₁ ε hε
   apply sub_eq_zero.mp; refine tendsto_nhds_unique (t'.sub t) ?_; apply hx.congr; intro k; exact map_sub ..
 intro h n v U q p' c d a b σ r r' w m t f f' ε hε
 let Y(k:ℕ):= P.singleState 3 (w k) x (P.sigVisit Q (reSup U R v) (σ k) (r' k) (w k) - P.sigVisit Q v (σ k) (r k) (w k)); have hx: Tendsto Y atTop (𝓝 0):=by
    have g:= (P.sig_tends x Q u F W Hf X _ a b (reSup U R v) m f').sub (P.sig_tends x Q u F W Hf X q c d v m f); rw [h n U p' _ c d a b v, sub_self] at g; exact g.congr (fun k=>(show Y k=_ from map_sub ..).symm)
 simpa only [dist_zero_right] using (Metric.tendsto_nhds.mp hx ε hε) -- let def?
omit X Hf
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open YM.CF.Buffered.Afterglow.Tower.VacuumSelection
#print axioms Spine.sig_tends
#print axioms Spine.raster_carriages
#print axioms Spine.sig_join
#print axioms Spine.earn_sig
