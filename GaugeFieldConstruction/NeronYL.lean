import GaugeFieldConstruction.LehuaImprovedMars
import GaugeFieldConstruction.IvyMajorL
import GaugeFieldConstruction.ArchicleYL
set_option autoImplicit false
set_option maxHeartbeats 240000
set_option synthInstance.maxSize 10050
noncomputable section
namespace YM.GaugeFieldConstruction.Ember.Volumetric
open Calibration Raw Cauchy Phys Apit Stage Fathom Function Set Filter Module Empire Hulse Salam Palace
open Floor Carat Dawn Sailing Angles Points Bulb Analysis MeasureTheory Complex Boundary Finset
open scoped Topology BigOperators Matrix.Norms.Frobenius ComplexConjugate ContDiff Classical
attribute [local instance] iG iF iX iU iT2 iW2 iV iS
variable {n m:ℕ} {S: City} {P:Axis→Across} {L:Sheds S P} {C: Supplies L} {u:ℕ→Carat}
variable {p:Ticket u C}{Y:AreaQc S}
namespace FirstPackMars
variable (H:FirstPackMars p Y) (G:NSF.Table.Hierarchy (BellTableMars p Y))
open Loft
attribute [local instance] floatA floatY
attribute [local instance 30000] topx topg
variable (k:Fin n)(F:Fin n→ΧiMars)(x:Points n)(b:Bulb)(a:Axis)(r:ℝ)
variable (p)
abbrev KarmaYL (i:Axis): Fin (n+1)→ΧiMars:= Fin.cons (TotalStarsMars p i a) F
variable (Y)
noncomputable abbrev habYL {n:ℕ}(F:Fin n→ΧiMars)(x:Points n):= CloudMeanL p Y n x F
lemma habContYL: ContinuousOn (habYL p Y F) (conf n):= (TerraSm p Y F).continuousOn.congr fun _ h=> CoronaPL p Y _ _ h
lemma calm0_YL (h:calmYL k a r x b): BreatherMars b k x:= by simpa [ledgeYL] using h 0 (by simp [α0_YL])
lemma calm1_YL (h:calmYL k a r x b): BreatherMars b k (ledgeYL k a r x 1):= h 1 (by simp [α0_YL]) -- other parameters
variable {p Y}
include H G
lemma PromiseYL (h:calmYL k a r x b): habYL p Y F (ledgeYL k a r x 1)= habYL p Y F x + r • ∑ i:Axis,ScrollOpYL a x b i k r (habYL p Y (KarmaYL p F a i)):=by -- tune parameter order
 let M(i:Axis):Points (n+1)→ℂ:= TerraMars p Y (Fin.cons (TotalStarsMars p i a) F)
 have he:= peakFTC_YL a x b k r h (TerraMars p Y F) M (TerraSm p Y F) (fun i=>(TerraSm p Y _).continuousOn) (fun t v=> OrbitFluxMars H G k F (ledgeYL k a r x t) b (h t v) a)
 rw [show habYL _ _ F _ = _ from CoronaPL p Y F _ (calm1_YL k x b a r h).bounds,show habYL _ _ F x= _ from CoronaPL p Y F x (calm0_YL k x b a r h).bounds,he]
 congr 2
 apply Finset.sum_congr rfl; intro i _; unfold ScrollOpYL; apply integral_congr_ae; refine Eventually.of_forall fun z=>?_ ; exact congrArg (rayPenYL b i z * ·) (CoronaPL p Y _ _ (RΦayHappyYL a x b i k r h z)).symm
-- persistence in calm world from same sum cancellation. No derivative hint required Sx.
lemma StillPointYL (h:BreatherMars b k x): ∑ j:Axis,∑ i:Axis,raysCostYL b i (habYL p Y (Fin.cons (TotalStarsMars p i j) (Function.update F k (TotalStarsMars p j a)))) x=0:=by
 let U(j:Axis):=Function.update F k (TotalStarsMars p j a)
 rw[← TotalDivergenceMars H G k F x h.bounds a]
 apply sum_congr rfl; intro j _; rw[OrbitFluxMars H G k _ x b h j]
 apply sum_congr rfl; intro i _
 let p':Fin (n+1)→ΧiMars:= Fin.cons (TotalStarsMars p i j) (U j)
 change raysCostYL b i (habYL p Y p') x= raysCostYL b i (TerraMars p Y p') x; rw [raysVisitYL,raysVisitYL]; exact integral_congr_ae (Eventually.of_forall fun v=> congrArg (DimYL b i v.val * ·) (CoronaPL p Y p' _ (RoomMars _ _ _ h _ (Bulb.cone b i v.2))))
#print axioms PromiseYL
#print axioms StillPointYL
end FirstPackMars
end YM.GaugeFieldConstruction.Ember.Volumetric
