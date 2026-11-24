import SatinFixedContrastNovember4
import SatinThinActual
import SatinThinDogwood
import SatinThinCourt
import SatinThinCivilization
import SatinThinCanvases

/-! # Estimates on the CONTINUOUS cost ambitions for the *excited comparison*.
       Public checkpoint before using it to lower-compare. See Warp.layout_receipt. -/
set_option autoImplicit false
set_option maxHeartbeats 380000
noncomputable section
set_option synthInstance.maxSize 28000
set_option maxRecDepth 2000

namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection

open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase
     MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound
     Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker
     ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy
     Tapestry Germ Alliance Lamour.Bridge.Celeste Designs Twah Prototype
open YM.Stationary (Gaia)
open CF.Onyx (riseX moor)
open Lamour.Bridge.Celeste.Morn

open CF.Velvet CF.Pannier.Chancel
open Spine Pitching.Focus
/-! # Projection milestones, and co-election. Preserve apparatus to compare *same* x & r,c.
      Positivity is of connected gauge-sector lower, NOT yet showing separated
      propagation in physical units (for CP1 raw version see SatinThinFront).
      No color-specific nor vacuum conflict: tag z supplied before; x thereafter fixed. -/
namespace Spine
open Regis.Head.Brecht Regis.Circuit Regis.Head.Garland Papal
open scoped Classical
variable (P:Spine)(R:P.Register)(z:ℕ→ℕ) (d:ℝ)
variable {X:Supplier}{t B:ℝ}{C:ℝ}(u:uniform P R X t B)
-- all simultaneously. further market may choose from this **filter**, not deploy multiple phase picks.
include u in
lemma further_stage (p:∀ᶠ s in atTop,∀ᶠ i in atTop,∀ k:ℕ,(P.run.voyage i).kick ≤ k → s ≤ P.run.uv k → Yoke.ShelterCost C P.run s i k)(w:0<d) : ∃ (c r:ℕ→ℕ), z≤r ∧ ∀ᵐ x∂P.pillars 3,
  (∃ J:P.Ellis 3 x,Spine.Experiment P R c r x J) ∧ ∀ᶠ i in atTop,P.haloCost d (c i) x < Yoke.canonWeight/32:=by
 obtain ⟨r,g,b,p'⟩:= Prototype.outing u keyV keyV_positive z; obtain ⟨f,q⟩:= P.chooseFarther p d (Yoke.canonWeight/32) w (by have ht:=Yoke.focus_positive; positivity); obtain ⟨c,h,t⟩:= choose_gradients fun i=> max (f i) (b i); obtain ⟨e,v,l⟩:= p' c h fun i=> (le_max_right ..).trans (t i)
 refine ⟨c,r,g,?_⟩; filter_upwards [P.many_stars 3 R,l, q c fun i=> (le_max_left ..).trans (t i)] with x j e' X'; obtain ⟨J⟩:=P.ellisP 3 x R; let hu:= P.parting 3 x R (P.homes_weather R 3 (P.all_phases 3 x j)); exact ⟨⟨J,e,e',hu, Spine.final_issues R J hu, P.footway _ J R hu⟩,X'⟩
lemma bill_positive {s:ℕ} (x:P.Spectrum0 3) (h:P.haloCost d s x ≤ Yoke.canonWeight/32) : Yoke.canonWeight/32 ≤ (Yoke.scout P.par d s:ℝ)^8 * (P.pulseQ 3 Yoke.witnessZ s (Yoke.CheckPoint P.par d s) 0 x).re := by
 let b:ℝ:= Yoke.scout P.par d s; let X:= P.pulseQ 3 Yoke.witnessZ s (Yoke.CheckPoint P.par d s) 0 x; let S:= Aster P.run P.period P.cutoff s; have e:‖(b:ℂ)^8*X-(S:ℂ)^4*spectrumℓ Yoke.witnessZ SU.group (YM.basis 3)‖≤ _:= h
 rw [Yoke.focusEst] at e; have ht : -(Yoke.canonWeight/32) ≤ ((((b:ℂ)^8*X-(S:ℂ)^4*(Yoke.canonWeight:ℂ)):ℂ)).re:= (abs_le.mp ((Complex.abs_re_le_norm _).trans e)).1; simp only [← Complex.ofReal_pow,←Complex.ofReal_mul,Complex.sub_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im, zero_mul,sub_zero] at ht; have hg:=pow_le_pow_left₀ (show 0≤(1/2:ℝ) by norm_num) (show (1/2:ℝ) ≤ S from (astral P.run P.period P.cutoff s).1.1) 4; change _≤ b^8*X.re; linarith only [mul_le_mul_of_nonneg_right hg Yoke.focus_positive.le,ht]
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.bill_positive
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.further_stage
