import GaugeFieldConstruction.IoneΛL
import GaugeFieldConstruction.LehuaImprovedMars
import GaugeFieldConstruction.ThreeShedPV

/-!
 # Translated letters on shelf three still have elementary letters on shelf four (continuum).
 `DerivativeFontSt` is frame-wide equality of kernels with ANY other insertions.
 -/
set_option autoImplicit false
set_option synthInstance.maxSize 10050
noncomputable section
namespace YM.GaugeFieldConstruction.Ember.Volumetric
open Calibration Raw Cauchy Phys Apit Stage Fathom Function Set Filter Module Empire Hulse Salam Palace
open Floor Carat Dawn Sailing Angles Points Bulb Analysis MeasureTheory Complex Boundary Finset
open NSF.Boundary
open scoped Topology BigOperators Matrix.Norms.Frobenius ComplexConjugate ContDiff Classical
attribute [local instance] iG iF iX iU iT2 iW2 iV iS
variable {n:ℕ}{S:City}{P:Axis→Empire.Across}{L:Sheds S P}{Cu:Supplies L}{u:ℕ→Carat}
variable (p:Ticket u Cu)(Y:Hulse.AreaQc S)
open FirstPackMars
abbrev GlyphSt:=Axis→UV three→ₗ[ℂ]UV four
abbrev OverprintsSt (X:Axis→Across)(U:GlyphSt):Prop:=∀ a,(Calibration.lift four) ∘ₗ U a=X a ∘ₗ Go3PV
abbrev CrayonSt (Q:ChefUL (X:=ΧiMars))(U:GlyphSt) (a:Axis)(k:Fin n)(F:Fin n→ΧiMars)(A:UV three): Prop:= Set.EqOn (Q n (Function.update F k (U a A))) (Analysis.D (mirDirYL k a) (Q n (Function.update F k (Go3PV A)))) (conf n)
abbrev DerivativeFontSt (Q:ChefUL (X:=ΧiMars))(U:GlyphSt):Prop:=∀ n (k:Fin n) F a,∀ A:UV three, CrayonSt Q U a k F A
private abbrev TerraCostSt (n:ℕ) (F:Fin n→ΧiMars): Points n→ℂ:= TerraMars p Y F
-- note maybe CostsYL defined in Shower; use equivalent ChefUL
lemma TerraGlyphSt (U:GlyphSt)(h:OverprintsSt P U): DerivativeFontSt (TerraCostSt p Y) U:=by
 intro n k F a A; let f:=Function.update F k (U a A);let g:=Function.update F k (Go3PV A); let v:= Calibration.lift four ∘ F
 have he: ContinuousOn (Analysis.D (mirDirYL k a) (TerraMars p Y g)) (conf n) := fun x hx => (dSmooth (m:=∞) (TerraAt p Y g x hx) _ (by simp)).continuousAt.continuousWithinAt
 apply (YM.Test.unique_kernel (TerraSm p Y f).continuousOn he).mp
 intro t; change t.applyTo (TerraMars p Y f) = t.applyTo (Analysis.D _ (TerraMars p Y g)); rw [← BillingMars,currentMars,←BillingMars]
 unfold f g; rw [pieceLMars,pieceLMars,show Calibration.lift four (U a A)= P a (Go3PV A) from LinearMap.congr_fun (h a) A,L.money,YM.GaugeFieldConstruction.Fathom.pays]; rfl

lemma TerraDueSt (U:GlyphSt)(h:OverprintsSt P U)(H:FirstPackMars p Y) (W:NSF.Table.Hierarchy (BellTableMars p Y))(b:Bulb)(F:Fin n→ΧiMars)(A:UV three)(k:Fin n)(a:Axis)(x:Points n)(v:BreatherMars b k x): TerraMars p Y (Function.update F k (U a A)) x = ∑ i:Axis,raysCostYL b i (TerraMars p Y (Fin.cons (TotalStarsMars p i a) (Function.update F k (Go3PV A)))) x:= (TerraGlyphSt p Y U h n k F a A v.bounds).trans (OrbitFluxMars H W k _ x b v a)

#print axioms TerraDueSt
end YM.GaugeFieldConstruction.Ember.Volumetric
