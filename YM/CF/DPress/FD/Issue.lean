import YM.CF.DPress.FD.Stock.Plane
/-!
# Stronger Roof for D.

 Public descriptor on the whole tag repair draw. Not assertions on any probes with
 *their own* priority dependences. Radius form of finite dependence supplies both
 consultation (Vision with distance bound per link and scout-map input radius) and
 lag (can use these arrays together with the iid group tags). -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
namespace YM.CF.DPress.FD
open Function Filter Lattice Spire Skye Cash Deck MeasureTheory SU Lat Finset Wilson Laurent OrderF BasicIid Spoke Gear Star
open Cube (More Guard)
open scoped Topology BigOperators ENNReal NNReal Classical Matrix.Norms.Frobenius
attribute [local instance] Gauge.frobInner
variable {n:Side}{u t:ℝ}{k r:ℕ}
def Firm (P:Orbit n→Pane n)(u:ℝ)(r:ℕ): Prop := ∃ d:ℕ,100*d ≤ r ∧ ∃ (t:ℝ) (I:Type)(_f:Fintype I), ∃ (X:Scout I n u t d), let _mI : MeasurableSpace I := ⊤; ∀ Y: Pane n, (depot n).map (fun y=>P (Y,y)) = ((Coral n).prod X.V.c.PM).map (uncurry (fairly X Y))
theorem booth (h:0<t)(a:ℝ)(x:0<a) :∃ u:ℝ, 0<u∧ u ≤ a ∧ ∃ r s:ℕ,∀ n:Side,s<(More n).val→∃ P,Roof n u t r P ∧ Firm P u r:=by
 obtain ⟨b,e,p⟩:= Skye.taxon h; obtain ⟨d,S,u,z,y,V⟩:= Turf.scale_S e a x; refine ⟨u,z,y,100*d,S,fun n v=>?_⟩; obtain ⟨I,f,X⟩:= V n v; obtain ⟨X⟩:=X; letI:MeasurableSpace I:=⊤; letI:MeasurableSingletonClass I:= ⟨fun _=>trivial⟩; obtain ⟨g,t,v⟩:= Seed.uniform (n:=n) X.V.c; exact ⟨ray X g (100*d), ray_troof X g t (by omega) _ (p n), d,le_rfl,b,I,f,X,fun A=> Star.reality X g A t v le_rfl⟩
#print axioms booth
end YM.CF.DPress.FD
