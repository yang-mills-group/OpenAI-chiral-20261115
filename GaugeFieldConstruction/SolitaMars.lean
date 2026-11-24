import GaugeFieldConstruction.MirtonΥMars
/-!
 # assembled mean relativistic precursor. still need FirstPackMars and hcap and RP on this actual mean.
-/
set_option autoImplicit false
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
variable (W:Fin n→ (BellTableMars p Y).Tag)(x:Points (n+1))(χ:Bulb)(h: BreatherMars χ 0 x)
variable (H:FirstPackMars p Y)
variable {d:ℕ}(A:(BellTableMars p Y).Field d)
lemma YieldValueMoon (y:Points (n+2))(i j:Axis): (BellTableMars p Y).useAt (BellTableMars p Y) y (Fin.cons ⟨4,CStressMars p Y i j⟩ (Fin.cons ⟨d,A⟩ W))= -(PFoilMoon A W i j y):=by
 change TideLunaMars (-BegMars p Y 4 (p.J i j)) (Fin.cons (upMarkMars d A) W) y= _
 rw [← LunaPriceMars,map_neg,LunaPriceMars]
lemma YardGradMars (i:Axis): NSF.Table.shellGrad (BellTableMars p Y) (CStressMars p Y) χ.f i x W A=ΘMilesMars A W x χ i:=by
 unfold NSF.Table.shellGrad ΘMilesMars; rw [← sum_neg_distrib]; apply sum_congr rfl; intro a _
 simp_rw [YieldValueMoon]; rw [← integral_neg]; apply integral_congr_ae; refine Eventually.of_forall fun y=>?_; dsimp only; rw [coatMars]; -- rfl sign
 simp only[mul_neg,neg_neg,Complex.real_smul]; rfl
lemma YardSpinMars (Ω:Ortho.Skew): NSF.Table.shellSpin (BellTableMars p Y) (CStressMars p Y) χ.f Ω x W A=ΩMilesMars A W x χ Ω:=by
 unfold NSF.Table.shellSpin ΩMilesMars; simp_rw [← sum_neg_distrib]; apply sum_congr rfl; intro j _; apply sum_congr rfl; intro i _; unfold RhythmMars RyeMars WrapMars
 simp_rw [YieldValueMoon]; rw [←integral_neg]; apply integral_congr_ae; refine Eventually.of_forall fun y=>?_; dsimp only; unfold SoilMars; rw [Payroll.angle]; simp only [mul_neg,neg_neg, Complex.real_smul]; rfl
include H
lemma YardScanMars: NSF.Table.StressLaws (BellTableMars p Y) (CStressMars p Y) (DictumMars p Y).deriv (SphereHoursMars H) where
 translation {n} {x} hx q {χ} w b d A:=by
    let X:Bulb:=⟨χ,w.1,w.2.1⟩
    have ht: BreatherMars X 0 x:=by
       refine ⟨hx,w.2.2.1, fun i h=>?_⟩; induction i using Fin.cases with
       | zero=>exact (h rfl).elim
       | succ i=> exact w.2.2.2 i
    exact (YardGradMars q x X A b).trans (WarrantTiltMars q x X ht H A b)
 rotation {n} {x} hx q {χ} w Ω d A:=by
    let X:Bulb:= ⟨χ,w.1,w.2.1⟩
    have ht:BreatherMars X 0 x:=by
       refine ⟨hx,w.2.2.1, fun i h=>?_⟩; induction i using Fin.cases with
       | zero=>exact (h rfl).elim
       | succ i=> exact w.2.2.2 i
    exact (YardSpinMars q x X A Ω).trans (WarrantSpinMars q x X ht H A Ω)
#print axioms YardScanMars
#print axioms expansΩMars
end FirstPackMars
end YM.GaugeFieldConstruction.Ember.Volumetric
