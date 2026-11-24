/- This file incorporates modified third-party source. See the source attributions in notices/. -/ import GaugeFieldConstruction.WardPikesMars
import Mathlib.Analysis.Calculus.VectorField
/- Lie extension lemmas adapting repository YM.Work.A08 to our U4 hierarchy. -/
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
variable (H:FirstPackMars p Y) (G:NSF.Table.Hierarchy (BellTableMars p Y))
open Loft
attribute [local instance] floatA floatY
attribute [local instance 30000] topx topg
/-- As vector fields the bracket has the opposite sign to `tick`. -/
private lemma velocityMars_lieBracket (u v : Ortho.Skew) (x : Points n) :
    VectorField.lieBracket ℝ (velocityMars u) (velocityMars v) x = -velocityMars (tick u v) x := by
  have h (a b : M4) (z : E4) : M4.move (a - b) z = M4.move a z - M4.move b z := by
    simp only [M4.move, map_sub, LinearMap.sub_apply]
  rw [VectorField.lieBracket, (velocityMars u).fderiv, (velocityMars v).fderiv]
  ext1 i
  simp only [PiLp.sub_apply, PiLp.neg_apply, velocityMars_apply, tick, h,
    M4.move_mul, neg_sub]



private def orbital (u : Ortho.Skew) (f : Points n → ℂ) (x : Points n) := D (velocityMars u x) f x

private lemma orbital_comm {f : Points n → ℂ} (u v : Ortho.Skew) {x : Points n}
    (hf : ContDiffAt ℝ ∞ f x) :
    orbital u (orbital v f) x - orbital v (orbital u f) x = -orbital (tick u v) f x := by
  have h := VectorField.fderiv_apply_lieBracket hf (by simp; exact WithTop.coe_le_coe.mpr le_top)
    (velocityMars (n := n) v).differentiableAt (velocityMars (n := n) u).differentiableAt
  rw [velocityMars_lieBracket, map_neg] at h
  exact h.symm

private def turnA (Y:Al)(q:Fin n→ΧiMars)(i:Fin n):= update q i (Y four (q i))

private def orbitAll (L':Al)(q: Fin n→ΧiMars)(x:Points n):= ∑ i, TerraMars p Y (turnA L' q i) x
def CrestPikesMars (K:Ortho.Skew)(Z:Al):Prop:=∀ (n:ℕ)(F:Fin n→ΧiMars) (x:Points n),x∈conf n→D (velocityMars K x) (TerraMars p Y F) x= - orbitAll (p:=p) (Y:=Y) Z F x
private lemma orbTwice {x:Points n} (hx:x∈conf n)(u v:Ortho.Skew)(a b:Al)(hu:CrestPikesMars (p:=p) (Y:=Y) u a)(hv:CrestPikesMars (p:=p) (Y:=Y) v b)(q:Fin n→ΧiMars): orbital u (orbital v (TerraMars p Y q)) x=∑ i,orbitAll (p:=p) (Y:=Y) a (turnA b q i) x := by
 have he:orbital v (TerraMars p Y q)=ᶠ[𝓝 x](fun y=> -orbitAll (p:=p) (Y:=Y) b q y):=((conf_open _).eventually_mem hx).mono fun y t=> hv n q y t
 change D (velocityMars u x) _ x=_; rw [GermD _ he]
 calc
    _ = -(∑ i,D (velocityMars u x) (TerraMars p Y (turnA b q i)) x):=by
       unfold D orbitAll; rw [fderiv_fun_neg,fderiv_fun_sum (fun i _=>(TerraAt p Y (turnA b q i) x hx).differentiableAt (by simp))]; simp only[_root_.neg_apply,_root_.sum_apply]
    _=_:=by simp_rw [hu n _ x hx, Finset.sum_neg_distrib,neg_neg]
private lemma crestDouble {x:Points n} (hx:x∈conf n)(a b:Al) (q:Fin n→ΧiMars) :
    (∑ i, orbitAll (p:=p) (Y:=Y) a (turnA b q i) x) - (∑ i, orbitAll (p:=p) (Y:=Y) b (turnA a q i) x) = orbitAll (p:=p) (Y:=Y) ((port Al).l a b) q x := by
  unfold orbitAll
  conv_lhs => rhs; rw [Finset.sum_comm]
  rw [← Finset.sum_sub_distrib]; apply Finset.sum_congr rfl; intro i _
  rw [← Finset.sum_sub_distrib, Finset.sum_eq_single_of_mem i (Finset.mem_univ _)]
  · simp only [turnA, update_self, update_idem, port_at]; let F:= (linearGownMoon p Y x hx).toLinearMap q i
    exact (F.map_sub _ _).symm
  · intro j _ hji
    unfold turnA
    rw [update_of_ne hji, update_of_ne hji.symm, update_comm hji.symm, sub_self]
include H G
lemma pikesInclMars (Ω:Ortho.Skew)(A:Al)(u':Nap (angleT C p.dawn.tect) Ω A) : CrestPikesMars (p:=p) (Y:=Y) Ω A:=by
 induction u' with
 | gen a=> exact fun n F x hx=> SciTurnMars H G F x hx a
 | zero=>
    intro n F x hx; unfold D
    have ht : velocityMars (n:=n) 0 x=0 := by ext1 i; rw [velocityMars_apply]; simp [M4.move]
    rw[ht,map_zero, orbitAll,sum_eq_zero,neg_zero]; intro i _; exact (((linearGownMoon p Y x hx).toLinearMap F i).map_zero)
 | @add x a y b _ _ v q=>
    intro n F W' hx
    have e: velocityMars (n:=n) (x+y) W'= velocityMars x W'+ velocityMars y W':=by ext1 i; simp only[PiLp.add_apply,velocityMars_apply,Submodule.coe_add]; simp only [M4.move,map_add,LinearMap.add_apply]
    rw [e, show D _ _ W'=D _ _ W'+ D _ _ W' from map_add (fderiv ℝ (TerraMars p Y F) W') (velocityMars x W') (velocityMars y W'),v _ F _ hx,q _ F _ hx]
    unfold orbitAll; rw[← neg_add,← Finset.sum_add_distrib]; congr 1; exact sum_congr rfl fun i _=> (((linearGownMoon p Y W' hx).toLinearMap F i).map_add _ _).symm
 | @sm r x a _ h=>
    intro n F W hx
    have e:velocityMars (n:=n) (r • x) W=r • velocityMars x W:=by ext1 i; simp only [PiLp.smul_apply, velocityMars_apply,Submodule.coe_smul]; simp only [M4.move,map_smul, LinearMap.smul_apply]
    rw [e, show D _ _ W=r • D _ _ W from map_smul (fderiv ℝ (TerraMars p Y F) W) r (velocityMars x W), h _ F W hx,smul_neg,orbitAll,orbitAll,Finset.smul_sum]; congr 1
    apply sum_congr rfl; intro i _; exact ((((linearGownMoon p Y W hx).toLinearMap F i).restrictScalars ℝ).map_smul r (a _ (F i))).symm
 | @fork a b c d _ _ v q=>
    intro n F x hx; change orbital _ _ x = _ -- tune
    have he:=orbital_comm a c (TerraAt p Y F x hx); rw [orbTwice hx a c b d v q,orbTwice hx c a d b q v,crestDouble hx b d] at he; rw [he,neg_neg]; rfl
lemma portBillMars (F:Fin n→ΧiMars)(K:Ortho.Skew) (x:Points n)(hx:x∈conf n): Analysis.D (velocityMars K x) (TerraMars p Y F) x = - ∑ i, TerraMars p Y (update F i (p.path.pi K four (F i))) x:= pikesInclMars H G K _ (p.path.paid K) _ F x hx
#print axioms portBillMars
end FirstPackMars
end YM.GaugeFieldConstruction.Ember.Volumetric
