/- This file incorporates modified third-party source. See the source attributions in notices/. -/ import GaugeFieldConstruction.SolitaMars
import GaugeFieldConstruction.StyriaRel.YM.Next.ROTATIONS.Route
/-!
 # actual M4--7. axis-orth angular from unselected hierarchy resources supplied.
 Velocity Lemmas adapted from project/YM/Work/A08.lean
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
variable (H:FirstPackMars p Y) (G:NSF.Table.Hierarchy (BellTableMars p Y))
include H G
lemma coalTurnMars: NSF.Ward.Collinear (DictumMars p Y) (SphereHoursMars H) := fun a _ K q x hx hp=> NSF.Outer.fullTurn _ G (DictTiltMars H) (DictRollMars H) _ _ _ ⟨CNetMars H,DrawRawMars H, YardScanMars H⟩ x hx q a hp K
-- include G may need due linter auto binder
lemma allTurnMars {x:Points n}(hx:x∈conf n): NSF.Ward.Still (DictumMars p Y) (SphereHoursMars H) x:= NSF.Ward.global (BellTableMars p Y) G (DictumMars p Y) (SphereHoursMars H) (DictTiltMars H) (expansΩMars H) (coalTurnMars H G) x hx
omit H G
/-- The simultaneous orbital velocityMars on all n positions. -/
def velocityMars (u : Ortho.Skew) : Points n →L[ℝ] Points n := LinearMap.toContinuousLinearMap {
  toFun x := points fun i => M4.move u.val (x i)
  map_add' x y := by
    ext1 i
    exact map_add (Matrix.toEuclideanLin u.val) (x i) (y i)
  map_smul' c x := by
    ext1 i
    exact map_smul (Matrix.toEuclideanLin u.val) c (x i) }

lemma velocityMars_apply (u : Ortho.Skew) (x : Points n) (i : Fin n) :
    velocityMars u x i = M4.move u.val (x i) := rfl

lemma velocityMars_directions (u : Ortho.Skew) (x : Points n) :
    velocityMars u x = ∑ i, ∑ b : Axis, M4.move u.val (x i) b • Points.direction i b := by
  ext1 i
  rw [velocityMars_apply]
  simp [WithLp.ofLp_sum, Finset.sum_apply, Points.direction, Pi.single_apply, smul_ite]
  ext1 j
  simp [WithLp.ofLp_sum, Finset.sum_apply]

abbrev sentronMars (i:ΧiMars): (BellTableMars p Y).Tag:=⟨4,BegMars p Y 4 i⟩
-- equality on generators
abbrev τBlankMars (w:Fin n→MariaMars): (LabelsMars fun _:Fin n=> 4):=fun i=> IndexMars 4 (w i, TrailBlankMars 4)
lemma MaskBlankMars (w:Fin n→ MariaMars) (i): maskMars (d:=fun _=> 4) (τBlankMars w) i= (w i,TrailBlankMars _):=Equiv.symm_apply_apply .. -- tune
lemma τEmptyMars (w:Fin n→MariaMars): τGuideMars (d:=fun _=>4) (τBlankMars w)= []:=by
 unfold τGuideMars LineMars; simp_rw [MaskBlankMars]; have hv (i: Fin n): railMars i (TrailBlankMars 4)= []:=rfl
 simp_rw [hv]; simp -- tune
include H
lemma TradedMintMars (w:Fin n→MariaMars)(x:Points n)(hx:x∈conf n): NSF.Ward.disc (sentronMars (p:=p) (Y:=Y) ∘ MCoreMars ∘ w) x= TerraMars p Y (MCoreMars ∘ w) x:=by
 let T:= BellTableMars p Y
 let W:= TiesMars (fun _: Fin n=>4) (τBlankMars w)
 rw [NSF.Ward.disc,show sentronMars (p:=p) (Y:=Y) ∘ MCoreMars ∘ w=T.classTokens ∘ W from ?_] -- tune
 · rw[T.at_project _ (SymHallMars H) (fun _=>le_rfl) hx, TiesPriceMars]; unfold ChartPriceMars; rw[τEmptyMars]; refine congrArg (fun u=>TerraMars p Y u x) (funext fun i=>?_); simp only [τCoreMars,MaskBlankMars, comp_apply]
 funext i; apply congrArg (fun z=> (⟨4,z⟩:T.Tag)); exact MonetArcMars H ..
lemma SavedMintMars (F:Fin n→ΧiMars)(x:Points n)(hx:x∈conf n): NSF.Ward.disc (sentronMars (p:=p) (Y:=Y) ∘ F) x = TerraMars p Y F x:=by
 let T:=BellTableMars p Y
 let U:= (T.classMoment T (fun _ : Fin n=>4) x).compLinearMap fun _=> BegMars p Y 4
 let A:=linearGownMoon p Y x hx
 let f(i:Fin n)(j:MariaMars):=valueUnoMars (F i) j • MCoreMars j
 have he:F=fun i=>∑ j:MariaMars,f i j:=funext fun i=>by rw[← UniAtMars, valueUnoAtMars] -- tune
 change U F=A F; rw[he]; simp_rw [MultilinearMap.map_sum]; apply sum_congr rfl; intro i _; unfold f; simp_rw [MultilinearMap.map_smul_univ]; congr 1 -- tune
 exact TradedMintMars H _ _ hx
include G
lemma SciTurnMars (F:Fin n→ΧiMars)(x:Points n)(hx:x∈conf n)(K:Ortho.Skew):D (velocityMars K x) (TerraMars p Y F) x = - ∑ i, TerraMars p Y (update F i (TrowMars p K (F i))) x:=by
 let W:=DictumMars p Y; let q:= sentronMars (p:=p) (Y:=Y) ∘ F
 rw [GermD _ (((conf_open _).eventually_mem hx).mono (fun i h=> (SavedMintMars H F i h).symm)), velocityMars_directions]
 have hi i b : fderiv ℝ (NSF.Ward.disc q) x (Points.direction i b)=NSF.Ward.disc (update q i (NSF.Ward.rise W b (q i))) x:= NSF.Ward.fromD W G (DictTiltMars H) hx i b q
 change D _ (NSF.Ward.disc q) x= _; simp_rw [D,map_sum,map_smul,hi]
 have h:=allTurnMars H G hx q K; unfold NSF.Ward.angular at h; rw [sum_add_distrib] at h
 refine eq_neg_of_add_eq_zero_right (show _=0 from ?_) -- order
 have he(i:Fin n): TerraMars p Y (update F i (TrowMars p K (F i))) x= NSF.Ward.disc (update q i (NSF.Ward.turns (SphereHoursMars H) K (q i))) x:=by
    rw [←SavedMintMars H _ _ hx]; congr 1
    funext j; by_cases l:j=i
    · subst j; simp only[comp_apply, update_self]; apply congrArg (fun z=> (⟨4,z⟩:(BellTableMars p Y).Tag)); exact LowerΩMars H _ _ _
    simp only [comp_apply,update_of_ne l]; rfl
 simp_rw [he]; exact h
#print axioms SciTurnMars
end FirstPackMars
end YM.GaugeFieldConstruction.Ember.Volumetric
