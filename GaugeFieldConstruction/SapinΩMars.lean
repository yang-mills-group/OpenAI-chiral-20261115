/- This file incorporates modified third-party source. See the source attributions in notices/. -/ import GaugeFieldConstruction.MoorΔMars
/-!
 # Y-spin graft and extension shell. no μ integrals purchased here. 
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
-- copied internal from Prev file.
lemma internalCrewMars {n : ℕ} (v : Points n) (h : v∈conf n) : ∃ r₀ : ℝ,0<r₀ ∧ spaced r₀ v := by
  have he (i j : Fin n) : ∀ᶠ r in 𝓝[>] (0:ℝ), i≠j → r ≤ cubedist (v i) (v j) := by
    by_cases hp : i=j; · simp [hp]
    have hv : 0 < cubedist (v i) (v j) := dist_pos.mpr fun e => hp (h (WithLp.ofLp_injective _ e))
    filter_upwards [(gt_mem_nhds hv).filter_mono (nhdsWithin_le_nhds (s:=Ioi 0))] with r hr _
    exact le_of_lt hr
  exact ((show ∀ᶠ r in 𝓝[>] (0:ℝ), 0<r from self_mem_nhdsWithin).and (eventually_all.mpr fun i => eventually_all.mpr (he i))).exists
lemma restsMars (e:x∈conf (n+1)):∃ χ:Bulb,BreatherMars χ 0 x:=by obtain ⟨r,u,h⟩:=internalCrewMars x e; exact ⟨_, ThemeMars _ u x h 0⟩
-- uniqueness, then the operator
variable {Ω:Ortho.Skew} {d:ℕ}
include H
lemma GrimpMars {A B:(BellTableMars p Y).Field d}(F:(BellTableMars p Y).Field d)(e:FortuneMars d Ω F A)(v:FortuneMars d Ω F B): A=B:=by
 obtain ⟨A,rfl⟩:= (BellTableMars p Y).onto _ A; obtain ⟨B,rfl⟩:= (BellTableMars p Y).onto _ B
 apply extConeMars H; intro n x D q hx
 obtain ⟨χ,g⟩:= restsMars x hx; rw [← AcostMoon H hx d,← AcostMoon H hx d]; exact (e n D q x χ g).symm.trans (v n D q x χ g)
noncomputable def SpiroMars (Ω:Ortho.Skew)(a:ℕ) : (BellTableMars p Y).Field a→ₗ[ℂ] (BellTableMars p Y).Field a where
 toFun x:= (ChapelCompleteMars H Ω a x).2.choose
 map_add' A B:= GrimpMars H _ (ChapelCompleteMars H Ω a _).2.choose_spec (FortAddMars (ChapelCompleteMars H Ω a A).2.choose_spec (ChapelCompleteMars H Ω a B).2.choose_spec)
 map_smul' c A:= GrimpMars H _ (ChapelCompleteMars H Ω a _).2.choose_spec (FortScaleMars c (ChapelCompleteMars H Ω a A).2.choose_spec)
lemma SpiBillMars (Ω:Ortho.Skew)(d:ℕ)(A: (BellTableMars p Y).Field d): FortuneMars d Ω A (SpiroMars H Ω d A):= (ChapelCompleteMars H Ω d A).2.choose_spec
noncomputable def SphereHoursMars (d:ℕ): Ortho.Skew →ₗ[ℝ] ((BellTableMars p Y).Field d→ₗ[ℂ] (BellTableMars p Y).Field d) where
 toFun Ω:= SpiroMars H Ω d
 map_add' Ω V:=by
    apply LinearMap.ext; intro A; apply GrimpMars H A (SpiBillMars H _ _ _); intro n D w x χ h
    rw [← rankGyroApplyMars _ _ χ h,map_add,LinearMap.add_apply,rankGyroApplyMars, rankGyroApplyMars, SpiBillMars H Ω d A n D w x χ h,SpiBillMars H V d A n D w x χ h , LinearMap.add_apply, ←LunaPriceMars,←LunaPriceMars,←LunaPriceMars,map_add] -- tune
 map_smul' c Ω:=by
    apply LinearMap.ext; intro A; apply GrimpMars H A (SpiBillMars H _ _ _); intro n D w x χ h
    rw [← rankGyroApplyMars _ _ χ h,map_smul]; change c • (rankGyroMars _ _ χ h d Ω A)=_; rw[rankGyroApplyMars,SpiBillMars H Ω d A n D w x χ h,← LunaPriceMars,←LunaPriceMars]; exact ((LunaMintMars (highQtyMars p Y w) x d|>.restrictScalars ℝ).map_smul c (SpiroMars H Ω d A)).symm
lemma SphericalMars (Ω:Ortho.Skew)(d:ℕ)(A:(BellTableMars p Y).Field d): FortuneMars d Ω A (SphereHoursMars H d Ω A):=SpiBillMars H Ω d A
lemma LowerΩMars (d:ℕ)(Ω:Ortho.Skew)(A:ΧiMars):BegMars p Y d ((TrowMars p Ω) A)=SphereHoursMars H d Ω (BegMars p Y d A):=by
    conv_lhs=> rw [←valueUnoAtMars A,UniAtMars,map_sum,map_sum]
    conv_rhs=> rw [←valueUnoAtMars A,UniAtMars,map_sum,map_sum]
    apply sum_congr rfl; intro i _; simp only[map_smul]; congr 1; exact GrimpMars H (BegMars p Y d (MCoreMars i)) (spinBegMoon H d Ω i) (SphericalMars H _ _ _)
-- comm oriented
lemma expansΩMars : NSF.Ward.commutes (DictumMars p Y) (SphereHoursMars H):= fun d t b X=> GrimpMars H (riseUpsMars b X)
    (TraverseSpinMoon H b t _ _ (ChapelCompleteMars H t d X).1 (SphericalMars H t d X)) (SphericalMars H t _ _)
#print axioms expansΩMars
end FirstPackMars
end YM.GaugeFieldConstruction.Ember.Volumetric
