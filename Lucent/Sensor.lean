import Lucent.Duomo
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4500
set_option maxHeartbeats 500000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry

open TopologicalSpace
namespace Spine
open Lamour.Bridge.Celeste
open Lamour.Bridge.Celeste.Morn
open Py.Rate.LocalLimit.Papal (Weaver household)
open TopologicalSpace Tapestry.Exhibition

open Spine Preparation.Yoke Lucent EmberWind
variable (P:Spine)
local notation "Ξ" => household (P.calibration)
local notation "φ" => P.groundZero 3
local notation "Kₚ" => P.calibration

open Ballad Arity Story Hiro
namespace Carillon
open Preparation.Yoke.Jewel
variable {a:ℝ}(e:0<a)
variable (u v:Staff)(b:ℕ)(ρ t:ℝ)(A:Finset Cover)(K:Calibration)
def dlink (W:Staff)(b:ℕ)(ρ t:ℝ)(i:Pig):PairsC→ℂ:=(fun x:LinksC=>(mug.coord i (W.docked ρ b t x):ℂ))∘ Prod.fst
def dgMix (u v:Staff)(b:ℕ)(ρ t:ℝ)(z:ℂ):PairsC→ℂ:= z • ∑i:Pig, dlink u b ρ t i * dlink v b ρ t i


lemma dg_pure {I:Type}(W:I→Staff)(j l:I)(z:ℂ):z •household K (kite b ρ t W (Arity.G j l))=scalar K (dgMix (W j) (W l) b ρ t z):=by
 funext m x; change z • dream _ W (Arity.G j l) (volley _ W _ _ _ x.1) = dgMix _ _ _ _ _ z _ •_
 rw [g_beats]
 simp only [dgMix, dlink, Pi.smul_apply, Pi.mul_apply,Finset.sum_apply, Function.comp_apply,Prod.map_apply,mug_eq,Staff.antenna]
 rw [real_inner_comm,EuclideanSpace.inner_eq_star_dotProduct]
 simp [dotProduct, smul_smul, volley,Staff.antenna]

lemma dg_skin(w:ℕ)(h:u.Pays b w)(p:v.Pays b w)(e:u.skyRent b⊆A)(d:v.skyRent b⊆A)(z:ℂ):
    Coeff true A (dgMix u v b ρ t z):=by
 have hv(i:Pig):Coeff true A (dlink u b ρ t i * dlink v b ρ t i):=
   Sound.tone ((u.docker ρ h t i).mono e) ((v.docker ρ p t i).mono d)
 have ht(B:Finset Pig):Coeff true A (∑ i∈B,dlink u b ρ t i * dlink v b ρ t i):=by
   induction B using Finset.induction_on
   · rw [Finset.sum_empty]; exact ⟨fun q=>by contradiction,Girt.rite_c _,fun _ _ _ _=>rfl⟩
   next i W p ih=> rw [sum_insert p]; exact ⟨fun q=>by contradiction,Girt.kitE _ _ (· + ·) (by fun_prop) (hv i).env ih.env,
      fun _ _ r s=> congrArg₂ (α:=ℂ) (β:=ℂ) (·+·) ((hv i).locus _ _ r s) (ih.locus _ _ r s)⟩
 change Coeff true A ((fun _:PairsC=>z)*_)
 exact Sound.tone ⟨fun q=>by contradiction,Girt.rite_c _,fun _ _ _ _=>rfl⟩ (ht _)

variable (R:ℝ){I:Type}(W:I→Staff)(w:ℕ)(i j k:I)
lemma lodgeG (h:(W i).Pays b w)(p:(W j).Pays b w)(e:(W i).skyRent b⊆A)(d:(W j).skyRent b⊆A):
 let F:=household K (qr W ρ R t (Arity.G i j) 2 0 b)
 (∃ x:PairsC→ℂ,Coeff true A x ∧ F=scalar K x):=by
 exact ⟨_,dg_skin (W i) (W j) b ρ t A w h p e d _,dg_pure b ρ t K W i j _⟩
lemma lodgeV (p:(W i).Pays b w)(e:(W i).skyRent b⊆A):
 let F:=household K (qr W ρ R t (Arity.V i) 1 1 b)
 F=maxZoom R 1 1 •household K ((W i).rungWeave ρ b t) ∧ InTest K true A false F :=by
 unfold qr; rw [v_returns]
 exact ⟨rfl,(((W i).letterBudget ρ K t p).mono e).smul _⟩

lemma lodgeD(z:Window.Family)(p:(W i).xo∈A):
 let F:=household K (qr W ρ R t (Arity.D z i) 0 1 b)
 F=maxZoom R 0 1 •household K (SitSpin.raw (W i).u z (W i).spin.1 (W i).spin.2) ∧ InTest K true A false F :=by
 unfold qr; rw [d_returns]; exact ⟨rfl,(((SitSpin.voice z (W i).u (W i).spin.1 (W i).spin.2).1.narrow K).widen.mono (singleton_subset_iff.mpr p)).smul _⟩
