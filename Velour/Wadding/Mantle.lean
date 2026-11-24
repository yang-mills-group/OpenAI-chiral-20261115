import Velour.Wadding.Wadding
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 5000
set_option maxHeartbeats 1250000
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




open Aria Casting Six OS.Semigroup OS.Semigroup.Balloon
open MacroGrid SatinNucleus SatinJets DoseTravel Set



open YM.Velour
open Boundary Probe

variable {F : SampleDose}
abbrev SampleDose.l1 (A:SampleDose):=∫p:Vantage, ‖A.val p‖

lemma dyed_compact {H:Hilbert}(v:Vantage→H):
 HasCompactSupport (fun p=>(F.val p:ℂ) • v p):=
 F.budget.mono (fun p t h=> t (by
   change F.val p=0 at h
   change (F.val p:ℂ) • v p=0
   rw [h,Complex.ofReal_zero,zero_smul]))

lemma velvet_integrable {H:Hilbert}(F:SampleDose){v:Vantage→H}(h:Continuous v):
 Integrable (fun p=>(F.val p:ℂ) • v p):=
   ((Complex.continuous_ofReal.comp F.smooth.continuous).smul h).integrable_of_hasCompactSupport (dyed_compact v)


section cloak
variable {H:Hilbert}(X:Vantage→H.Op)
    (h:∀v:H, Continuous (fun p=>X p v))(c:ℝ)(r:0≤c)(g:∀p, ‖X p‖≤c)(F:SampleDose)

def cloakₗ : H.space→ₗ[ℂ]H.space where
 toFun v:= ∫p, (F.val p:ℂ) • X p v
 map_add' v y:=by
     simp_rw [map_add,smul_add,integral_add (velvet_integrable F (h v)) (velvet_integrable F (h y))]
 map_smul' a v:=by
     simp_rw [map_smul, smul_comm _ a, integral_smul]
     rfl

include g in
lemma cloak_charged (v:H): ‖cloakₗ X h F v‖ ≤ SampleDose.l1 F * c * ‖v‖:=by
  rw [SampleDose.l1, ←integral_mul_const, ←integral_mul_const]
  refine norm_integral_le_of_norm_le (((F.smooth.continuous.integrable_of_hasCompactSupport
     F.budget).norm.mul_const c).mul_const _) (Eventually.of_forall fun p=>?_ )
  rw [norm_smul, Complex.norm_real, mul_assoc]
  exact mul_le_mul_of_nonneg_left (((X p).le_opNorm v).trans
    (mul_le_mul_of_nonneg_right (g p) (norm_nonneg _))) (norm_nonneg _)
def cloak:H.Op:= (cloakₗ X h F).mkContinuous (SampleDose.l1 F*c) (cloak_charged X h c g F)
end cloak


lemma vet_heat {H:Hilbert}{j:Axis}(S:OS.Semigroup H j)
  {G:Type*}[TopologicalSpace G]{d:G→ℝ}{v:G→H} (p:Continuous d)(g:Continuous v):
 Continuous (fun z=>S.E (d z).toNNReal (v z)):= by
  apply continuous_iff_continuousAt.mpr
  intro z; exact firmly _ zero_le_one (Eventually.of_forall fun _=> S.shrinks _)
    (((S.continuousE (v z)).comp (continuous_real_toNNReal.comp p)).tendsto z)
    (g.tendsto z)

variable (P:Spine)(j:Axis)(x:P.Spectrum0 j)
local notation "ℋ"=> P.ColorHil j x
local notation "𝓗"=> P.ManyF j x
local notation "Σ₀"=> P.physicalEnergy j x
local notation "Σ₁"=> P.seasons j x

local notation "E₀"=> (Σ₀).E
local notation "E₁"=> (Σ₁).E
local notation "ϕ"=> P.enter j x
local notation "ρ"=> P.wealth j x
local notation "W"=> P.cartage j x
local notation "Ξ"=> P.truck j x

variable (d l r:ℝ)
/-- Artist at real-position y strictly between walls l and r, when we can
spend d on both sides without going out. X price d in ManyF. Off this
paid region used only with weight zero. -/
def cloaked (X:(𝓗).Op)(y:Vantage):(𝓗).Op:=
 W y * ((Σ₁).pad (y j-l-d) (r-y j-d) X) * W (-y)
lemma cloaked_le(X:(𝓗).Op)(y:Vantage):
 ‖P.cloaked j x d l r X y‖≤ ‖X‖:=
  (norm_mul_le ..).trans ((mul_le_of_le_one_right (norm_nonneg _) (P.cart_pay j x (-y))).trans
  ((norm_mul_le ..).trans ((mul_le_of_le_one_left (norm_nonneg _) (P.cart_pay j x y)).trans
       ((Σ₁).pad_le _ _ X))))


lemma cloaked_cont(X:(𝓗).Op) (v:𝓗):
 Continuous (fun y=> P.cloaked j x d l r X y v):=by
  simp_rw [cloaked,pad_val,mul_apply_eq_comp]
  exact P.caravan _ _ _ _ continuous_id (vet_heat _ (by fun_prop)
    (X.continuous.comp (vet_heat _ (by fun_prop) (P.caravan j x _ _ continuous_neg continuous_const))))

def flounce (X:(𝓗).Op)(B:SampleDose): (𝓗).Op:=
 cloak _ (P.cloaked_cont j x d l r X) _ (P.cloaked_le j x d l r X) B
lemma flounce_act(X:(𝓗).Op)(B:SampleDose)(y:𝓗):
 P.flounce j x d l r X B y=∫p,(B.val p:ℂ) • P.cloaked j x d l r X p y:=rfl

lemma flounce_price(X:(𝓗).Op)(B:SampleDose):
 ‖P.flounce j x d l r X B‖≤ SampleDose.l1 B * ‖X‖:=
  ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (integral_nonneg fun _=>norm_nonneg _) (norm_nonneg _)) (cloak_charged _ (P.cloaked_cont j x d l r X) _ (P.cloaked_le j x d l r X) B)
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection

