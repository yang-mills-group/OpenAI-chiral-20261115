import Velour.Wadding.Mantle
import SatinThinSweep
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

variable (d l r : ℝ)
local notation "⊥₀"=> P.tableau j x 0
variable (F : SampleDose)(t:ℕ)
local notation "β"=> P.activation t F
local notation "ϵ"=> P.usedGrid t F
local notation "u"=> P.meshPose t
local notation "g"=> P.vtile t
-- y ranges over Cover
def lamSlot(X:(ℋ).Op)(k:Cover): (ℋ).Op:=
 P.charter j x (g k) ((Σ₀).pad (u k j-l-d) (r-u k j-d) X)
def lamina(X:(ℋ).Op): (ℋ).Op:= ∑ k∈ϵ, β k • P.lamSlot j x d l r t X k
-- charge
def package: ℝ :=∑ k∈ϵ,‖β k‖
lemma package_arrives: Tendsto (P.package F) atTop (𝓝 F.l1):= P.thin_activation_abs F


lemma lamina_bound (X:(ℋ).Op):
 ‖P.lamina j x d l r F t X‖≤P.package F t*‖X‖:= by
 unfold package lamina
 rw [Finset.sum_mul]
 refine (norm_sum_le ..).trans (Finset.sum_le_sum fun k e=>?_ )
 rw [norm_smul]
 exact mul_le_mul_of_nonneg_left ((P.charter_pay ..).trans ((Σ₀).pad_le ..)) (norm_nonneg _)

def streakV (v:𝓗)(p:Vantage):ℋ:=
 E₀ (r-p j-d).toNNReal (ϕ (W (-p) v))
def veneer (X:(ℋ).Op)(v:𝓗)(p:Vantage):ℋ:=
 E₀ (p j-l-d).toNNReal (X (P.streakV j x d r v p))
lemma lam_act (X:(ℋ).Op)(v:𝓗)(k:Cover):
 P.lamSlot j x d l r t X k (ϕ v)= Ξ (g k) (P.veneer j x d l r X v (u k)):=by
 rw [lamSlot,charter,pad_val]
 simp only [ContinuousLinearMap.comp_apply,mul_apply_eq_comp]
 rw [P.cart_and]
 have he:P.laysM (-(g k))= -(u k):=by
    ext i
    change ↑(- (g k i))= -(↑(g k i):ℝ)
    simp
 rw [he]
 rfl

lemma streakV_cont(v:𝓗): Continuous (P.streakV j x d r v):=
 vet_heat _ (by fun_prop) ((ϕ).continuous.comp (P.caravan j x _ _ continuous_neg continuous_const))
lemma veneer_cont(X:(ℋ).Op)(v:𝓗): Continuous (P.veneer j x d l r X v):=
 vet_heat _ (by fun_prop) (X.continuous.comp (P.streakV_cont j x d r v))

lemma cloaked_view(X:(ℋ).Op)(v:𝓗)(p:Vantage):
 P.cloaked j x d l r (⊥₀ X) p v=W p (ρ (P.veneer j x d l r X v p)):=by
 rw [cloaked,←P.lyre_pad, pad_val]; simp only [mul_apply_eq_comp,P.lyre]; rfl


lemma lamina_tick (X:(ℋ).Op)(v:𝓗):
    let f:=P.veneer j x d l r X v
    poseApprox ℋ (fun p=>(F.val p:ℂ) • f p)
      ((P.truck j x) ∘ (g)) (P.macroStep t) =P.lamina j x d l r F t X (ϕ v):=by
  -- based on sum_at_tick (SatinThinQuizLevel)
  intro f; let w:=fun i:Cover=> Ξ (g i) ((F.val (u i):ℂ) • f (u i))
  have he(i:Cover)(x:i∉ϵ): w i=0:= by
    have hu : F.val (u i)=0 := by by_contra q; exact x ((P.usedPose t F i).2 (subset_closure q))
    unfold w; rw [hu,Complex.ofReal_zero,zero_smul,map_zero]
  refine (room_price (P.macroStep t) (P.macroStep_pos t) w (ϵ) he).2.trans ?_
  rw [Finset.smul_sum,lamina,ContinuousLinearMap.sum_apply]; apply Finset.sum_congr rfl; intro i h
  unfold w; rw [map_smul, ContinuousLinearMap.smul_apply, P.lam_act,
    show Fintype.card Axis=4 by rfl, ← Complex.coe_smul ((P.macroStep t)^4), smul_smul]
  push_cast [activation]; rfl


-- to take projection via P.macroRiemann use advocates
lemma lamina_static (a:P.Spectrum0 3)(J:P.Ellis 3 a)
  (X:(P.ColorHil j (P.advocate 3 a j)).Op)(v:P.ManyF j (P.advocate 3 a j)):
 let x:=P.advocate 3 a j
 Tendsto (fun t=>P.lamina j x d l r F t X (P.enter j x v)) atTop
   (𝓝 (P.enter j x (P.flounce j x d l r (P.tableau j x 0 X) F v))):=by
 intro z
 let f:=P.veneer j z d l r X v
 have he:=P.macroRiemann a j J (fun p=>(F.val p:ℂ) • f p) (dyed_compact f)
    ((Complex.continuous_ofReal.comp F.smooth.continuous).smul (P.veneer_cont j z d l r X v))
 simp_rw [map_smul] at he -- outside f
 rw [P.flounce_act]; simp_rw [P.cloaked_view]
 exact he.congr fun t=> P.lamina_tick j z d l r F t X v

#print axioms lamina_static
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection

