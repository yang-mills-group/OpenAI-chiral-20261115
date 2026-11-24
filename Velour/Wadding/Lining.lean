import Velour.Quilt.Nap
import Velour.Organza.Boning
/-! Compression of positive price purchases to the ManyF slabs. -/
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

variable (P:Spine)(j:Axis)(x:P.Spectrum0 j)
local notation "ℋ"=> P.ColorHil j x
local notation "𝓗"=> P.ManyF j x
local notation "Σ₀"=> P.physicalEnergy j x
local notation "Σ₁"=> P.seasons j x


local notation "⊥₀"=> P.tableau j x 0 -- change notation
local notation "ρ"=> P.wealth j x
local notation "ι'"=> P.enter j x

lemma lyre (A : (ℋ).Op) (z:𝓗) : ⊥₀ A z = ρ (A (ι' z)):=by
 rw [tableau,neg_zero,P.cart_zero]
 rfl

lemma lyre_heat (a b:ℝ≥0)(A:(ℋ).Op):
 ⊥₀ ((Σ₀).E a*A*(Σ₀).E b)=(Σ₁).E a*(⊥₀ A)*(Σ₁).E b:=by
 ext z
 simp_rw [lyre, mul_apply_eq_comp, lyre]
 rw [P.banked,P.banked,P.bankHeat,P.soleHeat]

lemma lyre_pad (a b:ℝ)(A:(ℋ).Op):
 ⊥₀ ((Σ₀).pad a b A)=(Σ₁).pad a b (⊥₀ A):=P.lyre_heat ..

lemma lyre_star(A:(ℋ).Op): star (⊥₀ A)= ⊥₀ (star A):=P.boards_star ..

lemma lyre_glow {A:ℕ→(ℋ).Op}{a:(ℋ).Op}(h:Gleams ℋ A a):
 Gleams 𝓗 (fun i=>⊥₀ (A i)) (⊥₀ a):=by
 obtain ⟨B,b⟩:=h.bought
 refine ⟨⟨B,b.mono fun i c=>(P.tableau_pay j x _ _).trans c⟩,fun z=>?_,fun z=>?_⟩
 · simp_rw [P.lyre]; exact ((ρ).continuous.tendsto _).comp (h.gaze _)
 · simp_rw [P.lyre_star,P.lyre]; exact ((ρ).continuous.tendsto _).comp (h.turn _)

variable {P j x}
namespace Veloured
variable {T:ℕ→P.Apron}(h:P.Veloured j x T)
/-- Price in continuous space at center zero. -/
def adorning (t:ℝ≥0):(𝓗).Op:= ⊥₀ (h.printOp t)

lemma adorning_covetails:(Σ₁).Covetails h.adorning:=by
 intro t v r
 symm
 unfold adorning
 rw [←P.lyre_heat]
 have n:(0:ℝ)<t:=v
 have l:(t:ℝ)≤↑(t+r):=NNReal.coe_le_coe.mpr le_self_add
 rw [h.print_wrap n l,NNReal.coe_add]
 rw [add_sub_cancel_left,pad]
 dsimp; rw [Real.toNNReal_coe]


lemma adorning_mirror {t:ℝ≥0} (p:0<t) :
 h.mirror.adorning t=star (h.adorning t):=by
 unfold adorning
 rw [P.lyre_star]
 exact congrArg (⊥₀) (h.mirror_print p)

lemma cash:(Σ₁).Cashable h.adorning:=by
 let τ : ℕ→ℝ≥0:=fun k=>⟨_, (P.macroStep_pos k).le⟩
 obtain ⟨C,D,b,d,p⟩:=h.print_budget
 apply (Σ₁).cashable_of_tail (τ:=τ) h.adorning_covetails b d
   (fun k=>NNReal.coe_lt_coe.mp (P.macroStep_pos k)) (fun k=>P.halvesClock k)
 exact p.mono fun k c=>(P.tableau_pay j x _ _).trans c

end Veloured
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection

