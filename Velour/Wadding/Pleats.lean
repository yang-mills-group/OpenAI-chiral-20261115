import Velour.Wadding.Flutter
/-! # Seams of the euclidean print: insertion leg purchases. -/
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

variable (l r : ℝ)
variable (F : SampleDose)(t:ℕ)
local notation "g"=>P.vtile t
local notation "u"=>P.meshPose t
local notation "W₀" b:max=>(Apron.realWidth P b j)

/-- Closed grid slab operator rotated according to each print's grid
address, heated up to walls l,r, and smeared with the instrument F.
Only for paid addresses. -/
def pleat (b:P.Apron) : (ℋ).Op:=
 ∑ k∈P.usedGrid t F, P.activation t F k • P.raze j x b l r (g k)

lemma raze_lam (b:P.Apron)(k:Cover){d:ℝ}(v:W₀ b≤d)
   (a:d≤u k j-l)(e:d≤r-u k j):
 P.lamSlot j x d l r t (b.velour P j x d) k = P.raze j x b l r (g k):=by
 rw [lamSlot,Apron.velour, b.dye_twice P j x v v a e]


 ext1
 rw [Apron.dye,pad_val,raze,sub_right_comm (u k j) l, sub_sub r, meshPose]
 unfold charter
 simp_rw [ContinuousLinearMap.comp_apply, mul_apply_eq_comp,P.sixWard_truck_heat]

/-- Use when the smeared poses are strictly inside these walls (available
here with uniform room d>0; prefer this non-strict clearance clause). -/
def Corners (d:ℝ): Prop := ∀p∈tsupport F.val,
   d≤p j-l ∧ d≤r-p j

lemma lam_pleat {d:ℝ}(b:P.Apron)(p: W₀ b≤d)(y:Corners j l r F d):
 P.lamina j x d l r F t (b.velour P j x d)=P.pleat j x l r F t b:=by
 refine Finset.sum_congr rfl fun k q=> congrArg _ ?_
 obtain ⟨a,e⟩:=y _ ((P.usedPose t F k).mp q)
 exact P.raze_lam j x l r t b k p a e

variable {P j x}
lemma pleat_dynamic {a:P.Spectrum0 3}(j:Axis)(J:P.Ellis 3 a)
 {T:ℕ→P.Apron}(h:P.Veloured j (P.advocate 3 a j) T)
   {d:ℝ≥0}(p:0<d) (y:Corners j l r F d)
   {m:ℕ→ℕ}(w:Tendsto m atTop atTop):
 let x:=P.advocate 3 a j
 P.Spreads j x (fun i=>P.pleat j x l r F (m i) (T i))
    (P.flounce j x d l r (h.adorning d) F):=by


 exact (P.lamina_spreads j d l r F J (h.printed p) w).agree
     ((h.thin.eventually_le_const (show (0:ℝ)<d from p)).mono
       fun i v=>P.lam_pleat j _ l r F _ _ v y)

variable (P j x)
local notation "𝓑"=> P.Bobbin j x

def bobbinEu (d:ℝ≥0)(B:𝓑): (𝓗).Op:= P.flounce j x d l r (P.bobQuote j x B d) F
variable {P j x l r F}

lemma Bobbin.eu_purchase (a:P.Spectrum0 3)(j:Axis)(J:P.Ellis 3 a)
 (B:P.Bobbin j (P.advocate 3 a j))
   {d:ℝ≥0}(p:0<d) (y:Corners j l r F d)
   {n m:ℕ→ℕ}(v:Tendsto n atTop atTop)(w:Tendsto m atTop atTop):
 let x:=P.advocate 3 a j
 P.Spreads j x (fun i=>P.pleat j x l r F (m i) (B.spool (n i)))
    (P.bobbinEu j x l r F d B):=by
  intro z
  have h:=((B.restring v).ribbon.printed p).unique ((B.ribbon.printed p).glints v)
  rw [bobbinEu,bobQuote,Veloured.adorning]
  change P.Spreads _ _ _ (P.flounce j z d l r (P.tableau j z 0 (B.ribbon.printOp d)) F)
  erw [←h]
  exact pleat_dynamic l r F j J (B.restring v).ribbon p y w
#print axioms Bobbin.eu_purchase
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection

