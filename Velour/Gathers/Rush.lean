import Velour.Gathers.Rolled
import Velour.Gathers.Tapes
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

variable (P:Spine)(j:Axis)(x:P.Spectrum0 j)
local notation "ℋ"=> P.ColorHil j x
local notation "𝓗"=> P.ManyF j x
local notation "Σ₀"=> P.physicalEnergy j x
local notation "Σ₁"=> P.seasons j x


local notation "⊥₀"=> P.tableau j x 0 -- change notation
local notation "ρ"=> P.wealth j x
local notation "ι'"=> P.enter j x



open Boundary Probe
local notation "Θ"=>P.detects j x
local notation "E" => (Σ₁).E
local notation "G" => (Σ₁).heatL
local notation "J"=>P.Bobbin j x
namespace Bobbin

def quietSlot (B:P.Bobbin j x)(i:ℕ)(l r:ℝ≥0): (𝓗).Op :=
   E l * (B.spool i).compact P j x * E r
def visits (B:P.Bobbin j x)(i:ℕ)(l r:ℝ≥0)(f:Test4) :=
   (Σ₁).labelled (quietSlot P j x B i l r) f

/-- These are centered widths plus (possibly trivial) extra heat.
l r measured from the ENDPOINTS of the literal slab. -/
lemma knocks (B:J)(i:ℕ)(l r:ℝ≥0):
    B.quietSlot P j x i l r=(B.spool i).knock P j x
       ((B.spool i).realWidth P j+l) ((B.spool i).realWidth P j+r):=by
 unfold Apron.knock Apron.dye
 rw [P.lyre_pad,add_sub_cancel_left,add_sub_cancel_left,pad_val,Real.toNNReal_coe,Real.toNNReal_coe]
 rfl

variable {P j x}
/-- All widths control. -/
def Joint (B:P.Bobbin j x):Prop:=P.Totty j x B.spool

lemma Joint.turn {B:P.Bobbin j x}(h:B.Joint):
    B.windBack.Joint:= Totty.mirror h


variable {B:P.Bobbin j x}{n:ℕ→ℕ}{V:ℕ→Test4}{f:Test4}
def Receives (B:P.Bobbin j x)(m:ℕ)(A:ℝ)(X:(P.ManyF j x).Op):Prop:=
   (Σ₁).Ribs (fun i=>(B.spool i).compact P j x)
       (P.bobQuote j x B) m A X
lemma Joint.receives (h:B.Joint):∃m A X, B.Receives m A X:=by
 obtain ⟨m,A,_,X,_,t⟩:=B.ribbon.earned_joint h
 exact ⟨m,A,X,t⟩

lemma Joint.surges (h:B.Joint)
   (e:Tendsto n atTop atTop)(g:Tendsto V atTop (𝓝 f))
   {u v:ℕ→ℝ≥0}{l r:ℝ≥0}
   (tu:Tendsto u atTop (𝓝 l))(tv:Tendsto v atTop (𝓝 r)):
   (Σ₁).Surges atTop (fun i=> B.visits P j x (n i) (u i) (v i) (V i))
     (G l * Θ B f * G r):=by
 obtain ⟨m,A,X,p⟩:=h.receives
 exact Ribs.rushes_warm p (P.satin_storage j x|>.1 B) e g tu tv
end Bobbin


variable {κ:Type}

/-- Any joint or zero. -/
lemma joint_spin (L:List κ) (b:κ→J)(Y:κ→Test4)(l r:κ→ℝ≥0)
   (m:κ→ℕ→ℕ)(a c:κ→ℕ→ℝ≥0)(f:κ→ℕ→Test4)
   (h:∀z∈L, Tendsto (m z) atTop atTop ∧
     Tendsto (a z) atTop (𝓝 (l z)) ∧ Tendsto (c z) atTop (𝓝 (r z)) ∧
     Tendsto (f z) atTop (𝓝 (Y z)) ∧ (b z).Joint):
  (Σ₁).Surges atTop (fun i=> (L.map fun z=>
      (b z).visits P j x (m z i) (a z i) (c z i) (f z i)).prod)
     (L.map fun z=> G (l z)*Θ (b z) (Y z) * G (r z)).prod:=by
 refine Surges.per_word
    (F:=fun z i=>(b z).visits P j x (m z i) (a z i) (c z i) (f z i))
    _ ?_
 intro z u
 obtain ⟨e,g,t,y,p⟩:= h z u
 exact p.surges e y g t

lemma heatL_nil : G 0=1:=by
 ext1; apply Subtype.ext; rw [heatL_coe,(Σ₁).eZero]; rfl
#print axioms joint_spin
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
