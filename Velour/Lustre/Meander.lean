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
variable (P:Spine)(x:P.Spectrum0 3)(j:Axis)
local notation "ξ"=> P.advocate 3 x j
local notation "𝓗"=> P.ManyF j ξ
local notation "σ"=> P.seasons j ξ

def Latent := {A:ℕ→P.Apron // P.VelvetCup x A}

/-- Work with these registered simultaneously across axes. -/
def behold (u:P.Latent x) : P.Bobbin j ξ where
 spool:=u.val
 thin:=fun i=> (u.property i []).thin
 ribbon:= u.property j []

lemma Apron.pivot_cat (A:P.Apron)(n m:List Axis): (A.pivot P (n++m))=(A.pivot P m).pivot P n := by
 induction n with
 | nil=>rfl
 | cons y n e=> rw [List.cons_append,Apron.pivot_cons, Apron.pivot_cons,e]

def sheens (u:P.Latent x)(l:List Axis): P.Latent x:=
   ⟨fun i=> (u.val i).pivot P l,
    fun k m=> by
     simpa only [Apron.pivot_cat P] using u.property k (m++l)⟩

lemma behold_kiss (u:P.Latent x):
 P.behold x j (P.sheens x u [j])=(P.behold x j u).windBack:=rfl


def glimmers : P.Latent x→(σ).Detector:=
    P.detects j ξ ∘ P.behold x j
def twink : P.Latent x→ℝ≥0→(𝓗).Op:=
    P.bobQuote j ξ ∘ P.behold x j
theorem meander :
 (σ).Fray (P.twink x j) (P.glimmers x j):=
 ⟨fun u=> (P.satin_storage j ξ).1 (P.behold x j u),
  fun u=> ⟨P.sheens x u [j],
     eventually_mem_nhdsWithin.mono (fun _ t=> (P.behold x j u).backward t)⟩⟩

theorem meander_faces (u:P.Latent x)(f:Test4):
 (σ).Faces (P.glimmers x j u f) (P.glimmers x j (P.sheens x u [j]) (bar f)):=(P.behold x j u).op_star f

