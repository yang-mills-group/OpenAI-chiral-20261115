import Gingham.Ruff.Tambour
import Gingham.Ruff.Snowcap
import Gingham.Grotto
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 3000
set_option maxHeartbeats 500000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical ContDiff
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
namespace Spine.Gingham

open Spine
variable (P:Spine)

namespace VoyageB
open Diary
open CF.Gingham.Ruff
variable (a c μ E:ℝ)(d l s i k:ℕ)
local notation "Y"=>P.run
local notation "~p~" s:max=>P.run.meter.a s
local notation "K"=>P.calibration
local notation "W"=>underlay P.par
local notation "R" s:max i:max k:max => RootBook Y i k s
local notation "Ω" s:max i:max => Journey.side Y i s


structure Cosmos (a c μ:ℝ)(d:ℕ):Prop where
  aP: 0<a
  cP: 1≤c
  μP: 1≤μ
  height(E:ℝ)(h:0≤E)(l:ℕ)(hp:2≤l):
     ∀ᶠ s in atTop, ∀ i k,s<P.run.uv k→GlendaleInst P.run a c μ E d l s i k

lemma cosmos (w:Glendale P.run):∃ a c μ d,Cosmos P a c μ d:=by
  obtain ⟨a,c,μ,r,h,y,d,t⟩:=w
  exact ⟨a,c,μ,d,r,h,y,t⟩

/-- For activation, one lease includes the minimal Tagbill. Period visits not
    necessarily on the diagonal history yet. -/
structure Scene (a c μ : ℝ)(d s i k:ℕ) :Prop where
 ok: s<P.run.uv k
 gears: GlendaleInst P.run a c μ 1 d 2 s i k
 room: Roomy (wisp (~p~ s)) (Journey.side P.run i s)

def hpCost:ℝ:=GarlandBook.foufee W P.par.d a c -- P c omitted?
variable {P a c μ d s i k E l}

namespace Scene
variable (h:Scene P a c μ d s i k)
def bre :=h.gears.angular
include h in
def gb: GarlandBook W a c P.par.d
   (prince P.par.K.j (R s i k)) (princeps (R s i k)):=
    Classical.choice (pavilion h.gears.tag.1 h.gears.worn.1 W)

def printL : Leaf → Mark (Journey.side P.run i s)
 | none=> h.gb.fountain h.bre
 | some j=> h.gb.bassin h.bre j

lemma reception(t:Leaf): Opening (~p~ s) (hpCost P a c) (leafpure t) (h.printL t):=by
   have e: (~p~ s)=(R s i k).p:=
       (((P.run.voyage i).X (P.run.uv k)).pull.owns s h.ok.le).width
   rw [e]
   cases t with
   | none=>exact matinBud false (opera h.bre h.gears.tag h.gb.pump)
   | some j=>exact matinBud true (opera h.bre h.gears.tag (h.gb.point j))
lemma meets : GarlandBook.vase W (h.printL none) (fun j=>h.printL (some j))
       = h.gb.brim h.bre:=h.gb.brink h.bre h.gears.tag
end Scene

def boarding (P:Spine)(a c μ:ℝ)(d s n:ℕ):=
 Scene P a c μ d s (irr P n) (uvv P n)
lemma clearance (w:Cosmos P a c μ d)(E:ℝ)(t:0≤E)(l:ℕ)(r:2≤l):
   ∀ᶠ s in atTop,
    (∀ᶠ n in atTop,boarding P a c μ d s n) ∧
     ∀i k,s<P.run.uv k→GlendaleInst P.run a c μ E d l s i k:=by
   filter_upwards [w.height E t l r,w.height 1 zero_le_one 2 le_rfl] with s v m
   refine ⟨?_,v⟩
   filter_upwards [ (rising_i P).tendsto_atTop.eventually
      (roomyTail P.run P.large s (wisp (~p~ s))), (rising_depth P).tendsto_atTop.eventually
       (eventually_gt_atTop s)] with n J S
   exact ⟨S,m _ _ S,J⟩


