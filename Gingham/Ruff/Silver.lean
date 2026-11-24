import Gingham.Ruff.Gild
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



open VelourBoard
open Papyrus Papyrus.Franc Preparation Yoke
open Pressure.Worth
variable {P s i k} {C ρ v q :ℝ}
local notation "𝒳" s:max i:max => exhibit P.run P.large s i
set_option linter.unusedSectionVars false

namespace Shining
variable {f t:Family P.calibration}
local notation "ℳ" => Tower.mirror P.calibration
-- stated recursively
lemma poseShift(r:List (Axis×ℤ))(h:Shining P ρ s i f q):Shining P ρ s i (Ballet r f) q:=by
 intro u
 have x:Ballet (u++r) f=Ballet u (Ballet r f):=by
   induction u with
   | nil=>rfl
   | cons a u ih=> exact congrArg (Tower.mirror K a.1 a.2) ih
 rw [←x]
 exact h _
lemma poseB(a:Axis)(z:ℤ)(h: Shining P ρ s i f q): Shining P ρ s i (ℳ a z f) q:=
   h.poseShift [(a,z)]
lemma ticks(a:Axis)(z:ℤ)(h: Shining P ρ s i f q):Shining P ρ s i (relocate K a z f) q:= (h.poseB a 0).poseB a _
lemma pair(h:Shining P ρ s i f v)(g:Shining P ρ s i t q): Shining P ρ s i (f*t) (v*q):=by
 intro r
 have x:Ballet r (f*t)=CF.Gingham.Ruff.Ballet r f * CF.Gingham.Ruff.Ballet r t :=by
   induction r with
   | nil=> rfl
   | cons a l ih=>exact (congrArg (Tower.mirror K a.1 a.2) ih).trans (mirror_times ..)
 rw [x,actual_product]
 exact (h r).attach (g r)


lemma split(h:Shining P ρ s i f v)(g:Shining P ρ s i t q): Shining P ρ s i (f+t) (v+q):=by
 intro r
 have x:Ballet r (f+t)=CF.Gingham.Ruff.Ballet r f + CF.Gingham.Ruff.Ballet r t:=by
   induction r with
   | nil=> rfl
   | cons a l ih=>exact (congrArg (Tower.mirror K a.1 a.2) ih).trans (mirror_plus ..)
 rw [x,map_add]
 exact fun y=>(h r y).either (g r y)

lemma scale(h:Shining P ρ s i f v)(z:ℂ):Shining P ρ s i (z • f) (‖z‖ * v):=by
 intro r
 have x:∃u:ℂ, ‖u‖=‖z‖ ∧ Ballet r (z • f)=u • CF.Gingham.Ruff.Ballet r f:=by
   induction r with
   | nil=> exact ⟨z,rfl,rfl⟩
   | cons a l ih=>
      obtain ⟨u,v,p⟩:=ih
      exact ⟨star u, (norm_star ..).trans v,(congrArg (Tower.mirror K a.1 a.2) p).trans (mirror_scale ..)⟩
 obtain ⟨u,v,p⟩:=x
 rw [p,map_smul,←v]
 exact fun y=>(h r y).scale u

lemma subtract(h:Shining P ρ s i f v)(g:Shining P ρ s i t q): Shining P ρ s i (f-t) (v+q):=by
 simpa [sub_eq_add_neg] using h.split (g.scale (-1))

lemma raise(h:Shining P ρ s i f v)(a:v≤q): Shining P ρ s i f q:=fun r=>(h r).raise a



lemma pennies : Shining P ρ s i (0:Family K) 0:=by
 intro r; have x: Ballet r (0:Family P.calibration)=0:=by
              induction r with
              | nil=>rfl
              | cons a r ih=>
                have x:= mirror_scale K a.1 a.2 (F:=0) 0 -- argument order
                simp only [zero_smul,star_zero] at x
                exact (congrArg (Tower.mirror K a.1 a.2) ih).trans (by simpa only [zero_smul] using x)
 rw [x,map_zero]
 exact fun _=>Bright.space

lemma costume {I:Type*}{T:Finset I}{g:I→Family K}{C':I→ℝ}
    (h:∀x∈T,Shining P ρ s i (g x) (C' x)):
    Shining P ρ s i (∑x∈T,g x) (∑x∈T,C' x):=by
 induction T using Finset.induction_on with
 | empty=> rw [sum_empty,sum_empty]; exact pennies
 | insert j T u ih=> rw [sum_insert u,sum_insert u]; exact (h _ (mem_insert_self ..)).split (ih (fun x p=>h x (mem_insert_of_mem p)))
#print axioms costume

end Shining



#check Bouquet.scaleW
#check mirror_scale


/-- Shared path. Neutrality tested at BQueue landing (can mix paths only by other theorems). -/
structure Regalia(P:Spine)(ρ:ℝ) (s:ℕ) (ν:ℕ→ℕ) (S:Finset Cover)(A:Cluster P.calibration)(q:ℝ):Prop where
  queue : BQueue S (fun n=>A (some n)) (A none)
  legal : (inLeaf queue.landing)∈enclave P.calibration
  pos: 0≤q
  late : ∀ᶠ n:ℕ in atTop,Shining P ρ s (irr P (ν n)) (A (some n)) q
#print Regalia

