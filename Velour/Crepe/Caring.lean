import SatinThinSymphony
import Velour.Crepe.Glow
/-! # Convergence / price notion. -/
set_option autoImplicit false
set_option maxHeartbeats 350000
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4500
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
namespace Spine
open Aria Casting Six OS.Semigroup.Balloon



open MacroGrid SatinNucleus Velour

variable (P:Spine) (j:Axis)(x:P.Spectrum0 j)
local notation "X"=> P.ColorHil j x
local notation "S"=> P.physicalEnergy j x
local notation "τ"=> P.macroStep

/-- Buy symmetric closed slabs around the *printed* centers of T, along
axis j, in the given character. Dials include the entire intrinsic Apron
width; cost/convergence are eventual at each positive dial. -/
structure Veloured (T:ℕ→P.Apron):Prop where
 thin: Tendsto (fun i=> (T i).realWidth P j) atTop (𝓝 0)
 tender: ∀ a:ℝ, 0<a→ ∃Y, Gleams (P.ColorHil j x) (fun i=> (T i).velour P j x a) Y
 bill: ∃ B D:ℝ, 1≤B ∧ 1≤D ∧ ∀ᶠ k:ℕ in atTop, ∀ᶠ i:ℕ in atTop,
     ‖(T i).velour P j x (P.macroStep k)‖ ≤ B*D^k

variable {P j x} {T:ℕ→P.Apron}
lemma macro_tender (h:Tendsto (fun i=> (T i).realWidth P j) atTop (𝓝 0))
    (y:∀ᶠ k:ℕ in atTop, ∃Y, Gleams (P.ColorHil j x)
      (fun i=> (T i).velour P j x (P.macroStep k)) Y)


    (a:ℝ)(t:0<a): ∃Y,Gleams (P.ColorHil j x) (fun i=> (T i).velour P j x a) Y:=by
 obtain ⟨k,ek,Y,w⟩:= ((P.macroStep_zero.eventually (gt_mem_nhds t)).and y).exists
 let e:= a-τ k
 refine ⟨_, (w.wrap (S) e e).agree ((h.eventually (gt_mem_nhds (P.macroStep_pos k))).mono fun i hi=>?_ )⟩
 exact ((T i).velour_twice P j x (show (T i).realWidth P j < τ k from hi).le
      (show τ k ≤ a from (show τ k < a from ek).le)).symm

namespace Veloured
noncomputable def printOp (h:Veloured P j x T) (a:ℝ) : (P.ColorHil j x).Op:=
 if t:0<a then (h.tender a t).choose else 0

lemma printed (h:Veloured P j x T){a:ℝ}(t:0<a):
    Gleams (P.ColorHil j x) (fun i=> (T i).velour P j x a) (h.printOp a):=by
 rw [printOp,dif_pos t]; exact (h.tender a t).choose_spec
lemma print_wrap (h:Veloured P j x T){a b:ℝ}(t:0<a)(p:a≤b):
   h.printOp b=(S).pad (b-a) (b-a) (h.printOp a):=by
 apply (h.printed (t.trans_le p)).unique
 refine (((h.printed t).wrap (S) (b-a) (b-a)).agree
      ((h.thin.eventually (gt_mem_nhds t)).mono fun i hi=>?_))
 exact ((T i).velour_twice P j x (show (T i).realWidth P j < a from hi).le p).symm


lemma print_budget (h:Veloured P j x T):
   ∃ B D:ℝ, 1≤B ∧ 1≤D ∧ ∀ᶠ k:ℕ in atTop, ‖h.printOp (P.macroStep k)‖ ≤ B*D^k:=by
 obtain ⟨B,D,r,t,f⟩:=h.bill
 exact ⟨B,D,r,t,f.mono fun k hk=> (h.printed (P.macroStep_pos k)).norm_paid hk⟩
end Veloured

end Spine
namespace Spine
open Aria Casting
variable (P:Spine)(x:P.Spectrum0 3)(T:ℕ→P.Apron)
local notation "ξ" j:max=>P.advocate 3 x j
local notation "Ω" j:max=>P.colorZero j (ξ j)
/-- Issued including all pivot tests. -/
def VelvetCup:Prop:=∀ (j:Axis)(l:List Axis),
     P.Veloured j (P.advocate 3 x j) (fun i=> (T i).pivot P l)
lemma velour_view(j:Axis)(A:P.Apron)(d:ℝ):
    A.velour P j (ξ j) d (Ω j)=P.beamRaw j x A d:=by
 let σ:=P.physicalEnergy j (ξ j)
 let E:= (d - A.realWidth P j).toNNReal
 change σ.E E (A.engine P j (ξ j) (σ.E E (Ω j)))=_
 rw [show σ.E E (Ω j)=Ω j from P.sector_hot j (ξ j) E]

variable {P x T}
lemma VelvetCup.cinema_raw (h:P.VelvetCup x T):
   P.Radiates x T
      (fun j l a=> (h j l).printOp a (P.colorZero j (P.advocate 3 x j))):=
 ⟨fun j=>(h j []).thin,fun j l _ t=>
     (((h j l).printed t).gaze (Ω j)).congr fun _=>P.velour_view ..⟩
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection

