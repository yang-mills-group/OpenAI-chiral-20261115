import Velour.Gathers.Fringe
import Velour.Quilt.Nap
set_option autoImplicit false
set_option maxHeartbeats 1050000
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

open SatinJets OS.Semigroup


variable {P:Spine}{j:Axis}{x:P.Spectrum0 j}{T:ℕ→P.Apron}
lemma Totty.mirror (h:P.Totty j x T):
   P.Totty j x (fun i=>(T i).kiss P j):=by
 unfold Totty Costly priceCap
 simp_rw [Apron.kiss_width,←Apron.kissed,norm_star]
 exact h
end Spine
namespace Spine
open Aria Casting Six OS.Semigroup.Balloon MacroGrid SatinNucleus Velour SatinJets
variable (P:Spine) (Z:Lead.Clan)
local notation "π₀"=> (purePrice Z:ℂ)
variable (x:P.Spectrum0 3)(A:ℕ→P.Apron) {c r n:ℕ→ℕ}
local notation "ξ"=> P.advocate 3 x 3
local notation "σ"=> P.physicalEnergy 3 ξ
local notation "𝒞"=> P.ColorHil 3 ξ
local notation "τ"=> P.macroStep
variable (m:P.HandleWith x c r A n) (h:P.VelvetHandle c r A x n)
  (v:P.Totty 3 (P.advocate 3 x 3) A)
local notation "Q₀" i:max=> (P.stitchApron Z (A i) (c (n i)) (r (n i)))
local notation "G₀" i:max=> (P.gaugeStitch Z (A i) (c (n i)) (r (n i)))
local notation "d" i:max=> (A i).realWidth P 3


include m v h
lemma silky: P.Totty 3 ξ (fun i=>Q₀ i) ∧ P.Totty 3 ξ (fun i=>G₀ i):=by
 let e(i:ℕ):=(Q₀ i).realWidth P 3
 let t(k i:ℕ):=e i+τ k
 let l(k i:ℕ):=t k i + d i
 let b(k i:ℕ):=t k i - d i
 have y(k i:ℕ): e i≤t k i:=le_add_of_nonneg_right (P.macroStep_pos _).le
 have gt(i:ℕ):2*d i ≤ e i:=P.doubled_width Z _ _ (m.already i)


 let B(k i:ℕ):=π₀ • (A i).dye P 3 ξ (l k i) (b k i)
 have q: Costly (𝒞) B:= (v.capdyes l b (fun k i=>by
      unfold l t
      linarith only [(A i).real_width_pos P 3,P.hem_time (Nat.le_succ k),gt i])
      (fun k i=>by
      unfold b t
      linarith only [P.hem_time (Nat.le_succ k),gt i])).smul π₀

 have s: Costly (𝒞) (fun k i=>P.priceCap 3 ξ (Q₀ i) k -B k i):=
   Costly.bdd (τ 0) fun k i=>
     (P.weight_silver Z x A m h i (y k i)).trans
       (P.hem_time (Nat.zero_le _))
 exact ⟨(s.add q).agree fun k i=>sub_add_cancel ..,
        q.agree fun k i=>(P.silver_gauge Z x (A i) _ (m.already _) (y k i)).symm⟩

lemma silky_trumps (W:Lead.Clan→Prism):
   P.Totty 3 ξ (P.soldTrumpet A c r n W Z) ∧
   P.Totty 3 ξ (P.gaugeTrumpet A c r n W Z):=by
 obtain ⟨a,d'⟩:=P.silky Z x A m h v
 exact ⟨a.crop _,d'.crop _⟩
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
