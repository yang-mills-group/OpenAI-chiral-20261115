import ZecaLeaves
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 3000
set_option maxHeartbeats 400000
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
open Aria Casting Six OS.Semigroup OS.Semigroup.Balloon
open MacroGrid SatinNucleus SatinJets

variable (P:Spine) (x:P.Spectrum0 3)


open Hierarchy.Seld.Zeca
open Hierarchy.Seld (parabola)

open DoseTravel Set


open Hierarchy.Seld.Poin Hierarchy.Seld.Zeca.Monument
open Boundary
variable {ι:Type}(N:P.Tent x ι)


open Hierarchy.Seld.Zeca.Gilt
open Hierarchy.Seld.Poin.Gem Hierarchy.Seld.Poin.Galleon
-- careful Ambiguous Spot, Job, beam
variable (A:P.Shiver x N)(Y:N.Chip→ℕ→P.Apron)
local notation "Wₑ"=> P.Centripetal x
local notation "ωₑ"=>P.Sphere x
local notation "Kₑ"=>P.Retinue x


variable {n:ℕ}(M:Axis→List (Fin n))
 (u:Fin n→ι)(w:Galleon.Palette (K:=P.Retinue x) N u)
 (b:SpaceAxis)(p:Points n)(t:ℝ)

open Dai

variable (B:Regime)
local notation "τ"=>B.steps

/-- Actual raw angular bill. Allows YOUR CHOICE of mesh implementation of placements. -/
def RawJig (a:Dai.Spot n M B.delta B.eta):Prop:=
 ∀p ∈ Metric.ball a.center a.radius, p∈ B.sites n→
   ∀(u:Fin n→ι)(w:Galleon.Palette (K:=Kₑ) N u)(b:SpaceAxis),
   ∀ ε:ℝ,0<ε→∀ᶠ i in atTop,
     convoy b p (τ i) a.center a.radius ∧
     ∃L:P.Livery x N Y u w b p (τ i),∀ᶠ k in atTop,
          ‖P.stirUp x N Y M u w b p (τ i) L k‖ ≤ τ i * ε
structure RawArch:Prop where
 due : ∀(n:ℕ)(M:Axis→List (Fin n)),(debut n M).Nonempty→
       ∃a:Dai.Spot n M B.delta B.eta,P.RawJig x N Y M B a

variable {P x N A Y} (q:P.Ellis 3 x)(l:P.Regalia x N A Y)
include q l

lemma raw_price (a:Dai.Spot n M B.delta B.eta):
 P.RawJig x N Y M B a ↔
    AtJig (K:=Kₑ) Wₑ N ωₑ A M B.delta B.eta B.steps B.sites a:=by
   constructor <;> intro g p h f u w b ε e
   · filter_upwards [g _ h f u w b ε e] with i ⟨c,L,g⟩
     exact ⟨le_of_tendsto
       (stiff M u w b p (τ i) q l L
          (fun j=>(a.savings (ball_subset_closedBall (c j))).1)).norm g,
          (Dai.nice b p (τ i) _ _ h).mp c⟩
   filter_upwards [g _ h f u w b (ε/2) (half_pos e), B.shuffling]
      with i ⟨c, m⟩ d
   have v: Dai.convoy b p (τ i) a.center a.radius:= (Dai.nice b p (τ i) _ _ h).mpr m
   obtain ⟨L⟩:=P.livery x N Y u w b p (τ i)
   exact ⟨v,L,
      (stiff M u w b p (τ i) q l L (fun j=>
         (a.savings (ball_subset_closedBall (v j))).1)).norm.eventually
         (ge_mem_nhds (c.trans_lt (mul_lt_mul_of_pos_left (half_lt_self e) d)))⟩

lemma arch_bill:
 P.RawArch x N Y B ↔ initial (K:=Kₑ) Wₑ N A ωₑ B:=by
 constructor
 · intro h; exact ⟨fun n M e=>(h.due n M e).imp fun s=>(raw_price M B q l s).mp⟩
 intro h
 exact ⟨fun n M e=>(h.purchase n M e).imp fun s =>(raw_price M B q l s).mpr⟩
#print axioms arch_bill

lemma arch_tight: P.RawArch x N Y B ↔ Gilt.actual (K:=Kₑ) Wₑ N A ωₑ B :=
  (arch_bill B q l).trans (initial_actual (K:=Kₑ) Wₑ N A ωₑ (fun _=>P.prepaid ..) B)

lemma arch_real:P.RawArch x N Y B ↔ Gem.RotReal (K:=Kₑ) Wₑ N ωₑ A :=
  (arch_tight B q l).trans
    (Gilt.chamber (K:=Kₑ) Wₑ N A ωₑ (fun _=>P.prepaid ..) (fun _ p u=>diadem q l p u) B)

#print axioms arch_real
