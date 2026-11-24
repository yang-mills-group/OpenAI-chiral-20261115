import Merino.Dais.Latch
import SatinThinCarve
set_option maxHeartbeats 1050000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Merino.Dais
open YM.CF.QuadClock
open Neon
open Py
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open AnalyticBridge.Annulus1AD Ac Esti
open Atala Forge Cloak Rill Hive Fock Stilo Palot Scion
open Cube Lat Tenant Tulip
open Pastry Hake Levier Urn Peaks Fock Laic Branch Drapes
attribute [local instance] opCStarAlgebra
open Rush Scroll Paige Vault Phase Acorn Spire
attribute [local instance] opCStarAlgebra
open Tarn Cay Slate Esti Cour Hest Arena Reine Kennel Facet Broc Pec Push.SectorMeasure.Oriented
open Hom Vale Vale.Grace Next.Free Thera Nacre Dial Fock
open Tye Lich Stake Pail Pail.Dew
open Ione Moto Taxi Hove Haro Vow Bake Lilt Prism Rue Larch Push.AbsoluteSums.Trees Salt Jet
open scoped YM.CF.Mew

set_option autoImplicit false
open Mew Waxy Roots Rive Oise

variable {I:Type}[LinearOrder I][Fintype I]
variable {N P B n:Side}
variable {L:Side}
variable (G:Ratio (mid N B) (mid P B))
variable (X:GramM (mid N B))(Y:GramM (mid P B))
variable (o:I→Site (mid N B))
local notation "FINE" => mid P B
local notation "GRAFT" => mid N B
local notation "vFine" => Hove.heel G ∘ o

variable {R:Patch}{Kr:Teller SU.group}{Lr:ChartRatio SU.group}
 (V:Grace Kr R Lr) {e:ℝ}(U:Grasp V.U B e)
 (S:StepData (Domain N B) (Domain P B))
 (G₀:Scree.Loom (mid N B))(G₁:Scree.Loom (mid P B))
 (Xp:Op SU.Slot)(q:Chi)(d h Vp Vf T W C BQ Rt Zt b g κp w:ℝ)


lemma frosted {A D c:ℝ}
 {x:Site GRAFT}{F:Copy GRAFT}{E:RegBudget GRAFT}{G':Cusp GRAFT}{z:ℂ}{u:ArcΦ}
 (p:Ice L.val x X.p h A D c F E G' z u)
 (h0:0≤h):
 Ice L.val x X.p h (duty_Q X.p.order X.p.power*A) (strive_E X.p.order*D)
   c F E G' z u:=by
 obtain ⟨a,d',_⟩:=ice_nonneg _ p h0
 have hn:1 ≤ (X.p.order.factorial:ℝ):=by exact_mod_cast Nat.factorial_pos _
 have a':1≤ duty_Q X.p.order X.p.power:=by
     unfold duty_Q Jet.composeCost; apply one_le_mul_of_one_le_of_one_le
     · simpa using hn
     apply one_le_pow₀; exact le_add_of_nonneg_right (by positivity)
 have d1:1 ≤ strive_E X.p.order:=by unfold strive_E Jet.composeCost; apply one_le_mul_of_one_le_of_one_le (by linarith only [Nat.cast_nonneg (α:=ℝ) X.p.order]) (one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hn hn) (one_le_pow₀ (by norm_num)))
 obtain ⟨m,c',d2,f'⟩:=p.grant
 exact ⟨⟨Provides.liftE _ X _ _ p.axle.vest (le_mul_of_one_le_left a a'),p.axle.site,p.axle.flair⟩,p.phase,p.stout,⟨m,c',fun i=>(d2 i).trans (le_mul_of_one_le_left d' d1),f'⟩,p.wear⟩


variable (D:Key I→RegBudget (mid P B))(F:Key I→ForceBudget (mid P B))
variable (u:I→ArcΦ)(A:I→ℝ) {m n0:ℕ}
variable (Be:Observatory G X.p)(Vκ:Cusp (mid N B))(Ca:ArcΦ→ℝ→ℝ)
local notation "Duty" => duty_Q X.p.order X.p.power
local notation "Str" => strive_E X.p.order
local notation "Coast" => Cusp (mid N B)
local notation "Pay" => Cusp (mid N B)

structure Glissade (n0 m:ℕ):Prop where
 hired: OrbitPulse G X Y h b g R.L o D F u A m
 summons: ∃ (L':Key I→Pay),
   (∀ x∈hill I,Be.source (D x) (F x) (L' x)) ∧
   (∀ i x,River fun z=> heat_P X.p L' z i x)∧
   ∃ (E : I → RegBudget GRAFT) (K : I→Pay)
      (t : I→ℂ) (Y' : I→ArcΦ),
     (∀ i, let k:=nun_ω Y.F (heel G (o i))
          let r:=κprobe mintR R.L h (A i) T k (u i)
          Ice R.L.val (o i) X.p h (W*r) (Ca (u i) (A i))
            (C*r) (feeTip X.p L' i) (E i) (K i) (t i) (Y' i) ∧
          αPrice R.L h (A i) T BQ Rt Zt (u i) (Y' i) X.p Y.p k)∧
     let Kν:=fun z=>rust_L X.p (L' z) (Vκ+Φstack K z)
     ∃ R', Cause_P V U G S G₀ G₁ X Y D 0 F Xp q d h Vp Vf o A u R' Kν Y' t T
            (Duty*W) C BQ Rt Zt κp ∧
            (∀ z∈hill I, FlagWidth X.p (Kν z) n0)∧∀ i,νTip R' i= E i


variable {G X Y o V U S G₀ G₁ Xp q d h Vp Vf T W C BQ Rt Zt b g κp D F u A Be Vκ Ca}
lemma engagements
 (v:OrbitJet V U G S G₀ G₁ X Y Xp q d h Vp Vf T W C BQ Rt Zt b g κp Be Vκ Ca n0 m)
 (v₁:OrbitPulse G X Y h b g R.L o D F u A m)
 (h0:0≤h):
 Glissade G X Y o V U S G₀ G₁ Xp q d h Vp Vf T W C BQ Rt Zt b g κp D F u A Be Vκ Ca n0 m:=by
 obtain ⟨L',a,s,g,u'⟩:=v.heat _ _ _ _ _ v₁
 dsimp only at g
 choose E K τ κ born using g
 exact ⟨v₁,L',a,s,E,K,τ,κ,born,u' E K κ τ fun i=>⟨frosted _ _ (born i).1 h0,(born i).2⟩⟩
end YM.CF.Merino.Dais
