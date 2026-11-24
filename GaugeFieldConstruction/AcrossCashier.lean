import GaugeFieldConstruction.AcrossShots
import YM.CF.Buffered.Shooting

set_option autoImplicit false
noncomputable section
set_option synthInstance.maxSize 18000
set_option maxRecDepth 2600
set_option maxHeartbeats 450000
namespace YM.CF.Py.Rate
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
open Ione Beau Haro Cascade Fief VolumeRate
open scoped Mew

namespace AcrossShots
open LayerOverlap Branch
variable {K : Teller SU.group} {R : Patch} {L : ChartRatio SU.group} {V : Grace K R L}
variable {d h x delay : ℝ} {D C R0 : ℝ → ℝ} {m m' N B : Side} {U : Grasp V.U B d}
variable {W : GivenX V U} {J : Robes N V W} {q : Chi} {z:ℝ} {P : Prescription R B} {N0 k k' l₀ : ℕ} {T : Month x 1 6 2 N0 V W}

open AcrossLands
variable {X:Cape m B R.L} (p: T.q ≤ m.val) (H:Service V U W J q h D C R0 P N0 delay)(hh:1≤h)
 {f:ℕ→ℝ} {k:ℕ}
local notation "Ω"=> mid (mesh m R.L k) B
local notation "Y"=> Actual T p X f k
variable (hp:K.top.clip.direct≤1) (a:Bon J q h D delay (Actual T p X f k))

open Buffered
include H a
local notation "A" => (Actual T p X f k)
-- Reachable real perturbed history. author action marks advancing by ACTUAL β & W.
lemma paidStepsSt (r:Bet k){z b:ℝ}(e:CreditedBet (P:=P) (J:=J) (h:=h) (D:=D) (C:=C) (R0:=R0) (q:=q) (X:=X) (f:=f) p b z r): Buffered.Granted U ((Actual T p X f k).gram P r) X q J.d k ((Actual T p X f k).wave P r) (Buffered.steps V m B k) R.J := by
 refine ⟨?_, ?_, ?_, ?_, fun i _=>a.can.isle i,?_⟩
 · intro i _; unfold steps; rw [V.L.patch_x]; exact V.L.cloth
 · intro i _; exact Hom.rat_eq (show (Vale.apt m B R.L i).count= _ from (V.L.lent_L ..).symm)
 · intro i _; exact congrArg Patch.J (V.L.patch_x (x:=kint m B R.L i) (k-1-i))
 · intro i h0; obtain ⟨u,_,g,-⟩:= (e.paid i h0.le).2.2 h0
   rw [g]
   let Z:= (A).chargeLevel P r (i+1); let σ:= (A).offset P r (i+1); let β:= (r.read (i+1)).re; let A':= (A).toSpine.address i
   let T:= u.statv β Z 0 σ ((hat_step i) ▸ (e.paid (i+1) h0).2.1)
   exact rig V U W J q u.rocket _ u.roof _ T.sound A'.count (ward_m (V.L.mood A'.lag) ((a.flow (a.charged H e.core.toRealQ (i+1) h0)).toCost.lot _ _))
 intro i g v t; exact ((e.paid i g.le).2.2 g).2.2.2.2.2.1 v t
#print axioms paidStepsSt
end AcrossShots
end YM.CF.Py.Rate
end
