import SatinThinFrost
import SatinThinQuality
set_option autoImplicit false
set_option maxHeartbeats 1050000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.QuadClock
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
variable {n N B:Side}
lemma vow_life (Y:GramM (mid N B))(h:ℝ)(x:IncX primeU Y.F Y.p h 1)(t:1≤ h)(v:∀ s∈cycleSweep (mid N B), passingR (mid N B) s Y.F Y.F) : ∃ k:ℝ, (∀ i:Site (mid N B), nun_ω Y.F i=k)∧ Real.exp (-1) ≤ |k|∧ |k|≤ Real.exp 1:=by
 let o:Site (mid N B):=0; let k:=nun_ω Y.F o
 have u(s:Sweep (mid N B))(hc:s∈cycleSweep _)(i:Site (mid N B))(h:Earlier s o i): nun_ω Y.F i=Spire.payZ s k:=by
    let A:= Φrap (mid N B) o 10; let T:= Y.F A (1:Pane (mid N B)); unfold k nun_ω ωX lifeH; have hh(s:Sweep (mid N B))(z:ℂ) : Spire.payZ s (Complex.exp z)=Complex.exp (Spire.payZ s z):=by unfold Spire.payZ; cases wageZ s; rfl; exact (Complex.exp_conj _).symm
    rw [hh]; congr 1
    have hp:= v s hc A 1; rw [Facet.glacial] at hp; rw [← move_bill h 10]; change Pastry.pane (Y.F _ _)=_; rw [hp]; exact (Beau.pot_Z s T).trans (castT ..)
 let z:Sweep (mid N B):= ⟨1,0,true⟩; have hz: (starRingEnd ℂ) k=k:=by
    have he:v=v:=rfl
    have h:= u z quad_id o (show Earlier z o o from earlier_id o); change k=cSignX _ _ at h; rw [show wageZ z=true from (by change true.xor (detX 1)=true; rw [det_i]; rfl)] at h; exact h.symm
 have ht: (↑k.re:ℂ)=k:= Complex.conj_eq_iff_re.mp hz
 have hk:= κLife o Y x t; refine ⟨k.re,fun i=>?_ ,?_ ⟩
 · obtain ⟨s,a,g,l⟩:= poseAll 1 o i; rw [ht,u s (cycleQ _|>.mpr (a.symm ▸ quad_id)) i l,Spire.payZ,cSignX,if_neg ?_]; unfold wageZ; rw [g,a,det_i]; decide
 have hp:‖k‖= |k.re|:=by rw (occs := .pos [1]) [←ht]; rw [Complex.norm_real,Real.norm_eq_abs]
 rwa [show |k.re|=‖nun_ω Y.F o‖ from hp.symm]
end YM.CF.QuadClock
