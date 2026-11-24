import YM.CF.Salt.Rider
import YM.CF.Salt.Stone
import YM.CF.Salt.Piers
import YM.CF.Haro.Tacit
import YM.CF.Salt.Milk
import YM.CF.Salt.Desk
import YM.CF.Plume.Wager
import YM.CF.Haro.Silk
import YM.CF.Salt.Felt
import YM.CF.Tye.Wheel
import YM.CF.Salt.Dial
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 21000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Salt
open Function Filter Metric NormedSpace Finset Fock Lattice Wilson Laurent Lat Rush SU Drapes Fir Peaks Dial Paige Brace Vault Tulip Tenant Phase Broc Scroll Thera Branch Laic Cube Relation
open scoped Matrix.Norms.L2Operator Matrix Topology ContDiff MatrixOrder BigOperators InnerProductSpace Kronecker Classical
attribute [local instance] opCStarAlgebra
open Scree Pastry Stilo Urn Palot Hake Scion Levier Hive Nacre Tye Skye RG Pressure Next.SectorChange Planned.AtomRegular Girt Spire
open Eire Skye Levier Scion Urn Pastry Rill Kennel Pec
open Eire Girt Tulip Spire Proa RG Pressure Stilo Scree Palot Tye Cour Broc Hive Hake
open Esti Forge AnalyticBridge.Annulus1AD Ac AnalyticBridge.GaussianFieldAlignment Tensor Locations Push.SectorMeasure.Oriented
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Push.SectorMeasure Slate Atala
variable {P N B:Side}{G:Ratio (mid N B) (mid P B)}(S:StepData (Domain N B) (Domain P B))(x:ℝ)(t:S.ratio=ratio G)(s:Sweep (mid N B))(A:Stores S)(V:Pane (mid P B))(X:Support (Domain P B))
local notation "ζ"=> shiftFaces s.s (S.ratio.embed (Facet.pasta s))
section
variable {α:Type}[SemilatticeSup α][OrderBot α][Fintype α][DecidableEq α]{E:Type}[Ring E][Module ℝ E][FiniteDimensional ℝ E]{a b:α→E}(e:α ≃o α)(R:E→+E)(C:α)
open Function
lemma graven (h:∀ j,j ≤ C→ b (e j)= R (a j)): reconL.symm b (e C)=R (reconL.symm a C):=by
 let A:= fun i=> reconL.symm b (e i); let B:=fun i=>R (reconL.symm a i)
 have hp{Y:α→ E}(i): Stilo.view (e i) Y=Stilo.view i (Y ∘ e):=by unfold Stilo.view; exact (Finset.sum_equiv e.toEquiv (fun j=>by simp only [deckH]; exact e.le_iff_le.symm) (fun i _=>rfl)).symm
 change A C=B C; apply Stilo.proves; intro j v; change Stilo.view _ (reconL.symm b ∘ e)= _; rw [←hp, Scion.recon, h _ v, ←show Stilo.view j (reconL.symm a)=a j from Scion.recon .., Stilo.view,map_sum]; rfl -- tune
lemma tofu {Z:Type}[LinearOrder Z][Fintype Z]{S:Set (Oboe Z)}{X:FC Z}(p: Pitch bell S 0 X): Keys X:=by
 induction p with
 | term i t l=>exact Keys.roll i (Nat.even_iff.mpr t)
 | null=>exact Keys.null
 | add _ _ s t=>exact Keys.plus s t
 | stam v _ t=>exact Keys.col v t
end
end YM.CF.Salt
