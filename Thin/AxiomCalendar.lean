import Thin.Elect
import Thin.Rail
import YM.CF.Brood.Hara
set_option autoImplicit false

set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Py
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
open Cascade Fief Wray Oath Feu Feu.Corset Beau Haro Ione Salt
open Roots Mew Neon Rate Pitching Pitching.Focus LocalLimit

-- Choose before-L numbers exactly. need larger Ac etc for pure gauge, can force `tρ`. Include Pledge.
variable {K:Teller SU.group}
variable (tρ:∀ K:Teller SU.group,Morn K→ℝ)
variable (rF:∀ K:Teller SU.group,Morn K→ℕ)
variable (more:∀ K:Teller SU.group,Morn K→ℝ→ℝ→ℝ→ℕ)
private def Ja (G:Morn K): Morn K:= {G with cap:=(max (rF K G) (Fintype.card Ξθ))}

private noncomputable def qp (G:Morn K):ℝ:=(glints (Ja rF G).armor).choose
private noncomputable def eps (G:Morn K):ℝ:=(glints (Ja rF G).armor).choose_spec.choose
private lemma kvK (G:Morn K):glen_K (Ja rF G).armor (qp rF G) (eps rF G):=(glints (Ja rF G).armor).choose_spec.choose_spec
private noncomputable def Ap (G:Morn K):ℝ:=max (max 0 (tρ K G)) (kVh (qp rF G) (Ja rF G).armor.delta)
private lemma AKp (G:Morn K):0≤Ap tρ rF G:=(le_max_left ..).trans (le_max_left ..)
private noncomputable def V'_p (G:Morn K):ℝ:=(Ja rF G).armor.n*Ap tρ rF G+2+Ap tρ rF G+MF
-- L₀ may use all pre-choice inputs.
private theorem stampF (G:Morn K):∃ v:ℕ,∀ (L:Side),v ≤ L.val→∀ R:Patch,R.L=L→ Καlendar R (Ja rF G).armor (qp rF G) (Ap tρ rF G) (V'_p tρ rF G) (eps rF G):=by
 obtain ⟨z,hz⟩:= Eventually.exists (ht_H (Ja rF G).armor _ _ _ (AKp tρ rF G) (kvK rF G))
 refine ⟨z+10,fun L h R v=>?_⟩; subst L
 obtain ⟨hV,hT⟩:= hz R.L (by omega)
 have hp:=AKp tρ rF G
 exact ⟨le_max_right ..,kvK rF G,⟨hp,(show 0≤V'_p tρ rF G by unfold V'_p; have e:0 ≤ MF:= mul_nonneg (Real.exp_pos _).le hPπ; positivity)⟩,le_rfl,hV,hT,le_max_right ..,(by omega)⟩
def kaleidoscope : Pledge where
 cap K G:=(Ja rF G).cap
 Mult K G:=V'_p tρ rF G
 Lsize K G:= (stampF tρ rF G).choose + more K G (qp rF G) (Ap tρ rF G) (V'_p tρ rF G)
namespace Rate.LocalLimit
structure RGField (P:Preparation):Prop where
 shelf: ∃ (G:Morn P.K)(Q:Diary), let Dζ:= upright (kaleidoscope tρ rF more) P.K G; Q.fits P.R ∧ Morn.After Dζ P.R ∧ ShelfTh Dζ Q P.R0 P.δ P.C P.J Chi.canonical P.h P.P P.N0 P.delay ∧∃ Ak qv ε:ℝ, tρ P.K G ≤ Ak ∧ rF P.K G ≤ Dζ.cap ∧ more P.K G qv Ak Dζ.Mult ≤ P.R.L.val ∧ Καlendar P.R Dζ.armor qv Ak Dζ.Mult ε
lemma lightShelf (P:Preparation)(Y:Stairs P (kaleidoscope tρ rF more)):RGField tρ rF more P:=by
 obtain ⟨G,Q,h,hQ,T,v⟩:=Y.offered
 refine ⟨⟨G,Q,?_⟩⟩; intro Z
 let mT:= more P.K G (qp rF G) (Ap tρ rF G) (V'_p tρ rF G)
 exact ⟨hQ,T,v,Ap tρ rF G, qp rF G,eps rF G,(le_max_right ..).trans (le_max_left ..),le_max_left ..,le_trans (show mT ≤ (stampF tρ rF G).choose + mT by omega) h,(stampF tρ rF G).choose_spec _ (by apply le_trans (Nat.le_add_right ..) h) P.R rfl⟩
end Rate.LocalLimit
end YM.CF.Py
