import YM.CF.Vow.Palm
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Vow
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
open Jet Yaw Nor Prism Font Push.AbsoluteSums Wray
variable{n:Side} {P: BudgetPoint}{x y a b h c d:ℝ}{k m:ℕ}
local notation "DN"=>tangD n
local notation "E'"=>SU.group
variable {X D Y Z:Support (More n)}{U:Pane n}
local notation "Ink" n=> Hake.Raid (Dwell n)
-- Spin off Δ reimbursement. natural translations kernel even. arbitrary AlgHom linear
open Salt Trees Ursell
variable (T:Sweep n) (X Y:Aura n)
local notation "Yc"=> moldA T
local notation "Λ"=> Salt.quill (boxA T)
local notation "Υ"=> actY T
variable {F:Pax n}{K W:Cusp n} (C:Cipher n→ₐ[ℝ]Cipher n) (V:Orbit n)
variable (F1:Pax n) (p:∀ i,F1 (moldA T i) (yellA T V)= C (F i V))
include p
lemma rel_voyage (i:Tuple (Aura n) k):sta F1 (Yc X) m (⟨k,curlV T k i⟩) (yellA T V) = C (sta F X m ⟨k,i⟩ V):=by
 unfold sta; simp only [tideI,(moldA T).injective.eq_iff]; split; swap; · exact (map_zero _).symm
 unfold guava; simp only [Pi.smul_apply, Finset.prod_apply]; rw [patV,map_smul,map_prod]; refine congrArg _ ?_; apply prod_congr rfl; exact fun j _=> p _
variable {Q:Aura n→ℝ} {d1 d2 d3:ℝ}{M:ℕ}(Pv:Ready Palot.stern M Q c d1 d2 d3)(t:1≤h)(P_:∀ i,Medal P i.val ∅ (F i) h (Q i))(k_:0≤c)
variable {e0 e1 e2 e3:ℝ}{B2:ℕ}(Q1:Aura n→ℝ)(Pv1:Ready Palot.stern B2 Q1 e0 e1 e2 e3)(hc1:0≤e0)(h1:∀ i,Medal P i.val ∅ (F1 i) h (Q1 i))
include Pv t P_ k_ h1 Pv1 hc1
lemma rel_spinsE(m:ℕ):spinD P (Yc X) F1 m (yellA T V)= C (spinD P X F m V):=by
 by_cases x: visible P X.val (∅:Support _) V.1; swap; · exact (if_neg (mt (yarnV T V X 0).2 x)).trans (by rw [show spinD P X F m V=0 from if_neg x, map_zero]) -- tune
 let J(i k:ℕ):= V; rw [spiritD (Yc X) _ _ _ Pv1 hc1 ((yarnV T V X 0).1 x) m,spiritD X V _ _ Pv k_ x]; all_goals first| exact P_| exact t|exact h1|skip -- params
 let L:= C.toLinearMap.toContinuousLinearMap
 let A:=fun (s: Clusters (Aura n))=> sta F X m s V; obtain ⟨i,g,h⟩:=x; have hp:Summable A:=Summable.of_norm_bounded (glomM X Pv k_) (fun j=>by
    let K:=ponder X j t P_ m; unfold A; rw [K.same _ (i,V.2) h (fun _ _=>rfl)]; exact K.capF t _ g)
 let Y:= Equiv.sigmaCongrRight (fun m=> curlV T m)
 change _ = L (∑' (i:Clusters (Aura n)), A i); rw [←(L.hasSum hp.hasSum).tsum_eq] -- tune
 rw [← Y.tsum_eq]; exact tsum_congr fun s=> rel_voyage T X C V F1 p s.2
end YM.CF.Vow
