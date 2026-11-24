import GaugeFieldConstruction.Drumlin
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 55000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
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
open Ione Beau Haro Cascade Fief
open Wray Oath Feu Feu.Corset Nor Yaw Pig Oise Jade Plume Push.AbsoluteSums
open Trees Lich.Muster Jet
set_option linter.flexible false
open Eire Girt
open VolumeRate
namespace Pitching
open Vow Bake Larch
namespace Focus
open Neon
open Mew Vow Rive Roots
open scoped YM.CF.Mew
namespace CoeffArc
section
open Py.Riant
variable {I:Type}[LinearOrder I][Fintype I]{N:Side}{P:BudgetPoint}{t a b L:ℝ}{x:I→Seat N}
-- force drop zero.H.Entity
abbrev Lapse (F: Finset I→ ForceBudget N) (i:Finset I):= if i=∅ then 0 else F i
lemma lapKD (q:0<t) (u:0≤b)(V:Finset I→ ForceBudget N)(h:BookT (SecK P q.le N) V P.B (realm_C x) a b L) (p:Ledges (SecK P q.le N) x V): BookT (SecK P q.le N) (Lapse V) P.B (realm_C x) a b L∧ Ledges (SecK P q.le N) x (Lapse V):=by
 obtain ⟨C,H,W⟩:=h; let F(i:Finset I):=if i=∅ then (0:Force N→ℝ) else C i
 refine ⟨⟨F,fun i j k=>?_,fun i=>?_⟩,fun i k v j h=>?_⟩
 · unfold Lapse F; split; exact Vale.rinsed ..; exact H i j k
 · refine le_trans (sum_le_sum (fun j h=>?_)) (W i); refine mul_le_mul_of_nonneg_left (sum_le_sum (fun i v=>mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le)) (pow_nonneg u _)
   unfold F; split; exact Roots.gradeQ _ _ (H _ h _) q.le; exact le_rfl
 by_cases hv:j=∅; · exact False.elim (h (by change Lapse V j i k=0; unfold Lapse; rw [if_pos hv]; rfl)) -- tune
 exact p _ _ v j (by change V j i k≠0; change Lapse V j i k ≠ 0 at h; unfold Lapse at h; rwa [if_neg hv] at h)
lemma plus_Lapse (V:Finset I→ForceBudget N)(i:Key I): WritV x V i= V ∅+ WritV x (Lapse V) i:=by
 let R:=realm_C x; have he:∅ ∈R:=mem_filter.mpr ⟨mem_univ _,by simp⟩; let Q:=R.erase ∅
 have u(F:Finset I→ForceBudget N) : WritV x F i= F ∅+ (∑ j∈Q,pine j i • F j):=by
    unfold WritV; nth_rw 1 [←show insert ∅ Q=realm_C x from insert_erase he]; rw [sum_insert (show ∅∉Q from (by simp [Q]))]; congr 1; unfold Mew.pine; rw [prod_empty,one_smul]
 rw [u,u (Lapse V),show Lapse V ∅=0 from if_pos rfl,zero_add]; refine congrArg (fun v=> _+v) (sum_congr rfl fun j t=>?_) -- may fail metavars
 rw [Lapse,if_neg (mem_erase.mp t).1]
end
end CoeffArc
end Focus
end Pitching
end YM.CF.Py.Rate
end
