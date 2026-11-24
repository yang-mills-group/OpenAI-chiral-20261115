import GaugeFieldConstruction.Adepts
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Oath
open Nor
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
open Lich.Muster Lor
open Jet Vol Rel
open Cascade
open Fief
open Yaw Pig
open Lich.Muster Push.AbsoluteSums
open Iva Eire
open Wray Prism Font
open PhysicalNext.JointLoad PhysicalNext.JointLoad.Heir Siete
open Feu Feu.Corset Haro
open Hake Trees Jade Jet Plume
variable {N P B:Side}{S:StepData (Domain N B) (Domain P B)}{T: Tube SU.group S}{G:Ratio (mid N B) (mid P B)}
section
variable {A C:ℝ}{p0:Support (Domain N B)}{P0:Track (Ride S) (Raid (Dwell (mid N B)))}{Tρ:Finset (Dwell (mid N B))→ℝ} {b:ℕ}(v:Strung p0 (rateT Tρ P0) b A C)(J:Finset (Palot.leaf (Site (Domain N B))))
include v
lemma lands : (∑ j∈ J, Trees.currency b A j.val * Hake.joinV Tρ (P0 (beamH j.val)))≤ C:=by
 let f(j:Palot.leaf (Site (Domain N B))):Ride S := Stilo.beamH j.val; have hu : Injective f:=fun i j d=> Subtype.ext (by have he:= congr_arg Stilo.bay d; unfold f at he; simpa [bay_beam] using he)
 let G(i:Ride S):= Trees.currency b A (Stilo.bay i) * (Hake.rateT Tρ P0 i); let K:= J.map ⟨f,hu⟩
 exact le_trans (a:=∑ j∈J,_*_) (b:=∑ j∈K,G j) (le_of_eq (by unfold K; rw [sum_map]; refine sum_congr rfl (fun j _=>?_); unfold G; simp only [Embedding.coeFn_mk]; rw [show Stilo.bay (f j)= _ from Palot.bay_beam _])) ((sum_le_sum_of_subset_of_nonneg (subset_univ K) (fun j _ _=>mul_nonneg ((Real.exp_pos _).le) (v.hand j))).trans v.pay) -- `_`
lemma lumber (q:0≤A): joinV Tρ (∑ j∈J,P0 (beamH j.val)) ≤ C:=by
 rw [joinVsum]; apply le_trans _ (lands v J); refine sum_le_sum (fun i _=> le_mul_of_one_le_left (v.hand _) (Yaw.incline_v _ _ q _)) -- opaque hand
end
abbrev BeamCost (p:ℕ)(q:ℕ)(B:ℕ)(C:ℝ):= Jet.composeCost q (q.factorial*C) ((1+(B:ℝ))^p)
lemma sailSign (D:BudgetPoint)(A:Raid (Dwell (mid N B)))(U:Support (Domain N B))(b:ℕ) (v:0 ≤ A):0≤ sailTax D U b A:=by intro i; change 0≤ Jet.composeCost ..; unfold Jet.composeCost Feu.brim; have ht:0 ≤ A i:=v i; positivity
lemma sailm (D:BudgetPoint)(o:Seat (mid N B))(h:ℝ)(A:Raid (Dwell (mid N B)))(U:Support (Domain N B))(b:ℕ) (v:0 ≤ h) (Bq:ℕ)(hc:coverNumber b U≤Bq)(a:0≤ A) :Trees.currency b 2 U * joinV (Scree.tariff D o h) (sailTax D U b A) ≤ Real.exp (2*Bq) * BeamCost D.power D.order Bq 1 * joinV (Scree.tariff D o h) A:=by
 let p:= D.power; let q:= D.order; let u:= coverNumber b U; let Z(i:ℕ):= BeamCost p q i 1; have hp(i): 0 ≤ Z i:=by unfold Z BeamCost Jet.composeCost; positivity
 have he(j:Finset (Dwell (mid N B))): sailTax D U b A j=(Z u)*A j:=by unfold sailTax Z u BeamCost Jet.composeCost Feu.brim p q; ring
 have hh:Z u≤ Z Bq:=by
    unfold Z BeamCost Jet.composeCost; have hw:(1:ℝ)+↑u≤1+Bq:= add_le_add_right (Nat.cast_le.mpr hc) _
    gcongr -- tune
 let Tρ:= Scree.tariff D o h; have ha:0 ≤ joinV Tρ A:= by apply sum_nonneg; intro i _; exact mul_nonneg (by unfold Tρ Scree.tariff; positivity) (a i)
 rw [show joinV Tρ (sailTax D U b A)=Z u* joinV Tρ A from ?_]; swap; · unfold joinV; rw [mul_sum]; apply sum_congr rfl; intro j _; rw [he,mul_left_comm]
 rw [←mul_assoc]; exact mul_le_mul_of_nonneg_right (mul_le_mul (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (show (u:ℝ)≤ Bq from Nat.cast_le.mpr hc) (by norm_num:0 ≤ (2:ℝ)))) hh (hp _) (Real.exp_pos _).le) ha
end YM.CF.Oath
end
