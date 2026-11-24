import YM.CF.Taxi.Wood
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Taxi
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
open Next.Foundations Push.Local AnalyticBridge.VerifiedReset RG.PathData Next.Scheduling UVNext.PricedKernels Work.F03 WilsonStartup Vow
open AnalyticBridge.VerifiedReset.Geo Trees
local notation "Gp"=> SU.group
variable (Γ:ℝ) (P:BudgetPoint){q:Clip}(R: PathData SU.group) (x: Site (More n))
def numP (P:BudgetPoint):ℝ:=(P.order+1:ℝ)*composeCost P.order ((P.order.factorial:ℝ)*1) 1
def cap_cost (c:Clip)(P:BudgetPoint)(σ C z:ℝ):ℝ:=numP P * (price0 z P * Geo.lowerSize c C + price1 z P * (lowFee SU.group P σ * lowerSize c C))
variable {σ C Λ:ℝ}(p:R.Bounds q σ C Λ)(U:Pane n)(hc:0 ≤ Γ)
lemma bill_h(c:Clip)(z:AnalyticBridge.VerifiedReset.Low)(v:0≤Γ):0 ≤ bill_l R z c Γ P:=by
 obtain ⟨w,t⟩:=dotsP Γ P v; unfold bill_l; rw [oar_F]; refine mul_nonneg (show 0 ≤ numP P from ?_) (mul_nonneg (abs_nonneg _) (add_nonneg w (mul_nonneg t (row_nonneg ..))))
 unfold numP composeCost; positivity
include p hc
lemma baud : SumBudget (fun i:Low=> bill_l R i q Γ P * Real.exp ((σ/2)*i.length R)) (cap_cost q P σ C Γ):=by
 let t(i:Low):= bill_l R i q Γ P; let X:=numP P; have ht:0≤ X:=by unfold X numP composeCost; positivity
 obtain ⟨l,h⟩:=dotsP Γ P hc
 refine budget_mono (budget_scale ht (budget_plus (budget_scale l (lower_budget Gp R p)) (budget_scale h (low_budget Gp P R p)))) (fun i=> mul_nonneg (bill_h Γ P R q i hc) (Real.exp_pos _).le) (fun i=>?_)
 unfold bill_l; rw [oar_F, mul_assoc]; apply mul_le_mul_of_nonneg_left _ ht
 let A:= i.length R; let z:= |i.mark R q|; let m:= Real.exp ((σ/2)*A); let w:= pairBill Gp P
 rw [mul_add, add_mul]; change _≤ price0 Γ P* _+price1 Γ P* _; refine add_le_add ?_ ?_
 · rw [mul_comm z] -- tune defin
   rw [mul_assoc]; apply mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (Real.exp_monotone ?_) (abs_nonneg _)) l; exact mul_le_mul_of_nonneg_right (half_le_self p.width.le) (by positivity)
 rw [mul_left_comm z, mul_assoc]; refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)) (Real.exp_pos _).le) h; unfold lowCost; exact (le_add_of_nonneg_left (faceCost_nonneg ..)).trans (le_add_of_nonneg_left (mul_nonneg (by norm_num) (pair_nonneg ..))) -- tune
open Push.AbsoluteSums Footprint
lemma stunL (c:ℝ)(v:0≤c)(pQ:c/(P.B:ℝ) ≤ σ/8) : Ac.Hit (fun i:AnalyticBridge.VerifiedReset.Seat (More n) × Low=>i.1.spread (Low.home R i.2 P (0:Site (More n)))) P.B (fun i=> bill_l R i.2 q Γ P) c (Footprint.payment 1 P.B 0 (σ/8) 1 (Fintype.card Signed * cap_cost q P σ C Γ) c Geo.lowCount):=by
 let g (i : Low) := bill_l R i q Γ P; have hg i : 0 ≤ g i := bill_h Γ P R _ i hc; have he := Quotes.channel_anchored (n:=More n) _ g hg (baud Γ P R p hc)
 have hp:0 < σ:=p.width; have hQ:0 < (P.B:ℝ):=Nat.cast_pos.mpr P.B_pos
 refine Footprint.assigned (id : Site (More n)→ Site (More n)) 1 (fun Y : Support (More n)=>by simp) (fun i :AnalyticBridge.VerifiedReset.Seat (More n) × Low => i.1.2) (fun i=> g i.2) (fun i=> hg i.2) (fun i=> i.2.length R) (fun i:AnalyticBridge.VerifiedReset.Seat (More n) × Low=> i.1.spread (Low.home R i.2 P (0: Site (More n)))) he P.B 0 P.B (C:=1) (v:=Geo.lowCount) (a:=c) (ε:=σ/8) (v':=(P.B:ℝ)⁻¹) ?_ ?_ zero_le_one ⟨v,by linarith,by rw [← div_eq_mul_inv]; linarith⟩ (fun i =>g i.2) (fun i=>hg _) (fun _ => by simp)
 · rintro i y hy; obtain ⟨j,t,rfl⟩:= Finset.mem_image.mp hy
   simpa only [affine,separation_translate, Signed.act_zero,zero_add,id_eq] using! (spin_separation i.1.1 i.1.2 j (0:Site (More n))).trans_le (low_dist P R _ t)
 intro i; rw [AnalyticBridge.VerifiedReset.Seat.visit_count]; apply le_of_mul_le_mul_left (a:=(P.B:ℝ)) ?_ hQ; rw [mul_add,← mul_assoc,mul_inv_cancel₀ hQ.ne',one_mul]; exact_mod_cast low_geometry P R i.2 (0:Site (More n))
end YM.CF.Taxi
