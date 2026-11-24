import YM.CF.Reed.Wood
import YM.CF.Taxi.Pius
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
def price_μ (c:Clip)(P:BudgetPoint)(σ C z:ℝ):ℝ:=numP P * (price0 z P * Geo.lowerSize c C + (fee1K z P* P.threshold^2) * (lowFee SU.group P σ * lowerSize c C))
variable {σ C Λ:ℝ}(p:R.Bounds q σ C Λ)(U:Pane n)(hc:0 ≤ Γ)
lemma cap_e(c:Clip)(z:AnalyticBridge.VerifiedReset.Low)(v:0≤Γ):0 ≤ prix_b R z c Γ P:=by
 have w:=(dotsP Γ P v).1; have t:=cash_f Γ P v; unfold prix_b; rw [rise_y]; refine mul_nonneg (show 0 ≤ numP P from ?_) (mul_nonneg (abs_nonneg _) (add_nonneg w (mul_nonneg (mul_nonneg t (row_nonneg ..)) (sq_nonneg _))))
 unfold numP composeCost; positivity
include p hc
lemma kap_H (hv:Geo.Width P q σ): SumBudget (fun i:Low=> prix_b R i q Γ P * Real.exp ((σ/4)*i.length R)) (price_μ q P σ C Γ):=by
 let t(i:Low):= prix_b R i q Γ P; let X:=numP P; have ht:0≤ X:=by unfold X numP composeCost; positivity
 have l:=(dotsP Γ P hc).1; have h:0 ≤ fee1K Γ P * P.threshold^2:= mul_nonneg (cash_f Γ P hc) (sq_nonneg _)
 refine budget_mono (budget_scale ht (budget_plus (budget_scale l (lower_budget Gp R p)) (budget_scale h (low_budget Gp P R p)))) (fun i=> mul_nonneg (cap_e Γ P R q i hc) (Real.exp_pos _).le) (fun i=>?_)
 unfold prix_b; rw [rise_y, mul_assoc]; apply mul_le_mul_of_nonneg_left _ ht
 let A:= i.length R; let z:= |i.mark R q|; let m:= Real.exp ((σ/4)*A); let w:= pairBill Gp P
 rw [mul_add, add_mul]; change _≤ price0 Γ P* _+(fee1K Γ P*P.threshold^2)* _; refine add_le_add ?_ ?_
 · rw [mul_comm z]; rw [mul_assoc]; apply mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (Real.exp_monotone ?_) (abs_nonneg _)) l; exact mul_le_mul_of_nonneg_right (by have he:=p.width; linarith) (by positivity)
 let D:=i.length R; let f:= fee1K Γ P * P.threshold^2; let S:=rowCost Gp P D; let Q:= lowCost Gp P D
 calc
   _ = f*(z*S*Real.exp (D/q.relaxation+D/q.relaxation+σ/4*D)):=by unfold D z S f; unfold D; rw [Real.exp_add,Real.exp_add]; ring
   _ ≤ f*(z*Q*Real.exp (σ/2*D)):=by
      have htD:(D:ℝ)/q.relaxation≤ σ/8*D:=by
         have hx:= hv.2.1; have ht:1/q.relaxation≤ σ/8:= (div_le_iff₀ q.radius_pos).mpr (by linarith)
         exact (Eq.trans_le (by ring : (D:ℝ)/q.relaxation=1/q.relaxation*D) (mul_le_mul_of_nonneg_right ht (Nat.cast_nonneg D)))
      have hq:S≤Q:= (le_add_of_nonneg_left (faceCost_nonneg ..)).trans (le_add_of_nonneg_left (mul_nonneg (by norm_num) (pair_nonneg ..)))
      apply mul_le_mul_of_nonneg_left _ h; exact mul_le_mul (mul_le_mul_of_nonneg_left hq (abs_nonneg _)) (Real.exp_monotone (by linarith only [htD])) (Real.exp_pos _).le (mul_nonneg (abs_nonneg _) (low_nonneg ..))
open Push.AbsoluteSums Footprint
lemma stun_B (hk:Geo.Width P q σ)(c:ℝ)(v:0≤c)(pQ:c/(P.B:ℝ) ≤ σ/8) : Ac.Hit (fun i:AnalyticBridge.VerifiedReset.Seat (More n) × Low=>i.1.spread (Low.home R i.2 P (0:Site (More n)))) P.B (fun i=> prix_b R i.2 q Γ P) c (Footprint.payment 1 P.B 0 (σ/16) 1 (Fintype.card Signed * price_μ q P σ C Γ) c Geo.lowCount):=by
 let g (i : Low) := prix_b R i q Γ P; have hg i : 0 ≤ g i := cap_e Γ P R _ i hc; have he := Quotes.channel_anchored (n:=More n) _ g hg (kap_H Γ P R p hc hk)
 have hp:0 < σ:=p.width; have hQ:0 < (P.B:ℝ):=Nat.cast_pos.mpr P.B_pos
 refine Footprint.assigned (id : Site (More n)→ Site (More n)) 1 (fun Y : Support (More n)=>by simp) (fun i :AnalyticBridge.VerifiedReset.Seat (More n) × Low => i.1.2) (fun i=> g i.2) (fun i=> hg i.2) (fun i=> i.2.length R) (fun i:AnalyticBridge.VerifiedReset.Seat (More n) × Low=> i.1.spread (Low.home R i.2 P (0: Site (More n)))) he P.B 0 P.B (C:=1) (v:=Geo.lowCount) (a:=c) (ε:=σ/16) (v':=(P.B:ℝ)⁻¹) ?_ ?_ zero_le_one ⟨v,by linarith,by rw [← div_eq_mul_inv]; linarith⟩ (fun i =>g i.2) (fun i=>hg _) (fun _ => by simp)
 · rintro i y hy; obtain ⟨j,t,rfl⟩:= Finset.mem_image.mp hy
   simpa only [affine,separation_translate, Signed.act_zero,zero_add,id_eq] using! (spin_separation i.1.1 i.1.2 j (0:Site (More n))).trans_le (low_dist P R _ t)
 intro i; rw [AnalyticBridge.VerifiedReset.Seat.visit_count]; apply le_of_mul_le_mul_left (a:=(P.B:ℝ)) ?_ hQ; rw [mul_add,← mul_assoc,mul_inv_cancel₀ hQ.ne',one_mul]; exact_mod_cast low_geometry P R i.2 (0:Site (More n))
variable (T: Ids n)(hp:DayT P.order Γ)(hw:Decent q P)(ht:Geo.Width P q σ)
omit p
include hp hw
lemma gift_W(x:Lane n)(a:ℝ)(D:Support (More n))(h':0 ≤ h): Medal P (χx P R x).val D (regV T P R q a x (χx P R x) D) h (|a| *prix_b R x.2 q Γ P):=by
 unfold regV chasmR; rw [Pi.single_eq_same]; let G:=vow_b R x.1 x.2 T Γ hp hc hw (Y:=D) (h:=h); apply (G.rum _).big; rw [Real.norm_eq_abs, abs_mul, abs_of_pos factor_pos]; exact mul_le_mul_of_nonneg_right (mul_le_of_le_one_left (abs_nonneg _) factor_le) (G.wage h')
end YM.CF.Taxi
