import YM.CF.Continuum.Haven
import YM.CF.Continuum.Expanding
import YM.CF.Continuum.Receipt
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Py.Period
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
variable{N P B:Side}{K:Teller SU.group}{G:Ratio (mid N B) (mid P B)}{R:Patch}{L:ChartRatio SU.group}
variable {d e η z g A B':ℝ} {j k k' m n l:ℕ}
variable (V:Grace K R L)
open Lich.Muster Lor
open Jet Vol Rel
local notation "G5"=>SU.group
variable {x y0 β:ℝ}(pp:BudgetPoint){t₀ v v₁ p11 p22 p3 p4:ℝ}
local notation "SN"=> Site (Domain N B)
open Cascade
open Fief
open Yaw Pig
open Wray
open Lich.Muster Push.AbsoluteSums
open Iva Eire
local notation "ζ"=> (radiusB x)
open Trees Footprint Iva Eire
open Jade
open Oath Feu Feu.Corset Ione Nor Haro Beau Salt Vow
set_option maxHeartbeats 800000
variable {U:Grasp V.U B d}{W:GivenX V U}
variable (a:ℝ)(p i N0 k₀:ℕ)
variable {N':Side}(J:Robes N' V W)(q:Chi)(h:ℝ)(R0 δ:ℝ→ℝ)
local notation "Lr"=>dleaf R.L
open CF.Mint MeasureTheory
open CF.Window
open Graph Window Jade.Earn

local notation "Bₓ" t=> cell t B R.L
variable {K0 CΩ:ℝ}{M:Side}(hp:1≤h)(S:Session V a p i N0 J q h R0 δ x M l)
lemma Session.sailed (j:ℕ)(t:j≤l) : Integrable (denZ (S.E j) U (S.Y j)) (city _):=by
 let p:= footprint_B V a p i N0 J q h R0 δ S j t; have hg:= Girt.sailW (S.E j) (ward_m p ((S.scale.note.note j t).lot_p le_rfl le_rfl)) W.pearl V.note W.health (by have h:= V.L.lobby; have he:=R.order_cut; omega) J.n _ (loomActs V a _ i N0 J q h R0 δ S j) (J.gran.trans (S.scale.roof j).size)
 exact Integrable.of_bound hg.meas.aestronglyMeasurable _ (Eventually.of_forall hg.cost.choose_spec)
include S in
lemma epochAffordable (j:ℕ) : ((radiusB (hat R.L x j) +1:ℕ):ℝ) ≤ massMeter (cell M B R.L j):=by
 have ht(j:ℕ):= (S.val.clear S.tip 0 j).1.size
 let B':= More (cell M B R.L j); have he:100*(1+radiusB (hat R.L x j)) ≤ B'.val:= ht j; have hv0:=B'.property
 change _ ≤ ((B'.val^4:ℕ):ℝ); apply Nat.cast_le.mpr; apply le_trans (b:= B'.val) (by omega) ?_; exact le_trans (b:=B'.val^1) (by simp) (Nat.pow_le_pow_right hv0 (by omega))
open Next.Rank
variable (O:HaarBudget SU.group)
private def markCost(C:ℝ):=4*C+3*1*2^4+180*45*6*C
abbrev costPlan(V:Grace K R L)(S:ℝ) (O:HaarBudget SU.group):= markCost S + (upperMoney O K.top.paths V.W.bar (strength K.top.clip) 1 + SU.group.lieDim *2*3)
include hp
set_option maxHeartbeats 800000 in
lemma drives_epoch (j:ℕ)(p':j ≤ l) (χ:BigHeart (hat R.L x j))(hE: dleaf R.L (hat R.L x j) ≤ 1) : TV (S.E j) (S.Y j) U ≤ Real.exp (budgetCharge (S.E j) (soaked (hat R.L x j)) (costPlan V (cashU W.C) O)):=by
 let y:=hat R.L x j; let T:=temp y; let Z:= S.E j; let M':=cell M B R.L j; let N:=massMeter M'; let t:= Z.beta; let F:= soaked t; let w:=S.scale.note.owns j p'; let q':= S.val.boot j; have hZ:Z.p.threshold=T:=show _ from w.width ▸ q'.1; have he:Z.funds= K.top.clip:= w.fund.symm
 obtain ⟨p0,pA,tq,v,qb⟩:=χ.budget t (S.scale.note.sift j p')
 have hβ: F ≤ Z.p.threshold:= hZ ▸ pA; let hone:=amplifier t tq; obtain ⟨-,_,hu,b⟩:=hone; have hi:= Session.sailed V a p i N0 J q h R0 δ S j p'
 let β':=upperMoney O K.top.paths V.W.bar (strength K.top.clip) 1; let k:=cashU W.C; let C:=markCost k; have hk:0≤k:= cash_v _; let γ0:= dleaf R.L y
 have hx : TV (S.E j) (S.Y j) U ≤ _ := payLedger O (S.E j) (S.Y j) (expense V a p i N0 J q h R0 δ S j p' hp) (footprint_B V a p i N0 J q h R0 δ S j p') (loomActs V a p i N0 J q h R0 δ S j) hu b hβ (J.gran.trans (S.scale.roof _).size) hp ((level_p _).le) hk (hi.smul (Complex.exp (-Z.v))) -- parameter P vs U
 apply hx.trans; have hv: |Real.log F|≤ N*1:=by rw [mul_one]; refine qb.trans ?_; exact le_trans (by push_cast; exact le_rfl : (radiusB (hat R.L x j):ℝ)+1≤ ((radiusB (hat R.L x j)+1:ℕ):ℝ)) (epochAffordable V a p i N0 J q h R0 δ S j)
 apply le_trans (mul_le_mul_of_nonneg_left (upperRate O Z (wing_budget V) hu b hv (hZ.symm ▸ p0) _ (strength_pos K.top.clip) (by rw [he])) (Real.exp_pos _).le)
 rw [←Real.exp_add]; apply Real.exp_monotone; let s:ℝ:=SU.group.lieDim
 have he: strengthLog F ≤ strengthLog (soaked y)+s*2:= (mul_le_mul_of_nonneg_left v (Nat.cast_nonneg _)).trans_eq (mul_add s (Real.log (soaked y)) 2)
 have hu: 0≤N:=zero_le_one.trans (money_pos _); change flagBill M' γ0 γ0 k+ N*(3*strengthLog F+β') ≤ N*(3*strengthLog (soaked y)+(C+(β'+s*2*3)))
 have hC: flagBill M' γ0 γ0 k ≤ N*C:= flagBound _ 1 k _ _ hE hE zero_le_one hk; linarith only [hC, mul_le_mul_of_nonneg_left he hu]
omit hp
lemma Session.grows {x:ℝ}(M:Side)(S:Session V a p i N0 J q h R0 δ x M l)(Y: RootMoney V a p i N0 J q h R0 δ M CΩ S)(hv:0<CΩ)(s:0<x)(K0 K':ℝ)(e: CΩ+CΩ ≤ K')(z:K0≤K')(T:Tableau (Vale.mesh M R.L 0) (S.E 0) (S.Y 0) U (soaked x) K0) : ∀ j≤l, Real.exp (budgetCharge (S.E j) (soaked (hat R.L x j)) (-K')) ≤ rateBet (S.E j) (S.Y j) U := by
 intro j p'; refine fullPaid V a p i N0 J q h R0 δ s hv.le (by linarith) S Y ?_ j p'; exact (Real.exp_monotone (budgetLe _ _ _ _ (neg_le_neg z))).trans T.lowB
-- extends above starting any T, delete t
include hp
lemma Session.certify_loop (t:0<CΩ) (K0:ℝ) :∃ K':ℝ, 0<K'∧ ∀ᶠ x:ℝ in atTop,∀ (M:Side)(l:ℕ)(S:Session V a p i N0 J q h R0 δ x M l),RootMoney V a p i N0 J q h R0 δ M CΩ S → Tableau (Vale.mesh M R.L 0) (S.E 0) (S.Y 0) U (soaked x) K0 → ∀ j≤l, Tableau (Vale.mesh M R.L j) (S.E j) (S.Y j) U (soaked (hat R.L x j)) K' := by
 let O:=Classical.choice (Next.Rank.exists_budget SU.group); let R':=costPlan V (cashU W.C) O; let K:= max (max K0 R') (CΩ+CΩ); have hp₁: max K0 R'≤ K:=le_max_left ..; have ht:CΩ+CΩ≤K:=le_max_right ..; refine ⟨K,lt_of_lt_of_le (by positivity) ht,?_⟩
 obtain ⟨u,hu⟩:= eventually_atTop.mp (moneyK'.and (((dev_R R).1.low (k:=1) (by omega)).spine.eventually (ge_mem_nhds zero_lt_one))); filter_upwards [eventually_ge_atTop u,eventually_gt_atTop (0:ℝ)] with x h1 h2 M l S hg hd j v; have hv:= hu (hat R.L x j) (h1.trans (Vale.crown ..)); refine ⟨Session.sailed V a _ i N0 J q h R0 δ S j v,Session.grows V a p i N0 J q h R0 δ M S hg t h2 K0 K ht ((le_max_left ..).trans hp₁) hd j v,?_⟩
 exact (drives_epoch V a p i N0 J q h R0 δ hp S O j v hv.1 hv.2).trans (Real.exp_monotone (budgetLe (S.E j) _ _ _ ((le_max_right K0 R').trans hp₁)))
#print axioms Session.certify_loop
end YM.CF.Py.Period
