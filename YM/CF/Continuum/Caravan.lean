import YM.CF.Continuum.Carousel
import YM.CF.Continuum.Episode
import YM.CF.Continuum.Symmetric
import YM.CF.Continuum.Allowed
/-!
# Which expanding periods? Retain astronaut and grants

Details: use the SAME reconstruction apparatus on the old UV-limit witness and
on new periods. No separate positive measures. We express the non-anchored
inhabitance range and produce history witnesses `Session`s and normalized limit
on this permit. At anchor mark-specialized; may choose same f. This is phase I,
period extension NOT common-limit yet. Stamp requirements don't connect bare-data
values across those periods (including β_l). Need cross-period bounds.
-/
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
open Graph Girt
variable {M M0 : Side}
local notation "hatQ" => hat R.L x
open Jade.Earn
namespace Carousel
section
variable {KX b' vL c' l' b a' D E' C0 h1 r:ℝ}{kT d' :ℕ} (P_: Pic.Span W.pearl KX b' vL c' l' b kT)(Q:Roe.Port P_ D E' C0 h1 r d')(hX:C0 ≤ h)(hp:1≤h)
open MeasureTheory Pastures
local notation "Bₓ" v=> cell v B R.L 0
local notation "Mₓ" v=> Vale.mesh v R.L 0
local notation "Mζ" x=> oYY V N0 J x
private theorem zero_ap (X: Carousel V a p i N0 J q h R0 δ x M l): Graph.SkinT (X.E 0) (X.Y 0) d:= Mint.Stop.sage _ _ _ (loomActs V a p i N0 J q h R0 δ X 0) ((X.owns 0 (Nat.zero_le _)).width ▸ X.pole 0)

private theorem ordered_stop (P:∀ (x:ℝ)(M:Side)(l:ℕ),Carousel V a p i N0 J q h R0 δ x M l → Prop)
    (g:∀ (x:ℕ→ℝ)(M:ℕ→Side)(l:ℕ→ℕ)(S':∀ s,Carousel V a p i N0 J q h R0 δ (x s) (M s*N') (l s)), (∀ j:ℕ,Allowed V N0 J (x j) (M j))→ Tendsto x atTop atTop→ ∀ᶠ i in atTop,P (x i) (M i*N') (l i) (S' i)): ∀ᶠ x in atTop, ∀ M:Side, Allowed V N0 J x M →∀ l:ℕ,∀ v0:Carousel V a p i N0 J q h R0 δ x (M*N') l, P x (M*N') l v0:= by
 rw [eventually_atTop]; by_contra! hh
 choose f t m P0 l X H using fun i:ℕ=>hh i; exact (g f m l X P0 (tendsto_atTop_mono t tendsto_natCast_atTop_atTop)).exists.elim fun i v=> (H i) v
open YM.Next.Rank
include Q hX hp
lemma eventH :∃ K':ℝ,0<K'∧∀ᶠ x in atTop,∀ M:Side, Allowed V N0 J x M→∀ l:ℕ,∀ T:Carousel V a p i N0 J q h R0 δ x (M*N') l,Tableau (Vale.mesh (M*N') R.L 0) (T.E 0) (T.Y 0) U (soaked x) K':=by
 obtain ⟨P⟩:= YM.Next.Rank.exists_budget SU.group; obtain ⟨f,s,t⟩:= Window.basePrice P_ P Q hX 1 K.top.paths V.W.bar (levelQ W.C) K.top.width K.top.clip.direct (cashU W.C) K.top.clip.linear K.top.clip.tail_pos (cash_v _) (wing_budget V) -- ABI
 refine ⟨f,s,ordered_stop V a p i N0 J q h R0 δ (fun x M l T=>Tableau (Vale.mesh M R.L 0) (T.E 0) (T.Y 0) U (soaked x) f) ?_⟩
 intro g F H X u k; exact t _ g _ (fun i=>(X i).E 0) (fun i=>(X i).Y 0) (openStart V a p i N0 J q h R0 δ hp X (by_series V N0 J k u)) (by simpa only [one_mul] using logAllows V N0 J k u) (Eventually.of_forall (f:=atTop) fun i'=> zero_ap V a p i N0 J q h R0 δ (X i'))
end
section
include V
private lemma gainBelow (x:ℝ)(t:0<x) (k:ℕ)(M B:Side) (A:GramM (cell M B R.L k))(D:GramM (cell M B R.L (k+1))) {C G:ℝ}(w:0≤G)(s:2*G≤C): budgetCharge D (soaked (hat R.L x (k+1))) (-C) ≤ budgetCharge A (soaked (hat R.L x k)) (-C)+curve_F R.L (More (cell M B R.L k)) (More (cell M B R.L (k+1))) (hat R.L x k) G:=by
 let a:= hat R.L x k; let b:= hat R.L x (k+1); let r:= cell M B R.L k; let p:= cell M B R.L (k+1); let C₀:=massMeter r; let F:=massMeter p
 have he:x≤a:= Vale.crown ..; have ha:a≤b:=by unfold a b hat; push_cast; linarith [Vale.pitch R.L]
 let X:=soaked a; let Y:=soaked b; have hx:Y ≤ X:= inv_anti₀ (Real.sqrt_pos.mpr (t.trans_le he)) (Real.sqrt_le_sqrt ha); have ht:0<Y:=by change 0<(Real.sqrt b)⁻¹; apply inv_pos.mpr; exact Real.sqrt_pos.mpr ((t.trans_le he).trans_le ha)
 have hi:strengthLog Y ≤ strengthLog X:= mul_le_mul_of_nonneg_left (Real.log_le_log ht hx) (Nat.cast_nonneg _)
 have hp:(0:ℝ)≤C₀:=zero_le_one.trans (money_pos _); have hz:2*C₀≤F:= full_a V ..; have hh:C₀≤F:= by linarith
 unfold curve_F pathFees; rw [heir_s V,←same_room,←same_room]
 change F*(3*strengthLog Y+-C) ≤ C₀*(3*strengthLog X+-C)+_
 change _ ≤ _+(3*(F-C₀)*strengthLog Y-G*F); nlinarith only [mul_le_mul_of_nonneg_left hi hp, mul_le_mul_of_nonneg_left s (show 0≤F-C₀ from sub_nonneg.mpr hh), mul_le_mul_of_nonneg_left hz w] -- ht
end
-- growth coupon assertion at this *same* cutoff, not any inclusive retuning uniform only given builders.
abbrev Promoted (M:Side)(b:ℝ)(S:Carousel V a p i N0 J q h R0 δ x M l): Prop:= ∀ j<l, ‖Complex.exp (S.E (j+1)).v‖ * Real.exp (curve_F R.L (More (cell M B R.L j)) (More (cell M B R.L (j+1))) (hat R.L x j) b) ≤ ‖Complex.exp (S.E j).v‖
variable {CΩ K':ℝ} (s:0 < x)(u:0 ≤ CΩ)(w:2*CΩ ≤ K') (X:Carousel V a p i N0 J q h R0 δ x M l)
variable (Y:Promoted V a p i N0 J q h R0 δ M CΩ X)(k_:Real.exp (budgetCharge (X.E 0) (soaked x) (-K')) ≤ rateBet (X.E 0) (X.Y 0) U)
include u w s Y k_
theorem fullPaid (j:ℕ)(p:j≤ l) : Real.exp (budgetCharge (X.E j) (soaked (hat R.L x j)) (-K')) ≤ rateBet (X.E j) (X.Y j) U:=by
 induction j with
 | zero=> rw [show hat R.L x 0=x by simp [hat]]; exact k_
 | succ j ih=>
    let Q:=budgetCharge (X.E j) (soaked (hat R.L x j)) (-K'); let L:= Complex.exp (X.E j).v; let L':= Complex.exp (X.E (j+1)).v; let β:= rateBet (X.E j) (X.Y j) U; let z:=curve_F R.L (More (cell M B R.L j)) (More (cell M B R.L (j+1))) (hat R.L x j) CΩ; let D:= partitionZ (X.E X.top) U (X.Y X.top)
    have ht:‖L‖* Real.exp Q ≤ ‖D‖:=by
       have he:=ih (by omega); unfold rateBet at he; rw [Complex.exp_neg,norm_mul,norm_inv,X.balance j ((by omega:j≤l).trans X.probed)] at he; exact (le_inv_mul_iff₀ (norm_pos_iff.mpr (Complex.exp_ne_zero _))).mp he -- balance ???
    unfold rateBet; rw [Complex.exp_neg,norm_mul,norm_inv,X.balance _ (p.trans X.probed)]
    apply le_trans (Real.exp_monotone (gainBelow V x s j M B _ _ u w)); rw [Real.exp_add]; apply (le_inv_mul_iff₀ (norm_pos_iff.mpr (Complex.exp_ne_zero _))).mpr
    calc
       _ = (‖L'‖*Real.exp z)*Real.exp Q:=by unfold L' z Q; ring
       _ ≤ _:= (mul_le_mul_of_nonneg_right (Y j p) (Real.exp_pos _).le).trans ht
omit u w s Y k_
local notation "Bₓ" t=> cell t B R.L
variable {K0:ℝ}(hp:1≤h)(S:Carousel V a p i N0 J q h R0 δ x M l)
lemma sailed (j:ℕ)(t:j≤l) : Integrable (denZ (S.E j) U (S.Y j)) (city _):=by
 let p:= footprint_B V a p i N0 J q h R0 δ S j t; have hg:= Girt.sailW (S.E j) (ward_m p ((S.note j t).lot_p le_rfl le_rfl)) W.pearl V.note W.health (by have h:= V.L.lobby; have he:=R.order_cut; omega) J.n _ (loomActs V a _ i N0 J q h R0 δ S j) (J.gran.trans (S.roof j).size)
 exact Integrable.of_bound hg.meas.aestronglyMeasurable _ (Eventually.of_forall hg.cost.choose_spec)
include S in
lemma epochAffordable (j:ℕ) : ((radiusB (hat R.L x j) +1:ℕ):ℝ) ≤ massMeter (cell M B R.L j):=by
 have ht(j:ℕ):= (S.val.clear S.tip 0 j).1.size
 let B':= More (cell M B R.L j); have he:100*(1+radiusB (hat R.L x j)) ≤ B'.val:= ht j; have hv0:=B'.property
 change _ ≤ ((B'.val^4:ℕ):ℝ); apply Nat.cast_le.mpr; apply le_trans (b:= B'.val) (by omega) ?_; exact le_trans (b:=B'.val^1) (by simp) (Nat.pow_le_pow_right hv0 (by omega))
open Next.Rank
variable (O:HaarBudget SU.group)
private def myCost(C:ℝ):=4*C+3*1*2^4+180*45*6*C
abbrev costPlan(V:Grace K R L)(S:ℝ) (O:HaarBudget SU.group):= myCost S + (upperMoney O K.top.paths V.W.bar (strength K.top.clip) 1 + SU.group.lieDim *2*3)
include hp
set_option maxHeartbeats 800000 in
lemma toils_κ (j:ℕ)(p':j ≤ l) (χ:BigHeart (hat R.L x j))(hE: dleaf R.L (hat R.L x j) ≤ 1) : TV (S.E j) (S.Y j) U ≤ Real.exp (budgetCharge (S.E j) (soaked (hat R.L x j)) (costPlan V (cashU W.C) O)):=by
 let y:=hat R.L x j; let T:=temp y; let Z:= S.E j; let M':=cell M B R.L j; let N:=massMeter M'; let t:= Z.beta; let F:= soaked t; let w:=S.owns j (p'.trans S.probed); let q':= S.val.boot j; have hZ:Z.p.threshold=T:=show _ from w.width ▸ q'.1; have he:Z.funds= K.top.clip:= w.fund.symm
 obtain ⟨p0,pA,tq,v,qb⟩:=χ.budget t (S.sift j (p'.trans S.probed))
 have hβ: F ≤ Z.p.threshold:= hZ ▸ pA; let hone:=amplifier t tq; obtain ⟨-,_,hu,b⟩:=hone; have hi:= sailed V a p i N0 J q h R0 δ S j p'
 let β':=upperMoney O K.top.paths V.W.bar (strength K.top.clip) 1; let k:=cashU W.C; let C:=myCost k; have hk:0≤k:= cash_v _; let γ0:= dleaf R.L y
 have hx : TV (S.E j) (S.Y j) U ≤ _ := payLedger O (S.E j) (S.Y j) (expense V a p i N0 J q h R0 δ S j p' hp) (footprint_B V a p i N0 J q h R0 δ S j p') (loomActs V a p i N0 J q h R0 δ S j) hu b hβ (J.gran.trans (S.roof _).size) hp ((level_p _).le) hk (hi.smul (Complex.exp (-Z.v))) -- parameter P vs U
 apply hx.trans; have hv: |Real.log F|≤ N*1:=by rw [mul_one]; refine qb.trans ?_; exact le_trans (by push_cast; exact le_rfl : (radiusB (hat R.L x j):ℝ)+1≤ ((radiusB (hat R.L x j)+1:ℕ):ℝ)) (epochAffordable V a p i N0 J q h R0 δ S j)
 apply le_trans (mul_le_mul_of_nonneg_left (upperRate O Z (wing_budget V) hu b hv (hZ.symm ▸ p0) _ (strength_pos K.top.clip) (by rw [he])) (Real.exp_pos _).le)
 rw [←Real.exp_add]; apply Real.exp_monotone; let s:ℝ:=SU.group.lieDim
 have he: strengthLog F ≤ strengthLog (soaked y)+s*2:= (mul_le_mul_of_nonneg_left v (Nat.cast_nonneg _)).trans_eq (mul_add s (Real.log (soaked y)) 2)
 have hu: 0≤N:=zero_le_one.trans (money_pos _); change flagBill M' γ0 γ0 k+ N*(3*strengthLog F+β') ≤ N*(3*strengthLog (soaked y)+(C+(β'+s*2*3)))
 have hC: flagBill M' γ0 γ0 k ≤ N*C:= flagBound _ 1 k _ _ hE hE zero_le_one hk; linarith only [hC, mul_le_mul_of_nonneg_left he hu]
omit hp
lemma grows {x:ℝ}(M:Side)(S:Carousel V a p i N0 J q h R0 δ x M l)(Y: Promoted V a p i N0 J q h R0 δ M CΩ S)(hv:0<CΩ)(s:0<x)(K0 K':ℝ)(e: CΩ+CΩ ≤ K')(z:K0≤K')(T:Tableau (Vale.mesh M R.L 0) (S.E 0) (S.Y 0) U (soaked x) K0) : ∀ j≤l, Real.exp (budgetCharge (S.E j) (soaked (hat R.L x j)) (-K')) ≤ rateBet (S.E j) (S.Y j) U := by
 intro j p'; refine fullPaid V a p i N0 J q h R0 δ s hv.le (by linarith) S Y ?_ j p'; exact (Real.exp_monotone (budgetLe _ _ _ _ (neg_le_neg z))).trans T.lowB
-- extends above starting any T, delete t
include hp
lemma certify_loop (t:0<CΩ) (K0:ℝ) :∃ K':ℝ, 0<K'∧ ∀ᶠ x:ℝ in atTop,∀ (M:Side)(l:ℕ)(S:Carousel V a p i N0 J q h R0 δ x M l),Promoted V a p i N0 J q h R0 δ M CΩ S → Tableau (Vale.mesh M R.L 0) (S.E 0) (S.Y 0) U (soaked x) K0 → ∀ j≤l, Tableau (Vale.mesh M R.L j) (S.E j) (S.Y j) U (soaked (hat R.L x j)) K' := by
 let O:=Classical.choice (Next.Rank.exists_budget SU.group); let R':=costPlan V (cashU W.C) O; let K:= max (max K0 R') (CΩ+CΩ); have hp₁: max K0 R'≤ K:=le_max_left ..; have ht:CΩ+CΩ≤K:=le_max_right ..; refine ⟨K,lt_of_lt_of_le (by positivity) ht,?_⟩
 obtain ⟨u,hu⟩:= eventually_atTop.mp (moneyK'.and (((dev_R R).1.low (k:=1) (by omega)).spine.eventually (ge_mem_nhds zero_lt_one))); filter_upwards [eventually_ge_atTop u,eventually_gt_atTop (0:ℝ)] with x h1 h2 M l S hg hd j v; have hv:= hu (hat R.L x j) (h1.trans (Vale.crown ..)); refine ⟨sailed V a _ i N0 J q h R0 δ S j v,grows V a p i N0 J q h R0 δ M S hg t h2 K0 K ht ((le_max_left ..).trans hp₁) hd j v,?_⟩
 exact (toils_κ V a p i N0 J q h R0 δ hp S O j v hv.1 hv.2).trans (Real.exp_monotone (budgetLe (S.E j) _ _ _ ((le_max_right K0 R').trans hp₁)))

end Carousel
end YM.CF.Py.Period
