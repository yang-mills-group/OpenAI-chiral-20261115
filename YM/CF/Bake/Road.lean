import YM.CF.Bake.Pal
set_option autoImplicit false
set_option maxHeartbeats 350000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Jade
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
variable{N P B:Side}{S:StepData (Domain N B) (Domain P B)}{T: Tube SU.group S}{K:Teller SU.group}{G:Ratio (mid N B) (mid P B)}{R:Patch}{L:ChartRatio SU.group}
variable {d e η t z g A B':ℝ} {j k k' m n l:ℕ}
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
variable (F:Pilot)(Z:Pluck R) (I: Stake.Isle){σ:ℝ}(Q: Tun I Z F σ){H:Muster G S x d T}
variable {U:Grasp V.U B d}{W:GivenX V U}{X: GramM (mid N B)}{Y: GramM (mid P B)}(M: Sheep V U W G Y.J X.J (k+2) n A)(P_:∀ X: Support (Domain P B),Lend P B d X)
variable {r:ℕ}
variable (w':Hive.Vista U Y.J.M Y.J.P P_ (k+2) M.q ((Fintype.card Play:ℝ)*t) M.lot M.tone)
variable (V_:ℝ)
local notation "Φ"=> F.hat R x
variable(Y1: Monk SU.group S)
-- Rflare independent of Y except Bravo, discounted pref before.All
variable {a A' ε b α γ:ℝ}{q q':Chi}{u u0 s:ℝ}(ε':Fend V H M Z F q Y.p X.p γ α j l r)
variable{G₀:Scree.Loom (mid N B)}{G₁:Scree.Loom (mid P B)}(D_: Girt.BaseL U G Y G₀ G₁ q' u)(L0: StageP V H Y X U)
variable (k₀ k₁:ℕ)(s0:ℝ)(A_: Roof (mid N B) s s0 k₀ G₀)(A₁: Roof (mid P B) s s0 k₁ G₁)(heV:k₀+k₁ ≤ radiusB x)(pV:1<I.fine)(k_W:5*Y.p.B +4≤10*radiusB x)(η':l≤18)(ss:s ≤ s0)(tK:s0 < d)(hT:0 < s) (pT:0<u)(hU:u< firstRadius SU.group)
variable (Uq:(j+110)*radiusB x+14 ≤ r) (pQ:2*((j+5)*radiusB x) ≤ r)(ht:0 ≤ V_)(hY:Y.p.order=k)(pX:X.p.order=k)(hK:radiusB x ≤ X.p.B)
variable (P_B:Stake.PondP V F x s u j l (k+2)) (K0: Troupe S r (Words S))(P0: Eire.Ride S)
open Plume
open Nor
variable {c vL:ℝ}(Pz: Folk S r (Words S)→ Track (Eire.Ride S) ℝ)
open scoped Classical
variable {γ':ℝ}
variable (h0:vL=(tolQ X.p).supportExponent+γ')(uQ:X.p.B=radiusB x)(p0:0<γ')
local notation "Ue"=> Troupe S r (Words S) → Palot.leaf (Site (Domain N B)) → Raid (LeanV (Single (mid N B)))
local notation "Ωe"=> Troupe S r (Words S) → Palot.leaf (Site (Domain N B)) → Orbit (mid N B) → Cipher (mid N B)
-- Ribbon vector measured local Aux Proto.SP.Anchor.Norin. Does not assume vacuum.
open Vow Bake
variable (KcV:Troupe S r (Words S) → Palot.leaf (Site (Domain N B)) → Raid (LeanV (Single (mid N B))))(F':Troupe S r (Words S) → Palot.leaf (Site (Domain N B)) → Orbit (mid N B) → Cipher (mid N B))(Pinc: GroV V F Z M P_ w' ε' D_ KcV F' V_ c γ')
local notation "Zκ"=> pence_v X.p KcV V_
local notation "Zp"=> cone_f F'
 
variable {vS wS:ℝ}(vs:vS<s)(wp:0<wS)(vw:wS<u)(hB:∀ (Q: Monk SU.group S), ‖Q.z‖≤ F.hat R x→ Chir Q x→ Bell S Q x T H.trot H.room H.post H.beta vS wS)(u_B:3 ≤ X.p.B)
abbrev angK(B k p:ℕ)(a c:ℝ):= miteV B k p a c
abbrev ringT(B:ℕ)(u:ℝ):= u * degreePrice B u 1^0*(1-degreePrice B u 1)⁻¹
-- explicit installments
abbrev DriveT (B k p:ℕ)(a c r x:ℝ):Prop:=miteV B k p a c ≤ r ∧ 0<r ∧ degreePrice B r 1 < 1 ∧ ringT B r ≤ 1 ∧ 0 < x ∧degreePrice B x 1 < 1 ∧ r+Real.exp 1 *ringT B r ≤ x
abbrev stopE(B k p:ℕ)(r:ℝ):=reserveT p k B (1+(1:ℝ))*ringT B r
abbrev stopK(B k p:ℕ)(r:ℝ):=reserveT p k B 1 * ringT B r
local notation "Fe"=> nixV (cone_f F')
local notation "fE"=> nixV (pence_v X.p KcV V_)
local notation "rK"=> budgetR (roomV X.p (nixV (cone_f F')) (cone_f F') 0)
variable (xv yv:ℝ)(dV:DriveT X.p.B X.p.order X.p.power γ' c xv yv)(tP:1≤V_)
local notation "yp"=> (degreePrice X.p.B xv 1)
local notation "zp"=> (degreePrice X.p.B yv 1)
include ε' Pinc A_ A₁ heV u_B ss tK L0 vs wp vw hB uQ dV tP
lemma lev_BG : ∃ (E:RegBudget (mid N B))(Rν:ForceBudget (mid N B)), IncX (fun _=>False) E X.p V_ (stopE X.p.B X.p.order X.p.power xv) ∧ Dark (fun _=>False) Rν X.p V_ (stopK X.p.B X.p.order X.p.power yv) ∧∀ v:Orbit (mid N B),Rue.FleetS X.p.threshold v.1 → hGas (flags X.p.threshold v.1) (Jade.cargoL X.p F' v)=exp (exponentL X.p E v.1)*fueled X.p Rν v:=by
 obtain ⟨x1,x2,x3,x4,x5,x6,x7⟩:=dV; have x8:= x2.le; have hv:0 ≤ V_:=zero_le_one.trans tP
 let Kb:=cone_f F'; let Vb:=pence_v X.p KcV V_; let Fe':= nixV Kb; let f':= nixV Vb; let L':= X.p.supportExponent; let W:= reserveT X.p.power X.p.order X.p.B
 let A:Ids (mid N B):= Classical.choice inferInstance; let E:= cloveE (FeeD X.p Fe') A
 let Cκ:= spiceX V F Z M P_ w' V_ ε' D_ L0 _ _ _ A_ A₁ heV ss tK hv KcV F' Pinc vs wp vw hB u_B; let cκ:= pep_f V F Z M P_ w' V_ ε' D_ L0 _ _ _ A_ A₁ heV ss tK KcV F' Pinc vs wp vw hB
 let P':=spiceF V F Z M P_ w' V_ ε' D_ L0 _ _ _ A_ A₁ heV ss tK hv KcV F' Pinc vs wp vw hB u_B
 have q1:Ready Palot.stern X.p.B f' (X.p.supportExponent+1+1) xv 1 (degreePrice X.p.B xv 1):=by
    refine ⟨x2,zero_lt_one,le_rfl,x3,fun i=>(Cκ i).wage hv,fun i=>?_⟩
    have he:= (lad_e V F Z M P_ w' V_ ε' D_ hv uQ KcV F' Pinc i).trans x1; let F(j:Aura (mid N B)):= if i∈j.val then f' j*currency X.p.B (X.p.supportExponent+1+1+1) j.val else 0; have hp(i):0 ≤ F i:=by unfold F; split; exact mul_nonneg ((Cκ i).wage hv) (Real.exp_pos _).le; exact le_rfl
    apply budget_of_sum hp; intro X; exact (sum_le_sum_of_subset_of_nonneg (subset_univ X) (fun j _ _=>hp j)).trans (by unfold F; rw [←Finset.sum_filter]; exact he)
 have hx: 0≤ X.p.supportExponent+1:=add_nonneg X.p.exponent_pos.le zero_le_one
 refine ⟨E,budgetR (roomV X.p Fe' Kb 0),sixV Fe' cκ A f' (show Ready _ _ _ (X.p.supportExponent+(1+1)) _ _ _ from (add_assoc X.p.supportExponent 1 1) ▸ q1) tP Cκ (add_pos zero_lt_one zero_lt_one),?_,fun U h=>?_⟩
 · let P:= (0:Cusp (mid N B))
   have H :Dark (fun _=>False) (budgetR (roomV X.p Fe' Kb 0)) X.p V_ (W 1 * (1⁻¹*ringT X.p.B yv)):= dark_F (κ:= (1:ℝ)) (Q:=P) (L₁:=0) P' (w:=0) (fun i q _ _=>Medal.zeroT) le_rfl q1 hx zero_lt_one Cκ zero_lt_one tP le_rfl (fun i=>by simpa only [Pi.zero_apply,zero_add] using (show _ ≤ _ from x4)) (fun i=>by simp [tallB]) (fun i=> (lad_K V F Z M P_ w' V_ ε' D_ hv uQ KcV F' Pinc i).trans x1) le_rfl x6 x5 (by simpa [ringT] using x7) (fun s U T q=> q.elim)
   simpa [stopK,W] using H
 rw [key_c]; have ht:exponentL X.p E U.1+fuelV X.p 0 U=coldE X.p (FeeD X.p Fe') U:=by
    rw [show fuelV X.p 0 U=0 from sum_eq_zero fun i _=>rfl, add_zero]; exact lay_e (FeeD X.p Fe') (turfK Fe' cκ) A U
 exact asterT q1 hx Cκ zero_lt_one tP U h _ ht -- implicit K?
end YM.CF.Jade
