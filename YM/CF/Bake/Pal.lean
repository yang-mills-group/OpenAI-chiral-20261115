import YM.CF.Bake.Pep
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
 
abbrev miteV(B k p:ℕ)(a c:ℝ):= chi_f k * (reserveT p k B a * (c * degreePrice B c 1^0*(1-degreePrice B c 1)⁻¹))
local notation "M'"=> miteV X.p.B X.p.order X.p.power γ' c
include Pinc ht
private lemma ttV(i:Aura (mid N B))(k:Troupe S r (Words S)):0 ≤ taxV X.p KcV V_ i k:=mul_nonneg (spicy_f _) (sum_nonneg fun j _=>mul_nonneg (mul_nonneg (pow_nonneg (by positivity) _) (pow_nonneg ht _)) (Pinc.grace _ _ _))
include uQ
private lemma raw_v (o:Seat (mid N B)): tallB (fun i:Aura (mid N B)=> ∑ j:Troupe S r (Words S),taxV X.p KcV V_ i j) X.p.B (tolQ X.p).supportExponent o ≤ miteV X.p.B X.p.order X.p.power γ' c:=by
 let TU:=Pinc.dose o 0 (fun _ i=>fastV i) fun _ i=>fastX i; rw [show (univ.filter (fun i:Troupe S r (Words S)=> Palot.outC 0 i))= univ from filter_true_of_mem (fun (i:Troupe S r (Words S)) (_)=> show 0 ≤ i.card-1 from Nat.zero_le _)] at TU
 unfold miteV; rw [uQ]; apply le_trans _ (mul_le_mul_of_nonneg_left TU (spicy_f X.p.order)); unfold tallB; simp_rw [sum_mul]; rw [sum_comm,mul_sum]; refine sum_le_sum fun i _=>?_ ; rw [mul_sum]; refine sum_le_sum fun j q=>?_ ; unfold taxV Trees.currency BudgetPoint.mass; rw [mul_assoc, mul_comm _ (Real.exp _)]; rw [←uQ]; exact le_rfl
lemma lad_K (x:Seat (mid N B)): tallB (hymn (pence_v X.p KcV V_)) X.p.B (X.p.supportExponent+1+1) x ≤ miteV X.p.B X.p.order X.p.power γ' c:=by
 let TT:=ttV V F Z M P_ w' V_ ε' D_ ht KcV F' Pinc; refine le_trans ?_ (raw_v V F Z M P_ w' V_ ε' D_ ht uQ KcV F' Pinc x); refine sum_le_sum fun i t=>?_ ; let D(j:Troupe S r (Words S)):= (cook S j.toLeft).flags; let Q:= univ.filter fun j:Troupe S r (Words S)=>D j ∈ fullD i
 apply mul_le_mul _ (Real.exp_monotone (mul_le_mul_of_nonneg_right (show X.p.supportExponent+1+1 ≤ (tolQ X.p).supportExponent from le_add_of_nonneg_right zero_le_one) (by positivity))) (Real.exp_pos _).le (sum_nonneg fun j _=>TT i j)
 unfold Vow.hymn pence_v; -- sum subset
 refine le_trans ?_ (sum_le_sum_of_subset_of_nonneg (f:=fun j=>taxV X.p KcV V_ i j) (subset_univ Q) (fun j _ _=>TT i j))
 apply le_of_eq; rw [←sum_fiberwise_of_maps_to (g:=D) (t:=fullD i) (fun j u=>(mem_filter.mp u).2) (s:=Q)] -- check g nomen
 apply sum_congr rfl; intro j v; refine sum_congr ?_ fun j _=>rfl ; ext k; unfold Q; simp only [mem_filter,mem_univ,true_and]; exact ⟨fun t=>⟨(show D k∈_ from (show D k=j from t).symm ▸ v),t⟩,fun g=>g.2⟩
lemma lad_e (x:Seat (mid N B)): tallB (nixV (pence_v X.p KcV V_)) X.p.B (X.p.supportExponent+1+1+1) x ≤ miteV X.p.B X.p.order X.p.power γ' c:=by
 refine le_trans ?_ (raw_v V F Z M P_ w' V_ ε' D_ ht uQ KcV F' Pinc x); refine sum_le_sum fun i v=>?_ ; exact mul_le_mul_of_nonneg_right (sum_le_sum_of_subset_of_nonneg (filter_subset ..) (fun j _ _=>ttV V F Z M P_ w' V_ ε' D_ ht KcV F' Pinc _ _)) (Real.exp_pos _).le
end YM.CF.Jade
