import Thin.CapsTax
import YM.CF.Pith.Rime

/- Adapted from YM/CF/Pith/Rime.lean for the NoSlip, capped ScaledV use below. -/
set_option linter.unusedTactic false
set_option linter.unusedVariables false
set_option autoImplicit false
set_option maxHeartbeats 950000
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
local notation "Ωq"=> Troupe S r (Words S)
local notation "Xm"=> tolQ X.p
local notation "Wit"=>taxV X.p KcV V_
local notation "PW"=> grain_q X.p.B X.p.order X.p.power γ' c
variable {Hh Kk:ℝ}(h_:Kk ≤Hh)(kK:1 ≤Kk)(Z_ : ScaledV (fun i => min Hh (stampY Hh Kk i)) (tolQ X.p) V_ c x γ' KcV)
include ht Pinc
include uQ h_ kK Z_
lemma snow_b_Th(o:Site (Domain N B)): tallB (hymn (pence_v X.p KcV V_)) X.p.B (tolQ X.p).supportExponent o ≤ Hh⁻¹* PW 0:=by
 let Fν:=univ.filter fun i:Ωq=> (bargainP i).Nonempty
 let p:= frost_Q_Th V F Z M P_ w' V_ ε' D_ ht uQ KcV F' Pinc h_ kK Z_ o Fν 0 Hh (fun i v=>⟨show 0 ≤ i.card-1 from Nat.zero_le _,le_min (le_refl _) (grey_Q i (mem_filter.mp v).2 _ _ (kK.trans h_) kK)⟩)
 have he:= tax_v V F Z M P_ w' V_ ε' D_ ht KcV F' Pinc; have hf:=lt_of_lt_of_le zero_lt_one (kK.trans h_); rw [inv_mul_eq_div]; refine (le_div_iff₀ hf).mpr ((mul_comm ..).trans_le ((mul_le_mul_of_nonneg_left ?_ hf.le).trans p))
 refine sum_le_sum fun i _=> mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le; obtain ⟨u,h,v⟩:=amber_p V F Z M P_ w' V_ ε' D_ ht KcV F' Pinc i; apply v.trans_le; exact sum_le_sum_of_subset_of_nonneg (show u ⊆ Fν from fun i v=>mem_filter.mpr ⟨mem_univ _,h i v⟩) fun j _ _=>he i j
lemma old_V_Th(o:Site (Domain N B)): tallB (fun i:Aura (mid N B)=>∑ l:Ωq with elderB l,Wit i l) X.p.B (tolQ X.p).supportExponent o ≤ Kk⁻¹ * PW 0:=by
 have hu:=frost_Q_Th V F Z M P_ w' V_ ε' D_ ht uQ KcV F' Pinc h_ kK Z_ o (univ.filter fun i:Ωq=>elderB i) 0 Kk (fun i v=>⟨show 0 ≤ i.card-1 from Nat.zero_le _,le_min h_ (clear_Q i (mem_filter.mp v).2 _ _ (kK.trans h_) kK)⟩)
 rw [inv_mul_eq_div]; exact (le_div_iff₀ (zero_lt_one.trans_le kK)).mpr ((mul_comm ..).trans_le hu)
end YM.CF.Jade
end
