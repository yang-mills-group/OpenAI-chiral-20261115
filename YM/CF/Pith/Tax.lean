import YM.CF.Pith.Class
import YM.CF.Pith.Steel
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
include Pinc ht
lemma tax_v(i:Aura (mid N B))(k:Troupe S r (Words S)):0 ≤ taxV X.p KcV V_ i k:=mul_nonneg (spicy_f _) (sum_nonneg fun j _=>mul_nonneg (mul_nonneg (pow_nonneg (by positivity) _) (pow_nonneg ht _)) (Pinc.grace _ _ _))
abbrev grain_q(B k p:ℕ)(a c:ℝ)(m:ℕ):ℝ:= chi_f k * (reserveT p k B a * (c * degreePrice B c 1^m*(1-degreePrice B c 1)⁻¹))
local notation "Ωq"=> Troupe S r (Words S)
local notation "Xm"=> tolQ X.p
local notation "Wit"=>taxV X.p KcV V_
local notation "PW"=> grain_q X.p.B X.p.order X.p.power γ' c
variable {Hh Kk:ℝ}(h_:Kk ≤Hh)(kK:1 ≤Kk)(Z_ : ScaledV (stampY Hh Kk) (tolQ X.p) V_ c x γ' KcV)
include uQ Z_ kK h_
lemma frost_Q (o:Seat (mid N B))(i:Finset Ωq)(m:ℕ)(p:ℝ)(h:∀ j∈i,Palot.outC m j ∧ p≤ stampY Hh Kk j) : p*tallB (fun j:Aura (mid N B)=>∑ t∈i,Wit j t) X.p.B (tolQ X.p).supportExponent o ≤ PW m:=by
 let U:= Xm; let H:= Wit
 have hx(v):0≤ stampY (S:=S) (r:=r) Hh Kk v:= zero_le_one.trans (shelfX v _ _ (kK.trans h_) kK)
 have hv:= tax_v V F Z M P_ w' V_ ε' D_ ht KcV F' Pinc
 unfold tallB; let f':=univ.filter fun q:Aura (mid N B)=>o∈ q.val; let P':=U.supportExponent
 let L:=univ.filter fun i:Ωq=> Palot.outC m i; let Wv(q:Ωq):= stampY Hh Kk q
 let Tx(v:Ωq):=Wv v*(∑ j∈f',H j v * Trees.currency X.p.B P' j.val)
 have hp': (p * ∑ j∈f', (∑ t∈i,H j t)* Trees.currency X.p.B P' j.val) ≤ ∑ v∈L,Tx v:=by
    simp_rw [sum_mul]; rw [sum_comm,mul_sum]
    apply le_trans _ (sum_le_sum_of_subset_of_nonneg (f:=Tx) (show i ⊆ L from fun j v=> mem_filter.mpr ⟨mem_univ _,(h j v).1⟩) (fun j _ _=>mul_nonneg (hx _) (sum_nonneg fun l _=>mul_nonneg (hv l j) (Real.exp_pos _).le)))
    refine sum_le_sum fun j v=> mul_le_mul_of_nonneg_right (h j v).2 (sum_nonneg fun l _=> mul_nonneg (hv l j) (Real.exp_pos _).le)
 apply hp'.trans
 unfold grain_q; have hL:= mul_le_mul_of_nonneg_left (Z_ o m (fun i j=>fastV j) (fun i j=>fastX j)) (spicy_f X.p.order)
 rw [show X.p.B=_ from uQ]; apply le_trans _ hL; rw [mul_sum]; refine sum_le_sum fun i u=>?_
 unfold Tx f'; rw [mul_sum,mul_sum]; refine sum_le_sum fun j q=>?_ ; unfold H taxV BudgetPoint.mass Trees.currency Wv; change _ ≤ _ * (_ * (Real.exp ((tolQ X.p).supportExponent* (coverNumber X.p.B j.val:ℝ))* _)); exact le_of_eq (by unfold P' U tolQ; unfold Scree.tariff; dsimp; ring) -- radiusB tune
-- R+ reserve membership
abbrev tilt_Q(B k p:ℕ)(a c R K:ℝ):=R⁻¹ *grain_q B k p a c 0+K⁻¹ *grain_q B k p a c 1 + grain_q B k p a c 2
omit Pinc ht uQ h_ kK Z_
private lemma tall_i {ι : Type*}[DecidableEq ι] (Q1 Q2 Q3 R':Finset ι)(h:R' ⊆ Q1∪Q2∪Q3)(F:Aura N→ι→ℝ)(p:∀ i j,0≤ F i j)(o:Seat N): let Y(T:Finset ι):=tallB (fun j:Aura N=>∑ i∈T,F j i) k d o; Y R' ≤ Y Q1 + Y Q2 + Y Q3:=by
 intro Y; unfold Y tallB; rw [←sum_add_distrib,←sum_add_distrib]; refine sum_le_sum fun i _=>?_ ; rw [←add_mul,←add_mul]; apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
 have hl(D K':Finset ι):∑ i'∈D∪K',F i i' ≤ ∑ i'∈D,F i i' + ∑ i'∈K',F i i':= (le_add_of_nonneg_right (sum_nonneg (s:=D∩K') (f:=F i) (fun j _=> p _ _))).trans_eq sum_union_inter
 exact (sum_le_sum_of_subset_of_nonneg h (fun j _ _=>p i j)).trans ((hl (Q1∪Q2) Q3).trans (add_le_add_left (hl Q1 Q2) _))
abbrev cold_a (S:StepData (Domain N B) (Domain P B)) (r m:ℕ)(H K p:ℝ):= (fallow S r).filter fun j=>Palot.outC m j ∧ p≤ stampY H K j
include kK h_
private lemma split_T : fallow S r ⊆ cold_a S r 0 Hh Kk Hh ∪ cold_a S r 1 Hh Kk Kk ∪ cold_a S r 2 Hh Kk 1:=by
 intro t u; rcases pay_v Hh Kk kK h_ t u with v|v|v
 · rw [mem_union,mem_union]; exact Or.inl (Or.inl (mem_filter.mpr ⟨u,(show 0≤ t.card-1 from Nat.zero_le _),v⟩))
 · rw [mem_union,mem_union]; exact Or.inl (Or.inr (show t∈cold_a S r 1 Hh Kk Kk from mem_filter.mpr ⟨u,v⟩))
 rw [mem_union]; exact Or.inr (show t∈cold_a S r 2 Hh Kk 1 from mem_filter.mpr ⟨u,v⟩)
include Pinc ht
include uQ Z_ kK h_
set_option maxHeartbeats 1350000 in
lemma wintry_q (o:Seat (mid N B)): tallB (fun j:Aura (mid N B)=>∑ t∈ fallow S r,Wit j t) X.p.B (tolQ X.p).supportExponent o ≤ tilt_Q X.p.B X.p.order X.p.power γ' c Hh Kk:=by
 let u:=PW; let T:=fallow S r; let A(m:ℕ)(p:ℝ):=cold_a S r m Hh Kk p; let W:= Wit
 let F_(m:ℕ)(p:ℝ)(j:Aura (mid N B)):=∑ i∈ A m p,W j i
 have hP:=tax_v V F Z M P_ w' V_ ε' D_ ht KcV F' Pinc
 have hT (m p): p*tallB (F_ m p) X.p.B (tolQ X.p).supportExponent o ≤ u m:=frost_Q V F Z M P_ w' V_ ε' D_ ht uQ KcV F' Pinc h_ kK Z_ _ (A m p) _ p (fun i v=>(mem_filter.mp v).2)
 let rayP (p:Aura (mid N B)→ℝ):=tallB p X.p.B (tolQ X.p).supportExponent o -- replace
 have he(m)(p:ℝ)(h:0<p): rayP (F_ m p) ≤ p⁻¹*u m:=by rw [inv_mul_eq_div]; exact (le_div_iff₀ h).mpr ((mul_comm ..).trans_le (hT m p))
 have hz:= hT 2 1; rw [one_mul] at hz
 apply le_trans _ (add_le_add (add_le_add (he 0 Hh (lt_of_lt_of_le zero_lt_one (kK.trans h_))) (he 1 Kk (lt_of_lt_of_le zero_lt_one kK))) hz)
 exact tall_i (k:=X.p.B) (d:=(tolQ X.p).supportExponent) (A 0 Hh) (A 1 Kk) (A 2 1) T (split_T h_ kK) W hP o
end YM.CF.Jade
