import YM.SU5.Exchange.Seed.Ship
import YM.SU5.Exchange.Seed.Station
import SatinThinPoles
import YM.CF.Roots.Sort
import YM.SU5.Exchange.Seed.Zero
import YM.SU5.Exchange.Seed.Keys
import YM.SU5.Exchange.Seed.Marks
import YM.CF.Rive.New
import YM.CF.Song.Pads
import SatinThinTopic
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Vow
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
open Rue
namespace TreasuryFog
open Mew Roots
open scoped YM.CF.Mew
-- estimate per-support type counts; at ANY exponent slack d, pack enough separation.
variable {I:Type}[LinearOrder I][Fintype I](σ:I→ Seat n)
local notation "B"=> P.B
local notation "μ"=> cape_B P.B
variable (t:ℕ)(p:Force_M P.B σ t)(X:Support (More n))(y: Seat n)(u:y∈X)
def sits_at := univ.filter (fun i:I=>σ i∈X)
local notation "m"=> coverNumber P.B X
local notation "D"=> sits_at σ X
local notation "Θ"=> P.supportExponent
include p u
lemma sitsCap : ((D).card:ℝ)≤ ((m:ℝ)*6/(B:ℝ)^2+1)*(t:ℝ):=by
 have he:D∈Knot_B (μ) B m σ y:=mem_filter.mpr ⟨mem_univ _,X,u,(fun i h=>(mem_filter.mp h).2),le_refl m⟩
 have hz := P.B_pos
 let k:= m*(4*B+2)/μ; have h:(D).card≤ (k+1)*t:= (energy_E (μ) m B t y σ (by unfold cape_B; positivity) p.2).2 _ he
 refine le_trans (Nat.cast_le.mpr h) ?_; push_cast
 refine mul_le_mul_of_nonneg_right (add_le_add_left ?_ _) ?_ -- `add_le_add_left` adds second
 · have hm:k* B^3≤ m*(4*B+2):=Nat.div_mul_le_self ..
   have hp: ((k*B^3:ℕ):ℝ)≤ ((m*(6*B):ℕ):ℝ):= Nat.cast_le.mpr (hm.trans (Nat.mul_le_mul_left _ (by omega)))
   have hb:(0:ℝ)<B:=Nat.cast_pos.mpr hz; apply (le_div_iff₀ (by positivity)).mpr; push_cast at hp; apply le_of_mul_le_mul_right ?_ hb; nlinarith only [hp]
 positivity
omit u
lemma pairedDist (q:Finset I)(w:q∈manySet σ)(v:q⊆sits_at σ X): (B:ℝ)^2/3 ≤ (m:ℝ):=by
 let A:= (mem_filter.mp w).2.1; obtain ⟨i,h,z,g,r⟩:=one_lt_card.mp A
 have ht:= p.1 i z (fun x=>r ((mem_filter.mp w).2.2 h g x))
 have hu:= Lattice.Corona.extent X B ((mem_filter.mp (v h)).2) ((mem_filter.mp (v g)).2) -- flips? check
 let s:= μ+μ+B+B; have e:B^2 ≤ 3*m:=by
    suffices hx:B^2*B ≤ 3*m*B by exact Nat.le_of_mul_le_mul_right hx P.B_pos
    have he:(4*B+2) ≤ 6*B:=by have e:= P.B_pos; omega
    have hf := Nat.mul_le_mul_left m he; have hv:=hu; unfold cape_B at ht;
    nlinarith only [ht,hu,hf] -- norm poly
 apply (div_le_iff₀ (by norm_num : (0:ℝ)<3)).2; rw [mul_comm]; exact_mod_cast e

abbrev sigma(α:ℝ)(b:ℕ):= Real.exp (-α*(b:ℝ)^2/6)
include u
variable (z:Key I) (c':ℝ)(hp:∀ i, ‖z i‖≤ c') (δ a:ℝ)(hc:1 ≤ c') (cv:2*c' ≤ Real.exp a) (hA:0 ≤ a)(hδ:0 ≤ δ)
local notation "A₁"=> (manySet σ).filter (· ⊆ sits_at σ X)
local notation "A₂"=> (trueSet σ).filter (· ⊆ sits_at σ X)
include cv hp hA hc
lemma cloudS (S:Finset (Finset I))(v:S⊆(sits_at σ X).powerset) : (∑ i∈ S, ‖Mew.pine i z‖) ≤ Real.exp (a * ((m:ℝ)*6/(B:ℝ)^2+1)*t):=by
 -- include hypotheses
 have hc':0≤c':=zero_le_one.trans hc; refine (sum_le_sum (g:=fun _=> c'^(D).card) (fun i h=> (show ‖Mew.pine i z‖≤ c'^i.card from ?_).trans (pow_le_pow_right₀ hc (card_le_card (mem_powerset.mp (v h)))))).trans ?_
 · rw [Mew.pine,norm_prod]; exact (prod_le_prod (fun i _=>norm_nonneg _) (fun i _=>hp i)).trans_eq (Finset.prod_const ..)
 rw [sum_const,nsmul_eq_mul]; apply (mul_le_mul_of_nonneg_right (show (S.card:ℝ) ≤ (2:ℝ)^(D).card from ?_) (pow_nonneg hc' _)).trans; swap; · exact_mod_cast (card_le_card v).trans_eq (card_powerset _)
 rw [← mul_pow]; apply (pow_le_pow_left₀ (mul_nonneg (by norm_num) hc') cv (D).card).trans; rw [←Real.exp_nat_mul]; apply Real.exp_monotone; exact (mul_le_mul_of_nonneg_right (sitsCap σ t p X y u) hA).trans_eq (by ring)

-- mixed linear radius. plus 5/6d saving
include hδ
lemma stars (hε: 9*a*t ≤ (δ/2)*(P.B:ℝ)^2): (∑ i∈A₁, ‖Mew.pine i z‖) ≤ Real.exp (δ*m) * sigma δ P.B :=by
 by_cases e:(A₁).Nonempty; swap; · rw [not_nonempty_iff_eq_empty.mp e, sum_empty]; positivity
 obtain ⟨i,h⟩:= e; obtain ⟨g,v⟩:= mem_filter.mp h; have ht:= pairedDist σ t p X i g v
 apply (cloudS σ t p X y u z c' hp a hc cv hA _ (fun i p=> mem_powerset.mpr (mem_filter.mp p).2)).trans; rw [sigma,←Real.exp_add]
 apply Real.exp_monotone
 have hb:(0:ℝ)< B:= Nat.cast_pos.mpr P.B_pos; let M:ℝ:= m; let T:ℝ:= t; let Q:ℝ:= (B:ℝ)^2
 have hM:1≤ 3*M/Q:=by apply (le_div_iff₀ (by unfold Q; positivity)).mpr; unfold M Q; linarith only [ht]
 have he: a*( (M*6/Q)+1)* T ≤ a *( M*6/Q+3*M/Q)*T:=by unfold T; gcongr
 apply he.trans; change a*_ * T ≤ δ*M+ -δ*Q/6
 rw [show a*(M*6/Q+3*M/Q)*T=(9*a*T/Q)*M from (by ring)]
 refine le_trans (mul_le_mul_of_nonneg_right ((div_le_iff₀ (by unfold Q; positivity)).2 hε) (show 0 ≤ M from Nat.cast_nonneg _)) ?_; unfold Q M; nlinarith only [mul_le_mul_of_nonneg_left ht hδ]
lemma winter (hε: 6*a*t ≤ δ*(P.B:ℝ)^2): (∑ i∈A₂, ‖Mew.pine i z‖) ≤ Real.exp (δ*m)*Real.exp (a*t):=by
 apply (cloudS σ t p X y u z c' hp a hc cv hA _ (fun i p=> mem_powerset.mpr (mem_filter.mp p).2)).trans
 rw [←Real.exp_add]; apply Real.exp_monotone
 have h := (mul_le_mul_of_nonneg_right (α:=ℝ) (show 6*a*t/(B:ℝ)^2≤ δ from (div_le_iff₀ (by have h:=P.B_pos; positivity)).mpr hε) (Nat.cast_nonneg m))
 apply le_trans _ (add_le_add_left h _); exact le_of_eq (by ring)
end TreasuryFog
end YM.CF.Vow
