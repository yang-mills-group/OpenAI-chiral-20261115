import GaugeFieldConstruction.Cumin
import YM.SU5.Fineness.Stitch

-- P1 as VLine with decaying error, altering chain proof of Stitch; consumes Geometry and Spicing.
set_option autoImplicit false
set_option maxHeartbeats 160000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Py
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
local notation "G5"=>SU.group
open Cascade
open Fief
open Yaw Pig
open Wray
open Lich.Muster Push.AbsoluteSums
open Iva Eire
open Trees Footprint Iva Eire
open Jade
open Oath Feu Feu.Corset Nor
open Chaff Gloss Maize Tye RP RP.Str
open Brace
namespace Rate
open Pitching Focus CF.Mint
namespace LocalLimit
open Preparation
/-!
# Exact headroom asymptotic, all periods on the signed law.
 Not absolute values on the integrands. Comes from transporting the weights/norms of ZERO
 insertions; this still only pays downstream with further *matching upper* bounds.
-/
variable {Λ:Preparation}{l:ℕ} (Y:Course Λ (VolumeCape.Dream.Nimbus l))
local notation "ℒ"=> Λ.R.L
local notation "v'" i:max s:max=> sites (Λ.Ctor (Y.ir i) s)
local notation "X₀" i:max k:max=> (Y.voyage i).X (Y.uv k)
private lemma line_cheap (s i k:ℕ){x y:ℝ}(p:x≤y)(h:VLine Y s i k x) : VLine Y s i k y:= h.trans' (Real.exp_monotone (sub_le_sub_left (mul_le_mul_of_nonneg_right p (zero_le_one.trans (sites_pos _))) _))
local notation "R" => ( (Λ.R.L.val:ℝ)^4)
private abbrev budgetSeason (Λ:Preparation):=hat Λ.R.L Λ.x
local notation "Xₛ"=> budgetSeason Λ
abbrev Spicing (P:Preparation):Prop:= SpiceWay P.J Chi.canonical P.h P.P P.N0
include Λ
lemma chain_debit(q: Spicing Λ):∀ᶠ s in atTop,∀ i k:ℕ,s<Y.uv k → |(((X₀ i k).gram s).v.re-(( (X₀ i k).gram (s+1)).v).re)-(sod Y k (s+1) i-sod Y k s i)| ≤ (9*fourthDeck (Xₛ s))*sites (Λ.Ctor (Y.ir i) s):=by
 filter_upwards [Branch.cycleYearsX (α:=0) (x:=Λ.x) q Λ.H Λ.chart] with s hx i k hs; let T:=Y.voyage i; let Z:= X₀ i k
 obtain ⟨qT,b,v,h,H⟩:= T.paths (Y.uv k); unfold sod; dsimp only; change Z.gram=_ at h; change |((Z.gram s).v.re-(Z.gram (s+1)).v.re)-(entryFin _ _ _ (Z.gram (s+1)).J (Z.gram (s+1)).beta-entryFin _ _ _ (Z.gram s).J (Z.gram s).beta)|≤ _
 rw [h]; exact hx _ _ _ b qT v (Λ.W.pose _ _) hs
private lemma debitR (q:Spicing Λ):∀ᶠ s in atTop,∀ i k:ℕ,s<Y.uv k → ∀ r,VLine Y s i k r → VLine Y (s+1) i k ((r+9*fourthDeck (Xₛ s))/R):=by
 have he:R>0:=pow_pos (by positivity) _
 filter_upwards [chain_debit Y q] with s v i k u r hr; let ε:=9*fourthDeck (Xₛ s); let Z:= X₀ i k; let X:=Z.gram; let d:= ‖partitionZ (X s) Λ.U ((Y.voyage i).CapeT s)‖; let V:= v' i s; let a:=sod Y k s i; let b:=sod Y k (s+1) i; let A:= (X s).v.re; let B:= (X (s+1)).v.re
 have hx:b-a - ε*V ≤ A-B:=by
    have he:|A-B-(b-a)|≤ ε*V:= v i k u; linarith only [(abs_le.mp he).1]
 simp only [VLine,compensated,norm_mul,Complex.norm_exp,Complex.neg_re] at hr ⊢
 change Real.exp (a-r*V) ≤ Real.exp (-A)*d at hr
 rw [(Z.balance (s+1) u).trans (Z.balance s u.le).symm, expansionStep]
 let X' := b-a- ε*V
 change Real.exp (b-(r+ε)/R*(R*V)) ≤ Real.exp (-B)*d
 calc _= Real.exp X'*Real.exp (a-r*V) := by rw [← Real.exp_add]; congr 1; unfold X'; field
      _ ≤ _:= (mul_le_mul_of_nonneg_left hr (Real.exp_pos _).le).trans (by rw [←mul_assoc,←Real.exp_add]; apply mul_le_mul_of_nonneg_right _ (norm_nonneg _); apply Real.exp_monotone; unfold X'; linarith only [hx])

private lemma fourth_next : ∀ᶠ s in atTop, fourthDeck (Xₛ s) ≤ 2 * fourthDeck (Xₛ (s+1)):=by
 let F:=budgetSeason Λ
 have H:Tendsto F atTop atTop:=stage_slope Λ.V Λ.x
 filter_upwards [H.eventually_gt_atTop (0:ℝ),H.eventually_ge_atTop (Vale.billX ℒ)] with s u v
 let t:=F (s+1); have ht0:t= F s+Vale.billX ℒ:=by unfold t F budgetSeason hat; push_cast; ring
 have hh:F s ≤ t:=hat_mono (by omega)
 
 have hv:0 < t:=u.trans_le hh
 have hs:Real.sqrt (Real.sqrt t) ≤ 2*Real.sqrt (Real.sqrt (F s)):=by
    let a:= Real.sqrt t; let b:= Real.sqrt (F s); have hq:a≤2*b:=by nlinarith only [show t≤ 2* F s by linarith only [ht0,v],show a^2=t from Real.sq_sqrt hv.le,show b^2=F s from Real.sq_sqrt u.le,show 0≤a from Real.sqrt_nonneg _,show 0≤b from Real.sqrt_nonneg _]
    change Real.sqrt a≤ 2*Real.sqrt b
    nlinarith [Real.sq_sqrt (show 0≤a from Real.sqrt_nonneg _),Real.sq_sqrt (show 0≤b from Real.sqrt_nonneg _),Real.sqrt_nonneg a,Real.sqrt_nonneg b]
 let a:=Real.sqrt (Real.sqrt (F s)); let b:=Real.sqrt (Real.sqrt t)
 have hb:b>0:= Real.sqrt_pos_of_pos (Real.sqrt_pos_of_pos hv); have ha:a>0:= Real.sqrt_pos_of_pos (Real.sqrt_pos_of_pos u)
 change a⁻¹≤ 2*b⁻¹; rw [← one_div a,← div_eq_mul_inv]; apply (div_le_div_iff₀ ha hb).2; rw [one_mul]; exact hs

-- Solve monotone without summing, taking barrier ratio bound and absorbing initial toll.
lemma regulator_spike (p:Geometry Λ)(q:Spicing Λ): ∃ C >0, ∀ᶠ s in atTop,∀ i k:ℕ,(Y.voyage i).kick≤k → s≤Y.uv k → VLine Y s i k (C*fourthDeck (Xₛ s)):=by
 have hV: 4 ≤ R:=by
   have hp:2≤(Λ.R.L.val:ℝ):=by exact_mod_cast (show 2≤ Λ.R.L.val from le_trans (by decide) Λ.V.tallX)
   nlinarith only [pow_le_pow_left₀ zero_le_two hp 4]
 let v:= fun s=>fourthDeck (Xₛ s)
 obtain ⟨s,h⟩:= eventually_atTop.mp ((debitR Y q).and ((fourth_next (Λ:=Λ)).and ((stage_slope Λ.V Λ.x).eventually_gt_atTop 0)) |>.and (benchmarks Y 1 zero_lt_one p))
 have hs(n)(p:s≤n):0<v n:= inv_pos.mpr (Real.sqrt_pos_of_pos (Real.sqrt_pos_of_pos (h _ p).1.2.2))
 let C:=9+1/(v s); have hK:9 ≤ C:= le_add_of_nonneg_right (div_nonneg zero_le_one (hs s le_rfl).le)
 have h0:0<C:=zero_lt_one.trans_le ((by norm_num : (1:ℝ) ≤9).trans hK)
 refine ⟨C,h0,(eventually_ge_atTop s).mono ?_⟩
 intro n hn i k pv pK
 induction n,hn using Nat.le_induction with
 | base =>
   apply line_cheap Y s i k _ ((h s le_rfl).2 i k pv pK)
   apply le_trans (show 1 ≤ (1/v s)*v s from by rw [div_mul_cancel₀ _ (hs s le_rfl).ne'])
   exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_left (show (0:ℝ) ≤9 by norm_num)) (hs s le_rfl).le
 | succ n u ih=>
   apply line_cheap Y _ i k _ ((h n u).1.1 i k pK _ (ih (le_of_lt pK)))
   change (C*v n+9*v n)/R ≤ C*v (n+1)
   rw [div_le_iff₀ (show (0:ℝ)<R by linarith only [hV])]
   have ht:v n≤2*v (n+1):=(h n u).1.2.1
   nlinarith only [mul_le_mul_of_nonneg_left ht h0.le, mul_le_mul_of_nonneg_right hK (hs n u).le, mul_le_mul_of_nonneg_left hV (mul_nonneg h0.le (hs (n+1) (by omega)).le)]

lemma pressure_path (p:Geometry Λ)(q:Spicing Λ) :
 ∀ᶠ s in atTop,∀ i k:ℕ,(Y.voyage i).kick≤k → s≤Y.uv k →
 VLine Y s i k ((hat ℒ Λ.x s)^ (-(1/10):ℝ)):=by
 obtain ⟨C,hC,v⟩:=regulator_spike Y p q
 filter_upwards [v,(stage_slope Λ.V Λ.x).eventually_gt_atTop 0,(stage_slope Λ.V Λ.x).eventually ((tendsto_rpow_atTop (by norm_num : (0:ℝ)<3/20)).eventually_ge_atTop C)] with s h ht hv i k y n
 apply line_cheap Y _ _ _ _ (h i k y n)
 rw [fourthDeck_price (Xₛ s) (show 0<(Xₛ s) from ht).le]
 apply le_trans (mul_le_mul_of_nonneg_right hv (show 0≤Xₛ s^(-(1/4):ℝ) from (Real.rpow_pos_of_pos ht _).le)) (le_of_eq ?_)
 rw [← Real.rpow_add ht]; norm_num
end LocalLimit
end Rate
end YM.CF.Py
end
