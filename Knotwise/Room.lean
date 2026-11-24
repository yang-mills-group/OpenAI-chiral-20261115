import Knotwise.Thrills
import WinterX.Purchase
import YM.Work.E01
import Palm.Mature
import Palm.Trek
import Thin.Rail
set_option autoImplicit false
set_option maxHeartbeats 1100000
set_option quotPrecheck false
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Py.Rate
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
open Ione Beau Haro Cascade Fief VolumeRate
open scoped Mew
variable {K : Teller SU.group} {R : Patch} {L : ChartRatio SU.group} {V : Grace K R L} {d h x : ℝ}
  {m N B : Side} {U : Grasp V.U B d} {W : GivenX V U} (J : Robes N V W) (q : Chi) (h : ℝ) (D C R0 : ℝ→ℝ) {N0 : ℕ} (T : Month x 1 6 2 N0 V W) (ht : T.q ≤ m.val)
  (S : Cape m B R.L) (ρ : ℕ→ℝ) (f : ℕ→ℝ) (k i : ℕ)
namespace Parcel
open Branch
open Pitching Pitching.Focus
variable {J q h D C R0 T S ρ f i}
variable (s:Parcel J q h D C R0 T ht S ρ f k)
open Oath Roots
namespace TopHat_dummy
lemma roomN (L:Side)(p:1<L.val)(x:ℝ)(a:ℕ):∀ᶠ i:ℕ in atTop, a * radiusB (hat L x i) < L.val^i:=by
 let Q (i:ℕ):=hat L x i
 -- x_i ∼ i. ratioB/y→0 via log. Alternatively radiusB(x_i) ≤ [(|x|+i*g)^2]+1→i³. Compare pow via tendsto_pow_right.
 obtain ⟨m,hm⟩:= exists_nat_gt (|x|+|billX L|)
 have ht:0<billX L:=by unfold Vale.billX; exact mul_pos (Gauge.slopeConstant_pos Thera.yet_one) (Real.log_pos (by exact_mod_cast p)) -- #check
 have he:Tendsto Q atTop atTop:=by unfold Q hat; exact tendsto_atTop_add_const_left _ _ (Tendsto.atTop_mul_const ht tendsto_natCast_atTop_atTop)
 -- r: log² ≤ Q²≤ (m*(i+1))². nat cast estimate. eventual pow.
 have hv: Tendsto (fun n:ℕ=>(n:ℝ)^2 * (L.val:ℝ)⁻¹^n) atTop (𝓝 0):=by apply tendsto_pow_const_mul_const_pow_of_lt_one; positivity; exact inv_lt_one_of_one_lt₀ (by exact_mod_cast p)
 have hQ:= hv.const_mul (4*(m:ℝ)^2*a+2*a)
 filter_upwards [he.eventually_ge_atTop 2,eventually_ge_atTop (1:ℕ), hQ.eventually (gt_mem_nhds (show (4*(m:ℝ)^2*a+2*a)*0 <1 by ring_nf; exact zero_lt_one))] with i e w h
 change _*(_^_*((L.val:ℝ))⁻¹^i)<1 at h
 have q: Q i ≤ m*(i+1:ℝ):=by
    unfold Q hat
    calc
    _ ≤ |x|+i*|billX L|:=by gcongr; exact le_abs_self _; exact le_abs_self _
    _ ≤ _:=by nlinarith only [hm,abs_nonneg x, abs_nonneg (billX L), show (0:ℝ) ≤ i by positivity, mul_nonneg (show 0≤(i:ℝ) by positivity) (show (0:ℝ)≤(m:ℝ)- |x|- |billX L| by linarith [hm])]
 have hb: ((radiusB (Q i):ℕ):ℝ) ≤(m*(i+1:ℝ))^2+1:=((Nat.ceil_lt_add_one (by positivity:0≤Real.log (Q i)^2))).le.trans (by gcongr; apply Real.log_nonneg; linarith; exact (Real.log_le_sub_one_of_pos (by linarith)).trans (by linarith))
 apply (Nat.cast_lt (α:=ℝ)).mp; push_cast; rw [inv_pow] at h
 have hz: (0:ℝ)<(L.val:ℝ)^i:=by positivity
 have hl:(4*(m:ℝ)^2*a+2*a)*(i:ℝ)^2 <(L.val:ℝ)^i:=by rw [← div_eq_mul_inv,←mul_div_assoc] at h; linarith only [(div_lt_one hz).mp h] -- tune
 apply lt_of_le_of_lt _ hl; calc
 _ ≤ (a:ℝ)*((m*((i:ℝ)+1))^2+1):=mul_le_mul_of_nonneg_left hb (by positivity)
 _ ≤ _:=by
    have he:((1:ℝ)≤(i:ℝ)):=Nat.one_le_cast.mpr w
    have ht:((i:ℝ)+1)^2≤4*(i:ℝ)^2:=by nlinarith
    have hw:=mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ht (sq_nonneg (m:ℝ))) (show (0:ℝ)≤a by positivity); nlinarith only [hw,mul_le_mul_of_nonneg_left (show (1:ℝ)≤ 2*(i:ℝ)^2 by nlinarith only [he]) (show (0:ℝ)≤a by positivity)]
lemma comfort (L:Side)(p:1<L.val)(x:ℝ):∀ᶠ j:ℕ in atTop, ∀ (m B:Side) (P: BudgetPoint) , P.B=radiusB (hat L x j)→ ∀ i:Scree.Hub (cell m B L j), Moto.chose L.val P i→ Nonwrapping i.val.2 i.val.1:=by
 let a:ℕ:=10*(6*L.val+2)
 refine (Eventually.and (roomN L p x a) ((show Tendsto (fun j:ℕ=>radiusB (hat L x j)) atTop atTop from Work.E01.radiusB_tendsto.comp ?_).eventually_ge_atTop 1)).mono (fun j t m B P v i h z l=>?_)
 · unfold hat; apply tendsto_atTop_add_const_left; apply Tendsto.atTop_mul_const; unfold Vale.billX; exact mul_pos (Gauge.slopeConstant_pos Thera.yet_one) (Real.log_pos (by exact_mod_cast p)); exact tendsto_natCast_atTop_atTop
 · let g:=t.1;-- order goals?
   have hb:1≤P.B:=v.symm ▸ t.2
   have hx:= h; unfold Moto.chose at hx
   have ho: coverNumber P.B i.val.2 ≤ L.val := by by_cases p:coverNumber P.B i.val.2=0; rw [p]; omega; exact ((Nat.le_self_pow (by decide: (3:ℕ)≠0) _)).trans hx.le
   have hv:= (Corona.extent i.val.2 P.B l i.property)
   have he: L.val^j ≤ (More (cell m B L j)).val:=by
      change _≤ ((m.val * (L^j).val)*2*B.val)*2 -- side val.P nat pow defeq?
      have t:m.val>0:=m.property; have u:B.val>0:=B.property; have w:(L^j).val=L.val^j:=by norm_cast
      rw [w]; nth_rw 1 [←one_mul (L.val^j)]; apply le_trans ?_ (Nat.le_mul_of_pos_right _ (by decide:(2:ℕ)>0)); apply le_trans ?_ (Nat.le_mul_of_pos_right _ u); apply le_trans ?_ (Nat.le_mul_of_pos_right _ (by decide:(2:ℕ)>0)); exact Nat.mul_le_mul_right _ t
   show 10*separation _ _ < _
   refine lt_of_le_of_lt (Nat.mul_le_mul_left _ hv) ((lt_of_le_of_lt ?_ ((t.1).trans_le he)))
   rw [←v]; unfold a; have ht:=Nat.mul_le_mul ho (show 4*P.B+2 ≤ 6*P.B by omega); nlinarith only [ht]
end TopHat_dummy
end Parcel
end YM.CF.Py.Rate
