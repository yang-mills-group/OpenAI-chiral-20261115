import YM.CF.Vp929.Fixed.Tower
import YM.CF.Tar.Lime

/-!
# The cutoff-vs-period prices

`cone b n m` evaluates the cone m^5 ≤ n_phys at the truncation schedule used by this
ledger, n_phys = trunk b n = trunkY n b = n^4+n+1+b.
-/
set_option autoImplicit false
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
open Ione Beau Haro Cascade Fief
open scoped Mew

open Wray Oath Feu Feu.Corset Nor Yaw Pig Oise Jade Plume Push.AbsoluteSums
open Trees Lich.Muster Jet
set_option linter.flexible false
open Chaff Gloss Maize Tye RP RP.Str Oise
namespace LocalLimit

open Branch
variable {b n i j : ℕ} {m B : Side}

def cone (b n : ℕ) (m : Side) : Prop := m.val^5 ≤ trunk b n

lemma fraction_depth (b : ℕ) : Tendsto
    (fun n:ℕ => (buoy n:ℝ)/(trunk b n:ℝ)) atTop (𝓝 (1:ℝ)) := by
  have h (i:ℕ) (p:0 < i) : Tendsto (fun n:ℕ=> ((n:ℝ)^i)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp ((tendsto_pow_atTop p.ne').comp tendsto_natCast_atTop_atTop)
  have hv : Tendsto (fun n:ℕ=> ((trunk b n:ℝ)/(buoy n:ℝ))) atTop (𝓝 1) := by
    have he : Tendsto (fun n:ℕ => 1+((n:ℝ)^3)⁻¹ + (1+b:ℝ)*((n:ℝ)^4)⁻¹) atTop (𝓝 1) := by
      simpa only [mul_zero,add_zero] using ((show Tendsto (fun n:ℕ=> (1:ℝ)) atTop (𝓝 1) from tendsto_const_nhds).add (h 3 (by norm_num)) |>.add ((h 4 (by norm_num)).const_mul (1+b:ℝ)))
    apply he.congr'; filter_upwards [eventually_gt_atTop 0] with i hi; unfold trunk buoy; push_cast; have hx : (0:ℝ) < i := Nat.cast_pos.mpr hi; field_simp; ring
  simpa only [inv_div,inv_one] using hv.inv₀ one_ne_zero

lemma profound (i : ℕ) : ∀ᶠ n in atTop, i < buoy n :=
  (tendsto_pow_atTop (α:=ℕ) (by norm_num: (4:ℕ)≠0)).eventually_gt_atTop i

abbrev game (m:Side) : ℝ := (m.val:ℝ)^4

private lemma economy (b : ℕ) (c : ℝ) (d : ℝ) (hc : 0<c) :
    ∀ᶠ n in atTop, ∀ m:Side, cone b n m → d*game m ≤ c * buoy n := by
  by_cases h:d ≤ 0; · exact Eventually.of_forall fun n m _=> le_trans (mul_nonpos_of_nonpos_of_nonneg h (by unfold game; positivity)) (by positivity)
  have hd : 0 < d := lt_of_not_ge h
  obtain ⟨j,p⟩ := exists_nat_gt (2*d/c)
  let Y:= d*(j:ℝ)^4
  have hY : Tendsto (fun n:ℕ=> c*(buoy n:ℝ)) atTop atTop := Tendsto.const_mul_atTop hc (tendsto_natCast_atTop_atTop.comp (tendsto_pow_atTop (by norm_num : (4:ℕ)≠0)))
  filter_upwards [hY.eventually_ge_atTop Y, (fraction_depth b).eventually (le_mem_nhds (by norm_num : (1:ℝ)/2<1))] with n t e m ht
  by_cases hw : j ≤ m.val; swap; · exact le_trans (by unfold Y game; gcongr; omega) t
  have hT:0<trunk b n:=by unfold trunk; omega
  have ht : game m * (m.val:ℝ) ≤ (trunk b n:ℝ):= by unfold game; rw [←pow_succ]; exact_mod_cast ht
  have he : (trunk b n:ℝ) ≤ 2*(buoy n:ℝ) := by
    have he:= (le_div_iff₀ (Nat.cast_pos.mpr hT : (0:ℝ)< trunk b n)).mp e; linarith only [he]
  have hy:= (div_lt_iff₀ hc).mp (lt_of_lt_of_le p (show (j:ℝ)≤ m.val from Nat.cast_le.mpr hw))
  nlinarith only [mul_le_mul_of_nonneg_left (ht.trans he) hc.le, mul_le_mul_of_nonneg_left hy.le (by unfold game; positivity : 0 ≤ game m)]

def decay (n : ℕ) (c : ℝ) := Real.exp (-c * buoy n)
lemma decay_pos (n : ℕ) (c : ℝ) : 0 < decay n c := Real.exp_pos _
lemma decline_decay (r i : ℕ) : decline r = 2^(i+1) * Real.exp (-Real.log 2 * (r+i:ℕ)) := by
  unfold decline
  have hp(x:ℕ): Real.exp (-Real.log 2 * (x:ℝ))=(1/2:ℝ)^x := by
    rw [mul_comm, Real.exp_nat_mul,Real.exp_neg,Real.exp_log (by norm_num)]; exact congrArg (·^x) (one_div (2:ℝ)|>.symm)
  rw [hp,pow_add (1/2:ℝ),pow_succ]; rw [one_div]; rw [inv_pow,inv_pow]; field_simp

/-- Anything with a `decay c`, even after exponentiating extensive costs at fixed level,
is small on this cone eventually. -/
lemma collapse (b : ℕ) {c ε : ℝ} (h : 0<c) (v : 0<ε) (A D : ℝ) :
    ∀ᶠ n in atTop, ∀ m:Side, cone b n m →
      A * decay n c * Real.exp (D*game m) ≤ ε := by
  have hc : Tendsto (fun n:ℕ=> |A| * decay n (c/2)) atTop (𝓝 0) := by
    have he : Tendsto (fun n:ℕ=> -(c/2)*(buoy n:ℝ)) atTop atBot:=
      Tendsto.const_mul_atTop_of_neg (by linarith) (tendsto_natCast_atTop_atTop.comp (tendsto_pow_atTop (by norm_num : (4:ℕ)≠0)))
    simpa only [mul_zero,Function.comp_apply,decay] using ((Real.tendsto_exp_atBot.comp he).const_mul |A|)
  filter_upwards [economy b _ D (by linarith : 0<c/2),hc.eventually (ge_mem_nhds v)] with n e t m u
  rw [mul_assoc]
  refine le_trans (mul_le_mul (le_abs_self _) ?_ (mul_nonneg (decay_pos n c).le (Real.exp_pos _).le) (abs_nonneg A)) t
  unfold decay; rw [←Real.exp_add]; exact Real.exp_monotone (by linarith [e m u])

/-- Always use log-exponential at COPY-volume scale. -/
def postage (B L:Side) (j:ℕ) : ℝ := ((L.val:ℝ)^j *2*B.val*2)^4
lemma sites_postage (m B L:Side) (j:ℕ) : sites (cell m B L j) = postage B L j * game m := by
  change (((((Vale.mesh m L j).val*2*B.val*2:ℕ):ℝ))^4)=_
  unfold postage game Vale.mesh; simp; ring
lemma paid_postage (B L:Side)(j:ℕ) : 0 < postage B L j := by unfold postage; positivity
end LocalLimit
end YM.CF.Py.Rate
