import Refrain.Shrift
import YM.SU5.Fineness.Driving
set_option autoImplicit false
set_option maxHeartbeats 164000
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
variable {K : Teller SU.group} {R : Patch} {L : ChartRatio SU.group} {V : Grace K R L}
variable {d : ℝ} {m N B : Side} {U : Grasp V.U B d} {W : GivenX V U} {J : Robes N V W} {q : Chi}
  {h x delay : ℝ} {C D R0 : ℝ → ℝ} {N0 k : ℕ} (P : Prescription R B)
open Pitching.Focus AnalyticBridge.Annulus1AD
local notation "H'"=> Pannier.halfLie SU.group
variable {P}
open CF.Refrain BProof
local notation "G5"=>SU.group
local notation "Yx"=> Scales.y G5 R.L
lemma collateral (a:ℝ)(L':Side) :∀ᶠ x in atTop,a/x ≤ shrift L' x:=by
 let v:=L'
 filter_upwards [((Scales.year G5 v).eventually (coin_budget (a:=-1) (b:=0) (c:=0) (d:=-1/4) (e:=0) (f:=0) (by norm_num) (2*|a|) 1 zero_lt_one)),eventually_gt_atTop (0:ℝ),eventually_ge_atTop (SU.group.slopeConstant*Real.log v.val), (Scales.year G5 v).eventually_gt_atTop 0] with x hx h hB hV -- notation dot
 let y:=Scales.y SU.group v x
 have ht:y ≤2*x:=by unfold y Scales.y betaF; linarith only [hB]
 have hu:coin y (-1) 0 0=y⁻¹:=by nth_rw 2 [←coinY (show 0<y from hV)]; first | rw [coin_inv,neg_zero] | skip; -- will rewrite first y into coin nested
 change 2*|a| * _ < 1*coin y (-1/4) 0 0 at hx
 rw [hu,one_mul] at hx; refine hx.le.trans' ?_
 apply (div_le_iff₀ h).mpr
 have hp:0<y:=hV; field_simp; first | nlinarith only [mul_le_mul_of_nonneg_right ht (abs_nonneg a),mul_le_mul_of_nonneg_right (le_abs_self a) hp.le] | skip
lemma logFixed (M:ℝ)(x a b:ℝ)(p:0<x)(v:x/2 ≤ a)(u:x/2≤b)(h:|a-b|≤ M) : |Real.log a-Real.log b|≤ 2*M/x:=by
 rw [abs_le] at h ⊢
 have hM:0≤M:=by linarith only [h.1,h.2]
 have he{a b:ℝ}(hA:x/2≤a)(hB:x/2≤b)(t:a-b≤M): Real.log a-Real.log b≤2*M/x:=by
    have ha:0<a:= lt_of_lt_of_le (half_pos p) hA; have hb:0<b:=lt_of_lt_of_le (half_pos p) hB
    rw [← Real.log_div ha.ne' hb.ne']; refine (Real.log_le_sub_one_of_pos (div_pos ha hb)).trans (sub_le_iff_le_add.mpr ((div_le_iff₀ hb).mpr ?_)); field_simp; nlinarith only [mul_le_mul_of_nonneg_left t p.le, mul_le_mul_of_nonneg_right hB hM]
 refine ⟨neg_le.mp ?_,he v u h.2⟩; rw [neg_sub]; exact he u v (by linarith only [h.1])
lemma entryFiner (Q : Grace K R L)(H:LocalRatio L)(M:ℝ) : ∀ᶠ x:ℝ in atTop,∀ a b:ℝ,x/2≤a → x/2≤b →|a-b| ≤ M → ∀ i n F,|entryFin Q i n F a - entryFin Q i n F b|≤ 3*shrift R.L x*sites n:=by
 let f:=H'; have hf: 0≤H':= Pannier.pen_log_nonneg _
 filter_upwards [eventually_gt_atTop (0:ℝ), collateral (f*2*M) R.L] with x ht hx a b ha hb hΔ i n F
 have hh:=logFixed M x a b ht ha hb hΔ; let W:=sites n; have hw:1 ≤ W:=sites_pos n
 have hp: entryFin Q i n F a-entryFin Q i n F b= -(H'*(Real.log a-Real.log b)* (3*(W-1))):=by
    unfold entryFin Fineness.gaugedBase; rw [spare_formula _ H.scale ((half_pos ht).trans_le ha),spare_formula _ H.scale ((half_pos ht).trans_le hb),Pannier.shadowLie, sites_as_price]; unfold W; ring
 rw [hp, abs_neg,abs_mul,abs_mul,abs_of_nonneg hf,abs_of_nonneg (show 0≤3*(W-1) by linarith only [hw])]
 apply (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hh hf) (by linarith only [hw]:0≤ 3*(W-1))).trans
 have hz:0 ≤ shrift R.L x:= (BProof.coin_pos ..).le
 have hi:=mul_le_mul_of_nonneg_right hx (show 0 ≤ W-1 from by linarith only [hw]); change _ ≤ 3*shrift R.L x*W; change f*(2*M/x)*(3*(W-1)) ≤ _; rw [show f*(2*M/x)=f*2*M/x from by ring]; nlinarith only [hi,hz] -- tune

lemma height_shrift (Q: Grace K R L)(B:Side) (x:ℝ) (C:ℝ) : ∀ᶠ i in (atTop :Filter ℕ), ∀ m, C ≤ shrift R.L (hat R.L x i)*sites (cell m B R.L i):=by
 let a:ℝ:= R.L.val; have hp:a>1:=by unfold a; exact_mod_cast (show 1 < R.L.val by have ht:= Q.tallX; omega)
 let t:=billX R.L
 have hm:Tendsto (fun i:ℕ=> (hat R.L x i)/a^i) atTop (𝓝 0):=by
    have ht: Tendsto (fun i:ℕ=> x/a^i) atTop (𝓝 0):= tendsto_const_nhds.div_atTop (tendsto_pow_atTop_atTop_of_one_lt hp)
    have he:= (tendsto_pow_const_div_const_pow_of_one_lt 1 hp).mul_const t
    have hf:= ht.add he; rw [zero_mul,add_zero] at hf
    refine hf.congr fun i:ℕ=>?_ ; change x/a^i+((i:ℝ)^1/a^i)*t= (x+i*t)/a^i; ring
 filter_upwards [(stage_slope Q x).eventually (collateral (|C|) R.L), (stage_slope Q x).eventually_gt_atTop 0, hm.eventually (ge_mem_nhds (show (0:ℝ)<1 by norm_num))] with i ht hf hm m
 let N:=mesh m R.L i; have hh:1 ≤ ((More (cell m B R.L i)).val:ℝ):= by exact_mod_cast ((More (cell m B R.L i)).property)
 have hW:a^i ≤ sites (cell m B R.L i):=by
    apply (le_self_pow₀ hh (by decide: (4:ℕ)≠0)).trans'
    have he:R.L.val^i ≤ N.val:= Nat.le_mul_of_pos_left _ m.property
    have hx:N.val ≤ (More (cell m B R.L i)).val:= (Nat.le_mul_of_pos_right (N.val) Nat.zero_lt_two|>.trans (Nat.le_mul_of_pos_right _ B.property))|>.trans (Nat.le_mul_of_pos_right _ Nat.zero_lt_two)
    change (↑R.L.val:ℝ)^i≤ ((More (cell m B R.L i)).val:ℝ); exact_mod_cast he.trans hx
 let v:=hat R.L x i
 have hv:v≤a^i:=by linarith only [(div_le_iff₀ (pow_pos (zero_lt_one.trans hp) i)).mp hm]
 have hx:0≤ shrift R.L v:= (BProof.coin_pos ..).le
 exact (((le_abs_self C).trans ((div_le_iff₀ hf).mp ht)).trans (mul_le_mul_of_nonneg_left (hv.trans hW) hx))
end YM.CF.Py.Rate
