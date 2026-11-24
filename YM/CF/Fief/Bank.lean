import YM.CF.Fief.Beam
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Fief
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.Frobenius
open AnalyticBridge.Annulus1AD Ac Esti
open Atala Forge Cloak Rill Hive Fock Stilo Palot Scion
open Cube Lat Tenant Tulip
open Pastry Hake Levier Urn Peaks Fock Laic Branch Drapes
open Stilo Palot Scion Function Levier Hake Urn Peaks Fock Laic Branch Drapes
open Rush Scroll Paige Vault Phase Acorn Spire Eire
open Tarn Cay Slate Esti Cour Hest Arena Reine Kennel Facet Broc Pec Push.SectorMeasure.Oriented
open Jet Lich Corne
open Lich.Muster
attribute [local instance] opCStarAlgebra
local notation "G₅"=> SU.group
open SectorNext.Remainder.Scales
variable(L:Side)
def sizeK(L:Side)(n:ℕ)(F:ℝ→ℝ):Prop:= ∃ H:ℕ,∀ᶠ x:ℝ in atTop, |F x| ≤ g SU.group L x^n*p SU.group L x^H
namespace sizeK
variable {L}{n k m:ℕ}{F W:ℝ→ℝ}
local notation "G"=>Scales.g G₅ L
local notation "P"=>Scales.p G₅ L
variable (L)
lemma mild(v:ℝ):sizeK L 0 fun _=>v:=⟨1,(by simp_rw [pow_zero,pow_one,one_mul]; exact (peak G₅ L).eventually_ge_atTop _)⟩
lemma main:sizeK L 1 G:=⟨0,by filter_upwards [(year G₅ L).eventually_gt_atTop 0] with x t; rw [abs_of_pos ((Scales.gauge G₅ L t)),pow_one,pow_zero,mul_one]⟩
lemma height:sizeK L 0 P:=⟨1,by filter_upwards with x; rw [abs_of_pos (Scales.pos ..),pow_one,pow_zero,one_mul]⟩
lemma Bcash:sizeK L 0 (fun x=>(radiusB x:ℝ)):=by
 refine ⟨1,?_⟩; filter_upwards [(cover_pay G₅ L 1 (a:=1) (by norm_num)).eventually (ge_mem_nhds zero_lt_one)] with x v; rw [Real.rpow_one,pow_one,div_le_iff₀ (Scales.pos ..),one_mul] at v; simp only [abs_of_nonneg (Nat.cast_nonneg (α:=ℝ) _),pow_zero,pow_one,one_mul]; exact le_trans (le_add_of_nonneg_left zero_le_one) v
variable {L}
lemma cost_d (h:sizeK L n F)(p:∀ᶠ x in atTop,|W x| ≤ |F x|): sizeK L n W:= by obtain ⟨H,h⟩:=h; exact ⟨H,(h.and p).mono fun i v=>v.2.trans v.1⟩
lemma tint(h:sizeK L n F)(k:sizeK L m W) : sizeK L (n+m) (fun x=>F x*W x):=by
 obtain ⟨v,h⟩:=h; obtain ⟨u,g⟩:=k; refine ⟨v+u,?_⟩; filter_upwards [(year G₅ L).eventually_gt_atTop 0,h,g] with x p h g; rw [abs_mul,pow_add,pow_add]; exact (mul_le_mul h g (abs_nonneg _) ((abs_nonneg _).trans h)).trans_eq (by ring)
lemma low (h:sizeK L n F)(p:k≤n):sizeK L k F:=by obtain ⟨H,h⟩:=h; refine ⟨H,?_⟩; filter_upwards [h,(year G₅ L).eventually_gt_atTop 0,(minute G₅ L).eventually (ge_mem_nhds zero_lt_one)] with x h p' v; exact h.trans (mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one (Scales.gauge G₅ L p').le v p) (pow_nonneg (Scales.pos ..).le _))
lemma scale (h:sizeK L n F)(t:ℝ) : sizeK L n (fun x=>t*F x):=Nat.zero_add n ▸ (mild _ _).tint h
lemma square (h:sizeK L n F)(i:ℕ):sizeK L (n*i) (fun x=>F x^i):=by
 induction i with|zero=>simp only [mul_zero,pow_zero]; exact mild _ _| succ i ih=>simp_rw [pow_succ,Nat.mul_succ]; exact tint ih h
lemma powC (h:sizeK L 0 F)(i:ℕ):sizeK L 0 (fun x=>F x^i):=by simpa only [zero_mul] using h.square i
lemma accrue(h:sizeK L n F)(p:sizeK L n W):sizeK L n (fun x=>F x+W x):=by
 obtain ⟨m,h⟩:=h; obtain ⟨u,p⟩:=p; refine ⟨m+u+1,?_⟩; filter_upwards [h,p,(year G₅ L).eventually_gt_atTop 0,(Scales.peak G₅ L).eventually_ge_atTop 2] with x h p v k; have g:0<G x:=Scales.gauge G₅ L v; let X:=G x^n; let Y:=P x; have he:2 ≤ Y:=k; have hv:1 ≤ Y:=one_le_two.trans k; have hm:0≤ X:=pow_nonneg g.le _
 apply ((abs_add_le ..).trans (add_le_add h p)).trans; change X*Y^m+X*Y^u ≤ X*Y^(m+u+1); rw [←mul_add]; apply mul_le_mul_of_nonneg_left _ hm; have hp:= pow_le_pow_right₀ hv (show u ≤ (m+u) by omega); have ht:= pow_le_pow_right₀ hv (show m ≤ (m+u) by omega); rw [pow_succ]; nlinarith [pow_pos (zero_lt_one.trans_le hv) (m+u)]
lemma spine (h:sizeK L 1 F):Tendsto F atTop (𝓝 0):=by
 obtain ⟨H,h⟩:=h; rw [tendsto_zero_iff_norm_tendsto_zero]; refine squeeze_zero' (Eventually.of_forall fun _=>norm_nonneg _) h ?_; simpa only [pow_one,pow_zero,one_mul,mul_comm (P _ ^ H)] using tally_g G₅ L 0 H
variable (L)
lemma tip(v:ℝ)(hv:0<v):sizeK L 2 (tipPay v):=by
 refine ⟨0,?_⟩
 filter_upwards [tail_delay G₅ L v hv,(year G₅ L).eventually_gt_atTop 0] with x h hy; let p:=p G₅ L x; have hp: betaF G₅ x L=y G₅ L x:=rfl
 rw [hp] at h; have hh:=yg2 G₅ L hy; rw [pow_zero,mul_one,abs_of_pos (Real.exp_pos _)]
 refine le_trans (Real.exp_monotone ?_) (h.trans_eq ?_)
 · apply mul_le_mul_of_nonpos_left (Nat.cast_le.mpr (_ : Stores.till x ≤ radiusB x/60)) (neg_nonpos.mpr hv.le); unfold Stores.till; omega
 field_simp; linarith
lemma coin : sizeK L 1 Neige.lamp :=by
 have he:= ((Bcash L).powC 9).tint (((main L).tint (height L)).scale 2); apply he.cost_d; filter_upwards [Work.E07.temp_coarse_le G₅ L,eventually_gt_atTop (0:ℝ)] with x p v; have hv:= Work.E09.temp_pos v; unfold Neige.lamp; rw [abs_of_nonneg (by positivity : 0≤ (radiusB x:ℝ)^9*temp x)]
 -- tune explicit
 exact (mul_le_mul_of_nonneg_left (p.trans_eq (by rw [←Scales.fi])) (pow_nonneg (Nat.cast_nonneg _) _)).trans (le_abs_self _)
end sizeK
end YM.CF.Fief
