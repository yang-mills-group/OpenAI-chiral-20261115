import YM.CF.Buffered.Word

/-! # Strict nontriviality after bill-E

This one conclusion uses the two marked estimates of preceding `bill-E`, on
the resulting whole cone as stated there, applied to these very same
CapP cuts and mark. State EXACTLY this input (not compiled within this
file). The Gram positivity theorem didn't use it. No new coupling or limit
of epsilon (or R growing with period). Assumption as shown on the actual
Readers. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 16000
noncomputable section
namespace YM.CF.Buffered
open Function Fock Filter NormedSpace SU Lat Lattice Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree
open Bilinear
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder ComplexConjugate
attribute [local instance] opCStarAlgebra
def P20 := Onyx.pencil (Window.corner 1) 2 0
lemma P20_value : P20 = ((1/Real.pi^2:ℝ):ℂ) := by
 change Onyx.pencil (corner 1) (dnSpin 0) (upSpin 0) = _; rw [pencil_time]; norm_num [Window.kernel,one_div]
lemma normP20 : 0 < ‖P20‖ := by rw [P20_value,Complex.norm_real,Real.norm_of_nonneg (by positivity)]; positivity
def compared : ℝ := ‖P20‖^2 * (1+1/(5*512))
structure Tol (e : ℝ) : Prop where
 pos : 0<e
 small : e< ‖P20‖/2
 gap : 0 < compared-e-(‖P20‖+e)^2
-- before all data choice in bill-E
lemma tolerance : ∀ᶠ e : ℝ in nhdsWithin 0 (Set.Ioi 0), Tol e := by
 let f(e):= compared-e-(‖P20‖+e)^2; have hf:0<f 0:=by unfold f compared; rw [sub_zero,add_zero]; nlinarith [normP20]
 filter_upwards [self_mem_nhdsWithin, (eventually_nhdsWithin_of_eventually_nhds (gt_mem_nhds (half_pos normP20))), (eventually_nhdsWithin_of_eventually_nhds (show ∀ᶠ i in 𝓝 0,f i∈ Set.Ioi 0 from (show Continuous f from (continuous_const.sub continuous_id).sub ((continuous_const.add continuous_id).pow 2)).continuousAt (x:=0) (lt_mem_nhds hf)))] with i p h u; exact ⟨p,h,u⟩
lemma choose_tolerance : ∃ e : ℝ, Tol e := tolerance.exists
variable {K : Calibration} {C : Process K}
variable (P : Histories K)
def BillInput (e : ℝ) :=
 ∀ᶠ n in atTop, ∀ m:Side, K.Allowed m n →
   ‖P.cap n (word K m)-P20‖ < e ∧ ‖P.cap n ((word K*thetaK K (word K)) m)-(compared:ℂ)‖<e
-- tail in n equivalent for "u sufficiently large" along these data, since stage n → +∞.
private lemma Iterated.rec_bound {P : Histories K} {g : Family K} {t u : ℂ} {a : ℝ}
    (p : Iterated P C g u) (h : ∀ᶠ n:ℕ in atTop,∀ m:Side,K.Allowed m n → ‖P.cap n (g m)-t‖<a) : ‖u-t‖ ≤ a := by
 obtain ⟨l,p,k⟩:=p; apply le_of_tendsto ((k.sub_const t).norm); filter_upwards [p] with m p; apply le_of_tendsto ((p.sub_const t).norm); filter_upwards [(C.grows_n m).eventually h,(C.grows_n m).eventually (K.eventually_allowed (C.sides m))] with j u k; exact (u _ k).le
namespace Corollary
variable {P : Histories K} {wide : Bool} {E : Family K → ℂ} {e : ℝ}
local notation "A" => word K
def centered (h : Settled P C wide E) : Family K:= word K - E (word K) • (1:Family K)
lemma cent_eligible (h : Settled P C wide E) : Eligible K wide (centered h) := (eligible K wide).sub_mem (allowed K wide) ((eligible K wide).smul_mem _ Eligible.oneT)
-- decomposition (squared norm notation)
lemma decor (h : Settled P C wide E) : E (thetaK K (centered h)*centered h)= E (thetaK K (word K)*word K) - ((‖E (word K)‖^2:ℝ):ℂ) := by
 let M : eligible K wide:=⟨A,allowed K wide⟩; let U: eligible K wide:=⟨1,Eligible.oneT⟩
 let X:=E A; have ht:h.form U M=X :=by rw [form P C]; simp only [U,M,thetaK, ref_identity,one_mul]; rfl
 have he : h.form M U=star X := by rw [← ht, h.herm]
 have hp : h.form U U=1:=by rw [form P C]; simp only [U,thetaK,ref_identity, mul_one]; exact h.value
 change h.form (M-X • U) (M-X • U)= h.form M M - ((‖X‖^2:ℝ):ℂ)
 rw [map_sub h.form, LinearMap.sub_apply,map_smulₛₗ (f:=h.form)]; simp only [map_sub,map_smul,LinearMap.smul_apply, ht,he,hp,starRingEnd_apply,smul_eq_mul,mul_one,sub_self,mul_zero,sub_zero,mul_comm X,←Complex.star_def]
 rw [←Complex.normSq_eq_norm_sq,Complex.normSq_eq_conj_mul_self]; rfl
include K
/-- Here the application, with the reading on the same UV and period selections. -/
theorem output (t : Tol e) (h : Settled P C wide E) (hp : BillInput P e) : E (word K) ≠ 0 ∧ Eligible K wide (centered h) ∧ 0 < E (thetaK K (centered h)*centered h) ∧ 0 < Real.sqrt (E (thetaK K (centered h)*centered h)).re := by
 let w := (allowed K wide).forget; let x:=E A; let z:=E (thetaK K A * A); let l:= E (thetaK K (centered h)*centered h)
 have ht: ‖x-P20‖≤e:= Iterated.rec_bound (h.convergence _ w) (hp.mono fun n p m u=> (p m u).1)
 have hw: ‖z-(compared:ℂ)‖≤ e := by unfold z; rw [w.ref.comm w]; exact Iterated.rec_bound (h.convergence _ (w.mul w.ref)) (hp.mono fun n p m u=> (p m u).2)
 have hz : x ≠ 0:=by intro p; rw [p,zero_sub,norm_neg] at ht; linarith only [ht,t.small,normP20]
 have hb : ‖x‖≤ ‖P20‖+e := by have hh:= (norm_sub_norm_le x P20).trans ht; linarith
 have hu: compared-e ≤ z.re :=by have hg:= Complex.abs_re_le_norm (z - compared); rw [Complex.sub_re,Complex.ofReal_re, abs_le] at hg; linarith only [hg.1,hw]
 have hK : l≥0 := h.gram (cent_eligible h); have hA : l = _:= decor h; have gl : 0<l.re := by change l=z-((‖x‖^2:ℝ):ℂ) at hA; rw [hA,Complex.sub_re,Complex.ofReal_re]; nlinarith [norm_nonneg x,t.gap]
 exact ⟨hz,cent_eligible h, Complex.lt_def.mpr ⟨gl,(Complex.le_def.mp hK).2⟩, Real.sqrt_pos.mpr gl⟩
end Corollary
end YM.CF.Buffered
#print axioms YM.CF.Buffered.Corollary.output
