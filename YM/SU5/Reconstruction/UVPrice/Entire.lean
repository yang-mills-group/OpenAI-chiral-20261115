import YM.SU5.Reconstruction.UVPrice.Walls
import YM.SU5.Reconstruction.Seams.Ultralimit
import Mathlib.Analysis.Complex.Liouville
/-!
# Zero modes have compact support in momentum. Analytic continuation across observers will price it out.
-/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Roy
open Function Set Filter MeasureTheory Spectral Analysis Metric InnerProductSpace
open scoped Topology NNReal ENNReal ComplexOrder InnerProductSpace ComplexConjugate
open YM.Multiplier Chirp CrossedFrame OS Semigroup Boundary Probe CF.Buffered.Afterglow.Tower MeshClock Germ SelectionAnalysis ConePrice Real Picket
variable {H : Hilbert} {a b : Axis} (S : OS.Semigroup H a)
local notation "P" => S.ℚmeasure
local notation "μ" x:max=> (P).diagonal x
variable {R:ℝ}
noncomputable def gust (b:Axis)(R:ℝ)(z:ℂ)(p:E4) := Complex.exp (Complex.I*z*( (min (max (-R) (p b)) R:ℝ) :ℂ))
local notation "G"=> gust b R
variable (r:0≤R)(hz:IsCompact (Beneath S 0))(f:H)
include r
lemma gust_bound (z:ℂ)(p:E4): ‖gust b R z p‖≤ Real.exp (|z.im| *R):=by
 let u:=min (max (-R) (p b)) R
 have hp: |u| ≤ R:= abs_le.mpr ⟨le_min (le_max_left ..) (by linarith), min_le_right ..⟩
 unfold gust; rw [Complex.norm_exp]; apply Real.exp_le_exp.mpr
 suffices -(z.im*u)≤ |z.im| *R by simpa [u,Complex.mul_re, Complex.mul_im] using this
 refine (le_abs_self _).trans ?_; rw [abs_neg,abs_mul]; exact mul_le_mul_of_nonneg_left hp (abs_nonneg _)
lemma tagged (z:ℂ): Tag (gust b R z):=⟨by unfold gust;fun_prop,_,(exp_pos _).le,gust_bound r z⟩
local notation "Λ"=> Beneath S 0
local notation "Ξ" p:max=> μ (cue S p)
-- explicitly plane unbounded? uses clipped p even before continuation. No choosing some support sets depending z
noncomputable def reward (b:Axis)(R:ℝ)(z:ℂ) := inner ℂ (cue S f) (order P (gust b R z) (cue S f))
lemma collects (z:ℂ): reward S f b R z = ∫ p, G z p∂ Ξ f:= (order_reads P (tagged (b:=b) r z)).awakes _
lemma on_fullReal (z:ℝ)(h:b≠a)(g:∀ x∈ Λ,|x b|≤ R):
    reward S f b R z = inner ℂ (cue S f) (S.U (z • cross a b h) (cue S f)) :=by
 rw [collects S _ f, (costU S _).awakes]
 swap; exact r
 apply integral_congr_ae; filter_upwards [zero_μ S f] with x hx
 obtain ⟨t,u⟩:= abs_le.mp (g _ hx); change gust b R z x=plane x (z • basis b)
 unfold gust plane; rw [max_eq_right t,min_eq_left u,real_inner_smul_right,innerB]; push_cast; ring_nf
lemma interest : Differentiable ℂ (reward S f b R):= by
 intro z; let A:= |z.im|+1; have hv(w:ℂ)(p: w∈ball z 1): |w.im|≤ A:=by
   calc
    _ = |(w-z).im+z.im|:= by rw [Complex.sub_im,sub_add_cancel]
    _ ≤ |(w-z).im|+|z.im|:= abs_add_le ..
    _ ≤ _:= by
      have he:= Complex.abs_im_le_norm (w-z); rw [←dist_eq_norm] at he; unfold A; linarith [mem_ball.mp p]
 have he:= ciel P isOpen_ball (gust b R) (Real.exp (A*R)) (fun z=> order P (gust b R z)) (fun z _=> order_reads P (tagged r z)) (fun p=>Differentiable.differentiableOn (by unfold gust; fun_prop)) (fun w x p=>(gust_bound r w p).trans (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (hv w x) r))) (fun x=> (tagged r x).meas) z (mem_ball_self (x:=z) zero_lt_one) (cue S f)
 exact he.differentiableAt
lemma ready_bound (z:ℂ): ‖reward S f b R z‖ ≤ ‖cue S f‖^2*exp (|z.im| *R):= by
 rw [collects S r f]; refine le_trans (norm_integral_le_of_norm_le_const (C:= exp (|z.im| *R)) (ae_of_all _ (fun p=> gust_bound r z p))) ?_
 rw [Registers.size,mul_comm]
lemma bill_sym (z:ℂ): reward S f b R (-conj z)= conj (reward S f b R z):= by
 rw [collects S r f, collects S r f, ← integral_conj]
 refine integral_congr_ae (ae_of_all _ (fun x=>?_)); unfold gust; dsimp only; rw [←Complex.exp_conj]; simp
omit r
-- generic. Let analytic investor payment in right half give full constancy
open Asymptotics Complex PhragmenLindelof
lemma same_pay {F:ℂ→ℂ}{C D:ℝ}(q:0<D)(e:0 ≤ R)(h:Differentiable ℂ F)(p:∀ z,F (-conj z)=conj (F z))(v:∃ B:ℝ,0≤ B∧∀ z:ℂ, ‖F z‖≤ B*Real.exp (|z.im| *R)) (k:∀ z:ℂ,D≤ z.re→‖F z‖≤ C) : ∀ z:ℂ,F z=F 0:= by
 have k'(z:ℂ)(u:z.re≤ -D): ‖F z‖≤ C:=by rw [←Complex.norm_conj, ← p]; apply k; simp; linarith
 obtain ⟨B,B₀,r⟩:= v; intro z; apply Differentiable.apply_eq_apply_of_bounded h
 apply isBounded_iff_forall_norm_le.mpr; refine ⟨C, ?_⟩; rintro x ⟨y,rfl⟩
 rcases lt_or_ge y.re D with m|m; swap; exact k y m
 rcases le_or_gt y.re (-D) with u|u; · exact k' y u
 let c:=Real.pi/(4*D); have hc:0<c:= by unfold c; positivity
 apply PhragmenLindelof.vertical_strip h.diffContOnCl _ (fun z m=> k' z m.le) (fun z m=> k z m.ge) u.le m.le;
 refine ⟨c,?_,R/c, Asymptotics.IsBigO.of_bound B (Eventually.of_forall fun x=> (r x).trans ?_)⟩
 · unfold c; rw [div_lt_div_iff₀] <;> nlinarith [Real.pi_pos]
 apply mul_le_mul_of_nonneg_left _ B₀; rw [norm_eq_abs, abs_of_pos (Real.exp_pos _)]; apply Real.exp_le_exp.mpr; let T:=|x.im|
 have he:= (le_div_iff₀ hc).mpr (show T*c ≤ Real.exp (c*T) by linarith [Real.add_one_le_exp (c*T)]); exact (mul_le_mul_of_nonneg_right he e).trans_eq (by ring)
end YM.Roy
