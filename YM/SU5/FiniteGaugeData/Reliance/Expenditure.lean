import YM.SU5.FiniteGaugeData.Reliance.Chest
/-! # Shrinking of errors on this election. Express quantities on s-observing choices.

 This result also when taking an arbitrarily small FIXED fraction of the allowed temperature.
 This means e.g. we can cut away local rough fields even for s-indexed normalized probes with
 polynomial (in y_s) costs, or for bigger probes under footprint vs `magnified` spending,
 choose before limit E application. No statement about when artificially changing markup profit
 in comparing to another election. `s→∞` here is only for THE BUDGET ON THESE NATIVE MARKS;
 it isn't asserting a continuum effect or that the particular family has related operator limits.
 -/
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option synthInstance.maxSize 24000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Reliance
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder NNReal Classical
attribute [local instance] opCStarAlgebra
open Concord
open Py Py.Rate LocalLimit Preparation
open Afterglow Afterglow.Sound Afterglow.Satin Afterglow.Journey
namespace ShortWave
open Universum
variable (P:Preparation)
lemma tall_hat : Tendsto (hat P.R.L P.x) atTop atTop:=by
 have ht:0 < billX P.R.L:=by have he:= billx_T P.V; unfold ν_PS at he; linarith
 exact tendsto_const_nhds.add_atTop (tendsto_natCast_atTop_atTop.atTop_mul_const ht)
private theorem presence (k:ℝ) : ∀ᶠ x:ℝ in atTop,k*Real.log x ≤ Real.exp ((Real.log (Real.log x))^2):=by
 let u:=Real.log; let f(x:ℝ):=u (u x); let g:= Real.tendsto_log_atTop; let v: Tendsto f atTop atTop:= g.comp g; have he: Tendsto (fun x=>Real.exp (f x)) atTop atTop:= Real.tendsto_exp_atTop.comp v
 filter_upwards [he.eventually_ge_atTop k,g.eventually_gt_atTop 0, v.eventually_ge_atTop 2] with x q p t
 have hv: Real.log x= Real.exp (f x):=(Real.exp_log (show 0<u x from p)).symm
 have hx:2*f x ≤ f x^2:= by nlinarith
 exact (mul_le_mul_of_nonneg_right q p.le).trans ((show Real.exp (f x)*Real.log x=Real.exp (2*f x) from by rw [hv, two_mul,Real.exp_add]).trans_le (Real.exp_monotone hx))

open Pressure PathData Sods Precision YM.Next.Rank
private lemma smoke (C:ℝ)(p:0<C)(n:ℕ): Tendsto (fun x:ℝ=>x^n*Real.exp (-C*Real.exp ((Real.log (Real.log x))^2))) atTop (𝓝 0):=by
 let f(x:ℝ):= Real.exp (Real.log (Real.log x) ^ 2); let V(x:ℝ):= (n:ℝ)*Real.log x - C*f x
 have he:Tendsto V atTop atBot:=by
    refine tendsto_atBot_mono' _ ?_ (tendsto_neg_atTop_atBot.comp Real.tendsto_log_atTop)
    filter_upwards [presence (((n:ℝ)+1)/C)] with x v
    have hK:C*((((n:ℝ)+1)/C)*Real.log x) ≤ C*f x:= mul_le_mul_of_nonneg_left v p.le
    have hv: -Real.log x = (n:ℝ)*Real.log x-C*((((n:ℝ)+1)/C)*Real.log x):=by field_simp; ring
    change (n:ℝ)*Real.log x - C*f x ≤ -Real.log x; rw [hv]; -- rhs `rw` swaps all incl neg in defs? linarith
    linarith only [hK]
 refine (Real.tendsto_exp_atBot.comp he).congr' ?_; filter_upwards [eventually_gt_atTop (0:ℝ)] with x w; change Real.exp (V _) = _; unfold V; rw [show (n:ℝ)*Real.log x - C * _= (n:ℝ)*Real.log x+(-C*f x) from by ring, Real.exp_add,Real.exp_nat_mul,Real.exp_log w] -- rfl

def shutters (s:ℕ)(u:ℝ) := u * Pressure.temp (hat P.R.L P.x s)

lemma estimate (m:ℕ)(u:ℝ)(p:0<u): Tendsto (fun s:ℕ=>extinguish (Universum.slope P s) (shutters P s u) (hat P.R.L P.x s ^ m)) atTop (𝓝 0):= by
 let B:= strength P.K.top.clip; have he:0<B:= strength_pos _
 let c:= signs⁻¹*(B/4)*u; have ht:= signs_pos; have hc:0 < c:=by unfold c; positivity
 refine ((smoke _ hc m).comp (tall_hat P)).congr' ?_
 filter_upwards [(tall_hat P).eventually_gt_atTop 0] with i v
 let g:=hat P.R.L P.x i; let h:=Real.log (Real.log g); let U':= (Real.sqrt g)⁻¹; have hp:0<U':= inv_pos.mpr (Real.sqrt_pos.mpr (show 0<g from v)); change g^m*Real.exp (-c*Real.exp (h^2))= g^m*Real.exp (-(signs⁻¹*(B/(2*(2*U'))*(u*(U'*Real.exp (h^2))))))
 congr 2; unfold c; field_simp; ring -- ht
lemma shrinks (u:ℝ): Tendsto (fun s=> shutters P s u) atTop (𝓝 0):=by
 have he:Tendsto Pressure.temp atTop (𝓝 0):=by simpa using (YM.Work.E09.radiusB_temp 0)
 simpa only [Function.comp_apply,shutters,mul_zero] using (he.comp (tall_hat P)).const_mul u -- idem

variable {P}{l:ℕ} (Y:Course P (VolumeCape.Dream.Nimbus l))(H:Real.exp 1 ≤ P.x)(PQ:Cashbox P)
variable {i k:ℕ→ℕ}{F:ℕ→Family (tent Y H)→ℕ→ℂ}{E:ℕ→Family (tent Y H)→ℂ}{A:Playhouse P l}
local notation "Q"=> tent Y H
local notation "zM"=> magnified Q (grossC Y PQ)
variable (m d:ℕ)(u:ℝ)(p:0<u)(W:Traced Y H i k F E A)
include W PQ p
lemma relief (ε:ℝ)(h:0<ε): ∀ᶠ i:ℕ in atTop,∀ (A:ℝ), 0 ≤ A → ∀ (s:Finset Cover) (T:Finset (Face ℤ)) (g:restsOn T s), occupy s d → ∀ x:junior (tent Y H),x∈club (tent Y H) s→(∀ᶠ n:Side in atTop,∀ r, ‖x.val n r‖ ≤ (hat P.R.L P.x i)^m*A)→
    ‖E i (ablate T (shutters P i u) Q g*x).val‖ ≤ ε*A:=by
 have he : Tendsto (fun s:ℕ=> extinguish (Universum.slope P s) (shutters P s u) (hat P.R.L P.x s ^ m)* zM d) atTop (𝓝 0):=by simpa only [zero_mul] using (estimate P m u p).mul_const (zM d) -- ambiguous notation
 filter_upwards [he.eventually (ge_mem_nhds h),(tall_hat P).eventually_ge_atTop 0] with i p' hv A ha s T p z x t w
 apply (soot Y H PQ d W (mul_nonneg (pow_nonneg hv _) ha) i T s p z x t w).trans; apply le_trans ?_ (mul_le_mul_of_nonneg_right p' ha); unfold extinguish; apply le_of_eq; ring
end ShortWave
end YM.CF.Buffered.Reliance
#print axioms YM.CF.Buffered.Reliance.ShortWave.relief
