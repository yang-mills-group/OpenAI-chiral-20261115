import YM.SU5.Reconstruction.Crease.Grow
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.BridgeClub.Moth
open Function Set Filter MeasureTheory Spectral Analysis Metric ContinuousLinearMap Anvil Picket CrossedFrame Opera Multiplier
open scoped BigOperators Topology InnerProductSpace ComplexOrder NNReal ENNReal Complex Classical
variable {H D K: Hilbert} (C:Clasp K H D)
local notation "F"=>C.realF
local notation "P"=>C.angle
local notation "R"=>(1-C.angle:K.Op)
local notation "A"=>C.motion
local notation "X"=> spectrum ℂ C.angle
noncomputable def wage:= SimpleFunc.approxOn C.realF C.measurable_realF (Ioo 0 1) (1/2:ℝ) (by norm_num)
local notation "W"=>wage C
lemma wage_price (x:X)(n:ℕ): W n x∈ Ioo (0:ℝ) 1:= SimpleFunc.approxOn_mem ..
lemma wage_than (x:X) : Tendsto (fun n:ℕ=> W n x) atTop (𝓝 (F x)):= by
 apply SimpleFunc.tendsto_approxOn; rw [closure_Ioo (by norm_num: (0:ℝ)≠1)]; exact C.price x
omit C in -- not incl
private lemma boundMe (b:Bool){x:ℝ}(h:x∈ Ioo (0:ℝ) 1) : ‖envelope b x‖≤1:=by
 unfold envelope; split; unfold pole; rw [Complex.norm_real,Real.norm_eq_abs, abs_of_pos h.1]; exact h.2.le; rw [show gap x= (((1:ℝ)-x):ℝ) from ?_] -- casts
 · rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos (by linarith[h.2])]; linarith [h.1]
 push_cast; rfl
noncomputable def fareGate (b: Bool) : K.Op:= if b then P else R
local notation "e"=> fareGate C
lemma foster (t:ℝ)(b:Bool): Registers A (cash b t ∘ F) ((e b)^2 * C.Cabin (-t)):= by
   have h : Registers A (envelope b ∘ F) (e b):= by unfold fareGate; split_ifs with h; rw [h]; exact C.angle_reads; cases b; exact (Registers.one A).sub C.angle_reads; contradiction -- tune
   rw [show cash b t ∘ F=(envelope b ∘ F)^2 * (Clasp.river (-t) ∘ F) from funext (fun x : X=>by change _^2* ray t _=_; rw [chime]; rfl)]; exact (Registers.pow h 2).times (C.Cabin_reads _)
lemma foster2 : Registers A (petal ∘ F) (P*R):= C.angle_reads.times ((Registers.one A).sub C.angle_reads)
lemma grip(t:ℝ)(b:Bool)(x:ℝ)(h:x∈ Ioo (0:ℝ) 1): ‖cash b t x‖≤1:= by unfold cash; rw [norm_mul,norm_pow,ray,tune_norm,mul_one]; exact pow_le_one₀ (norm_nonneg _) (boundMe b h)
lemma here (n:ℕ)(t:ℝ)(b:Bool): ‖reel A (W n) t b‖ ≤1:= (counting A _ _).fare zero_le_one (fun x=> grip t b _ (wage_price ..)) -- C not param of grip!
lemma wave (x:K)(t:ℝ)(b:Bool): Tendsto (fun n:ℕ=> reel A (W n) t b x) atTop (𝓝 ((e b)^2 * C.Cabin (-t) <| x)):= by
 apply Registers.tends atTop (fun n=> cash b t ∘ W n) _ (foster C t b) (fun n=>counting ..) _ 1 (Eventually.of_forall fun n=>Eventually.of_forall fun x=> grip t b _ (wage_price ..))
 filter_upwards [C.inOpen x] with x h; suffices e':ContinuousAt (cash b t) (F x) from e'.tendsto.comp (wage_than C x)
 have hz:0<F x:=h.1; have ht:0<1-F x:=sub_pos.mpr h.2;  have pe:= (pom b).continuousAt (x:=F x); unfold cash ray tune tale; fun_prop (disch:=positivity) -- F x notation
lemma glowPath (x:K): Tendsto (fun n:ℕ=> royal A (W n) x) atTop (𝓝 (P (R x))):= by
 apply Registers.tends atTop (fun n=> petal ∘ W n) _ (foster2 C) (fun n=>counting ..) x 1 (Eventually.of_forall (fun n=>Eventually.of_forall fun y=> show ‖petal (W n y)‖ ≤ 1 from ?_)) (Eventually.of_forall (fun y=> (show Continuous petal from by unfold petal pole gap pole; fun_prop).continuousAt.tendsto.comp (wage_than C y))) -- tune
 exact (norm_mul (pole (W n y)) (gap (W n y))).le.trans (mul_le_one₀ (boundMe true (wage_price ..)) (norm_nonneg _) (boundMe false (wage_price ..)))
end YM.BridgeClub.Moth
