import YM.CF.BPress.Locale.Meter
/-! Lower Lc & after-PL room implied, can enforce extra minimum. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BPress.Locale
open Function Filter Finset Lattice Wilson RG Grid Branch Cube Bands Tunnel Wealth Weave Radix Push.AbsoluteSums Ledger Pressure
open scoped Topology BigOperators Classical Matrix
variable (G:GapSize)
lemma dawn (M:ℝ→ℕ)(h:PL fun i=>(M i:ℝ)): ∀ᶠ i in atTop, M i < umbra (G.select i):=by
 have he := high_purchase G (fun i=>2*(M i+1)+1) (by simpa only [Nat.cast_add,Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat] using ((PL.const 2).mul (h.add (PL.const 1))).add (PL.const 1)) (Eventually.of_forall fun i=>by omega); refine he.mono fun i t=>?_ ; have hf:= t.copy; unfold cloak at hf; unfold umbra; omega
lemma memory_fee (L:ℝ)(h:0<L): ∀ᶠ y in atTop, (frameWidth L y).val ≤ (G.select y).marked.val:=by
 let T:=fun i=>temp i; let V:=2*(G.collar:ℝ); let C:= 2*L; have he:= (npl_temp.const_mul C |>.add (npl_power npl_temp 2 (by omega) |>.const_mul V)).drop; filter_upwards [he.eventually (ge_mem_nhds zero_lt_one), frame_bounds h,eventually_gt_atTop (0:ℝ), G.bounds,G.tail_P,npl_temp.drop.eventually (ge_mem_nhds zero_lt_one)] with y p q u r t v; have hx:T y>0:=temp_pos u; let H:=(frameWidth L y).val; have hh:H≤H:=le_rfl -- tune
 have hp: (H:ℝ) ≤ C/T y:= le_trans q.2.le (by change 2*(L/Real.sqrt (T y))≤_; rw [←mul_div_assoc]; apply div_le_div_of_nonneg_left (by positivity) hx; have v:T y≤1:=v; nlinarith only [hx,v, Real.sqrt_nonneg (T y),Real.sq_sqrt hx.le]) -- tune sqrt by nlinarith
 apply Nat.cast_le (α:=ℝ)|>.mp; have he:=r.2.1; rw [← t,BandWidth.P,G.collar_select, inv_pow,←one_div] at he; push_cast at he; apply hp.trans; apply le_of_mul_le_mul_right _ (pow_pos hx 2); have hh:= (div_le_iff₀ (sq_pos_of_pos (temp_pos u))).1 he; have hP:C/T y*T y^2=C*T y:=by field_simp
 rw [hP]; change C * T y + V*T y^2≤1 at p; change 1≤ (((G.select y).marked.val:ℝ)+V)*T y^2 at hh; linarith
include G
lemma fr_PL (L:ℝ)(h:0<L): PL fun i=>(rFrame L i:ℝ):=by
 have hx:=Real.log_pos one_lt_two; apply (((PL.const (Real.log 2)).add PL.log).mul (PL.const ((Real.log 2)⁻¹))).mono; filter_upwards [memory_fee G L h,G.bound_y,eventually_gt_atTop (1:ℝ)] with y e p t; have ht: (2:ℝ)^rFrame L y≤2*y:=le_trans ?_ p; swap; · have he: (frameWidth L y).val ≤ (G.select y).P:= le_trans e (Nat.le_add_right ..); simp only [frameWidth, PNat.pow_coe] at he; exact_mod_cast he
 have hp:=Real.log_le_log (by positivity : 0<(2:ℝ)^rFrame L y) ht; rw [Real.log_pow, Real.log_mul (by norm_num) (by linarith)] at hp; rw [abs_of_nonneg (by positivity : 0≤ (rFrame L y:ℝ)), ←div_eq_mul_inv]; exact ((le_div_iff₀ hx).mpr hp).trans (le_abs_self _)
lemma lPL (L:ℝ)(o b:ℕ)(h:0<L): PL fun i=>(Lcharge o b L i:ℝ):=by
 unfold Lcharge; simp_rw [Nat.cast_mul]
 apply (PL.const _).mul; unfold pacer; simp only [Nat.cast_add,Nat.cast_mul]; apply (PL.const _).add; apply (PL.const _).mul; apply PL.add _ (PL.const _); exact ((PL.const _).mul (((PL.const _).add (fr_PL G L h)).add (PL.const _))) -- tune G included if signature?
-- compress calibration Lc. powers as explicit PolyLift array nonzero even officer. Radius depends on vol; out shadow.
def courant (l A:ℕ)(a u:ℝ): Prop:= A≤l ∧ a*A≤u/2*l
lemma Fits (A V:ℝ→ℕ)(u:ℝ→ℝ)(p:PL fun i=>(A i:ℝ))(v:PL fun i=>(V i:ℝ))(q:PL fun i=>(u i)⁻¹)(e:∀ᶠ i in atTop,0<u i)(a:ℝ)(w:0 ≤ a): ∃ r:ℝ→Side, PL (fun i=>((r i).val:ℝ)) ∧ ∀ᶠ i in atTop,Even (r i).val∧ V i ≤ (r i).val∧ courant (r i).val (A i) a (u i) ∧ (r i).val ≤ umbra (G.select i):=by
 let F(i:ℝ) := (2*a)* A i * (u i)⁻¹; let H(i:ℝ):=⌈F i⌉₊; let M(i):=A i+V i+H i+1; let r(i:ℝ):Side:= ⟨M i*2, by unfold M; positivity⟩; have hv : PL fun i=>(H i:ℝ):= (((PL.const _).mul p).mul q).ceil (e.mono fun i v=> show 0≤ F i from (by unfold F; positivity)); have he: PL fun i=>((r i).val:ℝ):=by change PL fun i=> (((M i*2:ℕ)):ℝ); unfold M; push_cast; exact (((p.add v).add hv).add (PL.const 1)).mul (PL.const 2)
 refine ⟨r,he,?_⟩; filter_upwards [dawn G _ he,e] with i h t; have hx:H i≤(r i).val:=by change _ ≤ M i*2; unfold M; omega
 have hm:(r i).val=(A i+V i+H i+1)*2:=rfl; refine ⟨ ⟨M i, mul_two _⟩, by omega,⟨by omega,?_⟩, h.le⟩; have hf:F i ≤ ((r i).val:ℝ):= (Nat.le_ceil _).trans (Nat.cast_le.mpr hx); unfold F at hf; rw [← div_eq_mul_inv] at hf; have h':= (div_le_iff₀ t).mp hf; linarith
end YM.CF.BPress.Locale
#print axioms YM.CF.BPress.Locale.floor_pays
#print axioms YM.CF.BPress.Locale.Floor.lightV
#print axioms YM.CF.BPress.Locale.microReceipt
#print axioms YM.CF.BPress.Locale.Fits
#print axioms YM.CF.BPress.Locale.FareP.purse
