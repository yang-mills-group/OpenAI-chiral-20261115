import YM.SU5.Reconstruction.UVPrice.Backline
/-!
# momentum bounded on low energy grants. True in ALL finite slices
-/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Roy
open Function Set Filter MeasureTheory Spectral Analysis Metric InnerProductSpace
open scoped Topology NNReal ENNReal ComplexOrder InnerProductSpace
open YM.Multiplier Chirp CrossedFrame OS Semigroup Boundary Probe CF.Buffered.Afterglow.Tower MeshClock Germ SelectionAnalysis ConePrice Real Picket
variable {H : Hilbert} {a b : Axis} (S : OS.Semigroup H a)
local notation "D₁" => {i:Axis//i≠a}

private lemma surf (e : ℝ) (p : E4) (b : 0 < e) (x : Cross a)
    (he : ∀ t : ℝ≥0, 0 < t → (t:ℝ)<e → tension ((t:ℝ) • x) t p ≤ 0) :
    (inner ℝ (SEP a p) x)^2 ≤ (p a)^2 := by
  let q:= inner ℝ (SEP a p) x
  let d := fun t:ℝ => exp (-(p a)*t)
  let f(t:ℝ):ℝ:= 2 * Real.sin (t*(q/2))*d t; let g(t:ℝ):ℝ:=1-d t
  have e₀ : d 0=1:= by simp [d];
  have f₀ : f 0=0:= by simp [f]
  have g₀ : g 0=0:= by simp [g,e₀]
  have hd : HasDerivAt d (-(p a)) 0 := by simpa [d] using (((hasDerivAt_id' (0:ℝ)).const_mul (-(p a))).exp)
  have hf : HasDerivAt f q 0 := by
    convert ((((hasDerivAt_id' (0:ℝ)).mul_const (q/2)).sin.const_mul 2).mul hd) using 1 <;> try rfl
    simp [e₀]; ring
  have hg : HasDerivAt g (p a) 0 := by simpa [g] using (hd.const_sub 1)
  apply le_of_tendsto_of_tendsto (hf.tendsto_slope_zero_right.pow 2) (hg.tendsto_slope_zero_right.pow 2)
  filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds b)] with t v ht
  change (t⁻¹ • (f (0+t) - f 0))^2 ≤(t⁻¹ • (g (0+t)-g 0))^2
  simp only [f₀,g₀,sub_zero,smul_eq_mul,mul_pow,zero_add]
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
  let bt : 0 < t := v
  have H₁:=he ⟨t,bt.le⟩ (show 0<(⟨t,bt.le⟩:ℝ≥0) from bt) ht
  erw [trig_rel, sub_nonpos, real_inner_smul_right (SEP a p) x t] at H₁
  dsimp only [f,g,d,q]; rw [← mul_div_assoc]; exact H₁
private lemma pours {x:E4}(i:D₁)(t d:ℝ≥0)(q:0<t): tension (((d*t:ℝ≥0):ℝ) • cross a i.val i.property) (d*t) x = tension ((t:ℝ) • cross a i.val i.property) t ((d:ℝ) • x):= by
 rw [trig_rel,trig_rel,map_smul, real_inner_smul_left (SEP a x) ((t:ℝ) • cross a i.val i.property) (d:ℝ), real_inner_smul_right (SEP a x) (cross a i.val i.property) ((d*t:ℝ≥0):ℝ),real_inner_smul_right (SEP a x) (cross a i.val i.property) (t:ℝ)] -- tune
 simp only [smul_eq_mul,NNReal.coe_mul,PiLp.smul_apply]; ring_nf
variable (u:∀ p∈ Shelf S,∀ q∈Shelf S, p+ q ∈Shelf S)(h:Wheater S)
include u
lemma addition (x:E4)(p:x∈Shelf S)(i:ℕ)(eps: 0 < i): (i:ℝ) • x∈Shelf S:=by
 induction i with
 | zero=> omega
 | succ i ih=>
   by_cases v:i=0; · subst i; simpa
   rw [Nat.cast_add,Nat.cast_one, add_smul,one_smul]; exact u _ (ih (by omega)) _ p
include h
theorem restore (b:Axis)(e:b≠a) : Paces b S:= by
 intro y x t; have hp:x∈Shelf S:= subset_closure (mem_iUnion_of_mem y t)
 let X:= cross a b e
 let F(t:ℝ≥0):= tension ((t:ℝ) • X) t x
 have he(p:ℝ≥0)(hx:0<p) : F p ≤0:=by
   apply le_of_forall_gt_imp_ge_of_dense
   intro ε hε; obtain ⟨t,z,g⟩:= h ε hε
   obtain ⟨i,hi⟩:= exists_nat_gt ((p:ℝ)/t)
   have hg: (0:ℝ)< i:= lt_trans (by have hp':0<(p:ℝ):= hx; positivity) hi
   let d:ℝ≥0:= p/(i:ℝ≥0); have hu:0<(i:ℝ≥0):=by exact_mod_cast hg
   have hh:0<d:= div_pos hx hu
   have hw: (d:ℝ)<t := by
     unfold d
     rw [NNReal.coe_div,NNReal.coe_natCast]; exact (div_lt_iff₀ hg).2 (by linarith [(div_lt_iff₀ z).1 hi])
   let p':= addition S u x hp i (by exact_mod_cast hg); refine le_trans (le_of_eq ?_) (g ⟨b,e⟩ d hh hw _ p');
   rw [show (i:ℝ)=(↑(i:ℝ≥0):ℝ) from by simp,← pours _ _ _ hh]
   unfold d; rw [mul_div_cancel₀ _ hu.ne']
 have v:= surf 1 x zero_lt_one X (fun t h _ => he t h)
 rw [← cone_mean] at v; change (inner ℝ x (basis b))^2 ≤ _ at v; rw [innerB] at v; exact (sq_le_sq₀ (abs_nonneg _) (S.nonneg y t)).mp (by rw [sq_abs]; exact v)
end YM.Roy
