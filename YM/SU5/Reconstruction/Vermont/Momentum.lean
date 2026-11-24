import YM.SU5.Reconstruction.Vermont.Recorder
/-!
# Simultaneous real-time prices, even spacelike near-zero, uniformly assessed
 at that one angle, for all stages along a subsequence.Measures detection.
-/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Lens
open Function Set Filter MeasureTheory Spectral Analysis OS.Semigroup ConePrice Sail BridgeClub ContinuousLinearMap Picket
open scoped BigOperators Topology NNReal InnerProductSpace ComplexOrder
-- scalar elementary budget. may apply to multiple roles.Plan.
structure Silent (f:ℕ→ℂ→ℂ):Prop where
 born : ∀ n,Continuous (f n)
 spent : ∀ n,AnalyticOnNhd ℂ (f n) inside
 paid : ∃ C:ℝ,0<C ∧ ∀ n:ℕ,∀ z:ℂ,‖f n z‖≤ C
namespace Silent
variable {f g:ℕ→ℂ→ℂ}(x:Silent f)(y:Silent g)
include x y
lemma mul : Silent (fun n z=> f n z*g n z):=by
 obtain ⟨A,p,v⟩:= x.paid; obtain ⟨a,b,c⟩:=y.paid; exact ⟨fun n=> (x.born n).mul (y.born n), fun n=> (x.spent n).mul (y.spent n),A*a,mul_pos p b, fun n z=> by rw [norm_mul]; exact mul_le_mul (v n z) (c n z) (norm_nonneg _) p.le⟩
lemma sub : Silent (fun n z=> f n z - g n z):=by
 obtain ⟨A,p,v⟩:= x.paid; obtain ⟨a,b,c⟩:=y.paid; exact ⟨fun n=> (x.born n).sub (y.born n), fun n=> (x.spent n).sub (y.spent n),A+a,add_pos p b, fun n z=> (norm_sub_le ..).trans (add_le_add (v n z) (c n z))⟩
omit y
lemma visible (a b:ℝ)(z:a<b){c:ℝ}(u:0<c)(w:∀ᶠ n in atTop,c≤‖f n 1‖): ∃ t∈ Set.Ioo a b,∃ ε>0,∃ᶠ n in atTop, ε≤‖f n (sideways t)‖:=by
 obtain ⟨C,p,v⟩:= x.paid
 obtain ⟨t,w,c0,h,f0⟩:= River.signal p.le f (fun n i _=>v n i) (fun i=>(x.spent i).differentiableOn) (x.born) (show -b < -a from neg_lt_neg z) p u w
 have h' := w.1; refine ⟨-t,⟨?_,?_⟩,c0,h,?_⟩; linarith [w.2]; linarith
 simpa [sideways] using f0
include y
lemma simultaneous (a b:ℝ)(z:a<b){d e:ℂ}(l:d≠0)(l':e≠0)(p:Tendsto (fun n=>f n 1) atTop (𝓝 d))(u:Tendsto (fun n=> g n 1) atTop (𝓝 e)) :
  ∃ t∈ Ioo a b,∃ ε>0,∃ᶠ n in atTop, ε≤ ‖f n (sideways t)‖ ∧ ε≤ ‖g n (sideways t)‖:=by
 have hp:0<‖d*e‖:=norm_pos_iff.mpr (mul_ne_zero l l'); let δ:= ‖d*e‖/2
 obtain ⟨t,k,c0,e0,Pq⟩:= (x.mul y).visible a b z (half_pos hp) (((p.mul u).norm).eventually (le_mem_nhds (half_lt_self hp)))
 obtain ⟨C,r,v⟩:= x.paid; obtain ⟨D,q,w⟩:= y.paid; let a:= max C D; have ha:0<a:= r.trans_le (le_max_left ..)
 refine ⟨t,k,c0/a,div_pos e0 ha,Pq.mono fun i h=>?_⟩; change c0≤ ‖f i _* g i _‖ at h; rw [norm_mul] at h; specialize v i (sideways t); specialize w i (sideways t)
 exact ⟨(div_le_iff₀ ha).mpr (h.trans (mul_le_mul_of_nonneg_left (w.trans (le_max_right ..)) (norm_nonneg _))), (div_le_iff₀ ha).mpr ((h.trans (mul_le_mul_of_nonneg_right (v.trans (le_max_left ..)) (norm_nonneg _))).trans_eq (mul_comm ..))⟩
end Silent
end YM.Lens
