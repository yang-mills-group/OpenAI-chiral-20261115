import LusterS.Rogue
import YM.SU5.Regis.Trophy
/-! # Sparse defect treatment under outer-threshold tree purchase -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.flexible false
set_option quotPrecheck false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 300000
noncomputable section
namespace YM.Gleam.Luster
open Function Lattice MeasureTheory Finset RG Wilson Tree Filter Metric Exterior Precision Next.Rank.Spindle Pressure Work.F03 Next.SectorChange Next.SectorChange.Gaussian
open Fineness Matrix
open scoped Matrix BigOperators Classical ContDiff Topology MatrixOrder ENNReal Kronecker Matrix.Norms.Frobenius
variable {c n : Side}{r:Ratio c n}{T:Forest r}{G:Gauge}{p:BudgetPoint}{q:Clip}{v t η C S w δ β κ ξ Λ v' ν θ ω':ℝ}{U:Config G n}{A:Support c}{m:ℕ} {R:Rules G} {Z:PathData G}{b:Cell n}{H:Bed}{F:Finset T.Free}{J:ChartRatio G}
variable {X Y:fieldDir G n 1}{D:Finset (Cell n)}
variable (B:Z.Bounds q η C S) (P:Attached H Z)(L:Floor H q n δ w)(D':LocalRatio J)
namespace Risa
open Regis ProbabilityTheory

/-- charge even EXACT chord at τ, where qualification doesn't ask equality-Haar. -/
def weak (t:ℝ)(U:Config G n) := univ.filter fun b:Cell n=> t ≤ G.chord (faceValue U b)
@[simp] lemma weak_mem (b:Cell n) : b∈ weak t U ↔ t ≤ G.chord (faceValue U b):= by simp [weak]
lemma poll {n:Side}(t:ℝ)(c:Cell n):MeasurableSet {U:Config G n|c∈weak t U}:=by
 simp only [weak_mem]; exact (isClosed_le continuous_const (G.continuous_chord.comp (show Continuous (fun U=> faceValue (K:=G.El) U c) from continuous_travel ..))).measurableSet
lemma counts_weak (D:Finset (Cell n))(v:ℝ): (∑ b:Cell n, if b∈D then v else 0)=v*(D.card:ℝ):= by rw [← sum_filter,filter_mem_eq_inter,univ_inter,sum_const,nsmul_eq_mul,mul_comm]
private lemma weak_reserve {k c:ℝ}(hr:p.threshold≤t)(hk:k+c≤q.linear*p.threshold^2/2)(hc:c≤q.direct*p.threshold^2/2) :let θ:=p.threshold; let z:=G.chord (faceValue U b); (if b∈ misdemean θ U then k else 0)+(if b∈ weak θ U then c else 0)+(if b∈misdemean t U then q.linear*θ*t/2 else 0) ≤ Z.baseTerm q p U b:=by
 intro θ z; by_cases h:b∈ misdemean θ U
 · have ht: b∈weak θ U:= by have g:θ<z:= (mem_filter.mp h).2; exact weak_mem _|>.2 g.le
   have h0:= both_reserve (b:=b) (U:=U) (Z:=Z) (q:=q) hr
   change (if b∈ misdemean θ U then _ else _)+ _ ≤ _ at h0
   rw [if_pos h] at h0; rw [if_pos h,if_pos ht]; exact h0.trans' (add_le_add_left hk _) -- goal dependent; simpa wrong cond on RHS only.Goal 
 have he: b∉misdemean t U:= fun e=> h (mem_filter.mpr ⟨mem_univ _,hr.trans_lt (mem_filter.mp e).2⟩)
 have hv:z≤θ:= le_of_not_gt (fun t=> h (mem_filter.mpr ⟨mem_univ _,t⟩))
 rw [if_neg h,if_neg he,PathData.baseTerm,PathData.clipped,if_pos hv,zero_add,add_zero]; refine le_trans ?_ (le_add_of_nonneg_right (by split; positivity; exact le_rfl)); split
 next h=> have hi:z=θ:= hv.antisymm ((weak_mem _).mp h); change c≤ _*z^2/2; rwa [hi]
 next => have h:=q.quadratic_pos; positivity
include B
private lemma priceBase (D:ℕ→G.Color)(h:∀ i:ℕ, let k:= (Z.row b.2 i).2.length; ‖D i‖≤ v * Real.exp (η*k))(p:0 ≤ v) : let F:ℕ→G.Color:= fun i=> (Z.row b.2 i).1 • D i; Summable F ∧ ‖∑' i,F i‖ ≤ C*v:=by
 intro F; let Ψ:= (fun i=> |(Z.row b.2 i).1| *Real.exp (η*(Z.row b.2 i).2.length)); have ht:= B.rows b.2
 have he (i:ℕ): ‖F i‖ ≤ Ψ i*v:=by unfold F Ψ; rw [norm_smul,Real.norm_eq_abs,mul_right_comm]; exact (mul_le_mul_of_nonneg_left (h i) (abs_nonneg _))|>.trans_eq (by ring)
 have hf : Summable fun i=> Ψ i * v:= ht.2.1.mul_right _; have hx:Summable (fun i=> ‖F i‖):=hf.of_nonneg_of_le (fun _=>norm_nonneg _) he; exact ⟨hx.of_norm,(norm_tsum_le_tsum_norm hx).trans ((hx.tsum_le_tsum he hf).trans (by rw [tsum_mul_right]; exact mul_le_mul_of_nonneg_right ht.2.2 p))⟩
private lemma loose_bound (h:ProbeBox X v)(w:0≤v) : ‖ellLine Z b X‖ ≤ C*(4*v):=by
 apply (priceBase B (fun i=> faceCurl (slotFace (Z.row b.2 i).2 b.1) X) _ (by positivity:0 ≤ 4*v)).2; intro i k; have hr:=B.width; exact (all_probe h _).trans (le_mul_of_one_le_right (by positivity) (Real.one_le_exp (by positivity)))
omit B in
private lemma d_fines {x y : G.Color}{D d:ℝ}(p:‖x-y‖≤D)(h:‖y‖≤d) : ‖y‖^2 ≤ ‖x‖^2 + (2*D*d):=by
 rcases le_total ‖y‖ ‖x‖ with h1|h1
 · refine le_trans (pow_le_pow_left₀ (norm_nonneg y) h1 _) (le_add_of_nonneg_right ?_); have he:0 ≤ D:= le_trans (norm_nonneg _) p; have hp :0≤d:= (norm_nonneg _).trans h; positivity
 have he: 0≤D:=(norm_nonneg _).trans p; have hw: ‖y‖-‖x‖ ≤ D:= (norm_sub_norm_le y x).trans ((norm_sub_rev ..).trans_le p)
 have hz:=mul_le_mul_of_nonneg_left hw (show 0 ≤ ‖y‖+‖x‖ from by positivity)
 nlinarith only [hz,mul_le_mul_of_nonneg_right h1 he,mul_le_mul_of_nonneg_right h he]

lemma weak_line {c':ℝ} {k2:ℝ}(hk2:k2+c'≤q.linear*p.threshold^2/2)(hc2:c'≤q.direct*p.threshold^2/2) (hr:p.threshold≤v')(f:ProbeBox X (2*v))(g:ProbeBox (X+Y) (2*v))(h:TrustLogs (X+Y) U r A v)(w:abandon X r A m)(j:vacuumR X (weak p.threshold U) (hallBill m)) (l:EnoughMark q p m)(p':0 ≤ v)(t':v≤ R.c)(hv:0 ≤ C) : let D:=weak p.threshold U; flash Z q r D A m b X Y + ((if b∈ misdemean p.threshold U then k2 else 0)+(if b∈D then c' else 0)+(if b∈misdemean v' U then q.linear*p.threshold*v'/2 else 0)) ≤ Z.baseTerm q p U b + Δ₁ R q v m η C:=by
 intro Dm
 let t:=p.threshold; let k:=insideB r (broken r t U) m b; let d:= G.chord (faceValue U b); have d0:0 ≤ d:= G.chord_nonneg _; have h0:=p.threshold_pos; have hL:=q.quadratic_pos
 have hδ : 0 ≤ faceCutError R v:=by unfold faceCutError; have h:=G.colorScale_pos; have xv:=R.positive; positivity
 let F:= acry R v m η C; have he:0 ≤ acry R v m η C:= acry_zero hv p'
 have v0:0≤ C*(4*(2*v)):=by positivity
 unfold flash; split
 next g0 =>
    have hl (b':Cell n)(z:separation b.1 b'.1 ≤ Sequest m) : G.chord (faceValue U b') ≤ t:=by
       by_contra! ht
       have hh:=g0.2 b' (mem_filter.mpr ⟨mem_univ _,le_of_lt ht⟩); rw [separation_comm] at hh; omega
    have hf:b ∉Dm:=by intro he; have hi:=g0.2 b he; simp at hi
    have hs: b∉misdemean v' U:= by
       intro he; apply hf; exact mem_filter.mpr ⟨mem_univ _,hr.trans (mem_filter.mp he).2.le⟩
    have hd:d ≤ p.threshold:= hl b (by simp)
    have ht:PathData.kept q t b.1 U:= by
       intro f; by_cases h:separation b.1 f.1 ≤ Sequest m; · exact (hl f h).trans (le_mul_of_one_le_right h0.le (Real.one_le_exp (div_nonneg (by positivity) q.radius_pos.le)))
       exact (G.chord_le_two _).trans ((show 2≤ p.threshold * Real.exp ((Sequest m:ℕ)/ (q.relaxation:ℝ)) from l).trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp_of_le (div_le_div_of_nonneg_right (Nat.cast_le (α:=ℝ).mpr ((le_of_not_ge h))) q.radius_pos.le)) h0.le))
    rw [if_neg (show b∉misdemean p.threshold U from fun e=> hf (mem_filter.mpr ⟨mem_univ _,le_of_lt (mem_filter.mp e).2⟩)), if_neg hf,if_neg hs,zero_add,zero_add,add_zero,PathData.baseTerm,PathData.clipped,if_pos hd,if_pos (show PathData.kept q p.threshold b.1 U from ht),research]
    have hF:= d_fines (angleFaceSmall h p' t' b (g0.1.shift (y:=b.1) (by simp [Sequest]))).2 (all_probe g b)
    have hw:= d_fines (payLine B g h p' t' g0.1) (loose_bound B g (by positivity))
    let D:=G.curvature (faceValue U b); have hg:‖D‖^2 ≤ d^2:= pow_le_pow_left₀ (norm_nonneg _) (G.curvature_norm _) _
    unfold Δ₁; have hm:=sq_nonneg (C*(4*(2*v)*trail η m)); unfold D d at hg; linarith only [mul_le_mul_of_nonneg_left hF hL.le,mul_le_mul_of_nonneg_left hg hL.le,hw,hm]
 next hx =>
    rw [add_comm, research]; obtain ⟨u,e⟩:= glazed B f w j hx (by positivity)
    apply add_le_add (weak_reserve hr hk2 hc2)
    rw [u,norm_zero,zero_pow (by decide : (2:ℕ)≠0),mul_zero,zero_div,zero_add,Δ₁]; apply le_trans (div_le_div_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) e (2:ℕ)) (by norm_num)) (le_add_of_nonneg_left ?_)
    positivity

end Risa
end YM.Gleam.Luster
