import YM.CF.BProof.Bracket
import YM.CF.BProof.Borel

/-! Nearest projection of the equal-weight mean. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof
open Filter Metric MeasureTheory NormedSpace Function Set Finset
open scoped Matrix.Norms.Frobenius Topology BigOperators Classical
variable {I : Type*}[Fintype I][Nonempty I]
variable {E : Type*}[NormedAddCommGroup E][NormedSpace ℝ E]
def average (F:I→E): E:= (Fintype.card I:ℝ)⁻¹ • ∑ i, F i
lemma average_le (f:I→E)(b:ℝ)(h:∀ i, ‖f i‖≤b):‖average f‖ ≤ b:=by
 let n:ℝ:=Fintype.card I; have hn:0<n:=by unfold n; positivity
 rw [average,norm_smul,Real.norm_of_nonneg (by positivity)]; apply (inv_mul_le_iff₀ hn).mpr; refine le_trans (norm_sum_le ..) ((sum_le_sum fun i _=> h i).trans_eq ?_); simp [n]
lemma average_add (f g:I→E):average (fun i=> f i+g i)=average f+average g:=by rw [average,sum_add_distrib,smul_add]; rfl
lemma average_sub (f g:I→E):average (fun i=> f i-g i)=average f-average g:=by rw [average,sum_sub_distrib,smul_sub]; rfl
lemma average_const (x:E):average (fun _:I=>x)=x:=by rw [average,sum_const, card_univ, ← Nat.cast_smul_eq_nsmul ℝ,inv_smul_smul₀]; positivity
lemma average_dist (f g:I→E)(b:ℝ)(h:∀ i,‖f i-g i‖≤b):‖average f-average g‖ ≤ b:=by rw [← average_sub]; exact average_le _ _ h
omit [Nonempty I] in
@[fun_prop] lemma mean_c {X:Type*}[TopologicalSpace X](f:X→I→E)(h:∀ i,Continuous fun x=> f x i): Continuous fun x=> average (f x):= Continuous.const_smul (continuous_finsetSum univ fun i _=> h i) _
variable (G : Gauge)
-- use explicit local Borel instance to avoid type mismatch when mapping from kernels?
local instance : MeasurableSpace G.Mat := borel _
local instance : BorelSpace G.Mat := ⟨rfl⟩

lemma nearest_choice : ∃ f:G.Mat→ G.El,Measurable f∧∀ x,G.Nearest (f x) x := by
 have ht:IsClosed {x:G.Mat × G.El|G.Nearest x.2 x.1}:=by unfold Gauge.Nearest; rw [setOf_forall]; exact isClosed_iInter fun i=> isClosed_le (by fun_prop) (by fun_prop)
 exact closed_choice _ ht (fun x=>G.nearest_exists _)

def closest := (nearest_choice G).choose
lemma closest_m : Measurable (closest G):=(nearest_choice G).choose_spec.1
lemma closest_p (x:G.Mat): G.Nearest (closest G x) x := (nearest_choice G).choose_spec.2 x

lemma left_shift (F:I→G.El)(v:G.El) : average (fun i=> G.mat (v* F i))=G.mat v * average (G.mat ∘ F):= by simp only [average, G.mat_mul, Matrix.mul_smul, Function.comp_def, Finset.mul_sum]
lemma right_shift (F:I→G.El)(v:G.El) : average (fun i=> G.mat (F i*v))=average (G.mat ∘ F)*G.mat v:= by simp only [average, G.mat_mul, Matrix.smul_mul, Function.comp_def, Finset.sum_mul]

variable (K : Chart G)
omit [Nonempty I] in
lemma nearest_all_same (x y:G.El) : G.Nearest x (G.mat y) ↔ x=y := by
 constructor
 · intro h; apply G.mat_injective; symm; apply sub_eq_zero.mp; have he:= h y; exact norm_le_zero_iff.mp (by simpa using he)
 rintro rfl v; simp
lemma average_close (C : ℝ)(F:I→G.El)(e:G.El) (h:∀ i,cd G e (F i) ≤ C) : ‖average (G.mat ∘ F)-G.mat e‖ ≤ C*G.colorScale:=by
 nth_rw 1 [← average_const (I:=I) (G.mat e)] -- occurrences?
 exact average_dist _ _ _ (fun i=> (norm_le_scale ..).mp ((cd_symm G ..).trans_le (h i))) -- syntax tune

include K
lemma average_projection : ∃ C ε : ℝ,0<C ∧ 0<ε ∧ ∀ (F:I→G.El) (e v:G.El) (d:ℝ),
    (∀ i, cd G e (F i) ≤ d) → d≤ε → G.Nearest v (average (G.mat ∘ F)) →
      ‖average (G.mat ∘ F)-G.mat v‖ ≤ C*d^2:= by
 have hk:=zero_lt_one.trans_le K.C_one
 let ε:= min K.radius (K.size/K.C); have he:0<ε:=lt_min K.positive (div_pos K.admitted hk)
 refine ⟨2*K.C^3,ε,by positivity,he,fun F e v d h hd hv =>?_⟩
 let A(i:I):=e⁻¹*F i; let L(i):=logG G (A i)
 have hr(i): G.chord (A i) ≤ d:=h i
 let B:=average L
 have hh:d≤K.radius:=hd.trans (min_le_left ..); have hx:K.C*d≤K.size:=mul_comm K.C d ▸ (le_div_iff₀ hk).mp (hd.trans (min_le_right ..))
 have hy(i): ‖L i‖≤K.C*d:=(K.width (A i) ((hr i).trans hh)).trans (by gcongr; exact hr i)
 have hB:‖B‖≤K.C*d:= average_le L _ hy
 have hz(i): G.lieExp (L i)=A i:=(K.exposes _ ((hr i).trans hh)).2
 have hE:=K.linear B hB hx; let u:= G.colorMat B
 rw [← Gauge.mul_frob_eq (G.mat e⁻¹) _ (G.mat_star_mul _), _root_.mul_sub,← left_shift, ← G.mat_mul]; let w:=average (G.mat ∘ A); change ‖w-G.mat (e⁻¹*v)‖ ≤ _
 have hp: G.Nearest (e⁻¹*v) w:=by
    have h:= (G.nearest_left e⁻¹ v _).mpr hv; rw [← left_shift] at h; exact h
 apply le_trans (hp (G.lieExp B)); apply (norm_sub_le_norm_sub_add_norm_sub _ (1+u) _).trans
 have hj : 0≤d:=(cd_nonneg G e _).trans (h (Classical.arbitrary _)); have hu(i): ‖G.mat (A i)-(1+G.colorMat (L i))‖ ≤ K.C*(K.C*d)*(K.C*d):=by rw [sub_add_eq_sub_sub]; have h:=K.linear _ (hy i) hx; rw [hz] at h; exact h.trans (by gcongr; exact hy i)
 have hb : average (fun i=>1+G.colorMat (L i))=1+u:=by rw [average_add,average_const]; unfold u B average; rw [map_smul, map_sum]
 apply le_trans (add_le_add (b:=K.C*(K.C*d)*(K.C*d)) (d:=K.C*(K.C*d)*(K.C*d)) _ _) (le_of_eq (by ring))
 · rw [← hb]; exact average_dist _ _ _ hu
 rw [norm_sub_rev,sub_add_eq_sub_sub]; exact hE.trans (by gcongr)
end YM.CF.BProof
