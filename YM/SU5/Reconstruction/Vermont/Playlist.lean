import YM.SU5.Reconstruction.Seams.Hole
import YM.Heat.Duration
/-!
# Wick scripts & ports. Script just an estimate, uniform in order if checked.
-/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Lens
open Function Set Filter MeasureTheory Spectral Analysis OS.Semigroup ConePrice Sail
open scoped BigOperators Topology NNReal InnerProductSpace ComplexOrder
variable {H:Hilbert}{a:Axis}(S:OS.Semigroup H a)(M:Set H.Op)
inductive Script : H.Op → ℝ≥0→ ℝ≥0→ Prop
| weather (d:ℝ≥0) : Script (S.E d) d 1
| now (A:H.Op)(t:ℝ≥0)(p:A∈ M)(e:‖A‖≤(t:ℝ)): Script A 0 t
| link {A B:H.Op}{d e c u} : Script A d c→ Script B e u→ Script (A*B) (d+e) (c*u)
| plus {A B:H.Op}{d c u} : Script A d c→ Script B d u→Script (A+B) d (c+u)
| scale {A:H.Op} {d c}: Script A d c→ (t:ℂ)→ Script (t • A) d (‖t‖₊*c)
| charge {A:H.Op} {d c u} : Script A d c→ c ≤ u→ Script A d u
variable {S M}
lemma Script.pays {A:H.Op}{d c:ℝ≥0}(p:Script S M A d c) : ‖A‖≤(c:ℝ):=by
 induction p with
 | weather d => exact S.shrinks d
 | now _ _ _ e => exact e
 | link _ _ ih h =>exact (norm_mul_le ..).trans (mul_le_mul ih h (norm_nonneg _) (le_trans (norm_nonneg _) ih)) -- check nnreal
 | plus _ _ ih h=> exact (norm_add_le ..).trans (add_le_add ih h)
 | scale _ t ih=> rw [norm_smul]; exact mul_le_mul_of_nonneg_left ih (norm_nonneg _)
 | charge _ h ih=> exact ih.trans h
-- Use CLOSED on horizontals (strict when making-real continuation). Easier concatenation.
variable (S) (L:H.Op)(r:ℝ)
def bore (r d:ℝ) :Set ℂ:={x|x.re∈ Set.Icc 0 d∧ |x.im| ≤ r}
lemma bore_c (r d:ℝ) : IsClosed (bore r d):=(isClosed_Icc.preimage Complex.continuous_re).inter (isClosed_le Complex.continuous_im.abs continuous_const)
lemma bore_v (r d:ℝ): Sail.veil 0 d r ⊆ bore r d:=fun _ p=> ⟨⟨p.1.le,p.2.1.le⟩,show |(_ : ℂ).im|≤ r from (show |(_ : ℂ).im|< _ from p.2.2).le⟩
local notation "Δ" z:max=> LorTime S (-(z:ℂ).im) L
structure Port (X:ℂ→H.Op)(B:H.Op)(d c:ℝ≥0) : Prop where
  order : ‖B‖ ≤ (c:ℝ)
  guard (p q:H): ContinuousOn (fun z=>inner ℂ p (X z q)) (bore r d)
  toll (z:ℂ) (h:z∈ bore r d): ‖X z‖ ≤ (c:ℝ) * ‖L‖
  analytic (p q:H): AnalyticOnNhd ℂ (fun z=> inner ℂ p (X z q)) (veil 0 d r)
  left (z:ℂ)(h:z.re=0)(e:|z.im|≤r): X z= Δ z*B
  right (z:ℂ)(h:z.re=(d:ℝ))(e:|z.im|≤r): X z=B* Δ z
lemma edge_price (t:ℝ):‖S.edge t‖≤1:= ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun x=> by rw [S.life,one_mul])
lemma lorP (t:ℝ): ‖LorTime S t L‖≤‖L‖:=by
 change ‖S.edge t*(L*S.edge (-t))‖≤‖L‖
 apply (norm_mul_le ..).trans; apply le_trans (mul_le_of_le_one_left (norm_nonneg _) (edge_price ..)) _
 exact (norm_mul_le ..).trans (mul_le_of_le_one_right (norm_nonneg _) (edge_price ..))
lemma instant {A:H.Op}(t:ℝ≥0)(e:‖A‖≤(t:ℝ))(x:∀ s:ℝ,|s|≤r→ Commute A (LorTime S s L)) : Port S L r (fun z=> A * Δ z) A 0 t:=by
 refine ⟨e,?_,?_,?_,fun z _ v=> x (-z.im) (by simpa using v),fun z _ _=> rfl⟩
 · intro p q; apply Continuous.continuousOn; apply (continuous_const.inner (A.continuous.comp (S.cont_edge _ _ ?_ Complex.continuous_im.neg)))
   exact (L.continuous.comp ((S.cont q).comp Complex.continuous_im.neg.neg)) -- argument order
 · exact fun z _=> (norm_mul_le ..).trans (mul_le_mul e (lorP ..) (norm_nonneg _) (by positivity))
 intro p q z hz; exact False.elim ((not_lt_of_ge hz.1.le) hz.2.1) -- tune

def storm (d:ℝ≥0)(z:ℂ):= phase S z * L * phase S (((d:ℝ):ℂ)-z)
lemma phase_price (z:ℂ): ‖phase S z‖≤1:= (ContinuousLinearMap.opNorm_comp_le _ _).trans ((mul_le_one₀ (edge_price ..) (norm_nonneg _) (S.shrinks _))) -- check
lemma storm_port (d:ℝ≥0): Port S L r (storm S L d) (S.E d) d 1:=by
 let D₀:ℂ:= (d:ℝ); refine ⟨S.shrinks _,?_,(fun z h=> ?_),?_,?_,?_⟩
 · intro p q; apply Continuous.continuousOn; exact continuous_const.inner (phase_cont S _ _ (L.continuous.comp (phase_cont S _ _ continuous_const ((continuous_const (y:=D₀)).sub continuous_id))) continuous_id) -- defeq
 · unfold storm; apply le_trans (norm_mul_le ..) ((mul_le_of_le_one_right (norm_nonneg _) (phase_price ..)).trans ((norm_mul_le ..).trans (mul_le_mul_of_nonneg_right (phase_price ..) (norm_nonneg _)))) -- tune mark
 · intro p q; apply DifferentiableOn.analyticOnNhd _ (veil_open 0 (d:ℝ) r); intro z e; apply DifferentiableAt.differentiableWithinAt; apply ((innerSL ℂ p).differentiableAt).comp;
   refine (phase_ana S z (show z∈ inside from e.1)).differentiableAt.clm_apply ?_
   apply L.differentiableAt.comp _
   refine ((phase_ana S (D₀-z) ?_).differentiableAt.comp z ((differentiableAt_const D₀).sub differentiableAt_id)).clm_apply (differentiableAt_const _)
   change 0<(D₀-z).re; unfold D₀; simpa using sub_pos.mpr e.2.1
 · intro z h v; rw [storm,phase,phase,Complex.sub_re,h]; simp only [Real.toNNReal_zero,S.eZero,Complex.ofReal_re,sub_zero,Real.toNNReal_coe,Complex.sub_im,Complex.ofReal_im,zero_sub]
   unfold LorTime; simp only [ContinuousLinearMap.comp_id]; simp only [mul_assoc]; rfl -- composition defeq
 intro z h v; rw [storm,phase,phase,Complex.sub_re,h]; simp only [Real.toNNReal_coe,Complex.ofReal_re,sub_self,Real.toNNReal_zero,S.eZero,Complex.sub_im,Complex.ofReal_im,zero_sub]
 rw [← S.eitherE]; unfold LorTime; ext x; rfl -- comp-id
end YM.Lens
