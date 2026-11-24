import YM.Spectral.Projection
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Bounded Borel spectral multiplication

Standalone, at the project's `PVM`s. No spectral support or Hilbert separability hypotheses.
Instead of adding a `complexMeasure` API we will take pair measures and their integrals by
polarization (finite linear combinations of finite positive measures, exact formula on every
Borel set).
-/

set_option autoImplicit false
noncomputable section

namespace YM.Spectral.PVM
open MeasureTheory Filter Set Topology
open scoped BigOperators InnerProductSpace ComplexConjugate

variable {H : Hilbert} {X : Type*} [MeasurableSpace X]

/-- Domain convention for the multipliers. Complex, bounded on **all** of `X`. If
using with spectral support information, use bounded extensions first. -/
structure Cost (f:X → ℂ) : Prop where
  borel : Measurable f
  covered : ∃ C:ℝ, 0 ≤ C ∧ ∀ x, ‖f x‖ ≤ C

namespace Cost
variable {f g:X → ℂ}
lemma integrable (hf:Cost f) (μ:Measure X) [IsFiniteMeasure μ] : Integrable f μ := by
  obtain ⟨C,_,h⟩ := hf.covered
  exact (integrable_const C).mono' hf.borel.aestronglyMeasurable (ae_of_all _ h)
lemma const (c:ℂ) : Cost (fun _:X=>c) :=
  ⟨measurable_const,‖c‖,norm_nonneg _,fun _=>le_rfl⟩
lemma one : Cost (1:X→ℂ) := const _
lemma add (hf:Cost f) (hg:Cost g) : Cost (f+g) := by
  obtain ⟨a,u,v⟩ := hf.covered; obtain ⟨b,s,t⟩ := hg.covered
  exact ⟨hf.borel.add hg.borel,a+b,add_nonneg u s,
    fun x=>(norm_add_le ..).trans (add_le_add (v x) (t x))⟩
lemma mul (hf:Cost f) (hg:Cost g) : Cost (f*g) := by
  obtain ⟨a,u,v⟩ := hf.covered; obtain ⟨b,s,t⟩ := hg.covered
  exact ⟨hf.borel.mul hg.borel,a*b,mul_nonneg u s,fun x=>(norm_mul_le ..).trans
    (mul_le_mul (v x) (t x) (norm_nonneg _) u)⟩
lemma smul (c:ℂ) (hf:Cost f) : Cost (c • f) := (const c).mul hf
lemma neg (hf:Cost f) : Cost (-f) := neg_one_smul ℂ f ▸ hf.smul (-1)
lemma sub (hf:Cost f) (hg:Cost g) : Cost (f-g) := sub_eq_add_neg f g ▸ hf.add hg.neg
-- explicit star function
lemma starCost (hf:Cost f) : Cost (fun x=>star (f x)) :=
  { borel := continuous_star.measurable.comp hf.borel
    covered := by simpa using hf.covered }
lemma indic {A:Set X} (ha:MeasurableSet A) (hf:Cost f) : Cost (A.indicator f) := by
  obtain ⟨c,u,v⟩ := hf.covered
  refine ⟨hf.borel.indicator ha, c,u,fun x=>?_⟩
  by_cases hx:x∈A <;> simp [hx,v,u]
end Cost

variable (P:PVM H X)

lemma univ_norm (v:H) : (P.diagonal v).real Set.univ = ‖v‖^2 := by
  rw [P.same MeasurableSet.univ,P.all]; rfl

/-- Specifying property of the (function,operator) pair. -/
def Valued (f:X→ℂ) (A:H.Op) : Prop := ∀ v:H, inner ℂ v (A v) = ∫ x, f x ∂P.diagonal v

lemma polarized (a:H → ℂ)(u v:H)(B:H.Op)(h:∀ x, inner ℂ x (B x)=a x) :
    inner ℂ u (B v) = (a (u+v)-a (u-v) - Complex.I * (a (u+Complex.I • v)-a (u-Complex.I • v))) / 4 := by
  simp only [← h,map_add,map_sub,map_smul,inner_add_right,inner_add_left,
    inner_sub_left,inner_sub_right,inner_smul_left,inner_smul_right,Complex.conj_I]
  linear_combination (norm:=ring) inner ℂ u (B v) / 2 * Complex.I_sq - inner ℂ v (B u) / 2 * Complex.I_sq

namespace Valued
variable {P} {f g:X→ℂ} {A B:H.Op}
lemma unique (a: P.Valued f A) (b:P.Valued f B) : A=B := by
  apply ContinuousLinearMap.ext
  intro v; apply ext_inner_left ℂ
  intro u
  let t v:=∫ x, f x ∂P.diagonal v
  rw [polarized t _ _ _ a, polarized t _ _ _ b]
lemma add (hf:Cost f)(hg:Cost g)(a:P.Valued f A)(b:P.Valued g B) : P.Valued (f+g) (A+B) := by
  intro v; simp only [Pi.add_apply,add_apply]
  rw [inner_add_right,a,b,integral_add (hf.integrable _) (hg.integrable _)]
lemma smul (c:ℂ)(a:P.Valued f A) : P.Valued (c • f) (c • A) := by
  intro v; simp [Pi.smul_apply,inner_smul_right,a v,integral_const_mul]
lemma starVal (a:P.Valued f A) : P.Valued (fun x=>star (f x)) A.adjoint := by
  intro v
  rw [ContinuousLinearMap.adjoint_inner_right, ← inner_conj_symm, a]
  simp only [Complex.star_def,integral_conj]
lemma characteristic {s:Set X}(hs:MeasurableSet s) : P.Valued (s.indicator 1) (P.region s) := by
  intro v
  rw [← P.at_pair hs, integral_indicator hs]
  change (↑((P.diagonal v).real s):ℂ) = ∫ _x in s, (1:ℂ) ∂P.diagonal v
  simp
end Valued

/-- Finite combinations of measurable indicators, evaluated simultaneously. -/
private inductive Element : (X→ℂ) → H.Op → Prop
| unit {s:Set X} : MeasurableSet s → Element (s.indicator 1) (P.region s)
| times {f:X→ℂ} {A:H.Op} (c:ℂ) : Element f A → Element (c • f) (c • A)
| plus {f g:X→ℂ} {A B:H.Op} : Element f A → Element g B → Element (f+g) (A+B)

namespace Element
variable {P} {f g:X→ℂ} {A B:H.Op}
private lemma cost (h:P.Element f A) : Cost f := by
  induction h with
  | unit hs => exact Cost.indic hs Cost.one
  | times c _ hi => exact hi.smul c
  | plus _ _ hi hj => exact hi.add hj

private lemma valued (h:P.Element f A) : P.Valued f A := by
  induction h with
  | unit hs => exact Valued.characteristic hs
  | times c _ hi => exact hi.smul c
  | plus hx hy hi hj => exact hi.add (cost hx) (cost hy) hj

private lemma minus (ha:P.Element f A)(hb:P.Element g B) : P.Element (f-g) (A-B) := by
  simpa only [neg_one_smul,sub_eq_add_neg] using plus ha (times (-1) hb)
private lemma conjElm (h:P.Element f A) : P.Element (fun x=>star (f x)) A.adjoint := by
  induction h with
  | @unit s hs =>
    rw [P.real hs, show (fun x=>star (s.indicator 1 x):X→ℂ)=s.indicator 1 by
      funext x; by_cases hx:x∈s<;>simp [hx]]
    exact unit hs
  | @times f A c _ hi =>
    rw [show (fun x=>star ((c • f) x)) = (conj c) • (fun x=>star (f x):X→ℂ) by
      funext x; simp]
    rw [map_smulₛₗ]; exact times _ hi
  | @plus f g A B _ _ hi hj =>
    rw [show (fun x=>star ((f+g) x)) = (fun x=>star (f x):X→ℂ)+(fun x=>star (g x):X→ℂ) by
      ext; simp]
    rw [map_add]; exact plus hi hj

private lemma unit_mul {s:Set X}(hs:MeasurableSet s)(hb:P.Element g B) :
    P.Element (s.indicator 1*g) ((P.region s).comp B) := by
  induction hb with
  | @unit t ht =>
    rw [P.joins hs ht, show (s.indicator 1*t.indicator 1:X→ℂ)=(s∩t).indicator 1 by
      funext x; by_cases h:x∈s <;> by_cases u:x∈t <;> simp [*,Set.indicator]]
    exact unit (hs.inter ht)
  | times c _ ih => rw [ContinuousLinearMap.comp_smul, mul_smul_comm]; exact times c ih
  | plus _ _ ih ik => rw [ContinuousLinearMap.comp_add,mul_add]; exact plus ih ik
private lemma mul (ha:P.Element f A)(hb:P.Element g B) : P.Element (f*g) (A.comp B) := by
  induction ha with
  | unit hs => exact unit_mul hs hb
  | times c _ ih => rw [ContinuousLinearMap.smul_comp,smul_mul_assoc]; exact times c ih
  | plus _ _ ih ik => rw [ContinuousLinearMap.add_comp,add_mul]; exact plus ih ik
end Element

-- Norm estimate whenever the product has already been evaluated (e.g. for simple functions)
lemma square_bound {f:X→ℂ} {A:H.Op} (hf:Cost f)
    (h:P.Valued ((fun x=>star (f x))*f) ((A.adjoint).comp A))
    {c:ℝ}(hc:0≤c) (b:∀x, ‖f x‖ ≤ c) : ‖A‖ ≤ c := by
  refine A.opNorm_le_bound hc fun v=>?_ 
  apply le_of_sq_le_sq _ (by positivity)
  let ff := (fun x=>star (f x))*f
  have he : ‖A v‖^2 = ‖∫ x, ff x ∂P.diagonal v‖ := by
    rw [← show _ = _ from h v,ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.adjoint_inner_right,inner_self_eq_norm_sq_to_K]
    simp
  rw [he,mul_pow]
  have hb (x:X) : ‖ff x‖ ≤ c^2 := by
    simpa only [ff,Pi.mul_apply,norm_mul,norm_star,pow_two] using
      pow_le_pow_left₀ (norm_nonneg _) (b x) 2
  refine (norm_integral_le_integral_norm _).trans ((integral_mono
    (((hf.starCost.mul hf).integrable _).norm) (integrable_const _) hb).trans_eq ?_)
  rw [integral_const,univ_norm,smul_eq_mul,mul_comm]

private lemma Element.bound {f:X→ℂ} {A:H.Op} {c:ℝ} (a:P.Element f A)
    (hc:0≤c)(b:∀x, ‖f x‖ ≤ c) : ‖A‖ ≤ c := P.square_bound a.cost (a.conjElm.mul a).valued hc b

private lemma elem_on_cover {f:X→ℂ} (h:Cost f) (s:Finset ℂ) (e:ℝ) :
    ∃ g A, P.Element g A ∧ ∀ x, (∃ c∈s, dist (f x) c < e) → dist (f x) (g x) < e := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨_,_,Element.unit MeasurableSet.univ,fun _ h=> by simp at h⟩
  | @insert c s _ ih =>
    obtain ⟨g,A,u,m⟩ := ih
    let t := f ⁻¹' Metric.ball c e
    have ht : MeasurableSet t := Metric.isOpen_ball.measurableSet.preimage h.borel
    refine ⟨_,_,(Element.times c (Element.unit ht)).plus
      ((Element.unit ht.compl).mul u), ?_⟩
    rintro x ⟨d,hd,r⟩
    by_cases hx:x∈t
    · simp [hx,show dist (f x) c < e from hx]
    have hds : d∈s := (Finset.mem_insert.mp hd).resolve_left (fun h=>hx (show dist (f x) c < e by
      rw [← h]; exact r))
    simpa [hx] using m x ⟨d,hds,r⟩

private lemma elem_close {f:X→ℂ} (h:Cost f) {e:ℝ}(he:0<e) :
    ∃ g A, P.Element g A ∧ ∀ x, ‖g x-f x‖ ≤ e := by
  obtain ⟨k,p,q⟩ := h.covered
  obtain ⟨s,_,hs,H⟩ := (isCompact_closedBall (0:ℂ) k).finite_cover_balls he
  obtain ⟨g,A,hg,t⟩ := P.elem_on_cover h hs.toFinset e
  refine ⟨_,_,hg,fun x=>?_⟩
  rw [norm_sub_rev,←dist_eq_norm]
  apply le_of_lt (t x _)
  have hh := H (show f x ∈ Metric.closedBall 0 k by simpa using q x)
  simp only [Set.mem_iUnion,Metric.mem_ball] at hh
  obtain ⟨c,hc,hcx⟩ := hh
  exact ⟨c,hs.mem_toFinset.mpr hc,hcx⟩

private lemma valued_limit {f:X→ℂ} {A:H.Op} (hf:Cost f)
    {g:ℕ→X→ℂ} {L:ℕ→H.Op} {e:ℕ→ℝ}
    (hs:∀i,P.Element (g i) (L i)) (ht:Tendsto L atTop (𝓝 A))
    (hr:Tendsto e atTop (𝓝 0)) (u:∀i x, ‖g i x - f x‖ ≤ e i) : P.Valued f A := by
  intro v
  have hu : Tendsto (fun i=>inner ℂ v (L i v)) atTop (𝓝 (inner ℂ v (A v))) :=
    tendsto_const_nhds.inner ((ContinuousLinearMap.apply ℂ H.space v).continuous.continuousAt.tendsto.comp ht)
  refine tendsto_nhds_unique (hu.congr fun i=>(hs i).valued v) ?_
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  let μ:=P.diagonal v
  have hp : Tendsto (fun i=>μ.real univ * e i) atTop (𝓝 0) := by
    simpa only [mul_zero] using hr.const_mul (μ.real univ)
  refine squeeze_zero (fun _=>norm_nonneg _) (fun i=>?_) hp
  rw [← integral_sub ((hs i).cost.integrable μ) (hf.integrable μ)]
  exact (norm_integral_le_integral_norm _).trans ((integral_mono
    (((hs i).cost.sub hf).integrable μ).norm (integrable_const _) (u i)).trans_eq (integral_const _))

private lemma elem_approx {f:X→ℂ} (hf:Cost f) :
    ∃ (A:H.Op) (g:ℕ→X→ℂ) (L:ℕ→H.Op) (e:ℕ→ℝ),
      (∀i,P.Element (g i) (L i)) ∧ Tendsto L atTop (𝓝 A) ∧
      Tendsto e atTop (𝓝 0) ∧ (∀i,0<e i) ∧ (∀i x, ‖g i x - f x‖ ≤ e i) := by
  let e (i:ℕ) := 1/(↑i+1:ℝ)
  have he : ∀i, 0<e i := fun i=>by unfold e; positivity
  have h0 : Tendsto e atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  choose g L t u using fun i=>P.elem_close hf (he i)
  have hp : CauchySeq L := by
    apply Metric.cauchySeq_iff.mpr
    intro ε h
    obtain ⟨N,n⟩ := eventually_atTop.mp (h0.eventually (gt_mem_nhds (half_pos h)))
    refine ⟨N,fun a ha b hb=>?_⟩
    rw [dist_eq_norm]
    refine lt_of_le_of_lt (((t a).minus (t b)).bound P
      (add_pos (he a) (he b)).le (fun x=>?_)) (by grw [n a ha,n b hb,add_halves])
    exact (norm_sub_le_norm_sub_add_norm_sub (g a x) (f x) (g b x)).trans (add_le_add
      (u a x) ((norm_sub_rev ..).le.trans (u b x)))
  obtain ⟨A,h⟩ := cauchySeq_tendsto_of_complete hp
  exact ⟨A,g,L,e,t,h,h0,he,u⟩

lemma exists_valued {f:X→ℂ} (hf:Cost f) : ∃ A:H.Op, P.Valued f A := by
  obtain ⟨A,g,L,e,u,h,z,_,k⟩ := P.elem_approx hf
  exact ⟨A,P.valued_limit hf u h z k⟩

namespace Valued
variable {P} {f g:X→ℂ} {A B:H.Op}
private lemma inherited_approx (hf:Cost f) (a:P.Valued f A) :
    ∃ (g:ℕ→X→ℂ) (L:ℕ→H.Op) (e:ℕ→ℝ),
      (∀i,P.Element (g i) (L i)) ∧ Tendsto L atTop (𝓝 A) ∧
      Tendsto e atTop (𝓝 0) ∧ (∀i,0<e i) ∧ (∀i x, ‖g i x - f x‖ ≤ e i) := by
  obtain ⟨C,k,L,e,t,u,v,r,h⟩ := P.elem_approx hf
  have hc:= a.unique (P.valued_limit hf t u v h)
  subst A
  exact ⟨_,_,_,t,u,v,r,h⟩

lemma mul (hf:Cost f)(hg:Cost g) (a:P.Valued f A) (b:P.Valued g B) : P.Valued (f*g) (A.comp B) := by
  obtain ⟨v,L,e,t,u,r,s,h⟩ := inherited_approx hf a
  obtain ⟨w,K,d,z,y,q,p,k⟩ := inherited_approx hg b
  obtain ⟨x,_,hx⟩ := hf.covered
  obtain ⟨c,_,hc⟩ := hg.covered
  have hr : Tendsto (fun i=> x * d i + e i * c + e i * d i) atTop (𝓝 0) := by
    simpa using ((q.const_mul x).add (r.mul_const c)).add (r.mul q)
  refine P.valued_limit (hf.mul hg) (fun i=>(t i).mul (z i)) (u.mul y) hr (fun i m=>?_)
  let V:=v i m - f m
  let W:=w i m - g m
  rw [show (v i * w i) m - (f*g) m = f m * W + V * g m + V * W by
        simp only [Pi.mul_apply,V,W]; ring]
  grw [norm_add_le,norm_add_le,norm_mul,norm_mul,norm_mul]
  exact add_le_add (add_le_add
    (mul_le_mul (hx m) (k i m) (norm_nonneg _) ((norm_nonneg _).trans (hx m)))
    (mul_le_mul (h i m) (hc m) (norm_nonneg _) (s i).le))
    (mul_le_mul (h i m) (k i m) (norm_nonneg _) (s i).le)

lemma op_le (hf:Cost f) (a:P.Valued f A) {c:ℝ}(hc:0≤c) (b:∀x, ‖f x‖ ≤ c) : ‖A‖ ≤ c :=
  P.square_bound hf (a.starVal.mul hf.starCost hf a) hc b
end Valued

/-- Multiplier at this PVM. Only use on `Cost`. -/
def price (f:X→ℂ) : H.Op := by
  classical
  exact if h: Cost f then (P.exists_valued h).choose else 0

lemma price_spec {f:X→ℂ} (h:Cost f) : P.Valued f (P.price f) := by
  unfold price
  rw [dif_pos h]; exact (P.exists_valued h).choose_spec

variable {f g:X→ℂ}

lemma price_add (hf:Cost f)(hg:Cost g) : P.price (f+g) = P.price f + P.price g :=
  (P.price_spec (hf.add hg)).unique ((P.price_spec hf).add hf hg (P.price_spec hg))
lemma price_smul (c:ℂ)(hf:Cost f) : P.price (c•f) = c • P.price f :=
  (P.price_spec (hf.smul c)).unique ((P.price_spec hf).smul c)
lemma price_neg (hf:Cost f) : P.price (-f) = -P.price f := by
  simpa only [neg_one_smul] using P.price_smul (-1) hf
lemma price_sub (hf:Cost f)(hg:Cost g) : P.price (f-g) = P.price f - P.price g := by
  rw [sub_eq_add_neg,P.price_add hf hg.neg,P.price_neg hg,sub_eq_add_neg]
lemma price_conj (hf:Cost f) : P.price (fun x=>star (f x)) = (P.price f).adjoint :=
  (P.price_spec hf.starCost).unique (P.price_spec hf).starVal
lemma price_mul (hf:Cost f)(hg:Cost g) : P.price (f*g) = (P.price f).comp (P.price g) :=
  (P.price_spec (hf.mul hg)).unique ((P.price_spec hf).mul hf hg (P.price_spec hg))
lemma price_commutes (hf:Cost f)(hg:Cost g) :
    (P.price f).comp (P.price g) = (P.price g).comp (P.price f) := by
  rw [←P.price_mul hf hg, mul_comm,P.price_mul hg hf]
lemma price_indicator {s:Set X}(hs:MeasurableSet s) : P.price (s.indicator 1) = P.region s :=
  (P.price_spec (Cost.indic hs Cost.one)).unique (Valued.characteristic hs)
lemma price_one : P.price 1 = ContinuousLinearMap.id ℂ _ := by
  simpa [P.all] using P.price_indicator MeasurableSet.univ
lemma price_const (c:ℂ) : P.price (fun _=> c) = c • ContinuousLinearMap.id ℂ _ := by
  rw [show (fun _=>c:X→ℂ)= c • (1:X→ℂ) from funext fun _=>(mul_one c).symm,
    P.price_smul _ Cost.one,P.price_one]
lemma price_restrict (hf:Cost f) {s:Set X}(hs:MeasurableSet s) :
    P.price (s.indicator f) = (P.region s).comp (P.price f) := by
  rw [←P.price_indicator hs, ←P.price_mul (Cost.indic hs Cost.one) hf]
  congr 1; funext x; by_cases h:x∈s<;>simp [h]
lemma price_on_restricted (hf:Cost f) {s:Set X}(hs:MeasurableSet s) :
    (P.price f).comp (P.region s) = P.price (s.indicator f) := by
  rw [P.price_restrict hf hs, ←P.price_indicator hs, P.price_commutes hf (Cost.indic hs Cost.one)]
lemma price_congr (hf:Cost f)(hg:Cost g)(h:∀ v:H, f=ᵐ[P.diagonal v] g) : P.price f = P.price g :=
  (P.price_spec hf).unique fun v=> (P.price_spec hg v).trans (integral_congr_ae (h v)).symm

/-- Squared norm identity. -/
lemma price_paid (hf:Cost f) (v:H) : ‖P.price f v‖^2 = ∫ x, ‖f x‖^2 ∂P.diagonal v := by
  have ht:=P.price_spec (hf.starCost.mul hf) v
  rw [P.price_mul hf.starCost hf,P.price_conj hf, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.adjoint_inner_right,inner_self_eq_norm_sq_to_K] at ht
  apply Complex.ofReal_injective
  rw [Complex.ofReal_pow]
  refine ht.trans ?_
  rw [← integral_complex_ofReal]
  simp_rw [Pi.mul_apply,Complex.star_def,mul_comm ((starRingEnd ℂ) _),Complex.mul_conj,
    Complex.normSq_eq_norm_sq]

/-!
Vector-pair measure: linear combination (4-price polarization formula) of the
four positive diagonal measures. Thus it is countably additive; for complex
integrals against these finite measures we use the same formula.
-/

def cross (v w:H)(s:Set X) : ℂ :=
  let a (u:H):ℂ:= (P.diagonal u).real s
  (a (v+w)-a (v-w) - Complex.I * (a (v+Complex.I • w)-a (v-Complex.I • w))) / 4

def crossIntegral (v w:H)(f:X→ℂ) : ℂ :=
  let a (u:H):ℂ:= ∫ x, f x ∂P.diagonal u
  (a (v+w)-a (v-w) - Complex.I * (a (v+Complex.I • w)-a (v-Complex.I • w))) / 4

lemma cross_spec (v w:H){s:Set X}(hs:MeasurableSet s) :
    P.cross v w s = inner ℂ v (P.region s w) :=
  (polarized _ _ _ _ (fun v=>(P.at_pair hs v).symm)).symm
lemma cross_restrict (v w:H){s:Set X}(hs:MeasurableSet s) :
    P.cross v w s = inner ℂ (P.region s v) (P.region s w) := by
  nth_rw 1 [← P.real hs]
  rw [cross_spec _ _ _ hs,ContinuousLinearMap.adjoint_inner_left,P.idempotent hs]
lemma crossIntegral_valued (v w:H){A:H.Op}(a:P.Valued f A) :
    P.crossIntegral v w f = inner ℂ v (A w) := (polarized _ _ _ _ a).symm
lemma crossIntegral_spec (v w:H)(hf:Cost f) :
    P.crossIntegral v w f = inner ℂ v (P.price f w) :=
  P.crossIntegral_valued v w (P.price_spec hf)
lemma crossIntegral_diag (v:H)(hf:Cost f) :
    P.crossIntegral v v f = ∫ x, f x ∂P.diagonal v :=
  (P.crossIntegral_spec v v hf).trans (P.price_spec hf v)
lemma crossIntegral_restrict (v w:H)(hf:Cost f){s:Set X}(hs:MeasurableSet s) :
    P.crossIntegral v w (s.indicator f) = P.crossIntegral (P.region s v) (P.region s w) f := by
  rw [P.crossIntegral_spec v w (Cost.indic hs hf),P.crossIntegral_spec _ _ hf]
  let A := P.region s; let B := P.price f; let C := P.price (s.indicator f)
  have hCB : C w = B (A w) := DFunLike.congr_fun (P.price_on_restricted hf hs).symm _
  have hCA : C w = A (C w) := by
    change P.price (s.indicator f) w = _
    unfold C
    rw [P.price_restrict hf hs,ContinuousLinearMap.comp_apply]; exact (P.idempotent hs _).symm
  have hA : A.adjoint=A := P.real hs
  calc inner ℂ v (C w)
       _ = inner ℂ (A.adjoint v) (C w) := by rw [ContinuousLinearMap.adjoint_inner_left,←hCA]
       _ = inner ℂ (A v) (B (A w)) := by rw [hA,hCB]
lemma crossIntegral_congr (v w:H)(h:∀ u:H, f=ᵐ[P.diagonal u] g) :
    P.crossIntegral v w f = P.crossIntegral v w g := by
  have hu (u:H) := integral_congr_ae (h u)
  simp only [crossIntegral,← hu]

end YM.Spectral.PVM
