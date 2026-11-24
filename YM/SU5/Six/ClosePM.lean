import YM.SU5.Six.ElemPM

/-!
# Pass to bounded Borel spectral multipliers

Approximate uniformly by elementary terms, keep track of operator products.
-/
set_option autoImplicit false
noncomputable section

namespace YM.Spectral.PVM
open MeasureTheory Filter Set
open scoped Topology InnerProductSpace ComplexConjugate

variable {H : Hilbert} {X : Type*} [MeasurableSpace X]
         {f g : X → ℂ} {T U : H.Op} {P : PVM H X}


private lemma approx_finset (P : PVM H X) (hf : Measurable f)
    (s : Finset ℂ) (ε : ℝ) :
    ∃ g U, P.Elementary g U ∧ ∀ x c, c ∈ s → dist (f x) c < ε → dist (f x) (g x) < ε := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨_,_, Elementary.zero_elem P, by simp⟩
  | insert c s _ ih =>
    obtain ⟨g,U,h,hg⟩ := ih
    let B := f ⁻¹' Metric.ball c ε
    have m : MeasurableSet B := hf Metric.isOpen_ball.measurableSet
    let I (B : Set X) := B.indicator fun _ => (1:ℂ)
    let v := c • I B + g*I Bᶜ
    refine ⟨v,_,(Elementary.scale c (.ind m)).plus (h.mul (.ind m.compl)),?_⟩
    intro x c' hc hc'
    by_cases hx : x ∈ B
    · have hvc : v x = c := by simp [v,I,hx]
      rwa [hvc]
    have hvg : v x = g x := by simp [v,I,hx]
    rw [hvg]
    refine hg _ c' ?_ hc'
    rcases Finset.mem_insert.mp hc with rfl | h <;> [exact (hx hc').elim; exact h]

/-- Sup-norm approximation of a BB cost by elementary terms. -/
lemma approx (P : PVM H X) (hf : BB f) {ε : ℝ} (hε : 0 < ε) :
    ∃ g U, P.Elementary g U ∧ ∀ x, dist (f x) (g x) < ε := by
  obtain ⟨C,hC⟩ := hf.bound
  obtain ⟨s,_,hs,hB⟩ := (isCompact_closedBall (0:ℂ) C).finite_cover_balls hε
  obtain ⟨g,U,h,hg⟩ := approx_finset P hf.me hs.toFinset ε
  refine ⟨g,U,h,fun x => ?_⟩
  obtain ⟨c,hcs,hc⟩ := mem_iUnion₂.mp
    (hB (show f x ∈ Metric.closedBall 0 C by simp [hC]))
  exact hg x c (hs.mem_toFinset.mpr hcs) hc

/-- Simultaneous approximation in uniform and operator norm. -/
def ApproxRep (P : PVM H X) (f : X → ℂ) (T : H.Op) : Prop :=
  ∃ g : ℕ → X → ℂ, ∃ U : ℕ → H.Op, TendstoUniformly g f atTop ∧ Tendsto U atTop (𝓝 T) ∧
    ∀ n, P.Elementary (g n) (U n)

lemma Elementary.cauchy {g : ℕ → X → ℂ} {U : ℕ → H.Op}
    (h : ∀ n, P.Elementary (g n) (U n))
    (huf : TendstoUniformly g f atTop) : CauchySeq U := by
  refine Metric.cauchySeq_iff.mpr fun ε hε => ?_
  obtain ⟨N,hN⟩ := eventually_atTop.1 (Metric.tendstoUniformly_iff.mp huf
    (ε/4) (by positivity))
  refine ⟨N, fun i hi j hj => ?_⟩
  rw [dist_eq_norm_sub]
  refine (((h i).diff (h j)).norm_le (show 0 ≤ ε/2 by positivity) (fun x => ?_)).trans_lt
    (half_lt_self hε)
  rw [Pi.sub_apply,←dist_eq_norm_sub]
  have d := dist_triangle_left (g i x) (g j x) (f x)
  linarith [hN i hi x,hN j hj x]

lemma approximable (P : PVM H X) (hf : BB f) : ∃ T, P.ApproxRep f T := by
  choose g U h hg using fun n : ℕ => approx P hf (show 0 < 1 / ((n:ℝ) + 1) by positivity)
  have huf : TendstoUniformly g f atTop := Metric.tendstoUniformly_iff.mpr fun ε hε =>
    (tendsto_one_div_add_atTop_nhds_zero_nat.eventually_lt_const hε).mono
      fun n he x => lt_trans (hg n x) he
  obtain ⟨T,hT⟩ := cauchySeq_tendsto_of_complete (Elementary.cauchy h huf)
  exact ⟨T,g,U,huf,hT,h⟩


lemma ApproxRep.represents (h : P.ApproxRep f T) (hf : BB f) : P.Represents f T := by
  obtain ⟨g,U,huf,hT,h⟩ := h
  refine ⟨admBB _ hf,fun x => ?_⟩
  let L := ContinuousLinearMap.apply ℂ H x
  have lim : Tendsto (fun i => inner ℂ x (U i x)) atTop (𝓝 (inner ℂ x (T x))) :=
    tendsto_const_nhds.inner (𝕜:=ℂ) ((L.continuous.tendsto T).comp hT)
  refine tendsto_nhds_unique lim (Metric.tendsto_nhds.mpr fun ε hε => ?_)
  let μ := P.diagonal x
  let C := μ.real univ + 1
  have hC : 0 < C := add_pos_of_nonneg_of_pos ENNReal.toReal_nonneg zero_lt_one
  filter_upwards [Metric.tendstoUniformly_iff.mp huf (ε/C) (by positivity)] with i hi
  rw [dist_comm,dist_eq_norm_sub,(h i).represents.on_diag,
    ←integral_sub (hf.integrable _) ((h i).represents.admissible.integrable x)]
  refine (norm_integral_le_of_norm_le_const
    (ae_of_all μ fun y => (dist_eq_norm_sub (f y) (g i y) ▸ hi y : ‖f y - g i y‖ < ε / C).le)).trans_lt ?_
  exact (mul_lt_mul_of_pos_left (lt_add_one _) (show 0 < ε/C by positivity)).trans_eq
    (div_mul_cancel₀ ε hC.ne')

lemma product_uniform {a b : ℕ → X → ℂ} (ha : TendstoUniformly a f atTop)
    (hb : TendstoUniformly b g atTop) (hf : BB f) (hg : BB g) :
    TendstoUniformly (a*b) (f*g) atTop := by
  obtain ⟨C,hC,H⟩ := hf.pos_bound
  obtain ⟨D,hD,G⟩ := hg.pos_bound
  refine Metric.tendstoUniformly_iff.mpr fun ε hε => ?_
  filter_upwards [Metric.tendstoUniformly_iff.mp ha _ (show 0 < (ε/2)/(D+1) by positivity),
    Metric.tendstoUniformly_iff.mp hb _ (show 0 < (ε/2)/C by positivity),
    Metric.tendstoUniformly_iff.mp hb 1 zero_lt_one] with i hi hj hm x
  change dist (f x * g x) (a i x * b i x) < ε
  rw [dist_eq_norm_sub, show f x * g x - a i x * b i x =
    (f x - a i x) * b i x + f x * (g x - b i x) by ring]
  have hy : ‖b i x‖ ≤ D + 1 := by
    rw [←dist_zero_right]
    refine (dist_triangle (b i x) (g x) 0).trans ?_
    rw [dist_comm,dist_zero_right,add_comm]
    linarith [hm x,G x]
  have h1 : ‖(f x - a i x) * b i x‖ < ε/2 := by
    rw [norm_mul,←dist_eq_norm_sub]
    exact (mul_le_mul_of_nonneg_left hy dist_nonneg).trans_lt
      ((lt_div_iff₀ (by positivity)).mp (hi x))
  have h2 : ‖f x * (g x - b i x)‖ < ε/2 := by
    rw [norm_mul,←dist_eq_norm_sub]
    exact (mul_le_mul_of_nonneg_right (H x) dist_nonneg).trans_lt ((lt_div_iff₀' hC).mp (hj x))
  exact (norm_add_le _ _).trans_lt ((add_lt_add h1 h2).trans_eq (add_halves _))

lemma ApproxRep.mul (h : P.ApproxRep f T) (k : P.ApproxRep g U) (hf : BB f) (hg : BB g) :
    P.ApproxRep (f*g) (T*U) := by
  obtain ⟨a,S,huf,hT,h⟩ := h
  obtain ⟨b,V,hug,hU,k⟩ := k
  exact ⟨a*b,S*V, product_uniform huf hug hf hg,hT.mul hU, fun i => (h i).mul (k i)⟩

/-- Existence for admissible costs. -/
lemma Admissible.exists_represents (hf : P.Admissible f) : ∃ T, P.Represents f T := by
  obtain ⟨f',b,hb⟩ := hf
  obtain ⟨T,hT⟩ := approximable P b
  exact ⟨T, (hT.represents b).congr hb.symm⟩

/-- Multiplicativity for admissible costs. -/
lemma Represents.mul (h : P.Represents f T) (k : P.Represents g U) :
    P.Represents (f*g) (T*U) := by
  obtain ⟨f',F,hf⟩ := h.admissible
  obtain ⟨g',G,hg⟩ := k.admissible
  obtain ⟨T',hT⟩ := approximable P F
  obtain ⟨U',hU⟩ := approximable P G
  rw [(h.congr hf).unique (hT.represents F),(k.congr hg).unique (hU.represents G)]
  exact ((hT.mul hU F G).represents (F.mul G)).congr (hf.mul hg).symm

end YM.Spectral.PVM
