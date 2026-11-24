import YM.CF.Fock.Glacier
/-!
Auxiliary estimate in the RP and vacuum problems. Divide by EXACT gauge-field
DEPENDENT flight. At fixed gauge field we can take unbounded heat heights in
operator norm, even with growing volumes in this estimate. This does *not*
apply after gauge average because of the factor divided out. The difference
between adding one scalar vacuum subtraction in both numerator and denominator
and dividing by `flight H t` is important. We will also NOT take the first
Fock generator to be the overlap obtained by this limit applied to the
reader vacuum; that can hit a zero of the fiber determinant.

Operator norm means the L2-operator norm of the FC matrix. This estimate costs
no ratio of dimensions or density of fermion sea per volume. cf d8's
construction of the unpaired/paired estimates in `Glacier`; we need this one in
operator norm before applying to the FiniteGaugeData Sea.
-/

set_option autoImplicit false
noncomputable section
namespace YM.CF.Fixed
open Function Fock NormedSpace MatrixOrder Filter Finset
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace Topology BigOperators
attribute [local instance] opCStarAlgebra
variable {n:Type*} [LinearOrder n] [Fintype n] [Nonempty n] {A:Op n}

omit [Nonempty n] in
/-- Propagating a special band condition: always funded on the cap. -/
lemma occupied_band_gap (U:UNI n)(d:n→ℝ)(h:Safe (spectral U d))(i:n) :
    (1:ℝ)/2 ≤ |d i| := by
  have hp:=h.margin; rw [spectral_pow,←spectral_one U,spectral_smul,spectral_le] at hp
  have he:= hp i
  simp only [Pi.smul_apply,Pi.one_apply,smul_eq_mul,mul_one,Pi.pow_apply] at he
  nlinarith [sq_abs (d i), abs_nonneg (d i)]

abbrev fermiEnergy (H:Op n) :ℂ:= (H*projector H).trace

def occupied (d:n→ℝ) := univ.filter fun i=>0<d i
lemma projector_occupied (U: UNI n)(d:n→ℝ)(h: Safe (spectral U d)) :
    projector (spectral U d) = twist U (cutM (occupied d)) := by
  rw [projector_spectral U d h]; unfold spectral; congr 2
  ext i; by_cases g:0<d i <;> simp [occupied,occ,g]
lemma fermi_energy (U: UNI n)(d:n→ℝ)(h: Safe (spectral U d)) :
    fermiEnergy (spectral U d) = ((∑ i∈occupied d,d i:ℝ):ℂ) := by
  unfold fermiEnergy; rw [projector_occupied U d h]; unfold spectral cutM; rw [←map_mul,trace_twist]
  rw [Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal]; simp only [occupied,
    sum_filter]; rw [Complex.ofReal_sum]; apply sum_congr rfl; intro i _;
  by_cases g:0<d i <;> simp [g]
lemma energy_real (h : Safe A) : fermiEnergy A = ((fermiEnergy A).re:ℂ) := by
  obtain ⟨U,d,rfl⟩:=spectral_exists A h.self; rw [fermi_energy U d h]; rfl
lemma flight_real (h:Safe A)(t:ℝ): flight A t= ((Real.exp (t*(fermiEnergy A).re)):ℂ) := by
  unfold flight; nth_rw 1 [show (A*projector A).trace=_ from energy_real h,←Complex.ofReal_mul, ←Complex.ofReal_exp]

/-- Auxiliary height. -/
def scaledHeat (H:Op n)(t:ℝ): FC n:= (flight H t)⁻¹ • quant (grow H t)

-- Express spectral gap on all non-sea occupations as dropping at least
-- one point P or adding at least one point in Pc.
omit [Nonempty n] in
lemma salary_gap (U: UNI n)(d:n→ℝ)(h:Safe (spectral U d))(S:Finset n)(e:S≠occupied d):
    ∑ i∈S,d i + 1/2 ≤ ∑ i∈occupied d,d i := by
  let T:=occupied d
  have ht:=occupied_band_gap U d h
  have h₁ : ∀ i∈S\T, d i ≤ -(1/2):=by
    intro i hi; have he:= (mem_sdiff.mp hi).2; simp only [T, occupied, mem_filter, mem_univ, true_and, not_lt] at he
    have H:=ht i; rw [abs_of_nonpos he] at H; linarith
  have h₂ : ∀ i∈T\S, 1/2 ≤ d i:=by
    intro i hi; have he:= (mem_sdiff.mp hi).1; simp only [T, occupied, mem_filter, mem_univ, true_and] at he; simpa [abs_of_pos he] using ht i
  suffices u : ∑ i∈S\T,d i +1/2 ≤ ∑ i∈T\S,d i by
    change _≤∑ i∈T,d i; rw [←sum_sdiff (show S∩T⊆T from inter_subset_right), ←sum_sdiff (show S∩T⊆S from inter_subset_left)]; simp only [sdiff_inter_self_left,sdiff_inter_self_right] ; linarith
  apply le_trans (add_le_add_left (sum_le_sum (s:=S\T) h₁) _)
  refine le_trans ?_ (sum_le_sum (s:=T\S) h₂)
  have hg:S\T≠∅ ∨ T\S≠∅ := by by_contra p; push Not at p; exact e (le_antisymm (sdiff_eq_empty_iff_subset.mp p.1) (sdiff_eq_empty_iff_subset.mp p.2))
  have he: 1 ≤ (S\T).card+(T\S).card:=by rcases hg with u|u <;> grind
  simp only [sum_const,nsmul_eq_mul]; linarith [show (1:ℝ)≤ (S\T).card + (T\S).card from by exact_mod_cast he]

lemma heat_equiv (U: UNI n)(d:n→ℝ)(h:Safe (spectral U d))(t:ℝ):
    scaledHeat (spectral U d) t= spectral (quantU U) (fun S=> Real.exp (t * (∑ i∈S, d i -∑ i∈occupied d,d i))) := by
  rw [scaledHeat,glacial]
  rw [show spectral U (fun i=>Real.exp (t*d i))=(twist U) _ from rfl,quant_twist,quant_diag]
  change _= (twist (quantU U)) _
  rw [←twist_scalar]; apply congrArg
  ext S T; by_cases g:S=T
  · subst T; rw [Matrix.smul_apply]; simp only [Matrix.diagonal_apply_eq,smul_eq_mul]
    change (Complex.exp ((t:ℂ)*fermiEnergy _))⁻¹ * _= _; rw [fermi_energy U d h]
    push_cast; rw [←Complex.exp_sum, ←Complex.exp_neg,←Complex.exp_add, ←mul_sum]; congr 1; ring
  simp [g]

lemma scaledHeat_est (t:ℝ) (h: Safe A) (g:0≤t):
    ‖scaledHeat A t-lineOp (projector A)‖ ≤ Real.exp (-t/2) := by
  obtain ⟨U,d,rfl⟩:= spectral_exists A h.self
  let T:=occupied d; let p(S : Finset n):ℝ:= Real.exp (t * (∑ i∈S, d i -∑ i∈occupied d,d i)); let f (S : Finset n):ℝ:=if S=T then 1 else 0; let R:=Real.exp (-t/2); let V:=quantU U
  rw [heat_equiv U d h, projector_occupied U d h,line_twist,cutLine]
  have hp: p T=1:=by unfold p; simp [T]
  change ‖spectral V p -twist V _‖ ≤ R
  rw [show twist V (cutM {occupied d})=spectral V f from ?_, spectral_sub]; swap
  · unfold spectral cutM; congr 2; ext S; by_cases g:S=T <;> simp [g, f, T] at *
  have he: 0 ≤ spectral V (p-f):=by
    rw [←spectral_zero V,spectral_le]; intro x; change 0≤p x-f x; by_cases g:x=T
    · rw [g,hp]; simp [f]
    rw [show f x=0 from if_neg g,sub_zero]; exact (Real.exp_pos _).le
  apply (CStarAlgebra.norm_le_iff_le_algebraMap _ (Real.exp_pos _).le he).mpr
  rw [Algebra.algebraMap_eq_smul_one,←spectral_one V,spectral_smul,spectral_le]; intro S
  change p S - f S ≤ R * 1; rw [mul_one]
  by_cases e:S=T
  · rw [e,hp]; have hi:=Real.exp_pos (-t/2); simp [f,R,hi.le]
  rw [show f S=0 from if_neg e, sub_zero]
  apply Real.exp_le_exp.mpr; nlinarith [salary_gap U d h S e]

lemma scaledHeat_tend (h: Safe A): Tendsto (scaledHeat A) atTop (𝓝 (lineOp (projector A))) := by
  have he: Tendsto (fun t:ℝ=>Real.exp (-t/2)) atTop (𝓝 0):= Real.tendsto_exp_atBot.comp (by exact (Tendsto.atBot_div_const (by norm_num) tendsto_neg_atTop_atBot))
  refine tendsto_iff_norm_sub_tendsto_zero.mpr (squeeze_zero' (Eventually.of_forall fun _=>norm_nonneg _) ((eventually_ge_atTop 0).mono fun t ht=> scaledHeat_est t h ht) he)

end YM.CF.Fixed
