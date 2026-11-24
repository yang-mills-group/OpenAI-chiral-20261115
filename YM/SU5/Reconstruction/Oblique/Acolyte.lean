import YM.SU5.Reconstruction.Sleet.Mitt
/-!
# Helper: Stieltjes kernel price from positive transfer powers. Lean in YM.Generator orientation.
-/
set_option autoImplicit false
set_option maxHeartbeats 350000
set_option maxRecDepth 5500
set_option synthInstance.maxSize 32000
set_option quotPrecheck false
noncomputable section
namespace YM.ConePrice.Storm.StepVoucher
open Function Set Filter NormedSpace MeasureTheory Spectral Analysis
open scoped Topology BigOperators ComplexOrder InnerProductSpace NNReal ENNReal Classical
open _root_.YM.Kernel
variable {X:Type} [AddCommGroup X] [Module ℂ X] (S:X→ₗ⋆[ℂ] X→ₗ[ℂ] ℂ)
local notation "E" => Gram fun x y:X=> S x y
variable (K : Gram (fun x y:X=> S x y))
-- datum on X still H dense. Capture
private lemma extinguish (x y : (show Gram _ from K).H) (p:∀ v:X, inner ℂ (K.plant v) x=inner ℂ (K.plant v) y): x=y:=by
 apply K.whole.eq_of_inner_right ℂ; intro w
 induction w using Finsupp.induction_linear with
 | zero=> simp
 | add u v h p=> simp only [map_add,inner_add_left,h,p]
 | single a r=> simp [Gram.stems,p]
noncomputable def footpath : X→ₗ[ℂ] K.H where
 toFun:=K.plant
 map_add' x y:= by apply extinguish S K; intro z; rw [inner_add_right,K.measure,K.measure,K.measure]; exact map_add ..
 map_smul' c x:= by apply extinguish S K; intro z; rw [show inner ℂ _ (_ • _)=_ from inner_smul_right .., K.measure,K.measure]; exact map_smul ..
private lemma firm (Q:Hilbert)(T:X→ₗ[ℂ] Q)(x:X→₀ℂ) : T (Finsupp.linearCombination ℂ (LinearMap.id :X→ₗ[ℂ] X) x)= Finsupp.linearCombination ℂ T x:=by
 induction x using Finsupp.induction_linear with
 | zero=> simp
 | add u v p q=> rw [map_add,map_add,map_add,p,q]
 | single a b=>simp
lemma everyone : DenseRange (footpath S K):= by
 apply K.whole.mono; rintro _ ⟨j,rfl⟩; exact ⟨_,firm K.H (footpath S K) j⟩
lemma extends_path (U:X→ₗ[ℂ] X)(t:∀x:X, ‖K.plant (U x)‖ ≤ ‖K.plant x‖) : ∃ (L: K.H.Op), ‖L‖≤1 ∧ ∀i:X,L (K.plant i)=K.plant (U i):= by
 apply K.by_bound (K.plant ∘ U) 1 (by norm_num); intro f; let T:=(footpath S K).comp U
 change ‖Finsupp.linearCombination ℂ T f‖ ≤ (1:ℝ)*‖Finsupp.linearCombination ℂ (footpath S K) f‖
 rw [one_mul,← firm K.H T,← firm K.H (footpath S K)]; exact t _
lemma pos_path (A:K.H.Op)(t:∀ x:X,0≤ inner ℂ (K.plant x) (A (K.plant x))): 0 ≤ A:= by
 have he: ∀ w:K.H,0≤ inner ℂ w (A w) :=by
    let Y : Set K.H :={w| 0 ≤ inner ℂ w (A w)}; refine fun x=> closure_minimal (t:= Y) ?_ (isClosed_le continuous_const (continuous_id.inner A.continuous)) (everyone S K x); rintro _ ⟨z,rfl⟩; exact t z -- tune OrderClosedTopology ℂ
 apply (ContinuousLinearMap.nonneg_iff_isPositive A).mpr
 apply (ContinuousLinearMap.isPositive_toLinearMap_iff _).mp ∘ (LinearMap.isPositive_iff_complex A.toLinearMap).2 -- tune
 intro x; have hx:0 ≤ inner ℂ (A x) x:= by rw [←inner_conj_symm]; simpa only [←Complex.star_def,star_nonneg_iff] using he x -- guess star_nonneg
 refine ⟨Complex.ext ?_ ?_, hx.1⟩
 · rfl
 exact hx.2 -- orientation

-- Operator-norm ticket via CFC. Real spectrum includes here (0 okay). No invert $T needed.
variable {H:Hilbert} (T:H.Op)(u:0≤T)(w:‖T‖≤1)
include u w in
private lemma shelf {z:ℂ}(v:z∈ spectrum ℂ T):∃ r:ℝ, 0≤r ∧ r≤1 ∧ z=(r:ℂ):=by
 have p:= ((ContinuousLinearMap.nonneg_iff_isPositive _).1 u).isSelfAdjoint
 have h: z=(z.re:ℂ):= SpectrumRestricts.real_iff.mp p.spectrumRestricts z v
 have ht: z.re ∈ spectrum ℝ T:= p.coe_mem_spectrum_complex.mp (h ▸ v)
 refine ⟨_,spectrum_nonneg_of_nonneg u ht,?_,h⟩; rcases subsingleton_or_nontrivial H.space with c|c
 · exfalso; apply v; change IsUnit ((algebraMap ℂ H.Op) z-T); rw [Subsingleton.elim ((algebraMap ℂ H.Op) z-T) (1:H.Op)]; exact isUnit_one
 exact (Complex.re_le_norm _).trans ((spectrum.norm_le_norm_of_mem v).trans w)
variable {R: Type*}(c:R→ℂ) (n:R→ℕ) (P:Finset R) {C:ℝ} (ρ:ℝ) (hρ : 0<ρ) (hc:∀ p:ℝ,0≤ p → ‖∑ i∈ P, c i * (Real.exp (-ρ * p*(n i)):ℂ)‖ ≤ C)
include hρ hc w u
lemma chip_pos (e: ∀ i∈ P, 0<n i) : ‖∑ i∈ P,c i • T ^ n i‖ ≤ C:=by
 let F(i:R)(z:ℂ):= c i*z^n i
 have p:T.IsPositive:= (ContinuousLinearMap.nonneg_iff_isPositive _).1 u
 rw [show (∑ i∈ P,c i • T^n i) = cfc (∑ i∈P, F i) T from Eq.symm ?_]
 · apply norm_cfc_le ((norm_nonneg _).trans (hc 0 le_rfl))
   intro z h; obtain ⟨r,s,t,rfl⟩:= shelf T u w h
   rcases s.eq_or_lt with rfl|s
   · simp only [Finset.sum_apply,F,Complex.ofReal_zero]; rw [Finset.sum_eq_zero (fun i v=>?_),norm_zero]; exact (norm_nonneg _).trans (hc 0 le_rfl)
     rw [zero_pow (e i v).ne',mul_zero]
   let q:= -Real.log r/ρ; have h:q≥0:= div_nonneg (neg_nonneg.mpr (Real.log_nonpos s.le t)) hρ.le
   have eq: -ρ*q=Real.log r:=by unfold q; field_simp
   specialize hc q h; simp only [eq, mul_comm (a:=Real.log r),Real.exp_nat_mul, Real.exp_log s,Complex.ofReal_pow] at hc
   simpa only [Finset.sum_apply] using hc
 rw [cfc_sum _ _ P (by intro i _; unfold F; fun_prop)]; apply Finset.sum_congr rfl; intro i x; unfold F; rw [show cfc (fun z:ℂ=> c i*z^n i) T= _ from (show _ from cfc_const_mul (c i) (fun z:ℂ=>z^n i) T)]; rw [cfc_pow_id (R:=ℂ) T (n i) p.isSelfAdjoint.isStarNormal]
lemma credit_pos (e:∀ i∈ P,0<n i)(x y:H): ‖∑ i∈P,c i*inner ℂ x ((T^n i) y)‖≤(‖x‖*‖y‖)*C:=by
 let U:= ∑ i∈P, c i • T^n i
 rw [show (∑ i∈P,c i*inner ℂ x ((T^n i) y))=inner ℂ x (U y) by unfold U; rw [ContinuousLinearMap.sum_apply,inner_sum]; simp only [ContinuousLinearMap.smul_apply, inner_smul_right]] -- notation `inner_sum` maybe `inner_sum` deprecated.
 rw [mul_right_comm]
 refine (norm_inner_le_norm ..).trans (le_trans (mul_le_mul_of_nonneg_left ((U.le_opNorm y).trans (mul_le_mul_of_nonneg_right (chip_pos T u w c n P ρ hρ hc e) (norm_nonneg _))) (norm_nonneg _)) ?_)
 rw [mul_assoc]
end YM.ConePrice.Storm.StepVoucher
