import YM.SU5.Voyager.Evolution
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
/-! # Account for all powers. High location expenses. -/
set_option autoImplicit false
noncomputable section
namespace YM.Caino
open Function Filter Set Metric NormedSpace Bornology Complex ContinuousLinearMap
open MeasureTheory Measure Boundary.Probe Boundary
open scoped NNReal ENNReal Topology InnerProductSpace ComplexConjugate ComplexOrder BigOperators
variable {X:Type*}[NormedAddCommGroup X][InnerProductSpace ℝ X][FiniteDimensional ℝ X][MeasurableSpace X][BorelSpace X]
private abbrev D (X:Type*) [AddCommGroup X][Module ℝ X]:= Module.finrank ℝ X+1
lemma blossoms {u v:ℝ}(h:0<u)(g:u<v)(K:ℝ)(d:ℕ) : ∀ᶠ n:ℕ in atTop,K*(n:ℝ)^d*u^n ≤ v^n:=by
 have hv:0<v:= h.trans g; let r:=u/v; have he:0<r:=(by positivity); have hg:r<1:= (div_lt_one hv).2 g
 have ht:= (tendsto_pow_const_mul_const_pow_of_lt_one d he.le hg).const_mul K; rw [mul_zero] at ht; filter_upwards [ht.eventually (le_mem_nhds (by norm_num: (0:ℝ)>-1)), ht.eventually (ge_mem_nhds (by norm_num: (0:ℝ)<1))] with n _ a
 unfold r at a; rw [div_pow, ←mul_div_assoc, ←mul_div_assoc, ←mul_assoc] at a -- incorrect check
 exact (div_le_one (pow_pos hv _)).mp a
lemma least {u v:ℝ}(h:0<u)(h':u<v)(K:ℝ) : ∀ᶠ n:ℕ in atTop,K*u^n ≤ v^n:= by simpa using blossoms h h' K 0
def drying (x:X):ℝ := ((1+‖x‖)^(D X))⁻¹
lemma dryRain : Integrable (drying (X:=X)):=by
 have hv: (Module.finrank ℝ X:ℝ)<(D X:ℝ):= by unfold D; norm_cast; omega
 have ht:= integrable_one_add_norm (μ:=(volume:Measure X)) hv
 exact (ht.congr (ae_of_all _ fun i=>by change (1+‖i‖)^(-(D X:ℝ))=_; rw [Real.rpow_neg (by positivity :0≤(1+‖i‖)),Real.rpow_natCast]; rfl)) -- tune
variable (F:ℕ→ X→ℂ)
structure FlairC : Prop where
 meas(i:ℕ): Measurable (F i)
 localC: ∃ C:ℝ,0<C∧∀ᶠ i:ℕ in atTop,∀ x, ‖F i x‖≤ C^i
 ray: ∃ C:ℝ,0<C∧∀ᶠ i:ℕ in atTop,∀ x,C*i≤‖x‖→ ‖F i x‖≤ (C*i/(1+‖x‖))^i
local notation "K"=> D X
variable {F}
lemma dryParcel (h:FlairC F) {c:ℝ} (hc:0<c) {u:ℝ}(hu:0<u) : ∃ A:ℝ,u ≤ A∧ ∀ᶠ i:ℕ in atTop,∀ x:X, A*i ≤ ‖x‖→ ‖F i x‖≤ c^i * drying x:=by
 obtain ⟨C,p,P⟩:= h.ray; let c':= c/2; let A:=max (C/c') (max u C); have h':0<c':=by positivity
 have hs : C≤ c'*A:= (div_le_iff₀ h').1 (le_max_left ..) |>.trans_eq (mul_comm ..)
 have ht : C ≤ A:= (le_max_right ..).trans (le_max_right ..)
 refine ⟨A,(le_max_left ..|>.trans (le_max_right ..)), ?_⟩; filter_upwards [eventually_ge_atTop K,P, blossoms (v:=c) h' (half_lt_self hc) ((C/c')^K) K] with i hv p g; intro x hx; let k:= 1+‖x‖; have h₁: C*i ≤ A*i:=(by gcongr); have hk:0<k:=(by positivity); refine (p x (h₁.trans hx)).trans ?_
 let w := C*i/k; let n:=K; let z:= i-K; have hz: i=n+z:=(Nat.add_sub_of_le hv).symm; have hw:0 ≤ w:=(by positivity); have H: w≤c':=by
    apply (div_le_iff₀ hk).2; unfold k; nlinarith [mul_le_mul_of_nonneg_right hs (by positivity:0 ≤ (i:ℝ)),mul_le_mul_of_nonneg_left hx h'.le]
 have hy:w^z≤ c'^z:=by gcongr
 -- multiply both sides by k^n
 calc (C*i/(1+‖x‖))^i = w^i:= rfl
      _ = w^n*w^z:=by nth_rw 1 [hz]; rw [pow_add]
      _ ≤ w^n*c'^z:= mul_le_mul_of_nonneg_left hy (by positivity)
      _ = (((C/c')^K)*(i:ℝ)^K*c'^i)*drying x:=by
         have he:c'^i=c'^K*c'^z:=(by nth_rw 1 [hz]; exact pow_add ..); rw [he]; change (C*i/k)^K*c'^z=_* (k^K)⁻¹; simp_rw [div_pow, mul_pow C]; field_simp
      _ ≤ _:=mul_le_mul_of_nonneg_right g (by unfold drying; positivity)
def rim (A:ℝ)(i:ℕ): Set X := closedBall 0 (A*i)
lemma drying_out {x:X}{A:ℝ}{i:ℕ}(p:x∈ (rim A i)ᶜ): A*i ≤ ‖x‖:=by unfold rim at p; simp at p; exact p.le
lemma dustFare (h:FlairC F){c m:ℝ}(p:0<c)(q:0<m): ∃ A:ℝ,m≤A∧∀ᶠ i:ℕ in atTop, Integrable (F i)∧ (∫ x in (rim A i)ᶜ, ‖F i x‖) ≤ c^i :=by
 let v:= c/2; have hz:0<v:=by positivity
 obtain ⟨A,H,W⟩:=dryParcel h hz q; obtain ⟨C,y,Y⟩:=h.localC; refine ⟨A,H,?_⟩; let w:X→ℝ:= drying; filter_upwards [W,Y,least hz (half_lt_self p) (∫ x:X,w x)] with i h₁ h₂ h₃
 let S:Set X:=rim A i; let f(x:X):=v^i*w x; have he:IsCompact S:= isCompact_closedBall ..
 have hg: Integrable f:= dryRain.const_mul _
 have ht : ∀ᵐ x ∂(volume.restrict Sᶜ), ‖F i x‖≤ f x := (ae_restrict_mem (he.measurableSet.compl)).mono (fun x v=> h₁ x (drying_out v))
 have hx: IntegrableOn (F i) Sᶜ:= hg.integrableOn.mono' ((h.meas i).aestronglyMeasurable) ht
 haveI : IsFiniteMeasure (volume.restrict S):= ⟨by simp [ne_eq, he.measure_lt_top]⟩
 have hu:IntegrableOn (F i) S:= (integrable_const (C^i)).mono' ((h.meas i).aestronglyMeasurable) (ae_of_all _ h₂); refine ⟨?_,?_⟩; · simpa only [Set.union_compl_self,integrableOn_univ] using hu.union hx
 exact (integral_mono_ae hx.norm hg.integrableOn ht).trans ((setIntegral_le_integral hg (ae_of_all _ fun x=>by dsimp [f,w,drying]; positivity)).trans (by unfold f; rw [integral_const_mul,mul_comm]; exact h₃))
end YM.Caino
