import YM.SU5.Reconstruction.Crease.Response
import YM.SU5.Reconstruction.Crease.Multiplexer
set_option autoImplicit false
set_option maxHeartbeats 350000
set_option quotPrecheck false
noncomputable section
namespace YM.BridgeClub.Moth
open Function Set Filter MeasureTheory Spectral Analysis Metric ContinuousLinearMap Anvil Picket CrossedFrame Opera Multiplier
open scoped BigOperators Topology InnerProductSpace ComplexOrder NNReal ENNReal Complex Classical
variable {H: Hilbert} {X:Type*}[MeasurableSpace X] (P:PVM H X)
noncomputable def leaf (S:SimpleFunc X ℝ)(t:ℝ):H.Op:=P.region ((S:X→ℝ) ⁻¹' {t})
noncomputable def grove (S:SimpleFunc X ℝ)(φ:ℝ→ℂ):H.Op:=∑ i ∈ S.range, φ i • leaf P S i
lemma counting(S:SimpleFunc X ℝ)(φ:ℝ→ℂ):Registers P (φ∘ S) (grove P S φ):=by
 let V(i:ℝ):= ((S:X→ℝ) ⁻¹' {i}).indicator (1:X→ℂ); let U(x:X):= φ (S x)
 have h : Registers P (∑ i∈ S.range, φ i • V i) (grove P S φ):= by
    unfold grove; generalize S.range=n; induction n using Finset.induction_on with
     | empty=> rw [Finset.sum_empty, Finset.sum_empty]; exact Registers.none _
     | insert i s h ih=> rw [Finset.sum_insert h,Finset.sum_insert h]; exact ((Registers.box P (S.measurableSet_preimage {i})).scale (φ i)).add ih
 rw [show φ∘ S=∑ i∈ S.range,φ i • V i from ?_]; exact h
 funext x; rw [Finset.sum_apply, Finset.sum_eq_single (S x)]
 · simp [V]
 · intro i h p; simp [V,Ne.symm p]
 simp [SimpleFunc.mem_range_self]
lemma grow (S:SimpleFunc X ℝ)(φ:ℝ→ℂ)(x:H): grove P S φ x=∑ i∈ S.range,φ i • leaf P S i x:=by unfold grove; simp
-- coordinate functions
abbrev pole (x:ℝ):= (x:ℂ)
abbrev gap (x:ℝ):=1-pole x
def tale (x:ℝ) := Real.log ((1-x)/x)
def ray (t x:ℝ):ℂ:= tune (- (t*tale x))
lemma story (x y:ℝ)(u:x∈ Ioo (0:ℝ) 1)(v:y∈Ioo (0:ℝ) 1): Complex.exp (tale x-tale y:ℂ)=gap x*pole y/(pole x*gap y):=by
 let E(x:ℝ):=(1-x)/x; have h(x)(p:x∈ Ioo (0:ℝ) 1): Complex.exp (tale x:ℂ)=gap x/pole x:= by
      have hx:0<E x:= div_pos (sub_pos.mpr p.2) p.1
      unfold pole gap tale; rw [← Complex.ofReal_exp,Real.exp_log hx, Complex.ofReal_div]; push_cast; rfl -- maybe
 have hp(t:ℝ)(p':t∈Ioo (0:ℝ) 1): pole t ≠0 ∧ gap t≠0:= by refine ⟨Complex.ofReal_ne_zero.mpr (p'.1).ne',sub_ne_zero.mpr (by unfold pole; exact_mod_cast (p'.2).ne')⟩
 rw [Complex.exp_sub,h x u,h y v]; rcases hp x u with ⟨a,b⟩; rcases hp y v with ⟨t,c⟩; field_simp
lemma chime (x t :ℝ): ray t x=Clasp.river (-t) x:= by unfold ray tune tale Clasp.river Chirp.sing; push_cast; congr 1; ring
@[fun_prop] lemma smooth_ray(x:ℝ): Continuous (fun t=>ray t x):=by unfold ray tune; fun_prop
variable {θ:ℝ}(p:θ∈ twilight) -- wrong case
local notation "z"=>Opera.spin θ
include p
lemma pop (x y:ℝ)(u:x∈ Ioo (0:ℝ) 1)(v:y∈Ioo (0:ℝ) 1):
    (∫ t:ℝ,cup θ t*(star (ray t x)*ray t y)*(gap x^2*pole y^2+z*pole x^2*gap y^2)) = pole x*gap x*pole y*gap y:= by
 let e:= tale x-tale y
 have ht(t:ℝ): star (ray t x)* ray t y=tune (t*e):= by unfold ray; rw [melody,rhyme]; congr 1; unfold e; ring
 have k : gap x^2*pole y^2+z*pole x^2*gap y^2=(Complex.exp (e:ℂ)+z*Complex.exp (-(e:ℂ)))*(pole x*gap x*pole y*gap y):=by
     unfold e; rw [Complex.ofReal_sub, story x y u v,neg_sub, story y x v u];
     have hp(t:ℝ)(p':t∈Ioo (0:ℝ) 1): pole t ≠0 ∧ gap t≠0:= by refine ⟨Complex.ofReal_ne_zero.mpr (p'.1).ne',sub_ne_zero.mpr (by unfold pole; exact_mod_cast (p'.2).ne')⟩
     rcases hp x u with ⟨a,b⟩; rcases hp y v with ⟨c,d⟩; field_simp
 simp_rw [ht]; rw [integral_mul_const,k,←mul_assoc,receipt θ _ p,one_mul]
end YM.BridgeClub.Moth
