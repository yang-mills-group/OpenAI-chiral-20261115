import YM.Compact.PVM
import YM.Analysis.Weak
/-!
# Bounded Borel calculus in our PVM
-/
set_option autoImplicit false
set_option quotPrecheck false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.Multiplier
open Function Set Filter MeasureTheory Spectral Analysis
open scoped Topology NNReal ENNReal ComplexOrder InnerProductSpace
variable {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  {H : Hilbert} (P : PVM H X)
local notation "𝔪" x:max => P.diagonal x
-- use only diagonal PVM data. Include Meas & budget to apply dominated convergence easily
structure Tag (f : X→E) : Prop where
 meas : Measurable f
 bound : ∃ v:ℝ, 0 ≤ v ∧ ∀ x, ‖f x‖ ≤ v
namespace Tag
variable {f g : X→E}
lemma const (c:E) : Tag (fun _ : X => c) := ⟨measurable_const,‖c‖,norm_nonneg _,fun _=> le_rfl⟩
variable [SecondCountableTopology E]
lemma rent (h: Tag f) (x:H) : Integrable f (P.diagonal x) := by
  obtain ⟨c,hc,z⟩ := h.bound
  apply Integrable.mono' (integrable_const (μ:=𝔪 x) c) h.meas.aestronglyMeasurable (Eventually.of_forall z)
lemma adds (h:Tag f) (e:Tag g): Tag (f+g):= by
  obtain ⟨u,b,hp⟩:= h.bound; obtain ⟨v,c,fv⟩:= e.bound; exact ⟨h.meas.add e.meas, u+v, add_nonneg b c, fun x => (norm_add_le ..).trans (add_le_add (hp x) (fv x))⟩
lemma minus (h:Tag f): Tag (-f) := by
 obtain ⟨u,b,e⟩:= h.bound; exact ⟨h.meas.neg, u,b,fun x => by simp [e x]⟩
lemma subs (h:Tag f)(p:Tag g): Tag (f-g):= sub_eq_add_neg f g ▸ h.adds p.minus
lemma mask (h:Tag f) {s : Set X}(hs: MeasurableSet s): Tag (s.indicator f):= by
 obtain ⟨u,b,e⟩:= h.bound; refine ⟨h.meas.indicator hs, u,b,fun x=>?_⟩; by_cases h:x∈s
 · simpa [h] using e x
 simp [h,b]
variable {a b : X→ℂ}
lemma times (h : Tag a) (g : Tag b) : Tag (a*b):= by
 obtain ⟨u,p,r⟩:= h.bound; obtain ⟨v,q,s⟩:=g.bound; refine ⟨h.meas.mul g.meas,u*v,mul_nonneg p q,?_⟩; intro x; simp only [Pi.mul_apply, norm_mul]; exact mul_le_mul (r _) (s _) (norm_nonneg _) p
lemma scale (h:Tag a) (z:ℂ): Tag (z • a):= (Tag.const z).times h
lemma conj (h:Tag a): Tag (star a):= by
 refine ⟨Complex.continuous_conj.measurable.comp h.meas,?_⟩; simpa using h.bound
end Tag
/-- Operator corresponding to this PVM registered by any measuring $x$. -/
structure Registers (f : X→ℂ) (A : H.Op) : Prop where
 price : Tag f
 awakes (x:H) : inner ℂ x (A x)= ∫ y, f y ∂P.diagonal x
variable {P}
lemma Registers.single {U V : H.Op} {f : X→ℂ} (p:Registers P f U)(h:Registers P f V): U=V:= by
 apply Rep.fact; intro x; rw [←inner_conj_symm,←inner_conj_symm (V x) _,p.awakes,h.awakes]
lemma Registers.agrees {A : H.Op} {f g : X→ℂ} (h: Registers P f A)(b:Tag g)(e:∀ x:H,f=ᵐ[P.diagonal x] g) : Registers P g A := ⟨b, fun x=> (h.awakes x).trans (integral_congr_ae (e x))⟩
namespace Registers
variable {U W : H.Op} {f g : X→ℂ} (h:Registers P f U) (p:Registers P g W)
include h
lemma scale (c:ℂ) : Registers P (c • f) (c • U):=
 ⟨h.price.scale c, fun x=> by simp only [Pi.smul_apply,_root_.smul_apply,inner_smul_right,h.awakes,smul_eq_mul,integral_const_mul]⟩
include p
lemma add : Registers P (f+g) (U+W):=
 ⟨h.price.adds p.price, fun x=> by simp only [_root_.add_apply,inner_add_right,h.awakes,p.awakes]; rw [←integral_add (h.price.rent P x) (p.price.rent P x)]; rfl⟩ -- `_root_`
lemma sub : Registers P (f-g) (U-W) := by
 rw [sub_eq_add_neg,sub_eq_add_neg, ←neg_one_smul ℂ W, ←neg_one_smul ℂ g]; exact h.add (p.scale (-1))
omit p
lemma adjoint : Registers P (star f) (ContinuousLinearMap.adjoint U) := ⟨h.price.conj, fun x => by
 rw [ContinuousLinearMap.adjoint_inner_right, ← inner_conj_symm, h.awakes]; change _=∫ y, (starRingEnd ℂ) (f y)∂_; rw [integral_conj] ⟩
omit h
variable (P)
lemma size (x : H) : (P.diagonal x).real univ = ‖x‖^2 := by rw [P.same MeasurableSet.univ, P.all]; rfl
lemma none : Registers P 0 0 := ⟨Tag.const _, by intro; simp⟩
lemma one : Registers P 1 1:= ⟨Tag.const _,fun x=> by
   change inner ℂ x x= ∫ _:X,(1:ℂ) ∂_; rw [inner_self_eq_norm_sq_to_K,integral_const,size,Complex.real_smul]; simp ⟩
lemma box {s : Set X} (hs:MeasurableSet s) : Registers P (s.indicator (1:X→ℂ)) (P.region s) := ⟨(Tag.const (1:ℂ)).mask hs,fun x=> by
   rw [←P.at_pair hs]; simp [integral_indicator hs]⟩
lemma restricted {s : Set X} (hs:MeasurableSet s) (x : H) : 𝔪 (P.region s x) = (P.diagonal x).restrict s := by
 ext t h
 rw [Measure.restrict_apply h]
 apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
 rw [← Measure.real, ← Measure.real, P.same h,P.same (h.inter hs), ← ContinuousLinearMap.comp_apply,P.joins h hs]
-- for multiplication in simple case. commutation must checked separately
variable {P}
include h
lemma mask {s} (e : MeasurableSet s) (u : Commute U (P.region s)) : Registers P (s.indicator f) ((P.region s)*U) := by
 refine ⟨h.price.mask e,?_⟩; intro x; rw [integral_indicator e,← restricted P e x,← h.awakes]
 change inner ℂ x (P.region s (U x)) = _; nth_rw 1 [← P.idempotent e (U x),← P.real e]; rw [ContinuousLinearMap.adjoint_inner_right]; congr 1
 exact DFunLike.congr_fun u.eq.symm _
end Registers
end YM.Multiplier
