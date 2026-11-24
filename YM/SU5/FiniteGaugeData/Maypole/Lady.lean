import YM.SU5.FiniteGaugeData.Maypole.Hex
/-! # transfer to b-direction, orbit-mixed tests -/
set_option autoImplicit false
set_option synthInstance.maxSize 16000
set_option maxHeartbeats 330000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy.Seld.Vp.Tufa
open Function Filter Metric Set MeasureTheory OS OS.Semigroup Mink General Lorentz
open scoped Topology BigOperators NNReal ENNReal InnerProductSpace ComplexOrder
open Poin Celeritas Land Leal Breve Poin.Gem Boundary Probe Flute
open Folio Canopy Spectral
variable {b c:Axis}{H Y:Hilbert} (S:OS.Semigroup H c)(y x:H)(f: Probe E4)(u:SO)
local notation "L"=> feel u
local notation "qf"=> Probe.hat f
local notation "Ω"=> S.unit
open Measure Complex
private lemma jobe : Integrable (fun p:E4=> Probe.hat f p • M S (feel u p) x):= by
 let v:= (Ω).moves x; exact ((Probe.hat f).integrable.norm.mul_const ‖x‖).mono' ((Probe.hat f).continuous.smul (v.comp (feel u).continuous)|>.aestronglyMeasurable) (Eventually.of_forall fun p=>by rw [norm_smul,tcost]) -- tune
private lemma bill : ‖∫ p:E4, qf p • M S (feel u p) x‖≤(∫ p:E4, ‖qf p‖)*‖x‖:=by rw [← integral_mul_const]; refine norm_integral_le_of_norm_le ((Probe.hat f).integrable.norm.mul_const _) (Eventually.of_forall fun p=>?_); rw [norm_smul,tcost]
abbrev hull: H.Op:= LinearMap.mkContinuous (σ:= RingHom.id ℂ) {
 toFun x:=∫ p:E4, qf p • M S (feel u p) x
 map_add' x y:= by simp only [map_add,smul_add]; exact integral_add (jobe ..) (jobe ..)
 map_smul' c x:= by simp_rw [map_smul,smul_comm _ c]; rw [integral_smul]; rfl } (∫ p:E4, ‖qf p‖) fun x=> bill ..
lemma βhull: inner ℂ y (hull S f u x)=∫ p:E4,inner ℂ y (M S (feel u p) x)*qf p:=by
 unfold hull; change inner ℂ _ (∫ p:E4, qf p • _ )=_ ; rw [←integral_inner (jobe ..)]; apply integral_congr_ae; filter_upwards with p; rw [inner_smul_right,mul_comm] -- tune
section
variable (T:OS.Semigroup Y timeAxis)(p:Reigns u b) (P:Cinema T)
local notation "d"=>timeAxis
local notation "Qy"=> T.ℚmeasure
include p
lemma boostPair (v:E4): feel u ( (SEP b v).val)=(SEP timeAxis (feel u v)).val:= boosty u b v p
include P
-- pushing through positive theory measure
lemma hull_n (h:HasCompactSupport ⇑f)(q:tsupport f⊆ (swingCone b)ᶜ): hull T f u=0:=by
 have he(y:Y): inner ℂ y (hull T f u y)=0:=by
    let U:= feel u⁻¹; let D:= (Qy).diagonal y; let A:=D.map U; have hm:= U.continuous.measurable; haveI ht:IsFiniteMeasure A:=inferInstanceAs (IsFiniteMeasure (Measure.map (⇑U) D)); have hv:A ((swingCone b)ᶜ)=0:=by
       unfold A; rw [map_apply hm (cone_c b).isOpen_compl.measurableSet]; have he:(U ⁻¹' (swingCone b)ᶜ)=(swingCone d)ᶜ:=by
          ext x; change U x∉_ ↔ x∉_; rw [←firmament u b _ p]; unfold U; rw [feel_h]
       rw [he]; exact ((Qy).null_pair ((cone_c d).isOpen_compl.measurableSet) _).2 (by rw [P]; rfl)
    have he(w:E4): charFun A w=inner ℂ y (M T (L w) y):=by
       rw [← show charFun D (L w)= inner ℂ y (M T (L w) y) from T.joint y (L w)]; rw [charFun_apply,charFun_apply]; unfold A; rw [integral_map hm.aemeasurable ((show Continuous (fun y:E4=> Complex.exp ((↑(inner ℝ y w):ℂ)*I)) from by fun_prop).aestronglyMeasurable)] -- parentheses tune
       apply integral_congr_ae; filter_upwards with p; rw [show inner ℝ (U p) w= inner ℝ p (L w) from ?_]; rw [←Ving u]; unfold U; rw [feel_h]
    rw [βhull]; simp_rw [← he]; rw [wave_integral,(picker A (cone_c b).isOpen_compl).1 hv f h q,smul_zero]
 have t:= (inner_map_self_eq_zero (hull T f u).toLinearMap).1 (fun x=> inner_eq_zero_symm.mp (he x)); ext1 x; exact LinearMap.congr_fun t x
-- enough mixed probes connecting
omit p P
end
variable (U:OS.Semigroup H b)(G:H.Op)
private lemma orth_i(A:Set H)(p:Dense (Submodule.span ℂ A:Set H))(q:∀ i∈A,inner ℂ i x=0): x=0:=by
 let F:=innerSL ℂ x; have he:Submodule.span ℂ A ≤ F.ker:= Submodule.span_le.mpr (fun i p=> inner_eq_zero_symm.mp (q i p)); exact inner_self_eq_zero.mp (show x∈F.ker from closure_minimal he F.isClosed_ker (p x))
lemma hemi(B A:Set H) (p:Dense (Submodule.span ℂ B:Set H))(q:Dense (Submodule.span ℂ A:Set H)) (t:∀ y∈ A,∀ z∈B, inner ℂ z (G y)=0): G=0:=by
 have he:Submodule.span ℂ A≤ G.ker:= Submodule.span_le.mpr (fun i v=> orth_i _ _ p (t i v)); ext1 x; exact (show x∈G.ker from closure_minimal he G.isClosed_ker (q x))
variable (T:OS.Semigroup Y timeAxis)
lemma witnessed (p:Reigns u b)(B A:Set H)(p':Dense (Submodule.span ℂ B:Set H))(q:Dense (Submodule.span ℂ A:Set H))(v:Cinema T) (k:∀ x∈B,∀ y∈A, ∃ x' y':Y, ∀ p:E4, inner ℂ x (M U p y)=inner ℂ x' (M T (feel u p) y')): Cinema U:=by
 refine ((U.unit).carrier U.ℚmeasure U.joint (swingCone b) (cone_c b) univ dense_univ).2 (fun x _ f a v'=>?_)
 have hG:=hull_n f u T p v a v'; let X:=hull U f 1; have hx(y z:H): inner ℂ y (X z)=∫ w,inner ℂ y (M U w z)* hat f w:=βhull ..; have he:X=0:= hemi _ B A p' q fun y o z e=>by
    obtain ⟨y',x',g⟩:= k z e y o; rw [hx]; simp_rw [g]; rw [←βhull,hG]; exact inner_zero_right _ -- inner zero t. shadow y
 rw [show (∫ p, inner ℂ x (U.unit.translation p x)* Probe.hat f p)=_ from (hx x x).symm, he]; simp
#print axioms witnessed
end YM.CF.Buffered.Afterglow.Hierarchy.Seld.Vp.Tufa
