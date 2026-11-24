import YM.SU5.Reconstruction.Trap.Shops
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
/-!
# Determination of images, for UNBOUNDED observables

Only need intertwining on a specified family e.g. exponentials or
for bounded case one moment price attached to the commuting operator.
-/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Multiplier
open Function Set Filter MeasureTheory Spectral Analysis
open scoped Topology NNReal ENNReal ComplexOrder InnerProductSpace
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
variable {H D : Hilbert} (P : PVM H X) (Q : PVM D Y)
local notation "𝔪" x:max => P.diagonal x
local notation "𝔫" x:max => Q.diagonal x
section registers
open Complex
variable {P} {f : X→ℂ} {A : H.Op}
lemma Tag.port {f:ℝ→ℂ}(b:Tag f)(g:X→ℝ)(m:Measurable g): Tag (f ∘ g):= by obtain ⟨t,h,q⟩:=b.bound; exact ⟨b.meas.comp m,t,h,fun x=> q (g x)⟩
lemma Registers.pow (h:Registers P f A)(n:ℕ): Registers P (f^n) (A^n):= by
 induction n with
 | zero=> rw [pow_zero,pow_zero];exact Registers.one ..
 | succ n ih=> rw [pow_succ,pow_succ]; exact ih.times h
lemma Registers.money (h:Registers P f A): Registers P (Complex.exp ∘ f) (NormedSpace.exp A):=by
 obtain ⟨c,v,b⟩:=h.price.bound
 let T:=Real.exp c
 let S (n:ℕ):ℂ:=(n.factorial:ℂ)⁻¹
 let g n:= (S n) • (f^n); let G n:= ∑ i∈Finset.range n, g i
 let k n:= (S n) • (A^n); let K n:= ∑ i∈Finset.range n,k i
 apply Registers.onLimit P K atTop G _ ⟨(continuous_exp.measurable.comp h.price.meas),T,(Real.exp_pos _).le,fun x=> (Complex.norm_exp_le_exp_norm (f x)).trans (Real.exp_le_exp.mpr (b x))⟩ T
 · refine Eventually.of_forall fun i x=>?_
   dsimp only [G,g]; simp only [Finset.sum_apply,Pi.smul_apply, Pi.pow_apply]
   apply le_trans (norm_sum_le ..)
   refine (Finset.sum_le_sum (g:=fun j=> c^j/(j.factorial:ℝ)) (fun i _=>?_)).trans (Real.sum_le_exp_of_nonneg v _)
   simp_rw [div_eq_mul_inv,norm_smul,norm_pow,S,norm_inv,norm_natCast]; rw [mul_comm]; gcongr; exact b x
 · intro x; unfold G g S; simp only [Finset.sum_apply,Pi.pow_apply,Pi.smul_apply,Function.comp_apply]
   rw [exp_eq_exp_ℂ]; exact (NormedSpace.exp_series_hasSum_exp' (𝕂:=ℂ) (f x)).tendsto_sum_nat
 · intro i; induction i with
   | zero=>simp only [G,K,Finset.range_zero, Finset.sum_empty]; exact Registers.none ..
   | succ i ih=> exact (show Registers .. from by unfold G K; rw [Finset.sum_range_succ,Finset.sum_range_succ]; exact ih.add ((pow h i).scale (S i)))
 intro x; exact (ContinuousLinearMap.apply ℂ H.space x).continuous.tendsto _|>.comp ((NormedSpace.exp_series_hasSum_exp' (𝕂:=ℂ) A).tendsto_sum_nat) -- tune defeq
noncomputable def sound (t x:ℝ):ℂ:= exp ((t:ℂ)*x*I)
lemma pure (t:ℝ):Tag (sound t):=⟨by unfold sound; fun_prop,1,zero_le_one,fun x=>by simp [sound,mul_re,mul_im,norm_exp]⟩
noncomputable def concern (P:PVM H X) (f:X→ℝ)(t:ℝ) := order P (sound t ∘ f)
lemma current (P:PVM H X)(f:X→ℝ)(m:Measurable f)(t:ℝ): Registers P (sound t ∘ f) (concern P f t):=order_reads _ ((pure t).port f m)
lemma replay (P:PVM H X)(f:X→ℝ)(m:Measurable f)(t:ℝ) : ContinuousLinearMap.adjoint (concern P f t)= concern P f (-t) := by
 apply Registers.single (V:= _) ((current P f m t).adjoint)
 rw [show star (sound t ∘ f)= sound (-t) ∘ f from ?_]; exact current P f m _
 funext x; simp [sound,← Complex.exp_conj]
noncomputable def pushed (P:PVM H X)(f:X→ℝ) (x:H) := Measure.map f (P.diagonal x)
lemma plays (P:PVM H X)(f:X→ℝ)(m:Measurable f)(t:ℝ)(x:H) : charFun (pushed P f x) t= inner ℂ x (concern P f t x) := by
 rw [charFun_apply_real,pushed, integral_map m.aemeasurable, (current P f m t).awakes]; rfl
 fun_prop
end registers
variable (U:H→L[ℂ] D) (f:X→ℝ)(g:Y→ℝ)(m:Measurable f)(n:Measurable g)
section travels
local notation "σ" t:max=> concern P f t
local notation "τ" t:max=> concern Q g t
local notation "κ" x:max=> pushed P f x
local notation "ℓ" x:max=> pushed Q g x
local notation "R" z:max=> order P (z ∘ f)
local notation "S" z:max=> order Q (z ∘ g)
instance (P:PVM H X)(f:X→ℝ)(x:H):IsFiniteMeasure (pushed P f x):=by unfold pushed; infer_instance
private lemma fare (G:ℝ→ℂ)(q:Tag G)(μ:Measure ℝ)[IsFiniteMeasure μ] : Integrable G μ:= by obtain ⟨b,t,p⟩:=q.bound; exact (integrable_const b).mono' q.meas.aestronglyMeasurable (Eventually.of_forall p)
private lemma plus (t:ℝ)(μ μ':Measure ℝ)[IsFiniteMeasure μ][IsFiniteMeasure μ']:
 charFun (μ+μ') t=charFun μ t+charFun μ' t := by simp_rw [charFun_apply_real]; exact integral_add_measure (fare _ (pure t) μ) (fare _ (pure t) μ')
variable (h: ∀ t:ℝ,U.comp (concern P f t)=(concern Q g t).comp U)
include m n h
private lemma pillars (t:ℝ)(x:D)(y:H):
 inner ℂ x ((τ t) (U y))=inner ℂ (U.adjoint x) ((σ t) y) ∧
 inner ℂ (U y) ((τ t) x)=inner ℂ y ((σ t) (U.adjoint x)):= by
 constructor
 · rw [← ContinuousLinearMap.comp_apply,← h,ContinuousLinearMap.comp_apply,ContinuousLinearMap.adjoint_inner_left] -- tune
 rw [show concern P f t = (concern P f (-t)).adjoint from (by rw [replay P f m,neg_neg]), show concern Q g t=(concern Q g (-t)).adjoint from by rw [replay Q g n,neg_neg],ContinuousLinearMap.adjoint_inner_right,ContinuousLinearMap.adjoint_inner_right]; rw [← ContinuousLinearMap.comp_apply,←h,ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right]
omit h n in
private lemma climb (x y:H)(t:ℝ): charFun (κ (x+y)) t-charFun (κ (x-y)) t=2* (inner ℂ x ((σ t) y)+inner ℂ y ((σ t) x)):=by
 simp only [plays P f m,map_add,map_sub,inner_add_left,inner_add_right,inner_sub_left,inner_sub_right]; ring
private lemma belongs (x:D)(y:H): κ (U.adjoint x+y) + ℓ (x-U y) = ℓ (x+U y) + κ (U.adjoint x-y):=by
 apply Measure.ext_of_charFun; funext t; rw [plus,plus]; -- use Abelian not linarith
 have e:= climb P f m (U.adjoint x) y t
 have v:= climb Q g n x (U y) t -- omit h n above!
 rw [(pillars P Q U f g m n h t x y).1,(pillars P Q U f g m n h t x y).2] at v; linear_combination e - v
omit h n in
private lemma exam (q:ℝ→ℂ)(b:Tag q)(x y:H):
 (∫ p,q p∂κ (x+y))-(∫ p,q p∂κ (x-y))= 2*(inner ℂ x ((R q) y)+inner ℂ y ((R q) x)):=by
 unfold pushed; simp_rw [integral_map m.aemeasurable b.meas.aestronglyMeasurable]
 simp_rw [show ∀ x:H,(∫ p, q (f p)∂𝔪 x)=inner ℂ x ((R q) x) from fun x=> (order_reads _ (b.port f m)).awakes x |>.symm]; -- rw maybe repeat
 simp only [map_add,map_sub,inner_add_right,inner_add_left,inner_sub_left,inner_sub_right]; ring -- tune
private lemma portTrig (q:ℝ→ℂ)(e:Tag q)(x:D)(y:H): inner ℂ (U.adjoint x) ((R q) y)+inner ℂ y ((R q) (U.adjoint x))=inner ℂ x ((S q) (U y))+inner ℂ (U y) ((S q) x) := by
 have hp:=congrArg (fun t:Measure ℝ=> ∫ p,q p∂t) (belongs P Q U f g m n h x y)
 rw [integral_add_measure (fare q e _) (fare q e _), integral_add_measure (fare q e _) (fare q e _)] at hp
 have hM:= exam P f m q e (U.adjoint x) y; have hv:= exam Q g n q e x (U y)
 linear_combination - (hM-hv-hp)/2 -- tune sign
lemma ballot (q:ℝ→ℂ)(e:Tag q) : U.comp (order P (q ∘ f))=(order Q (q ∘ g)).comp U := by
 ext1 x; apply ext_inner_left ℂ; intro y; let l:=q
 change inner ℂ y (U ((R q) x)) = _; rw [← ContinuousLinearMap.adjoint_inner_left]
 have ht:= portTrig P Q U f g m n h q e y x; have hp:= portTrig P Q U f g m n h q e y (Complex.I • x); rw [map_smul,map_smul,map_smul] at hp
 simp only [inner_smul_left,inner_smul_right,Complex.conj_I] at hp
 rw [ContinuousLinearMap.comp_apply]; linear_combination (norm := (ring_nf; simp)) (ht- Complex.I * hp)/2 -- sign
end travels
lemma exp_comm {K:Hilbert} {A:K.Op} {V:K→L[ℂ]H} {B:H.Op} (h:V.comp A=B.comp V): V.comp (NormedSpace.exp A)=(NormedSpace.exp B).comp V:= by
 have hp(n:ℕ): V.comp (A^n)=(B^n).comp V:= by
   induction n with
   | zero =>rw [pow_zero,pow_zero]; ext1; rfl
   | succ n ih=> rw [pow_succ,pow_succ]; change V.comp ((A^n).comp A)= ((B^n).comp B).comp V; rw [← ContinuousLinearMap.comp_assoc, ih,ContinuousLinearMap.comp_assoc,h,← ContinuousLinearMap.comp_assoc]
 ext1 x; let F:=V.comp (ContinuousLinearMap.apply ℂ K x); let G:=ContinuousLinearMap.apply ℂ H (V x)
 let q(n:ℕ):ℂ := (n.factorial:ℂ)⁻¹; let a n:= q n • A^n; let b n:= q n • B^n
 have he: F ∘ a= G ∘ b:= funext fun i=> by unfold comp a b; rw [map_smul,map_smul]; congr 1; exact DFunLike.congr_fun (hp i) _
 apply HasSum.unique (f:=F ∘ a) (F.hasSum (NormedSpace.exp_series_hasSum_exp' (𝕂:=ℂ) A)); rw [he]; exact G.hasSum (NormedSpace.exp_series_hasSum_exp' (𝕂:=ℂ) B)
lemma bounded_flow (p:Tag f){A:H.Op}(h:Registers P (fun x=>(f x:ℂ)) A) (t:ℝ): concern P f t=NormedSpace.exp (((t:ℂ)*Complex.I) • A):=by
 apply (current P f p.meas t).single
 convert (h.scale ((t:ℂ)*Complex.I)).money using 1
 funext x; unfold sound; change Complex.exp _ =Complex.exp (_*_); dsimp only [Function.comp_apply,sound]; congr 1; ring
include m n
lemma compare_at (α:Tag f)(β:Tag g){A:H.Op}{B:D.Op}(p:Registers P (fun x=>(f x:ℂ)) A)(q:Registers Q (fun x=>(g x:ℂ)) B)
    (w:U.comp A=B.comp U) (r:ℝ→ℂ)(h:Tag r): U.comp (order P (r ∘ f))=(order Q (r ∘ g)).comp U:= by
 apply ballot _ _ _ _ _ m n ?_ r h; intro t; rw [bounded_flow _ _ α p,bounded_flow _ _ β q]
 apply exp_comm; rw [ContinuousLinearMap.comp_smul,w,ContinuousLinearMap.smul_comp]
end YM.Multiplier
