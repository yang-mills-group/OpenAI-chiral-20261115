import YM.SU5.Reconstruction.Trap.Counts
/-!
# actual spectral functional calculus.
-/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Multiplier
open Function Set Filter MeasureTheory Spectral Analysis
open scoped Topology NNReal ENNReal ComplexOrder InnerProductSpace
variable {X E : Type*} [MeasurableSpace X] {H : Hilbert} (P : PVM H X)
local notation "𝔪" x:max => P.diagonal x
lemma dots_norm {f:X→ℂ} {U:H.Op} (h: Registers P (star f*f) (star U*U)) (x:H):
    ‖U x‖^2 = ∫ p, ‖f p‖^2 ∂𝔪 x := by
 apply Complex.ofReal_injective
 have ht (p:X) : (star f*f) p=(‖f p‖^2:ℝ) := by change star (f p) * f p= _; rw [← mul_comm]; exact (Complex.mul_conj (f p)).trans (by rw [Complex.sq_norm])
 rw [← integral_complex_ofReal,← funext ht] -- tune wrong
 -- easier
 have he:= h.awakes x; change inner ℂ x (U.adjoint (U x)) = _ at he; rw [ContinuousLinearMap.adjoint_inner_right,inner_self_eq_norm_sq_to_K] at he
 push_cast; exact he
lemma dots_bill {f:X→ℂ} {U:H.Op} (h: Registers P (star f*f) (star U*U)) {c:ℝ} (p:0≤c) (b:∀ x, ‖f x‖≤ c) (x:H) :
    ‖U x‖ ≤ c*‖x‖ := by
 rw [← sq_le_sq₀ (norm_nonneg _) (by positivity),mul_pow]
 apply Eq.trans_le (dots_norm P h x)
 refine (integral_mono_of_nonneg (Eventually.of_forall fun y=> sq_nonneg _) (integrable_const (c^2)) (Eventually.of_forall (p:=fun x=> ‖f x‖^2 ≤ c^2) fun y=> pow_le_pow_left₀ (norm_nonneg _) (b y) _)).trans_eq ?_
 rw [integral_const,Registers.size]; exact mul_comm ..
namespace Registers
-- Evaluate on all simple functions individually.
open SimpleFunc
local notation "S" => SimpleFunc X ℂ
private lemma express (v:ℂ) {s : Set X} (p:MeasurableSet s) : ⇑(SimpleFunc.piecewise s p (const X v) (const X 0)) = v • (s.indicator (1:X→ℂ)):= by
 funext x; by_cases e:x∈s <;> simp [e,smul_eq_mul]
lemma paid (f : S) : ∃ U : H.Op, Registers P f U ∧ ∀ {s:Set X}, MeasurableSet s → Commute U (P.region s) := by
 induction f using SimpleFunc.induction with
 | const x p =>
   rename_i s
   rw [express]; refine ⟨_, (box P p).scale x,fun {t} ht=> Commute.smul_left ?_ x ⟩ -- tune
   change (P.region s).comp (P.region t) = (P.region t).comp (P.region s); rw [P.joins p ht,P.joins ht p,inter_comm]
 | @add f g _ h t =>
   obtain ⟨V,h,v⟩:=h; obtain ⟨W,t,u⟩:=t; exact ⟨V+W,h.add t,fun {s} hs=> (v hs).add_left (u hs) ⟩
open scoped Classical in
noncomputable def hit (f:S) : H.Op := (paid P f).choose
local notation "𝔅" => hit P
lemma records (f:S) : Registers P f (hit P f):=(paid P f).choose_spec.1
lemma launches (f:S) {s:Set X} (h:MeasurableSet s) : Commute (hit P f) (P.region s):=(paid P f).choose_spec.2 h
lemma masks {q:X→ℂ} {V : H.Op}(h:Registers P q V)(x:∀ {s}, MeasurableSet s→ Commute V (P.region s)) (f:S) : Registers P ((f:X→ℂ)*q) (hit P f * V) := by
 induction f using SimpleFunc.induction with
 | @const z s p =>
   rw [show hit P (SimpleFunc.piecewise s p _ _)=z • P.region s from (records P _).single (by rw [express]; exact (box P p).scale z),express,Algebra.smul_mul_assoc, Algebra.smul_mul_assoc]
   have hp: (s.indicator (1:X→ℂ)) * q=s.indicator q:= by funext x; by_cases e:x∈s<;>simp [e]
   rw [hp]; exact (mask h p (x p)).scale z
 | add _ v w =>
   rw [show ∀ f g, hit P (f+g)=hit P f+hit P g from fun f g=> (records P _).single ((records P _).add (records P _)), coe_add, add_mul, add_mul]; exact v.add w
lemma logs (f:S) : Registers P (star (f:X→ℂ)* f) (star (hit P f)*(𝔅 f)):=by
 let g:= f.map (starRingEnd ℂ)
 rw [show star (hit P f)=hit P g from single (V:=hit P g) ((records P f).adjoint) (records P g) ]
 exact masks _ (records P f) (fun {_} => launches P f) g
section strong
variable {ι : Type*} (A : ι→H.Op)
lemma extendS (l:Filter ι) [l.NeBot] (c:ℝ) (p:∀ i,∀ y, ‖A i y‖ ≤ c*‖y‖)(e:∀ y:H,∃ z:H,Tendsto (fun i=> A i y) l (𝓝 z)) : ∃ U : H.Op,∀ y:H,Tendsto (fun i=> A i y) l (𝓝 (U y)):= by
 choose f h using e
 let W : H→ₗ[ℂ]H := {
   toFun x:=f x
   map_add' x y:= by
     apply tendsto_nhds_unique (h (x+y)); simp_rw [_root_.map_add]; exact (h x).add (h y)
   map_smul' v x:= by
     apply tendsto_nhds_unique (h _); simp_rw [map_smul]; exact tendsto_const_nhds.smul (h x) }
 exact ⟨W.mkContinuous c (fun y=> le_of_tendsto (h y|>.norm) (Eventually.of_forall (fun i=>p i y))),h⟩
lemma onLimit (l:Filter ι) [l.NeBot] [l.IsCountablyGenerated] (f:ι→X→ℂ)(q:X→ℂ)(h:Tag q)
    (c:ℝ)(p:∀ᶠ i in l,∀ x, ‖f i x‖ ≤ c)(x:∀ y,Tendsto (fun i=> f i y) l (𝓝 (q y))) (r:∀ i,Registers P (f i) (A i))
    {U:H.Op} (t:∀ v:H,Tendsto (fun i=> A i v) l (𝓝 (U v))) : Registers P q U := by
 refine ⟨h,fun w=>?_⟩; apply tendsto_nhds_unique (l:=l) (f:=fun i=>∫ p,f i p∂P.diagonal w)
 · simp_rw [← awakes (r _) w]; exact tendsto_const_nhds.inner (t w)
 exact tendsto_integral_filter_of_dominated_convergence (fun _=> c) (Eventually.of_forall fun i=> (r i).price.meas.aestronglyMeasurable) (p.mono fun i h=> ae_of_all _ h) (integrable_const _) (Eventually.of_forall x)
end strong
variable (f : ℕ→SimpleFunc X ℂ) (U:X→ℂ)(g:Tag U) (c:ℝ) (p:0≤c)(b:∀ i y, ‖f i y‖≤c)(h:∀ y,Tendsto (fun i=> f i y) atTop (𝓝 (U y)))
include h c b p
lemma reader : ∃ T : H.Op, ∀ x:H,Tendsto (fun i=> 𝔅 (f i) x) atTop (𝓝 (T x)) := by
 apply extendS _ _ c (fun i=> dots_bill P (logs P (f i)) p (b i))
 intro x; apply cauchySeq_tendsto_of_complete; apply Metric.cauchySeq_iff'.mpr
 let q(i:ℕ×ℕ) := f i.1-f i.2
 have bd:Tendsto (fun i:ℕ×ℕ=>∫ p, ‖q i p‖^2∂𝔪 x) atTop (𝓝 0):= by
   have he:= tendsto_integral_filter_of_dominated_convergence (F:=fun (i:ℕ×ℕ) y => ‖q i y‖^2) (l:=atTop) (μ:=𝔪 x) (f:=fun _=>0) (fun _=> (c+c)^2) (Eventually.of_forall (fun i=> ((measurable_norm.comp (q i).measurable).pow_const _).aestronglyMeasurable)) (Eventually.of_forall (fun i=>(Eventually.of_forall fun y=> show ‖‖q i y‖^2‖ ≤ (c+c)^2 from by rw [Real.norm_of_nonneg (by positivity)]; exact pow_le_pow_left₀ (norm_nonneg _) ((norm_sub_le ..).trans (add_le_add (b i.1 y) (b i.2 y))) _))) (integrable_const _) (Eventually.of_forall fun y=> ?_)
   · simpa using he
   · have ht:= (((h y).comp (show Tendsto (Prod.fst (α:=ℕ) (β:=ℕ)) atTop atTop from by rw [←prod_atTop_atTop_eq]; exact tendsto_fst)).sub ((h y).comp (show Tendsto (Prod.snd (α:=ℕ) (β:=ℕ)) atTop atTop from by rw [←prod_atTop_atTop_eq]; exact tendsto_snd))); simpa [Function.comp_def,q] using ht.norm.pow 2
 intro ε e; obtain ⟨r,k⟩:= eventually_atTop.mp (bd.eventually (Iio_mem_nhds (show (0:ℝ)<ε^2 from by positivity)))
 refine ⟨r.1+r.2,fun u hu=>?_⟩
 let w:=r.1+r.2
 rw [dist_eq_norm]
 have ht:= dots_norm P (logs P (q (u,w))) x
 rw [show hit P (q (u,w)) = hit P (f u)-hit P (f w) from (records P _).single ((records P _).sub (records P _)), _root_.sub_apply] at ht
 apply (sq_lt_sq₀ (norm_nonneg _) e.le).1; exact lt_of_le_of_lt ht.le (k (u,w) ⟨by simp [hu.trans' (Nat.le_add_right r.1 r.2)],by unfold w; exact Nat.le_add_left ..⟩)
end Registers
lemma find (q:X→ℂ)(h:Tag q): ∃ U:H.Op, Registers P q U ∧ ∀ {s}, MeasurableSet s → Commute U (P.region s) := by
 let f(n):= SimpleFunc.approxOn q h.meas univ 0 (mem_univ _) n
 have hv(x:X) : Tendsto (fun n=> f n x) atTop (𝓝 (q x)):= SimpleFunc.tendsto_approxOn h.meas (s:=Set.univ) (h₀:=mem_univ _) (by simp)
 obtain ⟨c,p,b⟩:= h.bound
 have hu (i x) : ‖f i x‖ ≤ c+c := (SimpleFunc.norm_approxOn_zero_le _ _ _ _).trans (add_le_add (b x) (b x))
 let A(n) := Registers.hit P (f n)
 obtain ⟨U,t⟩:= Registers.reader P f q (c+c) (add_nonneg p p) hu hv
 refine ⟨U,Registers.onLimit P A _ (fun n x=> f n x) q h (c+c) (Eventually.of_forall hu) hv (fun i=> Registers.records P _) t,?_⟩
 intro s hs; ext1 x; apply tendsto_nhds_unique (a:=U _) (t _); refine (((P.region s).continuous.tendsto _).comp (t x)).congr fun n=>?_ -- congr order
 exact (DFunLike.congr_fun (Registers.launches P (f n) hs).eq x).symm
end YM.Multiplier
