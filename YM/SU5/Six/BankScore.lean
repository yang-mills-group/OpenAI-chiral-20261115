import YM.SU5.Cordial.Balloon
import YM.SU5.Cheer.Chapel
set_option autoImplicit false
set_option maxRecDepth 2000
set_option synthInstance.maxSize 28000
set_option quotPrecheck false
noncomputable section
namespace YM.Score
open OS OS.Semigroup OS.Semigroup.Balloon Boundary Boundary.Probe Spectral
open Function Filter Set Metric MeasureTheory InnerProductSpace
open scoped Topology InnerProductSpace BigOperators Classical NNReal ENNReal ComplexOrder
/-!
# Energy projectors in the continuum experiment, normalization and matrix entries

Use a vector spectral integration argument (in finite diagonal measures) not
any smoothness of the regulator. Only spatial *selected* continuous sector.
No operator-norm smoothness of translation group assumed. Dispatch with
`Spine.seasons`. Time axis last.
-/
variable (X:Hilbert)
section
variable {E:Type}[MeasurableSpace E](P:PVM X E)
local notation "μ"=> P.diagonal
local notation "Γ"=> P.region
variable {s:Set E}(p:MeasurableSet s)
include p
lemma bill_in_zone (x:X) : μ (Γ s x)=(μ x).restrict s:= by
 ext a g; rw [Measure.restrict_apply g]
 apply ENNReal.toReal_eq_toReal_iff' (measure_ne_top (μ (Γ s x)) _) (measure_ne_top (μ x) _) |>.1
 change (μ (Γ s x)).real a=(μ x).real (a∩s)
 rw [P.same g,P.same (g.inter p),← ContinuousLinearMap.comp_apply,P.joins g p]
lemma orth_price (x y:X) (a:Γ s x=x)(b:Γ s y=0):inner ℂ x y=0:= by
 rw [← a,← ContinuousLinearMap.adjoint_inner_right,P.real p,b,inner_zero_right]
lemma below (x:X): ‖Γ s x‖^2 ≤ ‖x‖^2:= by
 rw [← P.same p x]; have hx : (μ x).real Set.univ=‖x‖^2:= by rw [P.same MeasurableSet.univ,P.all]; rfl
 rw [←hx]; exact measureReal_mono (Set.subset_univ _)
lemma orth_diagonal {x y:X}(a:Γ s x=x)(b:Γ s y=0) : μ (x+y)= μ x+μ y:= by
 ext t h
 apply ENNReal.toReal_eq_toReal_iff' (measure_ne_top (μ (x+y)) _) (measure_ne_top (μ x+μ y) _) |>.1
 rw [Measure.add_apply, ENNReal.toReal_add (measure_ne_top (μ x) _) (measure_ne_top (μ y) _)]
 change (μ _).real t= (μ x).real t+(μ y).real t
 have he:(Γ s).comp (Γ t)= (Γ t).comp (Γ s):= by rw [P.joins p h,P.joins h p, inter_comm]
 rw [P.same h,P.same h,P.same h,map_add,norm_add_sq (𝕜:=ℂ),orth_price X P p (Γ t x) (Γ t y)]
 · simp
 · rw [←ContinuousLinearMap.comp_apply,he,ContinuousLinearMap.comp_apply,a]
 rw [←ContinuousLinearMap.comp_apply,he,ContinuousLinearMap.comp_apply,b,map_zero]
lemma project_bill (T:X.Op) (f:E→ℂ)(h:∀ x:X, Integrable f (μ x)) (u:∀ x:X,inner ℂ x (T x)=∫ p,f p∂μ x) (x:X) :
    Γ s (T x)=T (Γ s x):= by
 let Q:=Γ s
 have hr (x z:X): inner ℂ x (Q z)=inner ℂ (Q x) z:=by rw [←ContinuousLinearMap.adjoint_inner_right Q, P.real p] -- direction
 have hx(z:X) : Q (z-Q z)=0:=by rw [map_sub,P.idempotent p,sub_self]
 have hv(z:X) : Q (Q z)=Q z:= P.idempotent p z
 have hf {y z:X}(hy:Q y=y)(hz:Q z=0):inner ℂ y (T z)+inner ℂ z (T y)=0:= by
   have H': inner ℂ (y+z) (T (y+z))=inner ℂ y (T y)+inner ℂ z (T z):=by rw [u,u,u,orth_diagonal X P p hy hz, integral_add_measure (h y) (h z)]
   rw [map_add,inner_add_left,inner_add_right,inner_add_right] at H'
   calc _= inner ℂ y (T y)+inner ℂ y (T z)+(inner ℂ z (T y)+inner ℂ z (T z))-(inner ℂ y (T y)+inner ℂ z (T z)):=by abel
        _=0:=by rw [H']; ring
 have he {y z:X}(hy:Q y=y)(hz:Q z=0):inner ℂ y (T z)=0∧inner ℂ z (T y)=0:=by
   let a:= inner ℂ y (T z); let b:=inner ℂ z (T y)
   have ho:a+b=0:= hf hy hz
   have hk:=hf hy (show Q (Complex.I • z)=0 by rw [map_smul,hz,smul_zero]); rw [map_smul,inner_smul_left,inner_smul_right,Complex.conj_I] at hk
   have hh:a-b=0:= (mul_eq_zero.mp (show Complex.I*(a-b)=0 from by rw [mul_sub, sub_eq_add_neg, ← neg_mul]; exact hk)).resolve_left Complex.I_ne_zero
   have ht:(2:ℂ)*a=0:=by rw [two_mul]; exact (congrArg (fun z=>a+z) (sub_eq_zero.mp hh)).trans ho
   have t:a=0:=(mul_eq_zero.mp ht).resolve_left (by norm_num)
   exact ⟨t,by change b=0; rw [t,zero_add] at ho; exact ho⟩
 apply ext_inner_left ℂ; intro w
 have hQ:inner ℂ (Q w) (T (x-Q x))=0:=(he (hv w) (hx x)).1
 have ht:inner ℂ (w-Q w) (T (Q x))=0:=(he (hv x) (hx w)).2
 rw [map_sub,inner_sub_right] at hQ; rw [inner_sub_left] at ht
 exact (hr w _).trans ((sub_eq_zero.mp hQ).trans (sub_eq_zero.mp ht).symm)
end

-- Semigroup laplace transform, unreconstructed projections
abbrev Clock:= Cross (3:Axis)
def lens (v:Clock)(t:ℝ≥0)(p:E4):ℂ:= plane p v.val * (tinct (3:Axis) t p:ℂ)
lemma lens_norm (p:E4)(h:0≤time p)(v:Clock)(t:ℝ≥0): ‖lens v t p‖≤1:= by
 rw [lens,norm_mul,plane_norm,one_mul,Complex.norm_real,Real.norm_of_nonneg (show 0 ≤ tinct (3:Axis) t p from Real.exp_pos _|>.le)]
 exact fuel t p h
lemma lens_identity(t:ℝ≥0)(v:Clock)(p:E4): lens v t p=lens v 0 p*lens 0 t p:= by
 simp [lens, tinct]
lemma lens_neg (v:Clock)(t:ℝ≥0)(p:E4): starRingEnd ℂ (lens v t p)= lens (-v) t p:= by
 rw [lens,map_mul,Complex.conj_ofReal]; rw [lens,NegMemClass.coe_neg,plane_inverse]; rfl
lemma lens_add (v w:Clock)(t u:ℝ≥0)(p:E4): lens (v+w) (t+u) p=lens v t p*lens w u p:= by simp_rw [lens,tint_add,Complex.ofReal_mul,AddMemClass.coe_add,plane_add]; ring
@[fun_prop] lemma lens_cont : Continuous (fun p:E4 × Clock × ℝ≥0=>lens p.2.1 p.2.2 p.1):= by unfold lens plane tinct; fun_prop
variable (S:OS.Semigroup X (3:Axis))
local notation "μ"=> S.ℚmeasure.diagonal
local notation "Γ"=> S.ℚmeasure.region
lemma plane_ready (v:Clock)(t:ℝ≥0)(x:X) : Integrable (lens v t) (μ x) := by
 apply Integrable.mono' (integrable_const («μ»:=μ x) (1:ℝ)) ((lens_cont.comp (continuous_id.prodMk (continuous_const (y:=(v,t))))).aestronglyMeasurable)
 exact (S.bright x).mono (fun i u=>lens_norm i u _ _)
variable {W:Set E4}(h:MeasurableSet W)
include h
lemma inside_lens (t:ℝ≥0)(v:Clock)(x:X): Γ W (S.U v (S.E t x))= S.U v (S.E t (Γ W x)):= project_bill X S.ℚmeasure h ((S.U v).comp (S.E t)) (lens v t) (plane_ready X S v t) (during S t v) x
lemma coolLens (x:X)(t:ℝ≥0): Γ W (S.E t x)= S.E t (Γ W x):= by
 have he:=inside_lens X S h t 0 x
 simpa only [S.uZero,ContinuousLinearMap.id_apply] using he
omit h
local notation "Z₀"=> {p:E4|time p=0}
lemma drops_vac (t:ℝ≥0)(x:X) : Γ Z₀ (x-S.E t x)=0:= by
 have ht:MeasurableSet Z₀:=by exact (Mink.clock_cont.measurable) (measurableSet_singleton _)
 let y:=Γ Z₀ x
 have he:∀ᵐ p∂μ y, time p=0:=by rw [show μ y=(μ x).restrict Z₀ from bill_in_zone X S.ℚmeasure ht x]; exact ae_restrict_mem ht
 rw [map_sub,coolLens X S ht x t]
 have hx: y=S.E 0 y:=by rw [S.eZero]; rfl
 have hv : ‖S.E 0 y-S.E t y‖^2=0:=by
    rw [distanceE]; apply integral_eq_zero_of_ae
    filter_upwards [he] with i g; change i (3:Axis)=0 at g; simp [tinct,g]
 exact sub_eq_zero.mpr (hx.trans (sub_eq_zero.mp (norm_eq_zero.mp (eq_zero_of_pow_eq_zero hv))))

-- matrix-element needed under Bochner integral: mix one *continuous motion* and strictly heated subtractions. Valid at any spectra diagonal.
private lemma slides (u v:Clock)(a b:ℝ≥0)(x:X): inner ℂ (S.U u (S.E a x)) (S.U v (S.E b x)) = ∫ p,lens (-u+v) (a+b) p∂μ x:= by
 let Y:= (show X.space →ₗᵢ[ℂ] X.space from { (S.U u).toLinearMap with norm_map':= S.unitary u })
 let y:= S.U (-u+v) (S.E b x); have he:Y y=S.U v (S.E b x):= DFunLike.congr_fun ((S.space u (-u+v)).symm.trans (congrArg S.U (add_neg_cancel_left ..))) _
 have H': (S.E a) y=S.U (-u+v) (S.E (a+b) x):=by rw [S.time]; exact DFunLike.congr_fun (S.independent a (-u+v)) (S.E b x)
 exact ((congrArg (inner ℂ (Y (S.E a x))) he.symm).trans (Y.inner_map_map _ y)).trans ((S.swing ..).trans ((congrArg (inner ℂ x) H').trans (during S _ _ _)))
local notation "ι" u:max t:max d:max p:max=> lens u t p-lens u (t+d) p
def vote (u:Clock)(t d:ℝ≥0)(p:E4):ℂ:= lens u t p-lens u (t+d) p
-- spectrally entire multipliers not needed. bounded on half-space
lemma vote_norm (u:Clock)(t d:ℝ≥0)(p:E4)(h:0 ≤ time p): ‖vote u t d p‖≤2:= (norm_sub_le ..|>.trans (add_le_add (lens_norm p h ..) (lens_norm p h ..))).trans (by norm_num)
lemma mix (u v:Clock)(a b c:ℝ≥0)(x:X):
    let y:= x-S.E c x
    inner ℂ (S.U u (S.E a y)) (S.U v (S.E b y))= ∫ p, starRingEnd ℂ (vote u a c p)*vote v b c p∂μ x := by
 intro y
 have e(u:Clock)(a:ℝ≥0):S.U u (S.E a y)= S.U u (S.E a x)-S.U u (S.E (a+c) x):=by rw [S.time,show y=_ from rfl,map_sub,map_sub]; rfl -- shape
 rw [e,e,inner_sub_left,inner_sub_right,inner_sub_right]; simp_rw [slides X S]
 let m:= -u+v; let L:= lens m; have pQ(t:ℝ≥0): Integrable (L t) (μ x):= plane_ready X S ..
 apply Eq.trans (b:=∫ p,(L (a+b)-L (a+(b+c))-(L (a+c+b)-L (a+c+(b+c)))) p ∂μ x) (?_)
 · apply integral_congr_ae (Eventually.of_forall (fun p=>?_))
   simp only [vote,map_sub,Pi.sub_apply,L,m,lens_neg,show ∀ t b:ℝ≥0,lens (-u+v) (t+b) p=lens (-u) t p*lens v b p from fun a b=>lens_add ..]; ring
 rw [integral_sub' ((pQ _).sub (pQ _)) ((pQ _).sub (pQ _)),integral_sub' (pQ _) (pQ _),integral_sub' (pQ _) (pQ _)]
end YM.Score
