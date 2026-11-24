import YM.SU5.Selected.Hill.Ice
import YM.SectorTools.PHYSICAL_GAUSSIAN_SWITCH.Kernel
/-! Counting cost over exposed coordinates, with affine shift. -/
set_option autoImplicit false
noncomputable section
namespace YM.Hill.Luge
open Function Filter Finset Lattice Tree Wilson RG Pressure MeasureTheory Chene Trunk Matrix Calculus Next.SectorChange Next.SectorChange.Gaussian SectorTools.PhysicalGaussianSwitch
open scoped Topology BigOperators Classical MatrixOrder Matrix InnerProductSpace NNReal
variable {G:Gauge}{I J:Type}[Fintype I][Fintype J][DecidableEq I][DecidableEq J]
variable {b:ℝ} {D: Matrix I I ℝ}{Q: Matrix J J ℝ}
-- one center (actually takes dot represented linear term)
lemma Hotels (p:Q.PosSemidef)(f:I→ J)(e:D=Q.submatrix f f)(u:D.PosDef)(w:J→ℝ): ∃ v:I→ℝ,∀ x:I→ℝ,quad D (x-v) ≤ quad Q (w+expand f x):=by
 let B:= Pad.walk f -- open?
 let g:=(B*ᵥ (Q*ᵥ w)); let v:=D⁻¹*ᵥ (-g)
 have hv:D*ᵥ v= -g:=by unfold v; rw [mulVec_mulVec, mul_nonsing_inv _ (IsUnit.mk0 _ u.det_pos.ne'),one_mulVec]
 have hz:Q.IsSymm:= isHermitian_iff_isSymm.mp p.isHermitian; have hf(x:I→ℝ):quad Q (expand f x)=quad D x:=by unfold quad; rw [e, expansion]
 have he(x:I→ℝ): quad Q (w+expand f x)= quad D (x-v)+ (quad Q w-quad D v):=by
    have hp: dotProduct w (Q*ᵥ expand f x)= x ⬝ᵥ g:=by
       rw [SectorTools.PhysicalGaussianSwitch.turn hz]; unfold expand; rw [mulVec_transpose,← Matrix.dotProduct_mulVec] -- tune
    rw [quad_add hz,hf,hp,quad_sub (symm_pos u),hv,dotProduct_neg]; ring
 have hx:=p.dotProduct_mulVec_nonneg (w+expand f v); rw [star_trivial] at hx; change 0 ≤ quad Q _ at hx; rw [he,sub_self, show quad D 0=0 from (by unfold quad; simp),zero_add] at hx; exact ⟨v,fun x=> by rw [he x]; exact le_add_of_nonneg_right hx⟩
lemma coaty (p:D.PosDef)(h:0<b): coat (b • D)⁻¹=(Real.sqrt (2*Real.pi* (coupling b)^2))^Fintype.card I / Real.sqrt D.det:=by
 have he:=p.det_pos; unfold coat dome; rw [Matrix.det_nonsing_inv]; -- inv? Non side
 rw [Matrix.det_smul]; have hp:0 < b^Fintype.card I:=pow_pos h _; have hk:= Real.pi_pos
 rw [Ring.inverse_eq_inv,Real.sqrt_inv,Real.sqrt_mul hp.le,Real.sqrt_mul (by positivity : 0 ≤ 2 * Real.pi),Real.sqrt_sq (coupling_pos h).le,show Real.sqrt (b ^ Fintype.card I) = (Real.sqrt b)^Fintype.card I from (by rw [Real.sqrt_eq_iff_eq_sq (by positivity) (by positivity), ← pow_mul, Nat.mul_comm, pow_mul,Real.sq_sqrt h.le])]; unfold coupling; rw [mul_pow, inv_pow, _root_.mul_inv_rev]; ring_nf -- tune mul_inv
lemma exp_integral (p:D.PosDef)(h:0<b)(x:I→ℝ) : let f(y:I→ℝ):= Real.exp (-b*quad D (y-x)/2); Integrable f ∧ (∫ y,f y)= (Real.sqrt (2*Real.pi*(coupling b)^2))^Fintype.card I / Real.sqrt D.det := by
 intro f; let g:= kernel (b • D) 0; have hp:f=fun y=>g ((-x)+y):=by funext y; unfold f g kernel exponent; rw [quad_smul, zero_dotProduct,zero_sub,sub_eq_neg_add y]; ring_nf
 have he : (b • D).PosDef:=p.smul h; obtain ⟨ht,hv⟩:= kernel_paid he 0; rw [show quad (b • D)⁻¹ 0=0 from (by unfold quad; simp),zero_div,Real.exp_zero,mul_one] at hv
 let e:= MeasurableEquiv.addLeft (-x); have hE:MeasurePreserving e volume volume:=measurePreserving_add_left ..; rw [hp,integral_add_left_eq_self,←coaty p h]; exact ⟨(hE.integrable_comp_emb e.measurableEmbedding).mpr ht,hv⟩
lemma accounts (K:Precision.ChartRatio G)(p:0<K.scale)(I:Type)[Fintype I](h:0<b){D:ℝ}(f:ℝ) : (K.scale*Real.exp f)^Fintype.card I*((Real.sqrt (2*Real.pi*(coupling b)^2))^Fintype.card (Pens G I) / Real.sqrt D) =
 Real.exp ((Fintype.card I:ℝ)*f)*(spare K b)^Fintype.card I /(Real.sqrt D):=by
 unfold spare Pens; rw [Fintype.card_prod, pow_mul',Real.exp_nat_mul,mul_pow,mul_pow]; ring
end YM.Hill.Luge
#print axioms YM.Hill.Luge.Hotels
#print axioms YM.Hill.Luge.exp_integral
