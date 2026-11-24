import YM.SU5.Reconstruction.Trap.Lantern
/-!
# Looking after vacuum. Opposite quadrants, because want modular as well.
-/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Picket
open Function Set Filter MeasureTheory Spectral Analysis Metric
open scoped Topology NNReal ENNReal ComplexOrder InnerProductSpace
open YM.Multiplier Chirp CrossedFrame OS Semigroup Boundary Probe Real
variable {H D K:Hilbert}
variable (C:Clasp K H D)
lemma valued {x:ℝ}{T:K.Op}(p:0 ≤T)(e:0<x)(v:K)(b:T (T v)=( (x*x:ℝ):ℂ) • v): T v=(x:ℂ) • v:=by
 let u:= T v-(x:ℂ) • v
 have hu: T u= -(x:ℂ) • u:=by unfold u; rw [map_sub,map_smul,b, Complex.ofReal_mul, mul_smul,neg_smul, smul_sub]; abel
 have hp : 0 ≤ (inner ℂ (T u) u).re := ((ContinuousLinearMap.nonneg_iff_isPositive _).1 p).re_inner_nonneg_left _
 rw [hu,inner_smul_left, map_neg, Complex.conj_ofReal, inner_self_eq_norm_sq_to_K] at hp; simp [Complex.mul_re] at hp
 apply sub_eq_zero.mp; apply norm_eq_zero.mp; change ‖u‖=0; rw [← Complex.ofReal_pow,Complex.ofReal_re] at hp; exact le_antisymm (le_of_not_gt (fun h=> (mul_pos e (pow_pos h 2)).not_ge hp)) (norm_nonneg u)
-- alternative via multiplier compare and 1D subalgebra frequency, avoid integral D approximation
lemma logOne (x:K)(p:C.angle x=((1/2:ℝ):ℂ) • x)(z:ℝ) : boost C z (C.Left x)= C.Left x:= by
 let S:= (spectrum ℂ C.angle); let P:= C.motion; let q:S→ℝ:= fun _=> 1/2
 let V: K.Op:= ((1/2:ℝ):ℂ) • 1; let u:= -z/Real.pi; let T:= C.Cabin u; unfold boost Clasp.cLeft
 rw [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply,LinearIsometryEquiv.symm_apply_apply]; apply congrArg C.Left
 change T x=x
 -- zero of angle-1/2 implies AE p
 let w:= fun y:S=> ((C.realF y:ℝ):ℂ)-((1/2:ℝ):ℂ)
 have hp: Registers C.motion w (C.angle-V) := by
    convert C.angle_reads.sub ((Registers.one _).scale ((1/2:ℝ):ℂ)) using 1
    ext1 y; change _= ((C.realF y:ℝ):ℂ)-((1/2:ℝ):ℂ) • (1:ℂ); unfold w; simp [smul_eq_mul]
 have hv: (C.angle-V) x=0:=by rw [sub_apply, p]; unfold V; simp
 have hx:= hp.squareCost x; rw [hv,norm_zero] at hx; simp only [ne_eq,OfNat.ofNat_ne_zero,not_false_eq_true,zero_pow] at hx
 have t: ∀ᵐ y∂P.diagonal x,C.realF y=1/2:= by
    have h : ∀ᵐ y∂P.diagonal x, ‖w y‖^2=0:= (integral_eq_zero_iff_of_nonneg_ae (Eventually.of_forall fun y=> sq_nonneg _) ?_).mp hx.symm
    · filter_upwards [h] with y hy; change ‖w y‖^2=0 at hy; exact_mod_cast (sub_eq_zero.mp (show w y=0 from by simpa using hy) : (C.realF y:ℂ)= _)
    apply Tag.rent P _ x
    obtain ⟨c,v,d⟩:= hp.price.bound
    exact ⟨(measurable_norm.comp hp.price.meas).pow_const _,c^2, by positivity,fun y=> by rw [Real.norm_of_nonneg (by positivity)]; exact pow_le_pow_left₀ (norm_nonneg _) (d y) _⟩
 have hz := C.Cabin_reads u; apply sub_eq_zero.mp; change (C.Cabin u-1) x=0;
 apply inner_self_eq_zero (𝕜:=ℂ)|>.mp; rw [inner_self_eq_norm_sq_to_K]; change ((‖(C.Cabin u-1) x‖:ℝ):ℂ)^2=0; rw [← Complex.ofReal_pow, (hz.sub (Registers.one P)).squareCost]; have he : (Clasp.river u ∘ C.realF)-(1:spectrum ℂ C.angle→ℂ)=ᵐ[P.diagonal x] 0:= by
   filter_upwards [t] with y hy; simp [Clasp.river,hy]; norm_num [sing]
 rw [integral_congr_ae (g:=fun x=>0) (he.mono fun s hs=> by rw [hs]; simp), integral_zero, Complex.ofReal_zero]
lemma victory (a:H)(b:D)(h:C.Latch a b)(p:∀ x : K, inner ℂ a (C.l x)=inner ℂ b (C.r x)): C.look a=b ∧ ∀ x:ℝ,boost C x a=a:=by
 obtain ⟨x,rfl,rfl⟩:=h; let S:= C.angle
 let z:= (1/2:ℝ); let u:= Real.sqrt z; have b:u*u=1/2:= Real.mul_self_sqrt (by norm_num)
 have e:0<u:=by unfold u z; positivity
 have h:C.l.adjoint (C.l x)=C.r.adjoint (C.r x):=by apply ext_inner_right ℂ; intro y; rw [ContinuousLinearMap.adjoint_inner_left,ContinuousLinearMap.adjoint_inner_left,p]
 have hp: C.angle x=(z:ℂ) • x:=by
   have v:= C.calculation x; rw [← h,← two_smul ℂ] at v; nth_rw 2 [← v]; rw [smul_smul]; norm_num [z]; rfl -- `nth_rw` orientation
 have hv: peel C.l x=(u:ℂ) • x:=valued (positive_peel _) e x ?_ -- tune
 · have hg: peel C.r x=(u:ℂ) • x:= valued (positive_peel _) e x ?_
   · have ht:= C.left_done x; rw [hv,map_smul] at ht; have he:= C.right_done x; rw [hg,map_smul] at he; constructor
     · rw [←ht,←he,map_smul]; simp [Clasp.look]
     intro y; rw [←ht, map_smul, logOne C x hp]
   rw [b]; calc
     _= C.r.adjoint (C.r x) := DFunLike.congr_fun (peel_sq C.r) x
     _ = _:= h.symm.trans hp
 rw [b]
 calc
   _= C.l.adjoint (C.l x) := DFunLike.congr_fun (peel_sq C.l) x
   _ = _:= hp
end YM.Picket
