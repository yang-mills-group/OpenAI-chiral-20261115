import YM.SU5.Reconstruction.Cone.Pressure
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Moat
open Function Set Filter MeasureTheory Measure InnerProductSpace Spectral OS Semigroup ConePrice
open scoped BigOperators NNReal ENNReal Topology InnerProductSpace ComplexOrder
variable {H : Hilbert} {a : Axis} (S : OS.Semigroup H a)
local notation "P" => S.ℚmeasure
local notation "𝔪" x:max => S.ℚmeasure.diagonal x
local notation "D" p:max t:max => Real.exp (-(p a)*(t:ℝ))
private lemma fare {x : Cross a} {t : ℝ≥0} (h:0<t) (p:E4) (v:p∈front a) : 2*(amplitude (0:Cross a) (t+t) p-amplitude x (t+t) p) ≤ (‖x‖ / (t:ℝ))^2:=by
 set w:= inner ℝ (SEP a p) x
 have ht:0<(t:ℝ):=h
 have u : 0 ≤ p a := (norm_nonneg _).trans v
 have e : |w| ≤ p a * ‖x‖:= (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right v (norm_nonneg _))
 have k:p a*(D p t) ≤ 1/(t:ℝ) := by
   rw [le_div_iff₀ ht]
   have hp:= exp_board (mul_nonneg u ht.le); rw [←neg_mul] at hp
   have hh:=Real.exp_pos (-(p a)*(t:ℝ)); calc
        _ = (p a*(t:ℝ))*(D p t):=by ring
        _ ≤ 1- D p t:=hp
        _ ≤ 1:=by linarith
 have f : |w| * D p t ≤ ‖x‖ / (t:ℝ):= calc
      _ ≤ (p a*‖x‖) * D p t:=by gcongr
      _ = (p a * D p t) * ‖x‖:=by ring
      _ ≤ 1/(t:ℝ)* ‖x‖:=by gcongr
      _ = _:=by ring
 calc
    _ = 2*(1-Real.cos w)*(D p t)^2:=by rw [amp_time,amplitude,cone_mean,NNReal.coe_add,mul_add,Real.exp_add]; ring
    _ ≤ w^2*(D p t)^2:= mul_le_mul_of_nonneg_right (by linarith [Real.one_sub_sq_div_two_le_cos (x:=w)]) (sq_nonneg _)
    _ ≤ _ := by rw [← sq_abs w,← mul_pow]; exact pow_le_pow_left₀ (by positivity) f _

lemma premiere (p:Forward S) (x:Cross a)(t:ℝ≥0)(ht:0<t) : ‖(1-S.U x)*S.E t‖ ≤ ‖x‖ / (t:ℝ) := by
 apply ContinuousLinearMap.opNorm_le_bound _ (by positivity); intro z
 change ‖(1-S.U x) (S.E t z)‖ ≤ _
 rw [_root_.sub_apply]; apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
 set M:= (‖x‖/(t:ℝ))^2 with e
 have hv : Integrable (fun p:E4=> amplitude (a:=a) 0 (t+t) p - amplitude x (t+t) p) (𝔪 z) := (amp_can S z (t+t) 0).sub (amp_can S z (t+t) x)
 rw [show (1:H.Op) (S.E t z)=S.E t z from rfl]
 calc
    _ = ∫ p, 2*(amplitude (a:=a) 0 (t+t) p-amplitude x (t+t) p) ∂𝔪 z := by
       rw [integral_const_mul,integral_sub (amp_can ..) (amp_can ..),norm_sub_sq (𝕜:=ℂ),S.unitary]; rw [← heat_norm,← cross_heat]; change _- (2:ℝ)*(inner ℂ _ _).re+_=_; ring
    _ ≤ ∫ _:E4, M ∂𝔪 z:= integral_mono_ae (hv.const_mul _) (integrable_const _) ((forward_ae S z p).mono fun y v=>fare ht y v)
    _ = _ := by rw [integral_const,all_norm,smul_eq_mul,e,mul_pow]; ring

-- real shifter formula; milk TWO powers.
lemma comm_UE (x:Cross a)(t:ℝ≥0): Commute (1-S.U x) (S.E t) := (Commute.one_left _).sub_left (S.independent _ _).symm
private lemma opReal (u:Cross a): ‖S.U u‖ ≤ 1:= ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x=> (S.unitary ..).trans_le (by simp only [one_mul,le_refl])
private lemma uAdd (x y:Cross a): S.U (x+y) = S.U x*S.U y:= S.space ..
lemma uDrop (x y:Cross a): S.U (x-y)= S.U x*S.U (-y):=by rw [sub_eq_add_neg]; exact uAdd ..

def four (x y z:Cross a)(t:ℝ≥0) := ((S.U x - S.U (x+y)) + S.U (x+z+y) - S.U (x+z))* S.E t
lemma four_knobs (p:Forward S) (t b:ℝ≥0)(h:0<b)(w:b+b≤t) (x y z:Cross a): ‖four S x y z t‖ ≤ (‖y‖ / (b:ℝ)) * (‖z‖ / (b:ℝ)):= by
 let K(q : Cross a) := (1-S.U q)*S.E b
 have h₀:four S x y z t=S.U x*(K y*K z)*S.E (t-(b+b)):= by
     unfold four K
     rw [add_right_comm x z y]
     simp_rw [uAdd]
     conv_lhs => rhs; rw [← add_tsub_cancel_of_le w]
     have g:= (comm_UE S z b).symm.eq
     rw [mul_assoc (1-S.U y), ← mul_assoc (S.E b), g,S.time,S.time]
     change _ *(S.E _ * S.E _ * S.E _)=_
     noncomm_ring
 -- rightmost e bound
 rw [h₀]; exact (norm_mul_le ..).trans ((mul_le_mul ((norm_mul_le ..).trans (mul_le_mul (opReal S x) ((norm_mul_le ..).trans (mul_le_mul (premiere S p y b h) (premiere S p z b h) (norm_nonneg _) (by positivity))) (norm_nonneg _) zero_le_one)) (S.shrinks _) (norm_nonneg _) (by positivity)).trans_eq (by ring))
lemma ticket_bound (x: Cross a)(t:ℝ≥0)(y:H): ‖S.U x (S.E t y)‖ ≤ ‖y‖:=by rw [S.unitary]; exact ((S.E t).le_opNorm _).trans (mul_le_of_le_one_left (norm_nonneg _) (S.shrinks t))
end YM.Moat
