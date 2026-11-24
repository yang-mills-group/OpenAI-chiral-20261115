import YM.SU5.Reconstruction.Quartz.Zodiac
import YM.SU5.Reconstruction.Crease.Dance
/-!
# The operator billing test itself is angular

price on X at Earth, Y on other clock. State in the CP boost convention. Don't drop the
star of the real transport: prices include spacelike shifts in use.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Quartz
open Function Set Filter MeasureTheory Spectral Analysis Metric Topology
open scoped Topology NNReal ENNReal Complex ComplexOrder InnerProductSpace Classical
open Multiplier CrossedFrame Clasp Complex HadamardThreeLines BridgeClub Anvil
variable {K H D:Hilbert}(C:Clasp K H D)
local notation "L" i:max=> C.Left.symm.conjStarAlgEquiv i
local notation "B" i:max=> C.Right.symm.conjStarAlgEquiv i
variable (X:H.Op)(Y:D.Op)
local notation "M"=> max ‖X‖ ‖Y‖
local notation "ℬ"=> verticalClosedStrip 0 1
local notation "L₀"=> verticalStrip 0 1
abbrev Quarterπ := Real.pi/2
abbrev chamber := Complex.im ⁻¹' (Icc 0 Quarterπ)
abbrev innerHall := Complex.im ⁻¹' (Ioo 0 Quarterπ)
noncomputable def storm_shift(z:ℂ):ℂ:= -I*z/ (Quarterπ:ℂ)
lemma shift_reg(u:ℝ): storm_shift (u:ℂ) = (((2 * (-u/Real.pi):ℝ):ℂ)*I) := by
 have p: (Real.pi:ℂ)≠0:=Complex.ofReal_ne_zero.mpr Real.pi_pos.ne'; unfold storm_shift Quarterπ; push_cast; field_simp
lemma shift_crest(u:ℝ): storm_shift ((u:ℂ)+(Quarterπ:ℂ)*I)= 1+storm_shift (u:ℂ):= by
 have e:0<Quarterπ:=half_pos Real.pi_pos; have p:(Quarterπ:ℂ)≠0:=Complex.ofReal_ne_zero.mpr e.ne'; unfold storm_shift; field_simp; linear_combination - (Quarterπ:ℂ)*I_sq -- tune
lemma shift_re(z:ℂ): (storm_shift z).re=z.im/ Quarterπ:= by rw [storm_shift,div_ofReal_re]; simp only [neg_mul,neg_re,I_re,I_im,mul_re, zero_mul, one_mul,zero_sub,neg_neg]
lemma vertical_shift(z:ℂ)(v:z∈ chamber): storm_shift z ∈ℬ:= by
 obtain ⟨a,b⟩:= (show z.im ∈ Set.Icc 0 Quarterπ from v); change _ ∈ Set.Icc (0:ℝ) 1; rw [shift_re]; exact ⟨div_nonneg a (half_pos Real.pi_pos).le, div_le_one_of_le₀ b (half_pos Real.pi_pos).le⟩
lemma vertical_in(z:ℂ)(v:z∈innerHall): storm_shift z∈ L₀ := by
 obtain ⟨a,b⟩:= (show z.im∈ Ioo 0 Quarterπ from v); change _∈ Ioo (0:ℝ) 1; rw [shift_re]; exact ⟨div_pos a (half_pos Real.pi_pos),(div_lt_one (half_pos Real.pi_pos)).mpr b⟩
lemma pole_actual(u:ℝ) : (u:ℂ)∈ chamber:= show _∈ Icc (0:ℝ) Quarterπ from ⟨le_rfl,(half_pos Real.pi_pos).le⟩
lemma crest_actual(u:ℝ): (u:ℂ)+(Quarterπ:ℂ)*I∈chamber:=by simp[chamber,show 0≤ Quarterπ from (half_pos Real.pi_pos).le]
structure Reflected (G:ℂ→H.Op):Prop where
 at_rail : ∀ u:ℝ, G u= BridgeClub.ascend u C X
 at_other (u:ℝ): G ((u:ℂ)+(Quarterπ:ℂ)*I)= BridgeClub.ascend u C (C.look.symm.conjStarAlgEquiv Y)
 cost(z:ℂ)(v:z∈ chamber):‖G z‖≤ M
 wot(p q:H) : ContinuousOn (fun z=>inner ℂ p (G z q)) chamber
 motions(p q:H) :DifferentiableOn ℂ (fun z=> inner ℂ p (G z q)) innerHall
variable (h:C.Pass X Y)
local notation "t"=> tirs C X Y h
include h
lemma reflected : ∃ G,Reflected C X Y G:= by
 let G(z:ℂ):= C.Left.conjStarAlgEquiv (t (storm_shift z)); have p:Continuous (storm_shift):= by unfold storm_shift;fun_prop
 have hx:C.Left.conjStarAlgEquiv (L X)=X:=by ext1 x; simp [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply]
 have hy:C.Left.conjStarAlgEquiv (B Y)=C.look.symm.conjStarAlgEquiv Y:=by ext1 x; simp [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply,look]
 refine ⟨G,?_,?_,?_,?_,?_⟩
 · intro u; let k:=2*(-u/Real.pi); unfold G; have v:= vertical_shift _ (pole_actual u); rw [shift_reg] at v ⊢; rw [wise C X Y h _ v _ (fun n=> spark C n X k),map_mul,map_mul,map_star,hx,show k/2=(-u/Real.pi) from by unfold k;ring]; rfl
 · intro u; let k:=2*(-u/Real.pi); unfold G; have v:= vertical_shift _ (crest_actual u); rw [shift_crest,shift_reg] at v ⊢; rw [wise C X Y h _ v _ (fun n=> summit C n X Y k h),map_mul,map_mul,map_star,hy,show k/2=(-u/Real.pi) from by unfold k;ring]; rfl
 · intro z v; exact (lift_budget C.Left _).trans (ties C X Y h (storm_shift z) (vertical_shift z v)).1
 · intro x y; obtain ⟨x,rfl⟩:=C.Left.surjective x; obtain ⟨y,rfl⟩:=C.Left.surjective y; unfold G; simp_rw [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply,LinearIsometryEquiv.symm_apply_apply, LinearIsometryEquiv.inner_map_map]; exact ((apex C X Y h x y).1.comp p.continuousOn (fun _ u=> vertical_shift _ u))
 intro x y; obtain ⟨x,rfl⟩:=C.Left.surjective x; obtain ⟨y,rfl⟩:=C.Left.surjective y; unfold G; simp_rw [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply,LinearIsometryEquiv.symm_apply_apply,LinearIsometryEquiv.inner_map_map]; exact (apex C X Y h x y).2.comp (Differentiable.differentiableOn (show Differentiable ℂ storm_shift by unfold storm_shift;fun_prop)) (fun _ h=> vertical_in _ h)
end YM.Quartz
#print axioms YM.Quartz.reflected
