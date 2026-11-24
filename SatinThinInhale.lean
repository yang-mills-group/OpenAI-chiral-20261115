import SatinThinRent
import SatinThinSkating
import SatinThinAbility
/-! # Subleague permit at unbounded Nr. -/
set_option autoImplicit false
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.Pressure.Worth.Pays
open Function Filter Finset Lattice CF.BProof CF CF.Skye CF.Py.Rate CF.Py.Rate.LocalLimit CF.Pannier CF.Pannier.Chancel CF.Pannier.Damask Rous
open scoped Topology
variable {r k:ℕ}{N:Side}{C R δ v u t g a:ℝ}
abbrev atmosphere (a x:ℝ):ℝ:= shieldC x+2*Real.exp (-(a* (radiusB x)))
abbrev fundsI (C R a g δ x:ℝ):= baseDaily a C R (atmosphere a x) + townDaily (terrace x) (shieldC x) R g δ (radiusB x)
abbrev rentI (C R:ℝ)(k:ℕ)(x:ℝ):= debtDaily k (radiusB x) C R+townDues (terrace x) R 1 k
lemma base_fr (a C R:ℝ)(t:0<a) : Worth.Pays r_shield 0 0 fun x=> baseDaily a C R (atmosphere a x):=by
 let v:= atmosphere a; have hv: Worth.Pays r_shield 0 0 v:= plus (whole ..) (scale 2 (damp a t r_shield 0 0)); have he: Worth.Pays r_shield 0 0 (fun x=>v x^2):= merit (pot hv 2) (Or.inl (by norm_num [r_shield]))
 unfold baseDaily; simp_rw [←mul_assoc (180^_) (_:ℝ)]; exact plus (scale _ he) (scale _ (scale _ (plus hv he)))
lemma debt_fr (k:ℕ)(C R:ℝ) : Worth.Pays 0 0 8 fun x=> debtDaily k (radiusB x) C R:=by
 let t':=(4:ℝ)*((((k+4)*2+1)^4:ℕ):ℝ); let Bm (x:ℝ):=(radiusB x:ℝ)+(radiusB x:ℝ)+1; have he:Worth.Pays 0 0 2 Bm:=by
    unfold Bm; simp_rw [add_assoc]; exact plus rising property_plus -- tune
 have hf:Worth.Pays 0 0 8 (fun x=>Bm x^4):=by
    convert pot he 4 using 1 <;> norm_num
 refine fix (scale (t'*(C*4)+180^2*((1+R)*R)*180*t'*(45*6*C)) hf) (Eventually.of_forall fun i=> ?_)
 unfold Bm t' debtDaily rimedR quake; push_cast; ring
lemma town_fr(R g δ:ℝ)(v:0<g) : Worth.Pays (-r_width) 0 2 (fun x=> townDaily (terrace x) (shieldC x) R g δ (radiusB x)):=by
 have he: Worth.Pays (r_width+r_shield) 0 0 (fun x=>scaleTown (terrace x) (shieldC x)):=by
    unfold scaleTown; have hv:= scale BPress.Spin.sphereRate (times (scale 4 terrace_size) (whole r_shield 0 0)); simpa only [zero_add] using hv
 have ht:=merit (right δ⁻¹ (times (right 4 rising) he)) (w:= -r_width) (p:=0) (q:=2) (Or.inl (by norm_num [r_width,r_shield]))
 have hx:= scale 2 (damp g v (-r_width) 0 2)
 have hs:= (times (scale 24 property_plus) terrace_inv); simp only [zero_add, add_zero] at hs
 unfold townDaily shortfall; simp_rw [div_eq_mul_inv _ (↑(terrace _).val:ℝ), div_eq_mul_inv _ δ]; exact plus (scale _ (right R (plus hx ht))) (right _ (right 180 hs))
lemma dues_fr (R:ℝ)(k:ℕ) : Worth.Pays (4*r_width) 0 0 (fun x=>townDues (terrace x) R 1 k):=by
 unfold townDues frame_h; apply right; apply right; apply scale; convert pot terrace_size 4 using 1 <;> norm_num [r_width]
lemma clamp_bill (C R a g δ S:ℝ)(w:0<a)(t:0<g)(k:ℕ): ∀ᶠ x:ℝ in atTop,S*fundsI C R a g δ x ≤ meterC x ∧ S*rentI C R k x≤ gateC x:=by
 apply Eventually.and
 · apply leap (scale S (plus (merit (base_fr a C R w) (Or.inl ?_)) (town_fr R g δ t))) (Or.inl ?_) <;> norm_num [r_meter,r_width,r_shield]
 apply leap (scale S (plus (merit (debt_fr k C R) (Or.inl ?_)) (dues_fr R k))) (Or.inl ?_) <;> norm_num [r_gate,r_width]
end YM.Pressure.Worth.Pays
