import YM.CF.BProof.Mood
import YM.CF.BProof.Bracket
import YM.CF.BProof.Scales

/-! Estimates on the background and if tangential links of a face are within C w_c.
Logs of the three types of plaquettes used with eq:B-mood. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Mag
open Function SU Filter Metric Set MeasureTheory Finset
open scoped Matrix.Norms.Frobenius Topology BigOperators

local notation "G" => SU.group
local notation "E'" => SU.group.lieExp
local notation "L" => SU.group.colorMat
local notation "M" => SU.group.mat
local notation "A" => group.colorScale

-- order agrees with numerical tangential axis order (time is axis zero)
def f₁ : Fin 3 → Fin 3 := ![0,0,1]
def f₂ : Fin 3 → Fin 3 := ![1,2,2]
lemma f₁f₂ (i : Fin 3) : f₁ i<f₂ i := by fin_cases i <;> decide

def bg (y : ℝ) (i : Fin 3) : E := E' (aA y • X i)
def curl {α : Type*} [Group α] (u v w x : α) := u*v*w⁻¹*x⁻¹
def comm (y : ℝ) (i j : Fin 3) := curl (bg y i) (bg y j) (bg y i) (bg y j)
lemma mag_ad (i : Fin 3) : group.ad (X (f₁ i)) (X (f₂ i))=magnetic i := by rw [triple]; fin_cases i <;> rfl

lemma curl_bound (u v w x U V W X : E) : cd G (curl u v w x) (curl U V W X) ≤ cd G u U+cd G v V+cd G w W+cd G x X := by
 apply (cd_perturb ..).trans; apply add_le_add
 · apply (cd_perturb ..).trans; apply add_le_add; apply cd_perturb; rw [cd_inv]
 simp only [cd_inv,le_refl]

variable (K : Chart G)
include K in
lemma pay : ∃ C : ℝ,0<C ∧ ∀ᶠ y:ℝ in atTop,
    (∀ i, cd G 1 (bg y i) ≤ C*aA y) ∧
    ∀ i j, ‖M (comm y i j)-1-L (mA y • group.ad (X i) (X j))‖ ≤ C*aA y^3 := by
 let k:=1+∑ i,‖X i‖; have hk:0<k:=by unfold k; positivity
 obtain ⟨C,hc,H⟩:= K.bracket_cost
 have hi i : ‖X i‖≤k:= le_trans (single_le_sum (f:=fun i=> ‖X i‖) (fun _ _=>norm_nonneg _) (mem_univ i)) (by unfold k; simp)
 let B:= max (K.C*k) (C*k^3); have hB:0<B := lt_of_lt_of_le (show 0<C*k^3 by positivity) (le_max_right ..)
 refine ⟨B,hB,?_⟩
 have ht:= coin_budget (a:= -1/4) (b:=3/8) (c:=0) (d:=0) (e:=0) (f:=0) (Or.inl (by norm_num)) k K.size K.admitted
 filter_upwards [ht] with y hy
 have u := coin_pos y (-1/4) (3/8) 0
 change 0<aA y at u
 simp only [coin_zero,mul_one] at hy
 let r:= k*aA y; have hp:r≤K.size:= hy.le
 have hw i: ‖aA y • X i‖ ≤ r:=by rw [norm_smul,Real.norm_of_nonneg u.le,mul_comm]; exact mul_le_mul_of_nonneg_right (hi i) u.le
 constructor
 · intro i; rw [cd_one]; exact (K.step _ ((hw i).trans hp)).trans ((mul_le_mul_of_nonneg_left (hw i) (zero_le_one.trans K.C_one)).trans (by unfold r; rw [←mul_assoc]; exact mul_le_mul_of_nonneg_right (le_max_left ..) u.le))
 intro i j
 have h : group.ad (aA y • X i) (aA y • X j)=mA y • group.ad (X i) (X j):=by simp only [map_smul,LinearMap.smul_apply,smul_smul]; rw [show aA y*aA y=mA y from by rw [coin_mul]; unfold mA; ring_nf]
 rw [← h]; exact (H r _ _ hp (hw i) (hw j)).trans (by unfold r; rw [mul_pow,← mul_assoc]; exact mul_le_mul_of_nonneg_right (le_max_right ..) (by positivity))

/-- License for B-mood: bare matrix estimate and its log consequence. Keeping C-price
independent of the level. -/
lemma log_background (D : ℝ) (hD : 0<D) : ∃ C : ℝ,0<C ∧ ∀ᶠ y:ℝ in atTop, ∀ i : Fin 3,
    ∀ u : E, cd G (comm y (f₁ i) (f₂ i)) u ≤ D*wc y →
    group.chord u<K.radius ∧ ‖logG G u - mA y • magnetic i‖ ≤ C*wc y := by
 let B:= 1+∑ i, ‖magnetic i‖; have hB:0<B:=by unfold B; positivity
 obtain ⟨C,hc,H⟩:= pay K
 let C' := C/A+K.C*B^2/A; have hs:= group.colorScale_pos; have hu:= zero_lt_one.trans_le K.C_one
 have hu' : 0<C':= by unfold C'; positivity
 have hb i : ‖magnetic i‖≤B:= le_trans (single_le_sum (f:=fun i=> ‖magnetic i‖) (fun _ _=>norm_nonneg _) (mem_univ i)) (by unfold B; simp)
 refine ⟨K.C*(D+C'),by positivity,?_⟩
 have h : ∀ᶠ y:ℝ in atTop,
     let r:=B*mA y; r ≤ K.size ∧ K.C*r ≤ K.radius/3 ∧ (D+C')*wc y ≤ K.radius/3 ∧ aA y^3≤wc y ∧ (mA y)^2≤wc y:=by
   let W a b (h : a<0) (u:ℝ){v:ℝ}(p:0<v): ∀ᶠ y:ℝ in atTop,u*coin y a b 0<v:= by
     have hv:= coin_budget (b:=b) (e:=0) (c:=0) (f:=0) (Or.inl h) u v p; simpa only [coin_zero,mul_one] using hv
   have hp:0<K.radius/3:=by have := K.positive; positivity
   filter_upwards [W _ (3/4) (by norm_num : (-1:ℝ)/2<0) B K.admitted,W _ (3/4) (by norm_num : (-1:ℝ)/2<0) (K.C*B) hp,W _ (1/2) (by norm_num : (-1:ℝ)/2<0) _ (show 0<K.radius/3 from hp), coin_budget (b:=9/8) (c:=0) (f:=0) (e:=1/2) (Or.inl (by norm_num : (-3:ℝ)/4< -1/2)) 1 1 one_pos,coin_budget (b:=3/2) (c:=0) (f:=0) (e:=1/2) (Or.inl (by norm_num : (-1:ℝ)< -1/2)) 1 1 one_pos] with y h1 h2 h3 h4 h5
   refine ⟨h1.le,(mul_assoc ..).symm.trans_le h2.le,h3.le,?_,?_⟩
   · have heq : aA y^3=coin y (-3/4) (9/8) 0:=by rw [coin_pow]; ring_nf
     rw [heq]; simpa only [one_mul] using h4.le
   have heq : mA y^2=coin y (-1) (3/2) 0:=by rw [coin_pow]; ring_nf
   rw [heq]; simpa only [one_mul] using h5.le
 filter_upwards [h,H] with y h HH
 dsimp only at h; obtain ⟨hw,hl,hm,ha,hM⟩:=h
 have hp:=show 0<mA y from coin_pos ..
 intro i u hx
 let r:=B*mA y; let v:=mA y • magnetic i
 have hv : ‖v‖≤r:=by unfold v; rw [norm_smul,Real.norm_of_nonneg hp.le,mul_comm]; exact mul_le_mul_of_nonneg_right (hb i) hp.le
 let z := comm y (f₁ i) (f₂ i)
 have he : cd G u (E' v) ≤ (D + C')*wc y:= by
   apply (cd_triangle G u z (E' v)).trans
   rw [cd_symm G u,add_mul]; apply add_le_add hx
   rw [norm_le_scale]; have he:= HH.2 (f₁ i) (f₂ i); rw [mag_ad] at he
   calc
     _ ≤ ‖M z - 1 - L v‖ + ‖M (E' v)-1 - L v‖ := by
           have p:=norm_sub_le (M z-1-L v) (M (E' v)-1-L v); simpa only [sub_sub_sub_cancel_right] using p
     _ ≤ C*wc y+K.C*r*r := add_le_add (le_trans he (by gcongr)) ((K.linear v hv hw).trans (mul_le_mul_of_nonneg_left hv (by unfold r; positivity)))
     _ ≤ _ := by unfold r C'; have hm:= mul_le_mul_of_nonneg_left hM (show 0≤K.C*B^2 by positivity); field_simp; -- tune
                 nlinarith -- tune
 have hy : group.chord (E' v) ≤ K.radius/3 := (K.step v (hv.trans hw)).trans ((mul_le_mul_of_nonneg_left hv hu.le).trans hl)
 have ht : group.chord u < K.radius := by have hk:=cd_triangle G 1 (E' v) u; rw [cd_symm G (E' v) u] at hk; simp only [cd_one] at hk; linarith [K.positive]
 refine ⟨ht,?_⟩; change ‖logG G u-v‖≤_; nth_rw 1 [← K.recognizes v (hv.trans hw)]; exact (K.lip u (E' v) ht.le (hy.trans (by have := K.positive; linarith))).trans (by rw [_root_.mul_assoc]; gcongr)
end YM.CF.BProof.Mag
