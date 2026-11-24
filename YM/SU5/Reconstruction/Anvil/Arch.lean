import YM.SU5.Reconstruction.Anvil.Partition
/-! # Analytic disc arcs on their leases. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Anvil
open Function Set Metric Filter
open scoped Topology BigOperators
local notation "π"=> Real.pi
local notation "ℭ"=> circleMap 0 1
lemma normP (t:ℝ): ℭ t∈Rim:= circleMap_mem_sphere _ zero_le_one _
lemma re_c (t:ℝ): (ℭ t).re=Real.cos t:= by simp [circleMap_zero_re]
lemma im_c (t:ℝ): (ℭ t).im=Real.sin t:= by simp [circleMap_zero_im]
lemma mul_c (r t:ℝ): ℭ r*ℭ t= ℭ (r+t):= by rw [circleMap_zero_mul,one_mul]
lemma div_c (r t:ℝ): ℭ r/ℭ t= ℭ (r-t):= by rw [circleMap_zero_div,div_one]
variable {n:ℕ}
namespace Score
variable (C:Score n) (i:Spin n) (r:ℝ)
local notation "Pole" => C.post
local notation "Past" i:max=> C.past i
local notation "Next" i:max=> C.future i
local notation "Ω" i:max=> C.span i
abbrev middle:ℝ:= C.past i+C.span i
abbrev seat:=shift i
local notation "τ" i:max=> C.middle i
local notation "I"=> Complex.I
-- center
abbrev radial (z:ℂ):= z / ℭ (C.middle i)
abbrev jet (z:ℂ):= 1+C.radial i z
local notation "uX" => draft (Pole i) 1 (ℭ r)
local notation "vX" => draft (Pole (shift i)) 1 (ℭ r)
local notation "w" => C.radial i (ℭ r)
private lemma budget0 : w * ℭ (Ω i)= ℭ r / Pole i ∧ w*ℭ (-(Ω i))= ℭ r / Pole (shift i):= by rw [radial, post_next,post,div_c,div_c,div_c,mul_c,mul_c]; simp [future,middle]; ring_nf; simp -- probable
private lemma ccalc : uX*vX=(1-w*ℭ (Ω i))*(1-w*ℭ (-(Ω i))) := by simp only [draft,Complex.ofReal_one,one_mul, (C.budget0 i r).1,(C.budget0 i r).2]
private lemma shift_add (t:ℝ) : ℭ (-t)+ℭ t = ((2*Real.cos t:ℝ):ℂ):= by apply Complex.ext<;>simp [ -Complex.ofReal_cos, re_c,im_c,two_mul]
private lemma shift_diff (t:ℝ) : ℭ t-ℭ (-t) = ((2*Real.sin t:ℝ):ℂ)*I:= by apply Complex.ext<;>simp [-Complex.ofReal_sin, re_c,im_c,two_mul]
private lemma shift_mul (t:ℝ) : ℭ t*ℭ (-t)=1:= by rw [mul_c]; simp [circleMap_zero] -- simp before? tune
private lemma spokes : 1+w*w= ((2*Real.cos (r-τ i):ℝ):ℂ)*w:= by
  unfold radial; rw [div_c,← shift_add]; conv_rhs=> rw [add_mul,mul_comm (ℭ (-_)),shift_mul]
lemma frame_poles : uX*vX= ((2*(Real.cos (r-τ i) -Real.cos (Ω i)):ℝ):ℂ)*w:= by
 push_cast; rw [C.ccalc i r]; calc
   _ = 1+w*w*(ℭ (Ω i)*ℭ (-(Ω i))) - (ℭ (-(Ω i))+ℭ (Ω i))*w:=by ring
   _ = _ := by rw [shift_add,shift_mul,mul_one,C.spokes i r]; push_cast; ring
lemma frame_withdraw : vX-uX=((2*Real.sin (Ω i):ℝ):ℂ)*I*w:= by
 simp only [draft,Complex.ofReal_one,one_mul]; rw [← shift_diff]; rw [← (C.budget0 i r).1,← (C.budget0 i r).2]; ring
lemma brace : (C.jet i (ℭ r))^2 = ((2*(1+ Real.cos (r-τ i)):ℝ):ℂ)*w:=by
 let T:=w; rw [jet, show (1+T)^2=1+T*T+2*T by ring,C.spokes i r]; push_cast; ring
variable {t:ℝ} {j:Spin n}
local notation "U" i:max=> Ioo (C.past i) (C.future i)
-- statements when anywhere arcs. tune `｀`
lemma off_center (e:t∈U j): Real.cos (Ω j) < Real.cos (t-C.middle j):= by
   have h:|t-C.middle j| < Ω j:= by
     rw [abs_lt]; unfold middle; constructor<;> linarith [e.1,e.2,show Past j+2*Ω j =Next j from rfl] -- tune
   rw [← Real.cos_abs (t-C.middle j)]
   exact Real.strictAntiOn_cos (show |t-C.middle j|∈Icc 0 π from ⟨abs_nonneg _, (h.trans (C.bud j).2).le⟩) (show Ω j∈Icc 0 π from Ioo_subset_Icc_self (C.bud j)) h  -- cos_abs at Ω? tune
private lemma outsideSwing {a b:ℝ}(h:a>b)(p:a<2*π-b)(v:b∈Ioo 0 π): Real.cos a<Real.cos b:= by
  by_cases q:a≤π; · exact Real.strictAntiOn_cos (Ioo_subset_Icc_self v) (show a∈ Icc 0 π from ⟨(v.1.trans h).le,q⟩) h
  rw [←Real.cos_sub_two_pi a,← Real.cos_neg (a-2*π)]; push Not at q; exact Real.strictAntiOn_cos (Ioo_subset_Icc_self v) (show -(a-2*π)∈Icc 0 π from ⟨by linarith [v.1],by linarith⟩) (by linarith)
lemma unlit (p:i≠j)(g:t∈U j) : Real.cos (t-τ i) < Real.cos (Ω i):= by
  rcases lt_or_gt_of_ne p with p|p
  · refine outsideSwing ?_ ?_ (C.bud i) -- rw holes
    · unfold middle; linarith [g.1,C.future_le p,show C.past i+2*Ω i=Next i from rfl]
    unfold middle; linarith [g.2,(C.budgets j).2,(C.budgets i).1]
  rw [← Real.cos_neg (t-τ i)]; refine outsideSwing ?_ ?_ (C.bud i)
  · unfold middle; linarith [g.2,C.future_le p]
  unfold middle; linarith [g.1,(C.budgets j).1,(C.budgets i).2,show Past i+2*Ω i=Next i from rfl]
end Score
end YM.Anvil
