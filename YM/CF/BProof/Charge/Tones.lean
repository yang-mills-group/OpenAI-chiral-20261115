import YM.CF.BProof.Charge.Stroke

/-! Pass Taylor per-oriented links and elementary square products. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Charge.Form
open Function Filter RG Wilson Lattice Finset Work Micro Moment MeasureTheory Angular AnalyticBridge.SectorAffine Mag
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius InnerProductSpace
local notation "G" => SU.group
local notation "Cl" => SU.group.colorScale
local notation "E" => SU.group.lieExp
variable (K:Chart G) {s:Side}(W: Argument s)(y:ℝ)(σ:Signed)(b:Bond s)(U:Config G s)

/-- strong tests on one physical bond. -/
structure Tone (W:Argument s)(y:ℝ)(b:Bond s)(U:Config G s): Prop where
 short : cd G (mag y b) (U b) ≤ thresh y/16
 step : ‖W b‖ ≤ thresh y
 aff : cd G (mag y b*E (W b)) (U b)≤xi y
variable {C:ℝ}(hK:Ink K C y)
lemma tones_sc (z:Config G s) : cd G (lRead σ U b) (lRead σ z b)=cd G (U (sendEdge σ 0 b)) (z (sendEdge σ 0 b)):=by rw [used,used]; split; rw [cd_inv]; rfl
lemma noise_pix (h:Tone W y (sendEdge σ 0 b) U): cd G (lRead σ (mag (s:=s) y) b) (lRead σ U b) ≤ thresh y/16:= (tones_sc ..).trans_le h.short
lemma noise_line (h:Tone W y (sendEdge σ 0 b) U): ‖part σ b W‖≤thresh y:=by rw [part,LinearMap.comp_apply,turn_size]; exact h.step
include hK
lemma noise_walk (h:Tone W y (sendEdge σ 0 b) U): SU.group.chord (lRead σ U b) ≤ stepC C y := by
 rw [← cd_one]; apply (cd_triangle G 1 (lRead σ (mag (s:=s) y) b) (lRead σ U b)).trans; apply le_trans (add_le_add le_rfl (noise_pix W y σ b U h)); rw [lay_link,cd_one]; exact hK.pay .. -- include hK? mention but not signature; explicit? include
lemma mag_walk : SU.group.chord (lRead σ (mag (s:=s) y) b) ≤ stepC C y:= (le_add_of_nonneg_right (by have ht:0<thresh y:=coin_pos ..; positivity : 0≤thresh y/16)).trans (by rw [lay_link]; exact hK.pay ..)
include hK
abbrev paper (C y:ℝ):=(1+Cl)*thin C y
def fourBill (C y:ℝ):= 4*paper C y+(12*Cl)*thin C y
lemma real_step (h:Tone W y b U): Aff G (mag y b) (U b) (W b) (paper C y):= ((affine_mul K h.step hK.t_size _ (by
     have hp:=mag_walk K y (1:Signed) b hK; unfold lRead at hp; simpa [pull_id] using hp)).noise h.aff).le hK.r_step
lemma pair_step (h:Tone W y (sendEdge σ 0 b) U): Aff G (lRead σ (mag (s:=s) y) b) (lRead σ U b) (part σ b W) (paper C y):=by rw [used,used,part,LinearMap.comp_apply,turn]; split; exact (real_step K W y _ U hK h).inv; exact (real_step K W y _ U hK h)
omit hK
variable (l:Cell s)
def Chromic := ∀ i,Tone W y (sendEdge σ 0 (positions l i)) U
lemma psi_cost (h: Chromic W y σ U l) : ‖curlP σ l W‖≤4*thresh y:=by
 rw [curl_px]; apply (norm_sub_le ..).trans; apply (add_le_add ((norm_sub_le ..).trans (add_le_add (norm_add_le ..) le_rfl)) le_rfl).trans; have e(i):= noise_line W y σ (positions l i) U (h i); linarith [e 0,e 1,e 2,e 3]
include hK
lemma sum_price (h:Chromic W y σ U l): Aff G (faceValue (lRead σ (mag (s:=s) y)) l) (faceValue (lRead σ U) l) (curlP σ l W) (fourBill C y) := by
 let A(i):= lRead σ (mag (s:=s) y) (positions l i); let B(i):= lRead σ U (positions l i); let X(i):=part σ (positions l i) W; let r:=stepC C y; let p:=paper C y; let t:=thresh y
 have hA(i):SU.group.chord (A i)≤r:=mag_walk K y σ _ hK -- tune
 have hB(i):SU.group.chord (B i)≤r:=noise_walk K W y σ (positions l i) U hK (h i)
 have H(i):Aff G (A i) (B i) (X i) p:=pair_step K W y σ _ U hK (h i); have hl(i):‖X i‖≤t:= noise_line W y σ _ U (h i)
 have hv (a b:SU.E) {g h:ℝ} (p:SU.group.chord a≤g)(q:SU.group.chord b≤h): SU.group.chord (a*b)≤g+h:= (SU.group.chord_triangle a b).trans (add_le_add p q)
 let Q:=r*t
 have g:= (H 0).product (H 1) (hA 0) (hB 1) (hl 0) (hl 1)
 have heA : SU.group.chord (A 0*A 1) ≤ r+r:= hv _ _ (hA 0) (hA 1)
 have heL : ‖X 0+X 1‖ ≤ t+t := (norm_add_le ..).trans (add_le_add (hl 0) (hl 1))
 have hk:=g.product (H 2).inv heA (show SU.group.chord (B 2)⁻¹≤ r from by simpa using hB 2) heL (show ‖-X 2‖ ≤ t by rw [norm_neg]; exact hl 2)
 have hz:=hk.product (H 3).inv (hv (A 0*A 1) _ heA (show SU.group.chord (A 2)⁻¹≤r from by simpa using hA 2)) (show SU.group.chord (B 3)⁻¹≤r from by simpa using hB 3) ((norm_add_le ..).trans (add_le_add heL ((norm_neg (X 2)).trans_le (hl 2)))) ((norm_neg (X 3)).trans_le (hl 3))
 rw [desc,desc,curl_px,sub_eq_add_neg,sub_eq_add_neg]; apply hz.le; unfold fourBill p r t stepC thin; apply le_of_eq; ring
private lemma chord_pay (h:Chromic W y σ U l): cd G (faceValue (lRead σ (mag y)) l) (faceValue (lRead σ U) l) ≤ 4*(thresh y/16):=by
 rw [desc,desc]; have hg(i):=noise_pix W y σ (positions l i) U (h i); apply (curl_bound ..).trans; exact (add_le_add (add_le_add (add_le_add (hg 0) (hg 1)) (hg 2)) (hg 3)).trans_eq (by ring)
lemma chord_price (h:Chromic W y σ U l): SU.group.chord (faceValue (lRead σ U) l)≤ thresh y:=by
 let f:= faceValue (lRead σ (mag y)) l; let g:= faceValue (lRead σ U) l; have hv : cd G f g≤4*(thresh y/16):= chord_pay K W y σ U hK l h
 rw [← cd_one]; apply (cd_triangle G 1 f g).trans; have hu: cd G 1 f≤ thresh y/2:=by unfold f; rw [cd_one,fixed_face]; exact hK.simple ..
 exact (add_le_add hu hv).trans (by linarith [show 0<thresh y from coin_pos ..])
def predicted (C y:ℝ) := thin C y+fourBill C y
lemma overall (h:Chromic W y σ U l): Aff G 1 (faceValue (lRead σ U) l) (mA y • mark σ l.2+curlP σ l W) (predicted C y) := by
 let a:=faceValue (lRead σ (mag (s:=s) y)) l; let b:= faceValue (lRead σ U) l; let x:= mA y • mark σ l.2; let z:= curlP σ l W; let F:=SU.group.mat; let L:=SU.group.colorMat
 have hp: Aff G 1 a x (thin C y):= (show baseF y σ l.2=a from (fixed_face y σ l).symm) ▸ hK.draw σ l.2 -- tune
 change ‖F b-F 1-L (x+z)‖≤Cl*predicted C y; rw [show F b-F 1-L (x+z)=(F a-F 1-L x)+(F b-F a-L z) by rw [map_add]; abel]; apply (norm_add_le ..).trans; exact (add_le_add hp (sum_price K W y σ U hK l h)).trans_eq (mul_add ..).symm
end YM.CF.BProof.Charge.Form
