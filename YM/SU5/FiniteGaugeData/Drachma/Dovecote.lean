import YM.SU5.FiniteGaugeData.Drachma.Faro

set_option autoImplicit false
set_option maxHeartbeats 500000
set_option synthInstance.maxSize 15000
set_option linter.flexible false
noncomputable section
namespace YM.SU5.FiniteGaugeData.Drachma
open Function Finset Matrix Lattice Wilson RG Precision Exterior Tree Laurent Bloch CF.Font Next.Rank.Axial
open scoped Topology BigOperators Matrix Classical
variable {c f:Side} {S:StepData c f}{p:Clip}{a A₀:ℝ}{P Q:Bed}
local notation "σ" => S.kernel.penalty
variable (F:Forest S.ratio)(A:AfterT c) (G:AfterT f)

abbrev bore(F:Forest S.ratio)(P:Bed): sp (LT f):= plaid P f + σ • prizes (probe S) + prizes (tickets F)
variable (S)
lemma doveA(P:Bed): (chips G P).det*σ^Fintype.card (LT c)=(jointK S P+prizes (oakC G c)+prizes (meter f c)).det:=by
 let T:=jointK S P+prizes (oakC G c)+prizes (meter f c); let U:=layer (probe S)
 change _=T.det; rw [← wager_det T U (layer_det _)]; suffices h: boost T U=sided (chips G P) (σ • 1) by rw [h,sided_det,det_smul,det_one,mul_one]
 have he (x:coin (spanJ f c)): um f c (U*ᵥ x)=um f c x:=by unfold um U; rw [layer_bill,born_l]
 have hu (x:coin (spanJ f c)): roc S*ᵥ (U*ᵥ x)=du f c x:=by rw [rocs,he]; unfold U du; rw [layer_bill,born_r]; change probe S *ᵥ um f c x+_ -_= _; abel
 apply wager; intro x y; rw [boost_bill,sidedBill]; unfold T; rw [plus_bill,plus_bill,fuel,hu,hu,he,he,prize_bill,prize_bill]; unfold oakC meter; simp only [←mulVec_mulVec, am,sty_l_bill]
 unfold um at *; rw [he,he,chips,plus_bill,plus_bill,smid,one_mulVec,prize_bill,prize_bill]; unfold du; ring
variable {S}
variable {V:Matrix (Body 1 f) (Body 1 c) ℝ} (i:Inputs S V (P.metric.acts f) (Q.metric.acts c))
local notation "𝓣" => extracted S F V
local notation "℃" => (1-probe S*𝓣)
include i
lemma mix_t(b:coin (LT c))(x:coin (LT f)): dotProduct x (plaid P f*ᵥ (𝓣*ᵥ b))=σ * dotProduct (probe S*ᵥ x) (℃ *ᵥ b):=by
 let A:=plaid Q c; rw [mulVec_mulVec,plaid,show K (P.metric.acts f)*𝓣=_ from (stationed F _ _ _ i).2, ←mulVec_mulVec,dotProduct_mulVec x (probe S).transpose,vecMul_transpose] -- tune
 rw [(stationed F _ _ _ i).1]; change dotProduct _ (A*ᵥ b)=_*dotProduct _ ((1-(1-σ⁻¹•A))*ᵥ b); simp only [sub_sub_cancel,smul_mulVec,dotProduct_smul,smul_eq_mul, mul_inv_cancel_left₀ S.kernel.penalty_pos.ne']
lemma license_t(x y:coin (LT c)):
 dotProduct (𝓣*ᵥ x) (plaid P f*ᵥ (𝓣*ᵥ y))+σ*dotProduct (℃*ᵥ x) (℃*ᵥ y)=dotProduct x (plaid Q c*ᵥ y):=by
 rw [←boost_bill,←prize_bill,←smid, ← plus_bill]; rw [show boost (plaid P f) 𝓣+σ •prizes ℃=_ from action F V _ _ i]
omit i
lemma cross_roc (x:coin (spanJ f c)): roc S*ᵥ (spray 𝓣 *ᵥ x)= (℃ *ᵥ du f c x) - probe S *ᵥ um f c x:=by
 rw [rocs, spray_bill, sub_mulVec, ← mulVec_mulVec,one_mulVec]; unfold du um; rw [born_r,born_l,mulVec_add]; abel
omit i in
lemma printT (x:coin (spanJ f c)): tickets F *ᵥ (um f c (spray 𝓣*ᵥ x))=tickets F*ᵥ um f c x:=by
 rw [spray_bill]; unfold um; rw [born_l,mulVec_add]; suffices h: tickets F*ᵥ (𝓣*ᵥ du f c x)=0 by simp only [add_eq_left]; exact h
 rw [tickets_bill]; funext u; exact Precision.stays F V (du f c x) u.val u.2
lemma meterD_t (x:coin (spanJ f c)): meterD f c *ᵥ x= lasers c*ᵥ du f c x:=by rw [meterD,←mulVec_mulVec,cd,sty_r_bill] -- tune
include i
lemma doveB (h:(P.metric.acts f).IsSymm): (jointK S P+prizes (oakD F A)+prizes (meterD f c)).det=(bore F P).det*(chips A Q).det:=by
 let T:=jointK S P+prizes (oakD F A)+prizes (meterD f c); change T.det=_; let U:=spray 𝓣; rw [← wager_det T U (spray_det _),← sided_det]; congr 1
 let L (x:coin (spanJ f c)):=du f c x; let H (x:coin (spanJ f c)):=um f c x
 have he (x:coin (spanJ f c)): du f c (U*ᵥ x)=L x:=by unfold U du; rw [spray_bill,born_r] -- maybe no goals
 have hi (x:coin (spanJ f c)): um f c (U*ᵥ x)=H x+𝓣*ᵥ L x:=by unfold um U; rw [spray_bill,born_l]
 have hz(x:coin (spanJ f c)):oakD F A *ᵥ(U*ᵥ x)=swapper (tickets F*ᵥ H x) (tickets A*ᵥ L x):=by rw [deckD,he,←tickets_bill,←tickets_bill]; unfold U; rw [printT]
 apply wager; intro x y
 have hk:dotProduct (𝓣*ᵥ L x) (plaid P f*ᵥ H y)=dotProduct (H y) (plaid P f*ᵥ (𝓣*ᵥ L x)):=by
    rw [dotProduct_mulVec, ← Matrix.mulVec_transpose,(plaidS h).eq,dotProduct_comm]
 rw [boost_bill]; unfold T; rw [plus_bill,plus_bill,fuel,prize_bill,prize_bill,hz,hz,bills,born_l,born_l,born_r,born_r,meterD_t,meterD_t,he,he,hi,hi,show roc S*ᵥ (U*ᵥ x)=_ from cross_roc (V:=V) F x, show roc S*ᵥ (U*ᵥ y)=_ from cross_roc (V:=V) F y, mulVec_add,add_dotProduct] -- tune add dotted order
 rw [sidedBill]; unfold bore chips; simp_rw [plus_bill,smid,prize_bill]
 dsimp only [L,H,du,um] at *; simp_rw [dotProduct_add, sub_dotProduct,dotProduct_sub]; rw [hk]
 have h1:=mix_t F i (ℜ _ _ y) (ℓ _ _ x); have h2:=mix_t F i (ℜ _ _ x) (ℓ _ _ y); have h3:=license_t F i (ℜ _ _ x) (ℜ _ _ y)
 rw [dotProduct_comm (℃ *ᵥ ℜ _ _ x) (probe S*ᵥ ℓ _ _ y)]; linarith only [h1,h2,h3]

/-- Uncut determinant: REAL counting measure. Comparison to the piecewise physical `Rows.gram` still to do. -/
theorem chimney (h:(P.metric.acts f).IsSymm):
 (chips G P).det*σ^Fintype.card (LT c)= (bore F P).det*(chips A Q).det:= by rw [doveA S G P,swap_horizon F A G P h,doveB F A i h] -- tune
end YM.SU5.FiniteGaugeData.Drachma
