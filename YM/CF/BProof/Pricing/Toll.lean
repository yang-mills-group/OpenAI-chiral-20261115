import YM.CF.BProof.Pricing.Sky

/- rarity: pay exponential bill grouped at each *actual* severe column incl short-support
 Jacobian; following `Cost assigns` in (Sbill2). Taylor cost independent of bad counts. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Pricing
open Function Filter RG Wilson Lattice Finset Work Micro MeasureTheory Mag Angular Angular.Yard Charge Charge.Form Matrix Gauss Roll Precision Release Release.hot
open scoped Topology BigOperators Classical ENNReal Matrix MatrixOrder InnerProductSpace Matrix.Norms.L2Operator
local notation "G"=> SU.group
variable (K:Chart G)(P: Pub G)(c:Clip)(d:ℕ)(M:ℝ→ℕ)(R κ y:ℝ)(h:0<d)(u:PL fun y=> (M y:ℝ))

def price := (gearBound d (M y):ℝ)*((c.direct+share)*summer R y)-plash c d κ*thresh y^2 -- without beta. remove f
abbrev issueC := plash c d κ/4
abbrev bill_c (β:ℝ):= issueC c d κ * β*thresh y^2
structure StampC (P:Pub G)(c:Clip)(d:ℕ)(M:ℝ→ℕ)(R κ y:ℝ) : Prop where
  clear (β:ℝ)(h:y≤2*β) : β*(Pricing.price c d M R κ y)+ |Real.log (σd P d y)|+jPay c d M R y≤ -bill_c c d κ y β
  early : 0<y
include h u
lemma asks (p:0≤R)(v:0<κ): ∀ᶠ y:ℝ in atTop, StampC P c d M R κ y:=by
 let A:= plash c d κ; let F'(y:ℝ):=|Real.log (σd P d y)|+jPay c d M R y; have hP:0<A/8:=by have ht:=plash_pos c d h v; unfold A; positivity
 filter_upwards [eventually_gt_atTop (0:ℝ),coin_strongLt (a:=0) (b:=1) (by norm_num) ((scope_pl P d).abs.add (jPay_bill c d M R h u)), coin_budget (a:=0) (b:=1) (c:=0) (d:=0) (e:=2) (f:=0) (by norm_num) 1 (A/8) hP,bill_weather (P:=R) c p d κ v h M u] with y hy H1 H2 H3 -- capitalization conflict G
 have hk:y*thresh y^2=coin y 0 2 0:=by nth_rw 1 [← coinY hy]; rw [coin_pow,coin_mul]; ring_nf
 refine ⟨?_,hy⟩; intro β h
 let B:=thresh y^2; have he:Pricing.price c d M R κ y≤ -(A/2)*B:=by unfold Pricing.price A B; linarith only [H3]
 change |F' y|< _ at H1; have hv:F' y ≤ A/8*(y*B):=by rw [show y*B=coin y 0 2 0 from hk]; exact (le_abs_self _).trans ((H1.trans (by simpa using H2)).le)
 rw [add_assoc]; change β*_+ F' y≤-(A/4*β*B); calc
 _ ≤ β*(-(A/2)*B)+A/8*(y*B):= add_le_add (mul_le_mul_of_nonneg_left he (by linarith)) hv
 _ ≤ β*(-(A/2)*B)+A/8*((2*β)*B):= by unfold B; gcongr
 _ = _:=by ring
omit h u
variable {s:Side}(Y:Yard s)(T:PathData G){θ q w β C:ℝ}
namespace Model
variable (p:Model K P c Y.short M R y κ)(H:Room Y (M y))(u₁:T.Bounds c w R q)(h₁:θ∈Set.Icc (1/2) 2)
variable (Z:Finset Y.Col)(x:Plan Y)(U:Config G s)(r:BudgetPoint)(V:Locale.House Y)(b:Y.Col)
variable (l: Ink K C y)(e:r.threshold=thresh y)(j:ValidR c r (M y))(g:thin C y ≤ mA y)
variable {S: Hall s} {F:Y.FaceS}(X:Y.Climate y S U F)(p₁: Set.EqOn U (Locale.issue Y (Release.γ Y T θ y p.X Z x V)) ↑Y.field)(p₂:Locale.bed Y κ y (Release.γ Y T θ y p.X Z x V)=Z)(p':Fares Y y x)
-- output jac matching crowd
include H h₁ u₁
variable (θ) -- u₁ h₁ sorted? implicit before
abbrev issued := splitD c Y.short M R y
def vault := Release.crowd P Y T θ y p.X r β Z x U b + (roster K P c M R Y y κ p T θ H u₁ h₁).short Z (issued c M R y Y) b -- tune
variable {θ}
variable (a:StampC P c Y.short M R κ y)
include l e j g X p₁ p₂ p' a
lemma regard (v:b∈Z)(hz:y ≤ 2*β): vault (β:=β) K P c M R κ y Y T θ p H u₁ h₁ Z x U r b ≤ -bill_c c Y.short κ y β:=by
 have hc := Release.cash Y T θ κ y p.X Z x U V p₁ p₂; let b' := Book K P Y κ p.X; let W := tape Y T θ p.X Z x; have he := holds K P Y T θ κ y p.X H u₁ h₁ (p.bought K P c M R Y y κ) Z x U V p₁ p₂ p'
 have ht:0≤β:=by have := a.early; linarith
 have hv:= bill Y (M y) y c r T β U W X he K H l e j u₁ ht b (hc.symm ▸ v) p.height.scarcity g -- order tune
 dsimp only at hv; rw [hc] at hv; have hr:=Night.Design.flee (roster K P c M R Y y κ p T θ H u₁ h₁) Z (issued c M R y Y) (rC_p c Y.short M R y).le b; let G':= Release.crowd P Y T θ y p.X r β Z x U b -- rename
 unfold vault Release.crowd; rw [← σd₀]; apply le_trans _ (a.clear β hz); apply add_le_add (by unfold Pricing.price; linarith only [hv,neg_le_abs (Real.log (σd P Y.short y))]) ((le_abs_self _).trans hr)
omit g
-- thermal costY version with beta at 2*y.
lemma taylor_pay (i:Tile s)(t:i∈ good Y (M y) Z)(v:β≤2*y)(hv:0≤β):
    |Taylor y (Y.roll (roof_cost Y T θ y p.X Z x)) c r T (M y) U β i|≤ costY c R C y (M y) (2*y):=by
 have hc:=Release.cash Y T θ κ y p.X Z x U V p₁ p₂; have hg:=holds K P Y T θ κ y p.X H u₁ h₁ (p.bought K P c M R Y y κ) Z x U V p₁ p₂ p'; have ht:=evaporate Y (tape Y T θ p.X Z x) hg -- tune
 obtain ⟨hs,he⟩: Stove Y (M y) i ∧ Cave Y (M y) i Z := (mem_filter.mp t).2; have hx : Tall y (Y.roll (roof_cost Y T θ y p.X Z x)) (M y) U i:=cavern Y (M y) i H (roof_cost Y T θ y p.X Z x) X (by unfold roof_cost; nth_rw 1 [←hc]; exact ht) hs (hc.symm ▸ he)
 have hp : 0≤ Bound R C y (M y):=by unfold Bound rough thinly point predicted fourBill paper thin; have :=l.up; have ht:=Push.AbsoluteSums.budget_nonneg u₁.three; have hx:=SU.group.colorScale_pos; have h₁':0<thresh y:=coin_pos ..; have hi:0<aA y:=coin_pos ..; positivity -- tune ambiguity `Bound`
 refine (regular_fee K y _ c r T (M y) U l e j u₁ β i hv hx).trans ?_; unfold costY; gcongr; exact add_nonneg c.quadratic_pos.le share_pos.le
end Model
end YM.CF.BProof.Pricing
