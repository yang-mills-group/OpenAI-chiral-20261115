import YM.SU5.Thin.Glacier.Responsive
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option quotPrecheck false
set_option linter.unusedSimpArgs false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 300000
set_option maxHeartbeats 800000
set_option maxHeartbeats 800000
noncomputable section
namespace YM.Gleam
open Function Lattice MeasureTheory Finset RG Wilson Tree Filter Metric Exterior Precision Next.Rank.Spindle Pressure Work.F03 Next.SectorChange Next.SectorChange.Gaussian
open Fineness Matrix
open scoped Matrix BigOperators Classical ContDiff Topology MatrixOrder ENNReal Kronecker Matrix.Norms.Frobenius
variable {c n : Side}{r:Ratio c n}{T:Forest r}{G:Gauge}{p:BudgetPoint}{q:Clip}{v t η C S w δ β κ ξ Λ:ℝ}{U:Config G n}{A:Support c}{m:ℕ} {R:Rules G} {Z:PathData G}{b:Cell n}{H:Bed}{F:Finset T.Free}{J:ChartRatio G}
namespace clocks
open Work.E09 AnalyticBridge.Annulus1AD
local notation "B" x:max=> (height x:ℝ)
open Sleigh Paddled
-- area
lemma slip (L:Side):∀ᶠ x:ℝ in atTop,∀ w:ℕ,starSpan x w L→ hallBill (height x)≤w/2:=by
 have he(n:ℕ)(s:2≤n): hallBill n ≤ 8*n:=by unfold hallBill Sequest; omega
 have hx:=((radpay (by norm_num : (0:ℝ)<1/250) 1).scale 16).pure (b:=1/200) (by norm_num)
 filter_upwards [Work.E08.eventual_radiusB 2,hx] with x h t w k; simp only [pow_one] at t; have hM: 16*height x ≤ w:= (Nat.cast_le (α:=ℝ)).1 (by push_cast; exact t.trans k.1); have hv:=he _ h; dsimp only [height] at *; omega
lemma stainBeat (C:ℝ)(p:0 ≤ C):∀ᶠ x:ℝ in atTop,4*(C* B x)*(speckCount (hallBill (height x)):ℝ)+B x ≤ grain x:=by
 let a:= C*4*17^4; have h:a≥0:= by unfold a; positivity
 filter_upwards [ (tendsto_natCast_atTop_atTop (R:=ℝ)|>.comp Work.E01.radiusB_tendsto).eventually_ge_atTop (a+2)] with x k
 let t:=B x; change a+2 ≤ t at k; have hk: (2:ℝ) ≤ t:=by linarith only [h,k]
 have he:1 ≤ t:=one_le_two.trans hk
 have hp:(speckCount (hallBill (height x)):ℝ)≤(17*t)^4:=by unfold speckCount hallBill Sequest; push_cast; apply pow_le_pow_left₀ (by positivity) _; change t+4+(t+4)+(t+4+(t+4))+1≤ 17*t; linarith only [hk]
 change _+t ≤ t^60; apply (pow_le_pow_right₀ he (by norm_num : (6:ℕ)≤60)).trans'; have hz:t≤ t^5:=le_self_pow₀ he (by decide: (5:ℕ)≠0); have hx':a*t^5+t ≤ t^6:=by nlinarith only [hz,mul_le_mul_of_nonneg_right k (by positivity : 0≤t^5),show 0≤t^5 by positivity]
 apply hx'.trans'; have h':0 ≤ C*t:=by positivity
 change 4*(C*t)*_+t≤_; linarith only [mul_le_mul_of_nonneg_left hp h', show C*t*(17*t)^4*4=a*t^5 by unfold a; ring] -- t let B
lemma ledge_due (L:Side)(A:ℝ)(p:0 ≤ A): ∀ᶠ x:ℝ in atTop,∀ w:ℕ,starSpan x w L →4*(A*B x)*(w:ℝ)^4 ≤ ledge x :=by
 let v:ℝ:= 2*L.val; let u(x:ℝ):=v*averge x; have hm:Paddled (1/250) (fun x=> (height x:ℝ)):=by simpa only [pow_one] using radpay (by norm_num:(0:ℝ)<1/250) 1
 have h:Paddled (1/200) u:= (park _).scale _
 filter_upwards [ ((((hm.scale A).scale 4).mul (h.power 4))).pure (b:=3/100) (by norm_num)] with x t w k; exact (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Nat.cast_nonneg _) k.2 4) (show 0≤4*(A* B x) from by positivity)).trans t
lemma fright_fee(C:ℝ)(h:0≤ C): ∀ᶠ x in atTop,C*Real.exp (-(B x))≤(1/12:ℝ)*oar x:=by
 have hv:= ( ((park (-(1:ℝ))).scale C)).discounts (b:=-(1/500:ℝ)) (by norm_num) (by norm_num:(0:ℝ)<1/12)
 filter_upwards [ (tail_gone (G:=CF.SU.group) 1 one_pos),hv] with x p t; change |C* _|≤_ at t; rw [Real.rpow_neg_one] at t; specialize p; unfold trail at p; rw [neg_mul,one_mul] at p; exact (mul_le_mul_of_nonneg_left p h).trans ((le_abs_self _).trans t)
lemma stainSurface (A:ℝ)(L:Side)(p:0≤A):∀ᶠ x:ℝ in atTop,∀ w:Side,starSpan x w.val L→Odd w.val→4*(A*B x)*(largerBill w.val (hallBill (height x)):ℝ) + Real.log 2 ≤ ((1/12:ℝ)*oar x)*(w.val:ℝ)^4:=by
 have hf:Paddled (3/1000) (fun x=>oar x*averge x):= ((park _).mul (park _)).agrees (by norm_num) -- useless
 let a:=256*A+Real.log 2; have hh:0≤a:=by unfold a; positivity
 have hx:= ((radpay (by norm_num : (0:ℝ)<1/500) 2).scale a).discounts (b:=3/1000) (by norm_num) (by norm_num:(0:ℝ)<1/12)
 filter_upwards [eventually_gt_atTop (0:ℝ),hx, Work.E08.eventual_radiusB 2, slip L] with x v hx p' w t i k
 let X:ℝ:= t.val; have hu: 1 ≤ X:= Nat.one_le_cast.mpr t.property
 let Z:=B x; have hpZ:2 ≤ Z:= Nat.ofNat_le_cast.mpr p' -- check name
 let e:= hallBill (height x); let hZ:= largerBill t.val e
 have he: (e:ℝ) ≤ 8*Z:=by unfold e hallBill Sequest; push_cast; change Z+4+(Z+4)≤_; linarith only [hpZ]
 have hp: 4*(A*Z)*hZ ≤256*A*Z^2*X^3:=by
    apply le_trans (mul_le_mul_of_nonneg_left (wall_cheap k (w _ i)) (by positivity : 0≤4*(A*Z))); have he':0≤ A*Z*X^3:=by positivity
    change 4*(A*Z)*(8*(e:ℝ)*X^3)≤_; nlinarith only [mul_le_mul_of_nonneg_right he he']
 have hg:a*Z^2 ≤ ((1/12:ℝ)*oar x)*X:=by
    have h:x^(3/1000:ℝ)=oar x * averge x:=by unfold oar averge; rw [←Real.rpow_add v]; norm_num
    have hl:a* Z^2≤ 1/12 * (x^ ( (3:ℝ)/1000)):= (le_abs_self _).trans hx; rw [h,←mul_assoc] at hl; exact hl.trans (mul_le_mul_of_nonneg_left i.1 (by have h:= (shinyH x v).2.2.2; positivity))
 let R:=Real.log 2; have he:0≤R:=Real.log_nonneg (by norm_num); have hd:R ≤ R*Z^2*X^3:= (le_mul_of_one_le_right he (one_le_pow₀ (show 1≤Z from one_le_two.trans hpZ))).trans (le_mul_of_one_le_right (by positivity:0 ≤ R*Z^2) (one_le_pow₀ hu)); change 4*(A*Z)*hZ + R ≤ _ * X^4; have hh: a=256*A+R:=rfl; rw [hh] at hg; nlinarith only [hp,hg,hd, mul_le_mul_of_nonneg_right hg (show 0≤ X^3 by positivity)]
end clocks

end YM.Gleam