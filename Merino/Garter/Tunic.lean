import Merino.Garter.Post
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 600000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Merino.Garter
open Function Lattice Finset RG Wilson Metric Exterior Work.F03
open Regis.Head MeasureTheory
open scoped Topology ContDiff InnerProductSpace Classical Matrix.Norms.Frobenius
variable {n:Side}{G:Gauge}

open Cuff Hem
variable {I:Type*}
open Tree Filter Precision Next.Rank.Spindle Pressure ProbabilityTheory
open Gleam Next.SectorChange Next.SectorChange.Gaussian
open Etch -- (includes river)
open StepIn
variable {c:Side}{r:Ratio c n}{H:Bed}{m:ℕ}{p:BudgetPoint}{q:Clip}{v η S C δ w β:ℝ}{A:Support c}{N:Finset (Cell n)}{Z:PathData G}

abbrev meanTick(q:Clip)(L M:ℝ):=L^2*(4*(M⁻¹)^2*noodlePrice (glint q))
abbrev spikeTick(q:Clip)(L M P:ℝ):= 2*Regis.trend*(salt q L*M^3)^2*P
def lost(q:Clip)(L e0 h M P:ℝ):=
 meanTick q L M + sceneTick L e0 h M P + spikeTick q L M P

variable {L e0 h M τ E:ℝ}{f:Config G n→ℂ} {T:Bundle G n}
variable (B:Z.Bounds q η C S)(P0:Attached H Z){R:Rules G}{z P:ℝ}

section Cone
lemma buoy (T u s π w z g A X :ℝ) (p:0≤T)
 (e:|u-s|≤w)(v:|z|≤π)
 (d:w+g+2*Regis.trend*A^2*π ≤X):
  2*(T*(z*u))+2*(T*(|z| *g))+Regis.trend*(A*|z| *Real.sqrt T)^2*2^2 ≤
   2*(T*(z*s+|z| *X)):=by
 have h0:0≤Regis.trend:=by unfold Regis.trend; positivity
 have k:z*u ≤ z*s+ |z| * w:= sub_le_iff_le_add'.mp <|
     by rw [← mul_sub]; exact (le_abs_self ..).trans ((abs_mul ..).trans_le (mul_le_mul_of_nonneg_left e (abs_nonneg _)))


 have r:z*u+ |z| *g +2*Regis.trend*A^2*|z|^2 ≤z*s+|z| *X:= calc
    _ ≤ z*s + |z| * w + |z| * g +2*Regis.trend*A^2*(|z| *π):=by
       rw [pow_two |z|]
       exact add_le_add (add_le_add_left k _) (by gcongr)
    _ = z*s + |z| *(w+g+2*Regis.trend*A^2*π):=by ring
    _ ≤ _:=add_le_add_right (mul_le_mul_of_nonneg_left d (abs_nonneg _)) _
 rw [mul_pow,Real.sq_sqrt p] -- mul_pow A? arg
 calc
   _ = 2*(T*(z*u+|z| *g +2*Regis.trend*A^2*|z|^2)):=by ring
   _ ≤ _:=mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left r p) (by positivity)


end Cone

section Coat
variable {X:ℝ}  -- total error allowance per |z|sample
variable [Fintype I]{j:I→StepIn n}{g:Duo n}
variable (b:I→Tint)(ℓ:Floor H q n δ w)(o:Bid.Sworn H n G)
include ℓ o

lemma glimmer
 (t:Scar (shellC m) p.threshold τ L E f T)
 (u:Offer R p m L β E τ e0 h M P v)
 (k:hallBill m ≤ r.count.val/2)(d:Odd r.count.val)
 (hj:Pavilion (wiggle m) g j)
 (bill:lost q L e0 h M P ≤ X)
 (hp:|z|≤P)(s₀:ℝ)(a:StepIn n):
 let f₀(V):=lorg β z g m f j b (a.cabin V)
 GaugeInvariant f₀ ∧ ∃ (W:Altar G n→ℝ)(R₁ R₂ y:ℝ),
   ContDiff ℝ 1 W∧(∀ i,|W i|≤ R₁)∧(∀ i,‖fderiv ℝ W i‖≤R₂)∧
   plumeCost B P0 W 2+y+Regis.trend*R₂^2*2^2≤
      2*(Fintype.card I*(z*seance B P0 T g + |z| *X)) ∧
   ∀ A N, RimScene B P0 p r m β v (y+1*fritTrap r m A N) s₀ A N 2 f₀ W:=by


 intro f₀
 let jj(i:I):=a*j i
 have hjj:Pavilion (wiggle m) g jj:=hj.turn a
 rw [show f₀=lorg β z g m f jj b from funext fun V=>lorg_turn ..]
 let K:ℝ:=Fintype.card I
 have L0:0≤L:=(norm_nonneg _).trans (t.bound 1)
 refine ⟨lorg_inv _ _ _ _ _ t.sang,
        displayBoard T q M⁻¹ g jj z,
        |z| *(K*((L*M^2)^2)),
        salt q L*M^3*|z| *Real.sqrt K,
        2*(K*(|z| *sceneTick L e0 h M P)),
        board_smooth ..,board_free q t.cloth.rent u.mp _ _ _,
        board_toll q t.cloth.rent u.mp L0 hjj _,?_,fun A N=>?_⟩
 · rw [hallFee B P0 T ℓ o u.mp]
   exact buoy K _ _ _ _ _ _ _ _ (Nat.cast_nonneg _) (meal_gap _ _ _ _ _ t.cloth.rent) hp bill
 rw [one_mul]; exact postRim B t u k d hjj b hp s₀
#check board_free
#check board_smooth
#check meal_gap

end Coat
end YM.CF.Merino.Garter
