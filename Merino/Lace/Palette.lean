import Merino.Lace.Pipes
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 600000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Merino.Lace
open Garter Regis.Circuit CF.Lat
open Stationary (Gaia)
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

variable (B:Z.Bounds q η C S)(P:Attached H Z)
local notation "wE"=>stamen B P n
local notation "χ"=>stdGaussian wE
local notation "J"=>Husk G n


abbrev crossing(g:Duo n):=toss B P g.1 g.2
abbrev rebate(e z:ℝ):=e*(z+e)+z*e

lemma combo {a b c d z ε : ℝ}
    (x:|a-c|≤ε) (y:|b-d|≤ε) (u:|c|≤z)(v:|d|≤z):
   |a*b-c*d| ≤ rebate ε z:=by
 rw [show a*b-c*d=(a-c)*b+c*(b-d) from by ring]
 apply (abs_add_le ..).trans
 rw [abs_mul,abs_mul]
 have h:0 ≤ ε:=(abs_nonneg _).trans y
 have r:|b|≤z+ε:=(by nth_rw 1 [show b=d+(b-d) by ring];exact (abs_add_le ..).trans (add_le_add v y)) -- use abs_sub?
 exact add_le_add (mul_le_mul x r (abs_nonneg _) h)
   (mul_le_mul u y (abs_nonneg _) ((abs_nonneg _).trans u))


variable {T:Bundle G n}
abbrev Kiss (g:Duo n)(z l ε : ℝ)(r:ℕ) :=
 ∀ (i j:J), separation 0 i.1.1 ≤ r→separation 0 j.1.1 ≤ r→
 |l^4*crossing B P g i j-receiptVal z i j|≤ε

lemma bouquet {k:ℕ}{L z l ε:ℝ}{g:Duo n}(t:Sheath 0 k L T)
   (f:Floor H q n δ v)(o:Bid.Sworn H n G)
   (u:0<z)(a:0<ε)(h:Kiss B P g z l ε k):
 |(l^8)*(seance B P T g-(pour T (toss B P 1 1))^2)
         -2*(z^2*pigment T)|≤2*(L^2*rebate ε z):=by
 rw [stroke B P T g f o t.flip, add_sub_cancel_left,←chroma]
 rw [mul_left_comm,←mul_sub,abs_mul,abs_of_pos (by norm_num:0<(2:ℝ)), squareb, squareb,← batches_scale,
   batches_sub]
 apply mul_le_mul_of_nonneg_left _ (by norm_num)
 apply batches_abs t.rent (by unfold rebate; positivity)
 intro i j k' m' p v₁
 rw [show l^8=(l^4)*(l^4) from by ring,mul_mul_mul_comm]
 exact combo (h i k' (t.both p).1 (t.both v₁).1)
    (h j m' (t.both p).2 (t.both v₁).2) (by unfold receiptVal;split<;>simp [abs_of_pos u,u.le])
      (by unfold receiptVal;split<;>simp [abs_of_pos u,u.le])

end YM.CF.Merino.Lace
