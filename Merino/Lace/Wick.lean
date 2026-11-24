import Merino.Lace.Ribbon
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


def leadCoin (f:Stripe G→ℝ) (α:ℝ) := armPay^2*(α^2/palette f)
lemma shines (f:Stripe G→ℝ)(α:ℝ)(p:0<α): 0<leadCoin f α:= 
  mul_pos (pow_pos gold 2) (div_pos (pow_pos p 2) (blooming f))
lemma reduceExpense (L ε:ℝ)(p:0<ε):
  ∃ e>0,2*(L^2*rebate e armPay) ≤ ε:=by
 have h: Tendsto (fun x=>2*(L^2*rebate x armPay)) (𝓝[>] (0:ℝ)) (𝓝 0):=by
    have w:Continuous (fun x=>2*(L^2*rebate x armPay)):=by unfold rebate; fun_prop
    simpa [rebate] using (w.tendsto 0).mono_left nhdsWithin_le_nhds
 obtain ⟨a,g,d⟩:= ((show ∀ᶠ x:ℝ in 𝓝[>]0,0<x from self_mem_nhdsWithin).and
                      (h.eventually (ge_mem_nhds p))).exists
 exact ⟨a,g,d⟩

variable (T:Bundle G n) (t:ℕ)
/-- Wick splits into square of disconnected, plus signal from
constant-curvature-tested collapsed coefficients at Maxwell lag.
Uniform absolute error at lag⁸ scale. -/
def illuminated(ε:ℝ):Prop:=
 |miles t^8*(seance B P T (showtime n t)-(pour T (toss B P 1 1))^2)
          - 2*(armPay^2*pigment T)| ≤ ε


theorem burning (G:Gauge)(q:Clip)(L:ℝ)(δ:ℝ) (a:0<v)(s₁:0<w)
   (ε:ℝ)(E:0<ε):
 ∀ᶠ t in atTop, ∀{m:ℕ}{n:Side}, Reach t m→Steam n t→Even n.val→
 ∀ {H:Bed},H.covered w v→Floor H q n δ v→Bid.Sworn H n G→
 ∀ {Z:PathData G}{η C S:ℝ}(B:Z.Bounds q η C S)(P:Attached H Z)(T:Bundle G n),
  Sheath 0 m L T→ illuminated B P T t ε:=by
 obtain ⟨e,h,u⟩:=reduceExpense L ε E
 filter_upwards [eventually_all.mpr (fun x=>eventually_all.mpr
    (fun y=>rainbow x y q δ s₁ a e h))] with t w₁
 intro m n y p g H d f o Z η C S B P T k
 exact (bouquet B P k f o gold h (kissing B P h y g s₁ d f
     (fun i j z r=>w₁ i j z r n p g H d f))).trans u


lemma illum_charge (f:Stripe G→ℝ)(α:ℝ)(p:0<α)
   (y:α≤dripQ T (f∘ridge) (f∘ridge))
   (b:illuminated B P T t (leadCoin f α)):
   leadCoin f α ≤ (miles t)^8*seance B P T (showtime n t) :=by
 have g:leadCoin f α≤ armPay^2*pigment T :=
   mul_le_mul_of_nonneg_left (rich_pos T f α p y) (sq_nonneg _)
 have e:0≤ miles t^8:=by unfold miles; positivity


 unfold illuminated at b
 linarith only [g,neg_le_of_abs_le b, mul_nonneg e (sq_nonneg (pour T (toss B P 1 1)))]

end YM.CF.Merino.Lace
