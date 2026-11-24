import Merino.Garter.Cupful
import Merino.Garter.Museum
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

variable (B:Z.Bounds q η C S)(P:Attached H Z)
local notation "wE"=>stamen B P n
local notation "χ"=>stdGaussian wE
local notation "J"=>Husk G n

-- Real Gaussian linear stats
def streamC(a:StepIn n)(i:Husk G n) : stamen B P n →L[ℝ] ℝ :=
  (silver q a i).comp (stamen B P n).subtypeL
abbrev rice(d:ℝ)(g:Duo n)(x:wE)(i j k l:J):=
 dishX (streamC B P g.1 i) (streamC B P g.1 j)
    (streamC B P g.2 k) (streamC B P g.2 l) d x
abbrev rent(d:ℝ)(g:Duo n)(i j k l:J):=
 noodle (streamC B P g.1 i) (streamC B P g.1 j)
        (streamC B P g.2 k) (streamC B P g.2 l) d
lemma affordable(a:StepIn n)(i:J):‖streamC B P a i‖ ≤ glint q:= 
  ContinuousLinearMap.opNorm_le_bound _ (holm q).le fun x=> silver_norm q a i x.val
variable (T:Bundle G n)(d:ℝ)(g:Duo n)
lemma rice_int(i j k l:J) : Integrable (fun x:wE=>rice B P d g x i j k l) (stdGaussian wE):= 
 idish ..


lemma displayRice(x:wE):
  couple T q d g x.val = batches T (rice B P d g x) :=
 (batches_prod (fun i j=>shine q d g.1 x.val i*shine q d g.1 x.val j)
    (fun i j=>shine q d g.2 x.val i*shine q d g.2 x.val j)).symm
lemma moments : meanD B P T d g= batches T (rent B P d g):=by
 unfold meanD clouds
 simp_rw [displayRice B P]
 exact batches_pull _ (rice_int B P d g)
lemma meal_low{L:ℝ}(t:laden T≤L): 
  |meanD B P T d g|≤ L^2*noodlePrice (glint q):=by
 rw [moments]
 apply batches_abs t (by unfold noodlePrice tile; positivity)
 exact fun i j k l _ _=> noodle_sup _ _ _ _ (affordable B P _ _) (affordable B P _ _)
    (affordable B P _ _) (affordable B P _ _) _
lemma meal_gap{L:ℝ}(t:laden T≤L):
 |meanD B P T d g-seance B P T g|≤ L^2*(4*d^2*noodlePrice (glint q)):=by
 rw [moments, seance,moments,batches_sub]
 apply batches_abs t (by unfold noodlePrice tile; positivity)
 exact fun i j k l _ _=> noodle_gap _ _ _ _ (affordable B P _ _) (affordable B P _ _)
    (affordable B P _ _) (affordable B P _ _) _
end YM.CF.Merino.Garter
