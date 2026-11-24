import Merino.Garter.Coating
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
abbrev meanD (T:Bundle G n)(d:ℝ)(g:Duo n):= clouds B P (couple T q d g)
abbrev seance (T:Bundle G n)(g:Duo n):= meanD B P T 0 g
variable (T:Bundle G n)(d:ℝ)
lemma across0 (X:Dir G n)(a b:StepIn n):
 gleam T q d b (tiler B P (a.steer X))=
 gleam T q d (a*b) (tiler B P X):=by
 unfold gleam
 congr 1 <;>
   (ext i; unfold shine; rw [shadowC B P,shadowC B P, a.steer_mul b X])
variable (ℓ:Floor H q n δ v)(o:Bid.Sworn H n G)
include ℓ o in 
lemma across (a:StepIn n)(g:Duo n):
 meanD B P T d (a.rotate g)=meanD B P T d g:= 
 (cover_calms a.face a.there B P ℓ o (couple T q d g) _ 
   (couple_smooth .. |>.continuous)
    (fun x=>congrArg₂ (·*·) (across0 B P T d x _ _) (across0 B P T d x _ _))).symm


lemma visits {M:ℝ}(u:0<M)(g:Duo n):
 Integrable (fun x: stamen B P n=>couple T q M⁻¹ g x.val)
  (stdGaussian (stamen B P n)) :=
 Regis.bree _ _ ((couple_smooth q M⁻¹ g|>.continuous).comp
   continuous_subtype_val|>.measurable) (fun x=>couple_free q (T:=T) le_rfl u g x.val)
include ℓ o in
lemma hallFee [Fintype I]{M:ℝ}(u:0<M) (g:Duo n)(j:I→StepIn n)(z:ℝ):
 plumeCost B P (displayBoard T q M⁻¹ g j z) 2= 
   2*(Fintype.card I*(z*meanD B P T M⁻¹ g)):=by
 rw [plumeCost,cloud_turn B P (displayBoard T q M⁻¹ g j z) (board_smooth ..|>.continuous)]
 unfold clouds displayBoard
 rw [integral_const_mul,integral_finsetSum _ (fun i _=>visits B P T u _)]
 let f(i:I):=meanD B P T M⁻¹ ((j i).rotate g)
 change 2*(z* ∑ i,f i)=_
 unfold f
 simp_rw [across B P T M⁻¹ ℓ o _ g]
 rw [sum_const,card_univ,nsmul_eq_mul]
 ring

end YM.CF.Merino.Garter
