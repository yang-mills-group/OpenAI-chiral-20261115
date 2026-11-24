import Organdy.Shower
import Organdy.Cumulus
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.flexible false
set_option maxHeartbeats 500000
noncomputable section
namespace YM.CF.Organdy.Optic
open Function Filter MeasureTheory Finset

open Regis Head Lattice Precision Wilson Pressure Work.F03 Exterior
open Larva (Chip Tint dot blush stains decree wet_iff)
variable {n N:Side}
local notation "G" => SU.group

open RG Gleam ProbabilityTheory
open scoped InnerProductSpace ComplexConjugate
variable {M:Bed}{Z:PathData G}{q: Clip}{ρ θ v a η C:ℝ}


-- pose-tangent
def sough(q:Clip)(ρ:ℝ)(s:Signed)(b:Site n)(x:Altar G n)(i:Chip n):ℝ:=
  let j:=relay s b i
  ρ*draftSig s i*(Etch.river q j.1 x j.2)
def unfurl(q:Clip)(k ρ:ℝ)(A:Ink (Chip n))(s:Signed)(b:Site n)(x:Altar G n):ℂ:=
  air k A (sough q ρ s b x)
def compose(q:Clip)(k ρ:ℝ)(A:Ink (Chip n))(y:Site n)(s:Signed)(b:Site n)
   (x:Altar G n):ℝ:=
   ((unfurl q k ρ A s b x) * conj (unfurl q k ρ A (s*mir) (affine s b y) x)).re

lemma sough_see(B:Z.Bounds q θ v a)(P:Attached M Z)
 (ρ:ℝ)(s:Signed)(b:Site n)(X:Larva.Dir n)(i:Chip n):
 sough q ρ s b (tiler B P X) i = ρ*blush (bank s b X) i:=by
 rw [blush_bank,sough];dsimp only;rw [Etch.river_now,mul_assoc]

lemma sough_smooth (s:Signed)(b:Site n)(i:Chip n):
 ContDiff ℝ 1 (fun x=>sough q ρ s b x i):=by
 unfold sough
 let j:=relay s b i
 let f:= (EuclideanSpace.proj j.2).comp (Etch.river q j.1 : Altar G n →ₗ[ℝ] SU.group.Color).toContinuousLinearMap
 change ContDiff ℝ 1 fun x=>_ * f x
 fun_prop

lemma unfurl_smooth {k:ℝ}(h:0<k)(A:Ink (Chip n))(s:Signed)(b:Site n):
 ContDiff ℝ 1 (unfurl q k ρ A s b):=by
 let L:=sough q ρ s b
 have hL(i): ContDiff ℝ 1 (fun x=> L x i) := sough_smooth ..
 unfold unfurl air haze read
 refine ContDiff.sum (fun i _=>ContDiff.mul contDiff_const ?_)
 exact Complex.ofRealCLM.contDiff.comp ((mist_smooth h).comp
       ((hL i.1).add (ContDiff.mul contDiff_const (hL i.2.1))))

lemma compose_smooth {k:ℝ}(h:0<k)(A:Ink (Chip n))(y:Site n)(s:Signed)(b:Site n):
 ContDiff ℝ 1 (compose q k ρ A y s b):= by
 exact Complex.reCLM.contDiff.comp ((unfurl_smooth h A s b).mul
   (Complex.conjCLE.contDiff.comp (unfurl_smooth h A _ _)))

variable (B:Z.Bounds q θ v a)(P:Attached M Z)(L:Floor M q n η C)(O:Bid.Sworn M n G)
  {k:ℝ}(pk:0<k)

lemma unfurl_two (ρ:ℝ)(A:Ink (Chip n))(s t:Signed)(b c:Site n)(X:Larva.Dir n):
   unfurl q k ρ A (s*t) (affine s b c) (tiler B P X)=
    unfurl q k ρ A t c (tiler B P (bank s b X)):=by
    unfold unfurl;apply congrArg
    funext i
    rw [sough_see,sough_see,tandem]

lemma hitched (ρ:ℝ)(A:Ink (Chip n))(y:Site n)(s:Signed)(b:Site n)(X:Larva.Dir n):
 compose q k ρ A y 1 0 (tiler B P (bank s b X))=
    compose q k ρ A y s b (tiler B P X):=by
 simp_rw [compose,←unfurl_two]; simp [affine]

abbrev monetary (k ρ:ℝ)(A:Ink (Chip n))(y:Site n):ℝ:=
  clouds B P (compose q k ρ A y 1 0)

include pk L O in
lemma even_keel (ρ:ℝ)(A:Ink (Chip n))(y:Site n)(s:Signed)(b:Site n):
 clouds B P (compose q k ρ A y s b) = monetary B P k ρ A y:=by
 symm
 apply cover_calms s b B P L O _ _ (compose_smooth pk A _ _ _|>.continuous)
 intro i; exact hitched ..
