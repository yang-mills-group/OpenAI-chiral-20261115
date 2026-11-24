import Merino.Garter.Duck
import YM.SU5.Thin.Avalanche.Shelter
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

open Regis.Resonance Brecht
section Four
variable {E:Type*}[NormedAddCommGroup E][InnerProductSpace ℝ E][MeasurableSpace E][BorelSpace E][FiniteDimensional ℝ E]
lemma mloan(a b:E):
 memo [a,b]=inner ℝ a b:=by 
 simpa [memo,payday,spanX] using appraisal a b
lemma wage(a b c d:E):
 (∫ x,inner ℝ a x*inner ℝ b x*(inner ℝ c x*inner ℝ d x)∂stdGaussian E)=
 inner ℝ a b * inner ℝ c d+
 inner ℝ a c * inner ℝ b d+
 inner ℝ a d * inner ℝ b c:=by
 trans memo [a,b,c,d]
 · simp [memo,payday,spanX,mul_assoc]
 rw [gramStein]
 simp [roster,mloan,add_assoc]
end Four


abbrev dartAt (a:StepIn n)(i:Husk G n): Body 2 n:=
 ((a.sent i.1).1,plaquette (a.sent i.1).2)
abbrev arch(a:StepIn n)(i:Husk G n) :=
   a.cost i.1 • trill B P i.2 (dartAt a i)
abbrev toss(a b:StepIn n)(i j:J):ℝ:=
   inner ℝ (arch B P a i) (arch B P b j)
lemma trill_s(a:StepIn n)(i:J)(x:wE):
   streamC B P a i x=inner ℝ (arch B P a i) x:=by
 erw [arch, real_inner_smul_left (trill B P i.2 (dartAt a i)) x (a.cost _), joy, dartAt,inspire]
 rfl


variable (e:Floor H q n δ v)(d:H.covered w v)(hw:0<w)(m₁:Even n.val)(o:Bid.Sworn H n G)
include e d m₁ hw in
lemma tossed (a b:StepIn n)(i j:J): (toss B P a b i j:ℂ)=
  ↑(a.cost i.1*b.cost j.1*sch (G:=G) i.2 j.2)*rimble n H (dartAt a i) (dartAt b j):=by
  have h:=chimes B P e d hw i.2 j.2 (dartAt a i) (dartAt b j) m₁
  simp_rw [←joy,appraisal] at h
  unfold toss arch
  erw [real_inner_smul_left (trill B P i.2 (dartAt a i)) (b.cost j.1 • trill B P j.2 (dartAt b j)) (a.cost _),real_inner_smul_right (trill B P i.2 (dartAt a i)) (trill B P j.2 (dartAt b j)) (b.cost _)]
  push_cast; rw [h]; ring


abbrev glitter(a:StepIn n)(q:Clip)(i j:J) :=
 fun x=>silver q a i x* silver q a j x
lemma glitters(a:StepIn n)(i j:J):
 clouds B P (glitter a q i j)=toss B P a a i j:=by
 change (∫ x:wE, streamC B P a i x*streamC B P a j x ∂χ) = _
 simp_rw [trill_s,appraisal]

include e o
lemma centers (a:StepIn n)(i j:J):
 toss B P a a i j=toss B P 1 1 i j:=by
 rw [←glitters,←glitters]
 symm; apply cover_calms a.face a.there _ _ e o
 · exact (silver q 1 i).cont.mul (silver q 1 j).cont
 have r:a*1=a:=by
    change (⟨a.face*1,a.apply1 0⟩:StepIn n)=a
    rw [mul_one,a.apply_zero]
 intro x; simp only [glitter]; simp_rw [shadowC]
 have v:=a.steer_mul 1 x;rw [r] at v
 rw [v]

lemma rent_wick(g:Duo n)(i j k l:J):
 rent B P 0 g i j k l=
 toss B P 1 1 i j*toss B P 1 1 k l+
 toss B P g.1 g.2 i k*toss B P g.1 g.2 j l+
 toss B P g.1 g.2 i l*toss B P g.1 g.2 j k:=by
 rw [←centers B P e o g.1 i j, ←centers B P e o g.2 k l]
 unfold Garter.rent noodle dishX dish bite
 simp_rw [trill_s]
 simp only [zero_mul,zero_pow (show (2:ℕ)≠0 by decide),add_zero,div_one]
 exact wage .. 

end YM.CF.Merino.Lace

