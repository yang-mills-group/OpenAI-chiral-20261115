import Merino.Lace.Trill
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


variable (T:Bundle G n)
lemma pour_flip(f:Husk G n→Husk G n→ℝ) (t:Cuff.symmetric T):
 pour T (swap f)=pour T f:=by
  unfold pour
  rw [Finset.sum_comm]
  simp only [Function.swap]
  exact sum_congr rfl fun i _=>sum_congr rfl fun j _=>by rw [t]

abbrev squareb(T:Bundle G n)(a:Husk G n→Husk G n→ℝ)
 :=batches T fun i j k l=>a i k*a j l
lemma stroke(g:Duo n)(e:Floor H q n δ v)(o:Bid.Sworn H n G)
   (t:Cuff.symmetric T):
  seance B P T g=
      pour T (toss B P 1 1)^2 + 2*squareb T (toss B P g.1 g.2):=by
  rw [seance, moments, show rent B P 0 g=_ from funext fun i=>funext fun j=>funext fun k=>funext fun l=>rent_wick B P e o g i j k l,batches_add,batches_add,batches_prod]
  have h(f:J→J→ℝ):batches T (fun i j k l=>f i l*f j k)=squareb T f:=
    congrArg (pour T) (funext fun i=>funext fun j=> pour_flip T _ t)
  rw [h,squareb];ring

abbrev δf(a:Stripe G)(i:Husk G n):ℝ:=if ridge i=a then 1 else 0
/-- δ-coincidence. -/
def receiptVal (v:ℝ)(i j:Husk G n):ℝ:=if ridge i=ridge j then v else 0
lemma hatch (i j:J): receiptVal 1 i j=∑ a:Stripe G,δf a i*δf a j := by
 unfold δf; simp [receiptVal,eq_comm]
-- compressed entries
abbrev tube(a b:Stripe G):= pour T (fun i j=>δf a i*δf b j)
def pigment :=∑ a:Stripe G,∑ b:Stripe G,(tube T a b)^2
lemma pour_many {I:Type}[Fintype I](f:I→J→J→ℝ):
   pour T (fun i j=>∑ a, f a i j)=∑ a,pour T (f a) :=by
  unfold pour
  simp_rw [mul_sum]
  rw [sum_comm (f:=fun a i=>∑ j,T i j*f a i j)]
  simp_rw [sum_comm (f:=fun a j=>T _ j*f a _ j)] -- unbound i?


lemma batches_many {I:Type}[Fintype I](f:I→J→J→J→J→ℝ):
 batches T (fun i j k l=>∑ a,f a i j k l)=∑ a,batches T (f a) :=by
 unfold batches
 simp_rw [pour_many]

lemma chroma(x:ℝ):squareb T (receiptVal x)=x^2*pigment T :=by
 have h₁(i k:J):receiptVal x i k=x*receiptVal 1 i k:=by simp [receiptVal,mul_ite]
 unfold squareb
 simp_rw [show ∀i j k l:J, receiptVal x i k *receiptVal x j l=
    x^2*∑ a:Stripe G,∑ b:Stripe G,(δf a i*δf b j)*(δf a k*δf b l) from by
      intro i j k l; rw [h₁ i k,h₁ j l]
      simp_rw [hatch]; rw [mul_mul_mul_comm, sum_mul_sum,←pow_two]
      congr 1;exact sum_congr rfl fun _ _=>sum_congr rfl fun _ _=>mul_mul_mul_comm ..]
 simp_rw [batches_scale,batches_many, batches_prod]
 simp [pigment,pow_two,tube]

def keyz :=Stripe G × Stripe G
lemma strike (f:Stripe G→ℝ): dripQ T (f∘ridge) (f∘ridge)=
   ∑ a:Stripe G,∑ b:Stripe G,tube T a b*(f a*f b):=by
 have h(i:J): f (ridge i) = ∑ a,δf a i*f a:=by unfold δf; simp


 rw [show dripQ T (f∘ridge) (f∘ridge)=pour T (fun i j=>∑ a,∑ b,
       (δf a i*δf b j)*(f a*f b)) from congrArg (pour T) (funext fun i=>funext fun j=> by
        simp only [Function.comp_apply]; rw [h i,h j, sum_mul_sum]
        exact sum_congr rfl fun a _=>sum_congr rfl fun b _=>mul_mul_mul_comm ..)]
 simp_rw [pour_many,tube,pour,sum_mul,mul_assoc]


def palette(f:Stripe G→ℝ):ℝ:= 1+∑ a:Stripe G,∑ b:Stripe G,(f a*f b)^2
lemma blooming (f:Stripe G→ℝ): 0<palette f:=by unfold palette; positivity
lemma rich (f:Stripe G→ℝ): (dripQ T (f∘ridge) (f∘ridge))^2 ≤ pigment T*palette f:=by
 have p:=sum_mul_sq_le_sq_mul_sq univ (fun i:(Stripe G × Stripe G)=>tube T i.1 i.2) (fun i=>f i.1 * f i.2)
 rw [strike];unfold palette pigment
 apply le_trans _ (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left zero_le_one) (by positivity))
 simpa only [Fintype.sum_prod_type] using p
lemma rich_pos(f:Stripe G→ℝ)(δ:ℝ)(u:0<δ)
   (w:δ≤dripQ T (f∘ridge) (f∘ridge)):
   δ^2 /palette f ≤ pigment T:=(div_le_iff₀ (blooming f)).mpr
   ((pow_le_pow_left₀ u.le w _).trans (rich T f))

end YM.CF.Merino.Lace
