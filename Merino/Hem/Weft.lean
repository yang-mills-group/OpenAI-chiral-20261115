import Merino.Hem.Scar
set_option linter.unusedSectionVars false
set_option maxHeartbeats 600000
set_option autoImplicit false
noncomputable section
namespace YM.CF.Merino.Hem
open Cuff MeasureTheory RG
open Function Finset Lattice Wilson
open scoped InnerProductSpace Topology
variable {G:Gauge}{N:Side}

variable {I:Type}[Fintype I]
variable {m:ℕ}{τ r C E:ℝ}
variable {f:I→Config G N→ℂ}{t:I→Bundle G N}
variable (a:I→ℝ) -- signed weights
def purl(a:I→ℝ)(f:I→Config G N→ℂ):Config G N→ℂ:=fun V=> ∑ i,(a i:ℂ)*f i V
def dart(a:I→ℝ)(t:I→Bundle G N):Bundle G N:=fun x y=>∑ i,a i*t i x y

lemma dart_reads(a:I→ℝ)(t:I→Bundle G N)(X Y:Husk G N→ℝ):
    dripQ (dart a t) X Y=∑ i,a i*dripQ (t i) X Y:=by
 simp_rw [dripQ,dart,sum_mul,sum_comm (f:=fun (y:Husk G N) i=>a i*t i _ _ * _)]
 rw [sum_comm]
 simp_rw [mul_sum,←mul_assoc]

variable (p:∑ i,|a i|=1)
include p
lemma dart_pays(h:∀ i, Sheath 0 m C (t i)):
   Sheath 0 m C (dart a t):=by
 refine ⟨fun x y=>sum_congr rfl fun i _=> by rw [(h i).flip],?_,?_⟩
 · rw [laden_l]
   refine le_trans (b:= ∑ x,∑ y,∑ i,|a i| * |t i x y|) ?_ ?_
   · simp_rw [←abs_mul]
     exact sum_le_sum fun x _=>sum_le_sum fun y _=> abs_sum_le_sum_abs ..

   simp_rw [sum_comm (f:=fun (y:Husk G N) i=>|a i| * |t i _ y|)]
   rw [sum_comm]
   rw [show C=(∑ i,|a i|)*C from by rw [p,one_mul]] -- tune
   simp_rw [sum_mul, ←mul_sum,←laden_l]
   exact sum_le_sum fun i _=>mul_le_mul_of_nonneg_left (h i).rent (abs_nonneg _)
 intro x y l
 by_contra u
 exact l (sum_eq_zero fun i _=>by rw [not_not.mp (mt ((h i).abode x y) u),mul_zero])

lemma a_bound {z:I→ℂ}{R:ℝ}(h:∀ i,‖z i‖≤R):
    ‖∑ i,(a i:ℂ)*z i‖≤R:=by
 refine (norm_sum_le ..).trans ?_
 simp_rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
 exact (sum_le_sum fun i _=>mul_le_mul_of_nonneg_left (h i) (abs_nonneg (a i))).trans_eq (by rw [←sum_mul,p,one_mul])

/-- Even if needing to subtract constants (complex) for component stencils,
if weighted constant cancels then buy Scar itself. -/
def Flap(m:ℕ)(τ r C E:ℝ)(f:Config G N→ℂ)(T:Bundle G N)(D:ℂ):Prop:=
 Sheath 0 (slim m) C T ∧ (∀ V,‖f V‖≤C) ∧ Measurable f ∧ LocalOn (Yardlet N m) f ∧ GaugeInvariant f ∧
 ∀ V (Y:Directions G N), ‖Y‖≤r→Lave τ (Yardlet N m) V→ Agrees (Yardlet N m) V (increment 1 Y) →
   ‖f V-(D+dripQ T (cseed Y) (cseed Y))‖≤ C*‖Y‖^3+E

variable {D:I→ℂ}
lemma pleated (h:∀ i,Flap m τ r C E (f i) (t i) (D i))(l:∑ i,(a i:ℂ)*D i=0):
    Scar m τ r C E (purl a f) (dart a t):=by
 simp only [Flap] at h
 choose hh hv hf he hu heq using h
 refine ⟨dart_pays a p hh,fun V=>a_bound a p (fun i=>hv i V),?_,?_,?_,?_⟩
 · exact Finset.measurable_sum _ fun i _=>measurable_const.mul (hf i)
 · intro U V hUV; unfold purl
   exact sum_congr rfl fun i _=>by rw [he i _ _ hUV]
 · intro b V;unfold purl
   exact sum_congr rfl fun i _=>by rw [hu i]
 intro V Y y hy r
 have b:=a_bound a p (fun i=>heq i V Y y hy r)
 simp only [purl,dart_reads,Complex.ofReal_sum,Complex.ofReal_mul]
 simpa only [mul_sub,sum_sub_distrib,mul_add,sum_add_distrib,l,zero_add] using b
