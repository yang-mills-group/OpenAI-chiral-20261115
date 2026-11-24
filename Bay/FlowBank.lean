import Bay.Flare
import YM.Push.STATIONARY_UNIFORM.Count
import YM.Corona.Fit
import YM.CF.Vow.Year
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 800000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Bay
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open Skye Scree Cadre Palot
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open Cube Lat Tulip Fock Rush Scroll Paige Vault Phase Acorn Spire
open Pastry Vow Rue
attribute [local instance] opCStarAlgebra
open Hake Jet Sault Stax Sour
attribute [local instance] Sour.loreM Sour.loreN
open Rill Branch Tenant Drapes Leaf
open Mew PowerSeries
open scoped YM.CF.Mew
variable {n:Side} {P:BudgetPoint}

open Push.Uniform
variable {n':Side}
variable {I : Type} [Fintype I] {B:ℕ}
  {a b e:ℝ}
-- spend e, charge incidence at a. M_e links count
abbrev incE (e:ℝ)(B:ℕ):ℝ:= e/(6*B+2)
abbrev incT (M B:ℕ)(e:ℝ)(V:ℝ):ℝ:=(M:ℝ)*countCost (incE e B)*V
lemma impactEx {X:Aura n}{x y:Seat n}(k:x∈X.val)(u:y∈X.val)(e:ℝ)(t:0≤e):
  incE e B * separation x y ≤ e*widthK n B X :=by
 rw [incE,div_mul_eq_mul_div,div_le_iff₀ (by positivity)]
 have v:(separation x y:ℝ) ≤ widthK n B X * (4*B+2)+2*B:= by
    unfold widthK; exact_mod_cast Corona.extent X.val B k u
 have w:1 ≤ widthK n B X:= (vigor n B).pos X -- tune
 apply (mul_le_mul_of_nonneg_left v t).trans
 simpa only [mul_one] using
   (show e*(widthK n B X * (4*B+2)+2*B) ≤ e*widthK n B X*(6*B+2) from by
    nlinarith only [mul_nonneg (mul_nonneg t (Nat.cast_nonneg B)) (sub_nonneg.mpr w)])

lemma payoffRise {M:ℕ}(g:0<e)
 (σ:I→Seat n)(p:Multiplicity σ M)(c:I→ Aura n → ℝ)(s:ℝ)
 (γ:∀ i X,0 ≤ c i X) (t:∀ i (X:Aura n), σ i∉X.val→ c i X=0)
 (u:∀ i,voyageB (c i) B (a+e)≤ s)
 (h:0≤ s) (x:Seat n):
 tallB (riseF c) B a x ≤ incT M B e s :=by
 unfold tallB
 simp only [riseF,sum_mul]
 rw [sum_comm]
 let f(i):=Decay (incE e B) x (σ i)
 have hp(i:I): tallB (c i) B a x ≤ f i * s:=by
   unfold tallB
   apply le_trans _ (mul_le_mul_of_nonneg_left (u i) (decay_pos ..).le)
   let T:=univ.filter (fun Y:Aura n=>x∈Y.val)
   have hh(Y:Aura n):0≤c i Y*tact (a+e) B Y:=mul_nonneg (γ ..) (Real.exp_pos _).le
   have ht:=sum_le_sum_of_subset_of_nonneg (subset_univ T)
       (fun Y _ _=>hh Y)
   apply le_trans _ (mul_le_mul_of_nonneg_left ht (decay_pos ..).le)
   rw [Finset.mul_sum]
   apply sum_le_sum
   intro Y j
   by_cases k:σ i∈Y.val
   · change c i Y*Real.exp (a*widthK n B Y) ≤ Real.exp (-incE e B*separation x (σ i))*(c i Y*Real.exp ((a+e)*widthK n B Y))
     rw [mul_left_comm, ←Real.exp_add]

     apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr _) (γ ..)
     nlinarith only [impactEx (B:=B) (mem_filter.mp j).2 k e g.le]
   rw [t i Y k,zero_mul,zero_mul,mul_zero]
 apply (sum_le_sum fun i _=> hp i).trans
 rw [←Finset.sum_mul]
 have h':0 < incE e B:=by unfold incE; positivity
 exact mul_le_mul_of_nonneg_right (p.count σ h' x) h



-- vouchers, root set A varies. gap incidence
variable {q:ℕ}{h:ℝ}
structure Grounds (P:BudgetPoint)(q:ℕ)(A:I→Support (More n))
 (h:ℝ)(m:I→ Sour.Bag n)(Q R:I→Aura n→ℝ)(s c r:ℝ):Prop where
    bill: ∀ i, Orchard P q h (m i) (Q i) (R i)
    far: ∀ i (X:Aura n), ¬ A i⊆ X.val → m i X=0 ∧ Q i X=0 ∧ R i X=0
    full: ∀ i, voyageB (Q i) P.B s ≤ c
    birth: ∀ i, voyageB (R i) P.B s ≤ r
lemma sow {m:I→Sour.Bag n}{A:I→Support (More n)}{s c r:ℝ}
 (p:∀ i,Barrage P q (A i) h (m i) s c r) :
 ∃ Q R: I→ Aura n→ℝ,Grounds P q A h m Q R s c r:=by
 have hv(i):=(p i).price
 choose Q R y using hv
 exact ⟨Q,R,fun i=>(y i).1,fun i=>(y i).2.1,fun i=>(y i).2.2.1,fun i=>(y i).2.2.2⟩
namespace Grounds
variable {c r s:ℝ}{M:ℕ}{m:I→ Sour.Bag n}{A:I→Support (More n)}{Q R:I→Aura n→ℝ}
variable (f: Grounds P q A h m Q R s c r)
include f
lemma tie (σ:I→Seat n)(p:∀ i,σ i∈ A i): Tether σ m:=
  fun i X h => (f.far i X (fun t=>h (t (p i)))).1 -- f include

lemma grants (k:a+e ≤ s)(σ:I→Seat n)(p:∀ i,σ i∈A i)(u:Multiplicity σ M)
 (z:0<e) :
 (∀ x,tallB (riseF Q) P.B a x ≤ incT M P.B e |c|) ∧
 ∀ x,tallB (riseF R) P.B a x ≤ incT M P.B e |r| :=by
 have hh(i):0≤Q i:=fun X=>(f.bill i X).tube.price
 have ht(i):0≤R i:=fun X=>(f.bill i X).forms.choose_spec.1.price
 exact ⟨payoffRise z σ u _ _ hh
    (fun i X h=>(f.far i X (fun t=>h (t (p i)))).2.1)
    (fun i=>(voyage_π (hh i) k).trans ((f.full i).trans (le_abs_self _))) (abs_nonneg _),
   payoffRise z σ u _ _ ht
    (fun i X h=>(f.far i X (fun t=>h (t (p i)))).2.2)
    (fun i=>(voyage_π (ht i) k).trans ((f.birth i).trans (le_abs_self _))) (abs_nonneg _)⟩
end Grounds
end YM.CF.Bay
