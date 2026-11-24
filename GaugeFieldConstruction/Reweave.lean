import GaugeFieldConstruction.Sclera
/-!
# Lifted response versus Taylor of underlying argument.
-/
set_option autoImplicit false
set_option maxHeartbeats 50000
set_option quotPrecheck false
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.TableF
open Function Filter Metric Lattice Wilson Finset MeasureTheory RG Precision Tree
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open FlightFlux Fluxim
open Fock Tulip Lat Spire Phase Cube
attribute [local instance] opCStarAlgebra
open AnalyticBridge VerifiedReset Taxi
open Lenten
open Stationary Vault Font
open Bank Laurent Bloch Tap Hove Spire
open Haro Peaks Rush Fir Next.Free Thorn
open Planned.PrimaryIntegral295 Carrier
namespace Boom
variable {c f:Side} {G:Ratio c f}{M:Male}{b:Bool}
section
variable {E:Type*}
-- no global Pi norm
abbrev Ytax (y:E→ ℝ)(S:Finset E)(f:E→ℂ):= ∑ t∈S,y t*‖f t‖
lemma DignityY (y:E→ℝ)(p:∀ x,0≤y x)(S:Finset E): Dignity (Ytax y S):=by
 refine ⟨fun x=>sum_nonneg (fun i _=>mul_nonneg (p _) (norm_nonneg _)),fun x z=>?_,fun a x=>?_⟩; · unfold Ytax; rw [← sum_add_distrib]; exact sum_le_sum fun i _=> (mul_le_mul_of_nonneg_left (norm_add_le ..) (p i)).trans_eq (mul_add ..)
 unfold Ytax; simp only [Pi.smul_apply,norm_smul,Real.norm_eq_abs]; rw [mul_sum]; exact sum_congr rfl fun _ _=> by ring
end
variable {U σ:ℝ}{n r:ℕ}{A:Site f}
local notation "jₛ"=> BudgetX G σ U
local notation "ρ"=> αN G.count
variable (p:Honed G.count M b U σ)(h:0<U)(w:0<σ)(T:Odd G.count.val)
abbrev Ytab (M:Male)(G:Ratio c f)(A:Site f)(b:Bool)(i:Kt)(x:Cover):= ware G A M b [] x i
def polynomialY (M:Male)(G:Ratio c f)(A:Site f)(b:Bool)(i:Kt)(r:ℕ) := wheelK (Ytab M G A b i) r
abbrev errorY (M:Male)(G:Ratio c f)(A:Site f)(b:Bool)(i:Kt)(x:Cover)(r:ℕ):= Ytab M G A b i x-polynomialY M G A b i r x
def ChipY (M:Male)(G:Ratio c f)(A:Site f)(b:Bool)(i:Kt)(r:ℕ):Cover→ Mill → ℂ:= match r with|0=>curb (Ytab M G A b i)|1=> slopeK (Ytab M G A b i)|2=>ticketK (Ytab M G A b i)| _+3=>0
lemma chip_more (i:Kt)(r:ℕ)(k:r<3): polynomialY M G A b i (r+1)= ChipY M G A b i r+polynomialY M G A b i r:=by
 interval_cases r
 · rw [show polynomialY M G A b i 0=0 from rfl,add_zero]; rfl
 · exact add_comm ..
 exact add_comm ..
lemma Xi_more (r:ℕ)(k:r≤3)(i:Kt): Ytab M G A b i= polynomialY M G A b i r+ fun x=> errorY M G A b i x r:=by funext x a; exact (add_sub_cancel ..).symm -- ext ℂ ambiguous ext target
private lemma Asepit (F:Cover→Mill→ℂ) (l:List Axis)(x: Cover)(i:Mill): loom l F x i= loom l (fun x=> F x i) x:=by induction l generalizing x with|nil=>rfl|cons a l ih=>rw [loom_cons,loom_cons]; change loom l F (_+_) i-loom l F _ i=_; rw [ih,ih]; rfl
include p h w
lemma slate (A:Site f)(i:Kt)(x:Cover)(n:ℕ): chime (wagN n) (Ytab M G A b i x) (BudgetX G σ U n*(usingF G x)^n):=by convert gene_budget (A:=A) p h w x i [] (by simp) n using 1; simp
include T
lemma Y_Goose (S:Finset Mill)(A:Site f)(i:Kt) (n:ℕ)(v:n≤3): Goose (DignityY (wagN n) (fun _=>zero_le_one.trans (wagE ..)) S) (BudgetX G σ U n) ρ (Ytab M G A b i) 3:=by
 have he:= Bux_pos G U σ h w n; have hv:=α_pos G.count; refine ⟨he.le,hv.le,fun l x k=>?_⟩
 have hQ:loom l (Ytab M G A b i) x=ware G A M b l x i:=funext fun j=> (Asepit _ _ _ _).trans (congrFun (X_one G T A M b l i j k) x)
 rw [hQ]; apply (SBleast (gene_budget (A:=A) p h w x i l k n) S).trans -- tune named implicit placement
 exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (using_v G x) v) (mul_nonneg he.le (pow_nonneg hv.le _))
lemma GoaErr (A:Site f) (i:Kt)(n r:ℕ)(k:n≤3)(v:r ≤3)(x:Cover): chime (wagN n) (errorY M G A b i x r) (12*BudgetX G σ U n*ρ^r*Ladder x^3):=by
 apply SBwork (fun j=> mul_nonneg (zero_le_one.trans (wagE _ _)) (norm_nonneg _)); intro S
 exact Goa_total _ _ _ _ r v x ((Y_Goose p h w T S A i n k).lower v) (αsmall _)
lemma GoaChip(A:Site f)(i:Kt)(n r:ℕ)(k:n≤3)(v:r<3)(x:Cover): chime (wagN n) (ChipY M G A b i r x) (BudgetX G σ U n*ρ^r* Ladder x^r):=by
 let Q:=jₛ n; let F:= Ytab M G A b i; have hQ:0≤Q:=(Bux_pos G U σ h w n).le; have hu:0 ≤ ρ:= (α_pos _).le
 apply SBwork (fun j=> mul_nonneg (zero_le_one.trans (wagE j n)) (norm_nonneg _)); intro S; let V:=Ytax (wagN n) S; have Z:=Y_Goose p h w T S A i n k; have he:Dignity V:=DignityY (wagN n) (fun i=> zero_le_one.trans (wagE i n)) S -- tune proof
 have hh(i:List Axis)(v:i.length≤3): V (loom i F 0) ≤ Q * ρ^i.length:= by simpa only [lateral_zero,Nat.cast_zero,mul_zero,add_zero,one_pow,mul_one] using Z.H i 0 v
 let A:= Ladder x
 have hp:(lateral x:ℝ)≤A:= le_add_of_nonneg_left zero_le_one
 have hx:0 ≤ (lateral x:ℝ):=Nat.cast_nonneg _
 interval_cases r
 · change V (F 0)≤ Q*ρ^0*A^0; exact (hh [] (by simp)).trans_eq (by simp)
 · change V (slopeK F x)≤ Q*ρ^1*A^1; rw [pow_one,pow_one]; apply (scaleStance he F x (Q*ρ) (fun i=>(hh [i] (by simp)).trans_eq (by simp))).trans; exact (mul_le_mul_of_nonneg_right hp (mul_nonneg hQ hu)).trans_eq (mul_comm ..)
 change V (ticketK F x) ≤ Q*ρ^2*A^2; apply (GoldT he F _ _ (show 0≤Q*ρ^2 from by positivity) (fun i j=> by simpa only [loom_cons,List.length_cons,List.length_nil,Nat.zero_add, show loom [] F=F from rfl] using hh [i,j] (by simp))).trans
 exact (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hx hp 2) (mul_nonneg hQ (sq_nonneg _))).trans_eq (mul_comm ..)
end Boom
end YM.CF.TableF
end
