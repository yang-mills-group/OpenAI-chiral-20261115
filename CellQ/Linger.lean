import CellQ.Ratio
import Nankin.Bern
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4500
set_option maxHeartbeats 220000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance
namespace Spine
namespace PledgeT
open Calico
open Py.Rate.Pitching.Focus
variable (P:Spine) {U:P.Roster}(M:Morn P.par.K)
open Py.Dyad Keeping
lemma smallgeom {v:ℝ}(e:0≤ v)(u:v≤1/2)(n:ℕ): ∑ i ∈ range n, v^i ≤2:=by
 have h:(1-v)*∑ i∈range n,v^i= 1-v^n:=mul_neg_geom_sum v n
 let Y:ℝ:= ∑ i∈ range n,v^i
 have ht:0 ≤ Y:=Finset.sum_nonneg (fun i _=>pow_nonneg e _)
 change (1-v)*Y=1-_ at h; change Y ≤2; nlinarith only [mul_le_mul_of_nonneg_right u ht,h,pow_nonneg e n]

variable {F:ℕ}(C D:ℕ→ℕ→ℝ)(L:Side)(p:∀ s,F ≤ s→ Bills F (s+1) s L (C s) (D s))
local notation "W" i:max x:max=> revenue L (C i) (D i) i x
include p
lemma sustain (j s:ℕ)(h:F≤ j)(n:ℕ): |stepsK C D L j s n/basket L C D F (j+s+n)| ≤ Real.exp 2 * |(basket L C D F (j+s))⁻¹|:= (ford_bound C D L p j s h n).trans (mul_le_mul_of_nonneg_right (Real.exp_monotone (smallgeom (by norm_num) (by norm_num) _)) (abs_nonneg _))
variable {E:Type*}[NormedAddCommGroup E][NormedSpace ℂ E]
local notation "Q" L:max=>ThinGauge.boost (Xη L)
lemma rolling_abs {t j:ℕ}{c:ℝ} (f:ℕ→ E)(e:F ≤ j)(g:0≤c)
 (h:∀ i, t ≤ i → ‖((eraK C D L j (j+i):ℝ):ℂ) • f (i+1)-f i‖ ≤ (2/(Q L))^i*c) :
 ∀ i:ℕ, ‖ ((stepsK C D L j t i:ℝ):ℂ) • f (t+i)-f t‖ ≤ (2/(Q L))^t*c*(∑ q∈range i,(1/16:ℝ)^q) :=by
 intro i; let S:=2/Q L; let X(n):=stepsK C D L j t n; have hv:0<S:=div_pos zero_lt_two (boostP L)
 let H:=2*gainCost L; have hH:0<H:=by unfold H; have ht:=gainCost_pos L; linarith only [ht]
 have he: H*S ≤ 1/16:=by unfold H S; have h:= hC64 L; field_simp [boostP L]; field_simp at h; first|linarith only [h]| exact h
 induction i with
 | zero=> simp [stepsK] -- stepsK needs recursor
 | succ i ih=>
    let EPS:=(∑ q∈range i,(1/16:ℝ)^q)
    let a:=t+i; let b:=eraK C D L j (j+a)
    have k: ‖ ((X (i+1):ℝ):ℂ) • f (t+i.succ)-f t‖ ≤ |X i| * (S^a*c)+ S^t*c*EPS:=by
       have he:(X (i+1):ℂ)=(X i:ℂ)*(b:ℂ):=by unfold X b a; rw [stepsK_succ,Nat.add_assoc]; push_cast; rfl
       rw [he,show t + i.succ = a+1 from by unfold a; omega, show _-f t= (X i:ℂ) • ((b:ℂ) • f (a+1)-f a)+((X i:ℂ) • f a-f t) from (?_)]
       · exact (norm_add_le ..).trans (add_le_add (le_trans (le_of_eq (norm_smul (↑(X i):ℂ) _)) (by rw [Complex.norm_real,Real.norm_eq_abs]; exact mul_le_mul_of_nonneg_left (h a (by unfold a; omega)) (abs_nonneg _))) ih)
       rw [smul_sub,mul_smul,sub_add_sub_cancel] -- maybe orientation
    change ‖ ((X (i+1):ℝ):ℂ) • f (t+i.succ)-f t‖ ≤S^t*c*_
    rw [sum_range_succ,mul_add]; apply k.trans; rw [add_comm]; apply add_le_add_right -- left summand? test
    apply le_trans (mul_le_mul_of_nonneg_right ((stepsK_bound C D L p j t e i).1) (by positivity)); change H^i*(S^a*c) ≤ S^t*c*(1/16:ℝ)^i
    unfold a; rw [pow_add,show H^i*(S^t*S^i*c)=S^t*c*(H*S)^i from (by rw [mul_pow H S]; ring)]; exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (mul_nonneg hH.le hv.le) he _) (by positivity)

lemma diminish {t j:ℕ}{c:ℝ}(f:ℕ→ E)(e:F ≤ j)(g:0≤c)
 (u:Tendsto (fun i:ℕ=>((basket L C D F (j+i):ℝ):ℂ) • f i) atTop (𝓝 0))
 (h:∀ i, t ≤ i → ‖ ((eraK C D L j (j+i):ℝ):ℂ) • f (i+1)-f i‖ ≤ (2/(Q L))^i*c) :
 ‖f t‖ ≤ (2/(Q L))^t*c*2 :=by
 let X(i):=stepsK C D L j t i
 let Y(i):=basket L C D F (j+(t+i))
 have ht:Tendsto (fun i:ℕ=> ‖((Y i:ℝ):ℂ) • f (t+i)‖) atTop (𝓝 0):=by
    rw [← norm_zero (E:=E)]; exact u.norm.comp ((tendsto_add_atTop_nat t).congr (fun x=>Nat.add_comm x t))
 let H:=Real.exp 2*|(basket L C D F (j+t))⁻¹|
 have hv:Tendsto (fun i=> ‖((X i:ℝ):ℂ) • f (t+i)‖) atTop (𝓝 0):= by
    apply squeeze_zero' (Eventually.of_forall (fun i=> norm_nonneg _)) ?_ (show Tendsto (fun i=>H*‖((Y i:ℝ):ℂ) • f (t+i)‖) atTop (𝓝 0) from (mul_zero H) ▸ (ht.const_mul H))
    filter_upwards with i
    have he: Y i≠0:= (basket_price L C D F p (e.trans (Nat.le_add_right ..))).2
    rw [norm_smul, norm_smul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_real,Real.norm_eq_abs,←mul_assoc]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _); apply (div_le_iff₀ (abs_pos.mpr he)).mp; rw [←abs_div]; unfold Y; rw [←Nat.add_assoc]; exact sustain C D L p j t e i
 have hs:Tendsto (fun i=> ((X i:ℝ):ℂ) • f (t+i)) atTop (𝓝 (0:E)):= tendsto_zero_iff_norm_tendsto_zero.mpr hv
 have he:Tendsto (fun i=> ‖ ((X i:ℝ):ℂ) • f (t+i)-f t‖) atTop (𝓝 ‖f t‖):=by simpa only [zero_sub,norm_neg] using (hs.sub_const (f t)).norm
 apply le_of_tendsto' he
 intro i; exact (rolling_abs C D L p f e g h i).trans (mul_le_mul_of_nonneg_left (smallgeom (by norm_num) (by norm_num) i) (by have h:=boostP L; positivity))
end PledgeT
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
