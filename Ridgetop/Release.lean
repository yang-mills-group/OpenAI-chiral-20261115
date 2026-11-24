import Ridgetop.Bream
import Ridgetop.Traces
import Risa.Cultural
import Compass.Prime
import YM.AnalyticBridge.VERIFIED_RESET_STEP.Channels
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.flexible false
set_option quotPrecheck false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 305000
noncomputable section
namespace YM.Gleam.Luster
open Function Lattice MeasureTheory Finset RG Wilson Tree Filter Metric Exterior Precision Next.Rank.Spindle Pressure Work.F03 Next.SectorChange Next.SectorChange.Gaussian
open Fineness Matrix
open scoped Matrix BigOperators Classical ContDiff Topology MatrixOrder ENNReal Kronecker Matrix.Norms.Frobenius
variable {c n : Side}{r:Ratio c n}{T:Forest r}{G:Gauge}{p:BudgetPoint}{q:Clip}{v t η C S w δ β κ ξ Λ v' ν θ ω':ℝ}{U:Config G n}{A:Support c}{m:ℕ} {R:Rules G} {Z:PathData G}{b:Cell n}{H:Bed}{F:Finset T.Free}{J:ChartRatio G}
variable {X Y:fieldDir G n 1}{D:Finset (Cell n)}
variable (B:Z.Bounds q η C S) (P:Attached H Z)(L:Floor H q n δ w)(D':LocalRatio J)
namespace Risa
open Regis ProbabilityTheory
open _root_.YM.Regis.Head AnalyticBridge.VerifiedReset StressFlux Lattice.PlaqAxes Virgo _root_.YM.CF.Scree
namespace Ridgetop
open CF.Compass _root_.Factory
open scoped RealInnerProductSpace
local notation "Sx"=> stamen B P n
local notation "μ*"=>stdGaussian Sx
variable (o b:Site n)(Zx:Hike)(hx:0<δ)
private lemma spring {E:Type*}[NormedAddCommGroup E][InnerProductSpace ℝ E](x:E):clipQ Zx.cost x ≤ ‖x‖^2:=by
 have h:0< coil Zx.cost x:=by have := Zx.safe; unfold coil; positivity
 unfold clipQ; rw [div_le_iff₀ h]; unfold coil; nlinarith [sq_nonneg (‖x‖^2)]
local notation "χ"=>Zx.cost
private lemma spring_pair {E:Type*}[NormedAddCommGroup E][InnerProductSpace ℝ E](x y:E):
 |clipQ χ x*clipQ χ y-‖x‖^2*‖y‖^2|≤ 3*(χ⁻¹^2)*(‖x‖^6 + ‖y‖^6):=by
 let a:=clipQ χ x; let b:=clipQ χ y; let k:=χ⁻¹^2
 let p:=‖x‖^2; let q:=‖y‖^2; let u:=‖x‖; let v:=‖y‖
 have he:a≤p:=spring Zx _; have ht:b ≤q:=spring Zx _
 have hp:0 ≤ p-a:=sub_nonneg.mpr he; have hq:0 ≤ q-b:=sub_nonneg.mpr ht
 have e₁:p-a≤k*u^4:= (le_abs_self _).trans (recoil _ Zx.safe _)
 have e₂:q-b≤k*v^4:= (le_abs_self _).trans (recoil _ Zx.safe _)
 have hb:a*b≤p*q:=mul_le_mul he ht (clip_pos _ Zx.safe _) (sq_nonneg _)
 change |a*b-p*q|≤3*k*(u^6+v^6); rw [abs_of_nonpos (sub_nonpos.mpr hb)]
 have h: -(a*b-p*q) ≤ k*(u^4*v^2 +u^2*v^4):=by
    change u^2-a ≤ _ at e₁; change v^2-b ≤ _ at e₂
    change -(a*b-u^2*v^2) ≤ _
    have e₁':=(mul_le_mul_of_nonneg_right e₁ (sq_nonneg v)); have e₂':= mul_le_mul_of_nonneg_left e₂ (sq_nonneg u); change 0 ≤ u^2-a at hp; change 0 ≤ v^2-b at hq
    nlinarith only [e₁',e₂',mul_nonneg hp hq]
 nlinarith only [h,mul_le_mul_of_nonneg_left (expiry (norm_nonneg x) (norm_nonneg y)) (show (0:ℝ) ≤ k from sq_nonneg _)]
local notation "A₀"=> ((Fintype.card PlaqAxes):ℝ)
lemma route_est (z:ℝ){i m:PlaqAxes}(t:Sx):
 |(dye i*clipQ χ (z • @heeled n _ q o i t.val))*(dye m * clipQ χ (z • @heeled n _ q b m t.val)) -(z^4)*((dye i*stampB q o i t.val) *(dye m*stampB q b m t.val))|
 ≤ (3*(χ⁻¹^2)*|z|^6)*(tpack B P o i t+tpack B P b m t):=by
 let f:=@heeled n _ q o i t.val; let g:=@heeled n _ q b m t.val
 let x:=z • f; let y:=z • g
 have h: z^4*(dye i*stampB q o i t.val*(dye m*stampB q b m t.val)) = dye i*dye m*(‖x‖^2*‖y‖^2):=by unfold x y f g stampB; rw [norm_smul,norm_smul,Real.norm_eq_abs,mul_pow,mul_pow,sq_abs]; ring
 rw [h,show (dye i*clipQ _ x)*(dye m*clipQ _ y)=dye i*dye m*(clipQ χ x*clipQ χ y) from (by ring),← mul_sub_left_distrib,abs_mul]
 have ht:|dye i*dye m| ≤1:=by rw [abs_mul]; exact (mul_le_mul (dye_t i) (dye_t m) (abs_nonneg _) zero_le_one).trans_eq (one_mul _)
 apply (_root_.mul_le_of_le_one_left (abs_nonneg _) ht).trans ((spring_pair Zx x y).trans (?_))
 unfold x y; rw [norm_smul,norm_smul,Real.norm_eq_abs]; unfold tpack; change _ ≤ 3*(χ⁻¹^2)* |z|^6*(‖f‖^6+‖g‖^6); apply le_of_eq; ring
private lemma balanceEst (z:ℝ)(t:Sx):|(posess G Zx).sketch q z o t.val*(posess G Zx).sketch q z b t.val- z^4/4*(imagine q o t.val*imagine q b t.val)|≤
 (3*(χ⁻¹^2)*|z|^6)*(∑ i:PlaqAxes,∑ j:PlaqAxes,(tpack B P o i t+tpack B P b j t)):=by
 rw [sketch_is,sketch_is]
 let k:=3*(χ⁻¹^2)*|z|^6
 let f(o:Site n)(j:PlaqAxes):=dye j*clipQ χ (z • @heeled n _ q o j t.val); let e(o:Site n)(j:PlaqAxes):=dye j * stampB q o j t.val
 change |((∑ i:PlaqAxes,f o i)/2)*((∑ j:PlaqAxes,f b j)/2)-z^4/4*((∑ i:PlaqAxes,e o i)*(∑ j:PlaqAxes,e b j))|≤ _
 rw [show ∀ r s u v:ℝ,r/2*(s/2)-z^4/4*(u*v)=(r*s-z^4*(u*v))/4 from fun _ _ _ _=> (by ring),abs_div]
 rw [abs_of_nonneg (by norm_num: (0:ℝ)≤4)]
 apply (div_le_self (abs_nonneg _) (by norm_num)).trans
 simp_rw [Finset.sum_mul,Finset.mul_sum,← Finset.sum_sub_distrib]
 apply (Finset.abs_sum_le_sum_abs ..).trans
 exact sum_le_sum fun i _=>(Finset.abs_sum_le_sum_abs ..).trans (sum_le_sum fun j _=>route_est B P o b Zx z t)
include L hx
noncomputable abbrev extent:ℝ:= 6*A₀^2*@wingN G q
set_option maxRecDepth 5000 in
lemma section_is(z:ℝ):|meal B P Zx z true (fun i:Bool=> if i then b else o) (fun _=>1) -z^4/4*clouds B P (fun t=>imagine q o t*imagine q b t)|≤ @extent G q *(χ⁻¹^2)*|z|^6:=by
 let c:Bool→Site n:= fun i=> if i then b else o
 let f(t:Sx):=raiseZ G q Zx z true t.val (fun _=>1) c; let e(t:Sx):=imagine q o t.val*imagine q b t.val
 let k:=3*χ⁻¹^2*|z|^6; let l:=z^4/4; let g(t:Sx):=k*(∑ i:PlaqAxes,∑ j:PlaqAxes,(tpack B P o i t+tpack B P b j t))
 have hk:0 ≤ k:=by unfold k; positivity
 have fe:=raise_int B P Zx z true c fun _=>1; change Integrable f μ* at fe
 have ee: Integrable e μ*:=by
    unfold e imagine; simp_rw [Finset.sum_mul,Finset.mul_sum]
    refine integrable_finsetSum _ fun i _=>integrable_finsetSum _ fun j _=>?_
    simp_rw [show ∀ i j:PlaqAxes,∀ a v:ℝ,(dye i*a)*(dye j*v)= (dye i*dye j)*(a*v) from fun _ _ _ _=>by ring]; exact (moon B P L o i hx b j).const_mul _
 have eg:Integrable g μ*:=by unfold g; exact (integrable_finsetSum _ (fun i _=> integrable_finsetSum _ (fun j _=> (tpack_int B P L o i hx).add (tpack_int B P L b j hx)))).const_mul _
 have h(t:Sx): ‖f t-l*e t‖ ≤ g t:=by
    obtain ⟨x,hh⟩: ∃ x:fieldDir G n 1,tiler B P x=t.val:= t.property
    change ‖(posess G Zx).chalk q z 1 (c false) t.val*(posess G Zx).chalk q z 1 (c true) t.val-l*e t‖≤g t
    change ‖(posess G Zx).chalk q z 1 o t.val*(posess G Zx).chalk q z 1 b t.val-l*e t‖≤g t
    rw [←hh,canon,canon,hh,Real.norm_eq_abs]; exact balanceEst B P o b Zx z t
 let rt:= ∫ x:Sx,f x-l*e x∂μ*
 have Ht: |rt|≤ ∫ x:Sx,g x∂μ*:=by rw [← Real.norm_eq_abs]; exact norm_integral_le_of_norm_le eg (Filter.Eventually.of_forall h)
 change |(∫ x,f x ∂μ*)-l*(∫ x,e x ∂μ*)| ≤ _; rw [← integral_const_mul,←integral_sub fe (ee.const_mul _)]
 apply Ht.trans; unfold g
 rw [integral_const_mul]; apply le_trans (mul_le_mul_of_nonneg_left (?_ : (∫ x:Sx, ∑ i:PlaqAxes,∑ j:PlaqAxes,(tpack B P o i x+tpack B P b j x)∂ μ*) ≤ A₀^2*(2* @wingN G q)) hk)
 · apply le_of_eq; unfold k extent; ring
 -- sum.expense
 rw [integral_finsetSum]; swap; · exact fun _ _=>integrable_finsetSum _ (fun _ _=> (tpack_int B P L _ _ hx).add (tpack_int B P L _ _ hx))
 apply (sum_le_sum (s:=univ) (g:=fun _=> ∑ _:PlaqAxes,2* @wingN G q) _).trans
 · simp [wingN]; ring_nf; exact le_rfl
 intro i _; rw [integral_finsetSum]; swap; · exact fun _ _=> (tpack_int B P L _ _ hx).add (tpack_int B P L _ _ hx)
 apply sum_le_sum; intro j _; rw [integral_add (tpack_int B P L _ _ hx) (tpack_int B P L _ _ hx)] -- potential .rw
 linarith only [relish B P L o i hx,relish B P L b j hx]
#print axioms section_is
end Ridgetop
end Risa
end YM.Gleam.Luster
