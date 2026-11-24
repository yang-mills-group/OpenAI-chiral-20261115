import LusterS.Bills
import Refrain.Shrift
import Refrain.Kernel
/-! # Sparse defect treatment under outer-threshold tree purchase -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.flexible false
set_option quotPrecheck false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 300000
noncomputable section
namespace YM.Gleam.Luster
open Function Lattice MeasureTheory Finset RG Wilson Tree Filter Metric Exterior Precision Next.Rank.Spindle Pressure Work.F03 Next.SectorChange Next.SectorChange.Gaussian
open Fineness Matrix
open scoped Matrix BigOperators Classical ContDiff Topology MatrixOrder ENNReal Kronecker Matrix.Norms.Frobenius
variable {c n : Side}{r:Ratio c n}{T:Forest r}{G:Gauge}{p:BudgetPoint}{q:Clip}{v t η C S w δ β κ ξ Λ v' ν θ ω':ℝ}{U:Config G n}{A:Support c}{m:ℕ} {R:Rules G} {Z:PathData G}{b:Cell n}{H:Bed}{F:Finset T.Free}{J:ChartRatio G}
variable {X Y:fieldDir G n 1}{D:Finset (Cell n)}
variable (B:Z.Bounds q η C S) (P:Attached H Z)(L:Floor H q n δ w)(D':LocalRatio J)
namespace Almanac
open CF.BProof Grade
abbrev tauA:ℝ:=1/1000
abbrev yieldA:ℝ:=tauA/4
abbrev glorio (x:ℝ):= x^tauA
def cliffs (x:ℝ):ℕ:= ⌈glorio x⌉₊
def walls (L:Side)(x:ℝ):ℕ:=L.val*cliffs x
abbrev stride (x:ℝ) := x^(6*tauA)
def sax (x:ℝ):= temp x*stride x
def tuition (L:Side)(x:ℝ):= 100*((walls L x:ℕ):ℝ)^2*sax x
lemma lofty : Tendsto glorio atTop atTop:= tendsto_rpow_atTop (by norm_num [tauA] : 0<tauA)
lemma cliffs_loft:Tendsto cliffs atTop atTop:= Tendsto.comp tendsto_nat_ceil_atTop lofty -- lemma
lemma cliff_b : Grade tauA (fun x=> (cliffs x:ℝ)):= ceil_float (pitch tauA) (lofty.eventually_ge_atTop 0) (by norm_num [tauA])
lemma walls_b (L:Side): Grade tauA (fun x=> ((walls L x:ℕ):ℝ)):=by unfold walls; push_cast; exact cliff_b.scaleB _
lemma sax_b : Grade (-1/2+6*tauA) sax:= Grade.mul temp_b (pitch (6*tauA))
lemma tuition_b (L:Side): Grade (-2/5) (tuition L):=by
 apply Grade.grow (Grade.mul (((walls_b L).pwr 2).scaleB 100) sax_b); norm_num [tauA]
lemma gain_a :∀ᶠ x in atTop,temp x≤ sax x∧0< temp x:=by
 filter_upwards [eventually_gt_atTop (0:ℝ),(tendsto_rpow_atTop (by norm_num [tauA]:0<6*tauA)).eventually_ge_atTop 1] with x h g
 have ht:0<temp x:=Work.E09.temp_pos h; exact ⟨le_mul_of_one_le_right ht.le g,ht⟩
lemma paceSize (L:Side) :∀ᶠ x:ℝ in atTop,0<tuition L x∧ ∀ m:ℕ,1 ≤ m→m≤ walls L x → suitedFee m (sax x) ≤ tuition L x:=by
 filter_upwards [cliffs_loft.eventually_ge_atTop 1,gain_a] with x hx ⟨hz,h⟩
 let B:ℝ:=walls L x; have hB: 1 ≤ B:= by unfold B; exact_mod_cast (show 1≤walls L x from Nat.mul_pos L.property hx)
 have hp:0<sax x:=h.trans_le hz
 unfold tuition; change 0<100*B^2*sax x ∧ _; refine ⟨by positivity,fun m hm hM=>?_⟩; unfold suitedFee
 have hg:(1:ℝ) ≤ m:=by exact_mod_cast hm
 have hw:(m:ℝ)≤B:=by unfold B; exact_mod_cast hM
 calc
 _ ≤ 9*B*(4*sax x*(2*B)):=by have hv:0≤B:=zero_le_one.trans hB; gcongr <;> linarith
 _ ≤100*B^2*sax x:=by nlinarith only [mul_nonneg (sq_nonneg B) hp.le]
lemma ΔGrade (L:Side)(R:Rules G)(q:Clip)(η C:ℝ)(h:0<η): Grade (-6/5) (fun x=>Δ₁ R q (tuition L x) (radiusB x) η C):=by
 let p:= tuition L
 let W:= (-2/5:ℝ); have hp:Grade W p:=tuition_b L
 let hd:= hp.pwr 2
 have hv: Grade (W+W) (fun x=>faceCutError R (p x)):=by apply Grade.grow (hd.scaleB (G.colorScale*16+R.C*4)); unfold W; norm_num
 have hm':Grade (W+W) (fun x=>(8*G.colorScale*(radiusB x:ℝ))*p x^2):=by
    apply Grade.grow ((radiusBill.scaleB (8*G.colorScale)).mul hd); unfold W; norm_num
 have hE:=hv.plus hm'
 let E(x):= trail η (radiusB x); have he:Grade (-1) E:=trail_b h; have ht:=hp.grow (show W≤0 from by norm_num [W])
 have ha:Grade (W+W) (fun x=>acry R (p x) (radiusB x) η C):=(hE.plus ((((block 2).plus ((ht.scaleB 2).scaleB 4)).mul he).grow (by norm_num [W]))).scaleB C
 have hz:= (hp.scaleB 2).scaleB 4
 refine (Grade.plus (Grade.plus (Grade.grow ((hv.mul hz).scaleB q.direct) (by norm_num [W])) (Grade.grow (ha.mul (hz.scaleB C)) (by norm_num [W]))) ?_)
 have hi:= Grade.grow ((((hz.mul he).scaleB C).pwr 2).scaleB (2:ℝ)⁻¹) (show (-2/5+-1)*((2:ℕ):ℝ) ≤ -6/5 by norm_num) -- target expression index scaleB not +0
 convert! hi using 1
 funext x; ring

end Almanac
end YM.Gleam.Luster
