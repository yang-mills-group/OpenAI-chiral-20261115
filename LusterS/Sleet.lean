import LusterS.Bruin
import LusterS.Rogue
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
local notation "pFlo" => scaleY
-- chart cost x^-tauA and width*v √
local notation "Xc" x:max=> ((x:ℝ)^(-tauA))
lemma prices_j (L:Side)(J:ChartRatio G)(H:LocalRatio J)(R:Rules G) :∀ᶠ x:ℝ in atTop, tuition L x ≤ R.c ∧ 2*tuition L x<J.radius ∧ ∀ a:G.Color, ‖a‖ ≤2*tuition L x→J.J a ≤ Real.exp (Xc x):=by
 let b:=J.radius/2; obtain ⟨C,hC,hf⟩:= SectorNext.Vacuum.Jacob_linear J H (half_lt_self H.patch) (half_pos H.patch).le
 have hE:Tendsto (fun x=>2*tuition L x) atTop (𝓝 0):=by simpa only [mul_zero] using ((tuition_b L).roots (by norm_num)).const_mul 2
 have hg:= ((tuition_b L).scaleB (C*2)).cost_p (b:=-tauA) (by norm_num [tauA])
 filter_upwards [hE.eventually (gt_mem_nhds (half_pos H.patch)),((tuition_b L).roots (by norm_num)).eventually (ge_mem_nhds R.radius),hg] with x u q g
 refine ⟨q,u.trans (half_lt_self H.patch),fun a h=>?_⟩
 have h0:=hf a (h.trans u.le)
 refine (show _ ≤ Xc x+1 from ?_).trans (Real.add_one_le_exp _)
 change |C*2*tuition L x| ≤ Xc x at g
 nlinarith only [h0,le_abs_self (J.J a-1), g,le_abs_self (C*2*tuition L x),mul_le_mul_of_nonneg_left h hC.le]
lemma scale_shock {x:ℝ}(p:0<x): x*temp x^2=pFlo x^2:=by
 unfold temp; rw [mul_pow,inv_pow,Real.sq_sqrt p.le,←mul_assoc,mul_inv_cancel₀ p.ne',one_mul,coin_scale]
lemma yield_prec (c:ℝ)(L:Side):∀ᶠ x:ℝ in atTop, |c| *((walls L x:ℕ):ℝ)^4* (radiusB x:ℝ) ≤ stride x:=by
 have he:= Grade.mul (Grade.scaleB (|c|) ((walls_b L).pwr 4)) radiusBill
 exact (he.cost_p (b:=6*tauA) (by norm_num [tauA])).mono (fun x h=> (le_abs_self _).trans h)
-- full charges. margin ≤ A*m, choose ξ=4 A*m*walls^4; χ similar; ν=radiusB x, buys arbitrarily fixed inverse power in exp.
abbrev beard (B:ℝ) (x:ℝ):= B*(radiusB x:ℝ)
abbrev flagCup (p:BudgetPoint)(q:Clip)(b:ℝ):= b*(q.linear*p.threshold^2)/10
abbrev needle (L:Side)(A:ℝ)(x:ℝ) := 4*beard A x*((walls L x:ℕ):ℝ)^4
abbrev sampleS (A:ℝ)(x:ℝ):=4*beard A x*(lusterBill (hallBill (radiusB x)):ℝ)
lemma fee_plead (A:ℝ):PL (fun x=> sampleS A x+(radiusB x:ℝ)):=by
 have h:=Grade.radius_log
 unfold sampleS beard lusterBill hallBill Sequest; push_cast
 let f(x:ℝ):= (radiusB x:ℝ)+4
 have he:=h.add (PL.const 4); let v:=he.add he
 exact (((PL.const 4).mul ((PL.const A).mul h)).mul (((v.add v).add (PL.const 1)).pow 4) |>.add h)
lemma plume_fee (L:Side)(R:Rules G)(J:ChartRatio G)(H:LocalRatio J)(q:Clip)(D t:ℝ)(h:0<t):∀ᶠ x:ℝ in atTop,∀ β:ℝ,x/2 ≤ β → ∀ p:BudgetPoint,p.threshold=temp x→∀ w:Side,w.val ≤ walls L x→ Radiance J R q p w.val (radiusB x) β (flagCup p q β) (D*((walls L x:ℕ):ℝ)^4) (sax x) (needle L t x) (sampleS t x) (radiusB x:ℝ) (tuition L x) (Xc x):=by
 let a:= q.linear; have hp:0 < a:= q.tail_pos
 let A:= |D|+(21:ℝ)^4*4*t; have hA:0 ≤ A:=by unfold A; positivity
 filter_upwards [eventually_gt_atTop (0:ℝ), paceSize L,gain_a,(sax_b.cost_p (b:=0) (by norm_num [tauA])), coin_strongLt (a:=0) (b:=1) (f:=fun x=>sampleS t x+(radiusB x:ℝ)) (by simp) (fee_plead t), prices_j L J H R, clocks.parliament (G:=G) q, yield_prec (4*A/a) L, Work.E08.eventual_radiusB 1, (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually_ge_atTop (20/a)] with x hx v tA hS hk hX hW hu hB hY β hβ p ht w hw
 let s:=p.threshold; have hs:0<s:=p.threshold_pos
 have hb:=scale_shock hx; let f:=pFlo x; have hf:0<f:=coin_pos ..
 -- f ≥ 10/a and ≥1
 have hg: (5:ℝ)≤ a*f:=by
    rw [←ge_iff_le]; unfold f; rw [coin_scale]; let b':=Real.log (Real.log x); have hv:20/a≤b':=hY
    have he:= Real.add_one_le_exp (b'^2); field_simp at hv; have hW:b'≤Real.exp (b'^2):=(by nlinarith only [sq_nonneg (b'-1),he]); change _≥5; linarith only [hv,mul_le_mul_of_nonneg_left hW hp.le]
 have hm:1≤ f:=by unfold f; rw [coin_scale]; exact Real.one_le_exp (sq_nonneg _)
 have he:sax x≤1:=by change |sax x| ≤ _ at hS; rw [Real.rpow_zero] at hS; exact (le_abs_self _).trans hS
 refine ⟨ht ▸ tA.1, he,hW p ht,v.2 w.val w.property hw,hX.1,hX.2.1,hX.2.2,?_,?_,by unfold needle beard; positivity,by positivity⟩
 · have hP:sampleS t x+(radiusB x:ℝ)≤ f:= (le_abs_self _).trans (hk.le)
   have hq:x*(a*s^2)=a*f^2:=by unfold a f; rw [show s=temp x from ht]; nlinarith only [congrArg (fun y:ℝ=> q.linear*y) hb]
   unfold flagCup; change β*(a*s^2)/10+ _ ≤ _
   nlinarith only [hP, mul_le_mul_of_nonneg_right hβ (show 0≤a*s^2 from by positivity),hq, mul_le_mul_of_nonneg_right hg hf.le]
 let b:ℝ:=radiusB x; have h0:1≤b:=by unfold b; exact_mod_cast hB
 let M:ℝ:=walls L x
 have hu': A*M^4*b≤a*stride x/4:=by
    have e:0≤4*A/a:=by positivity
    rw [abs_of_nonneg e] at hu
    field_simp at hu
    nlinarith only [hu]
 have hj:0 ≤ stride x:=Real.rpow_nonneg hx.le _
 have hZ:x*(a*(temp x)*(sax x))≥a*stride x:=by
    unfold sax
    have hm':1≤pFlo x^2:=one_le_pow₀ hm
    have he:=congrArg (fun y:ℝ=>a*stride x*y) hb
    nlinarith only [he,mul_le_mul_of_nonneg_left hm' (show 0≤a*stride x from mul_nonneg hp.le hj)]
 have htB:=mul_le_mul_of_nonneg_right hβ (show 0 ≤ q.linear*p.threshold*sax x/2 from by have he':0<sax x:=tA.2.trans_le tA.1; have h0:=p.threshold_pos; have he:=q.tail_pos; positivity)
 change D*M^4+21^4*(4*(t*b)*M^4)≤ _
 unfold A at hu'; unfold a at *; rw [ht] at htB ⊢ -- at * may collapse s; just RHS
 have hM:0≤M^4:=by positivity
 nlinarith only [htB,hZ,hu',mul_le_mul_of_nonneg_right (le_abs_self D) hM,mul_le_mul_of_nonneg_left h0 (mul_nonneg (abs_nonneg D) hM)]

end Almanac
end YM.Gleam.Luster
