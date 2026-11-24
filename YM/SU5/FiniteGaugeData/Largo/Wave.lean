import YM.CF.Fir.Graph
import YM.SU5.FiniteGaugeData.Brique.Frequency
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
/-!
# A layer-capacity calculation
Work on a slab patch [1,2] in each transverse Fourier momentum. Want infinite normal Hankel capacity even when levels and L-buffer offsets are fixed large. Prove using a pole argument on the limiting of the flat-history CP symbol. This avoids needing any positivity estimate of the truncating/varying M versions. While we need both real upper Spinor projections, it suffices to have unbounded ranks from just a linear combination (normal mix entry) using finitely many. 
-/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 380000
noncomputable section
namespace YM.CF.Window.Largo
open Function Filter Lattice Laurent Metric Next.Free Bloch Complex Finset
open scoped Topology BigOperators Set Pointwise
open CF.Fir
abbrev Tang := Fin 3
abbrev Rim:= Tang→ℝ
abbrev Tip:= Tang→ℤ
variable (o:Rim)(r:ℝ) (z:ℂ)(i:Tip)(j:ℤ)
def Slab (o:Rim):Prop:=∀ i,1≤o i∧o i≤2
abbrev τ := 2*Real.pi
lemma tau_pos : 0<τ:=mul_pos (by norm_num) Real.pi_pos
abbrev scar (r:ℝ)(j:ℤ):= r+τ*j
abbrev afar (z:ℂ)(j:ℤ):ℂ:= z+(τ:ℂ)*j
abbrev snow (i:ℤ):ℕ:= (i:ℤ).natAbs
lemma conductor (p:1≤r)(q:r≤2) : 1+(snow j:ℝ) ≤ |scar r j|:=by
 have hx: 4 ≤ τ:= (by unfold τ; linarith [Real.pi_gt_three]); rw [show (snow j:ℝ)=|(j:ℝ)| from (by simp [snow])]; unfold scar; by_cases h:0 ≤ j; · have he:0 ≤ (j:ℝ):= (by exact_mod_cast h); rw [abs_of_nonneg he]; nlinarith only [hx,mul_le_mul_of_nonneg_right hx he, p,he, le_abs_self (r+τ*j)]
 have he:(j:ℝ)≤ -1:= (by exact_mod_cast (show j ≤ -1 by omega)); rw [abs_of_nonpos (by linarith : (j:ℝ)≤0)]; have hv:=neg_le_abs (r+τ*j); nlinarith only [hv,mul_le_mul_of_nonpos_right hx (he.trans (by norm_num)),he,q] -- ℝ snow
lemma origin_price (p:1≤r)(q:r≤2) : 1≤ |scar r j|:=le_trans (le_add_of_nonneg_right (by positivity)) (conductor r j p q)
def bush := Real.sqrt (∑ k:Tang,(scar (o k) (i k))^2)
lemma bush_sphere : bush o i ^2= ∑ k:Tang,(scar (o k) (i k))^2:= Real.sq_sqrt (by positivity)
lemma bush_ge (a:Tang): |scar (o a) (i a)| ≤ bush o i:= le_of_pow_le_pow_left₀ (by decide:(2:ℕ)≠0) (Real.sqrt_nonneg _) (by rw [sq_abs,bush_sphere]; exact single_le_sum (fun k _=>sq_nonneg (scar (o k) (i k))) (mem_univ a))
lemma bush_pos (p:Slab o): 0 < bush o i:=zero_lt_one.trans_le ((origin_price _ _ (p 0).1 (p 0).2).trans (bush_ge o i 0))
def gateL (i:ℤ):ℝ:= ((1+(i.natAbs:ℝ))^2)⁻¹
lemma gate_summ : Summable gateL:=by
 unfold gateL; have he:=(summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow (p:=2) |>.mpr one_lt_two); rw [summable_int_iff_summable_nat_and_neg]; constructor <;> simpa [one_div,add_comm] using he
abbrev billC:= ∏ k:Tang,gateL (i k)
lemma gate_pp (i:ℤ):0 < gateL i:=by unfold gateL; positivity
lemma bill_pos :0<billC i:= Finset.prod_pos fun i _=> gate_pp _
lemma bill_summ:Summable billC:=by
 let B:= ∑' i,gateL i
 apply summable_of_sum_le (fun i=> (bill_pos i).le) (c:= B^3); intro s; let V(k:Tang):= s.image (fun x=>x k)
 have he: s ⊆ Fintype.piFinset V:=fun i t=> Fintype.mem_piFinset.mpr fun k=> mem_image_of_mem _ t
 refine (sum_le_sum_of_subset_of_nonneg he (fun i _ _=>(bill_pos i).le)).trans ?_; unfold billC; rw [← Finset.prod_univ_sum (κ:=fun _=>ℤ) V (fun _=>gateL)]; simpa only [prod_const,card_univ,Tang,Fintype.card_fin] using (Finset.prod_le_prod (s:=@univ Tang _) (f:=fun i=> ∑ j∈V i,gateL j) (g:=fun i=>B) (fun i _=>sum_nonneg (fun j _=>(gate_pp j).le)) (fun i _=>gate_summ.sum_le_tsum _ (fun j _=> (gate_pp j).le)))

/- local meromorphic shape with all tang frequencies kept. `hsinc` argument not scaled by half yet. -/
def hsinc : ℂ→ℂ := dslope Complex.sin 0
lemma hzero : hsinc 0=1:=by simp [hsinc]
lemma haway (p:z ≠0): hsinc z=Complex.sin z / z:=by rw [hsinc,dslope_of_ne _ p, slope_def_module, sub_zero, Complex.sin_zero,sub_zero, smul_eq_mul,inv_mul_eq_div]
@[fun_prop] lemma hschi : Differentiable ℂ hsinc :=by rw [hsinc,←differentiableOn_univ,Complex.differentiableOn_dslope univ_mem]; fun_prop
lemma h_real : hsinc (r:ℂ)=(Real.sinc r:ℝ):=by
 by_cases p:r=0; · simp [p,hzero]
 rw [haway _ (by exact_mod_cast p),Real.sinc_of_ne_zero p, Complex.ofReal_div,Complex.ofReal_sin] -- indent
lemma s_height_pos (p:0<r) : hsinc (Complex.I*r)= (Real.sinh r/r:ℝ) ∧ 0 < Real.sinh r/r:= by
 constructor
 · rw [haway _ (mul_ne_zero Complex.I_ne_zero (by exact_mod_cast p.ne'))]; push_cast; rw [mul_comm _ (r:ℂ),Complex.sin_mul_I]; field_simp
 exact div_pos (Real.sinh_pos_iff.mpr p) p
-- sine sign integer periodic even sin^2
lemma sx (p:1≤r)(q:r≤2): Real.sinc (scar r j/2)≠0:=by
 have he:= Real.sin_pos_of_pos_of_lt_pi (by linarith : 0<r/2) (by linarith [Real.pi_gt_three])
 have h:Real.sin (scar r j/2)≠0:=by rw [show _/(_ :ℝ)= r/2 + j*Real.pi from ?_,Real.sin_add_int_mul_pi]; exact mul_ne_zero (zpow_ne_zero _ (by norm_num : (-1:ℝ) ≠ 0)) he.ne'; unfold scar τ; ring
 have ht:scar r j/2≠0:=fun v=>h (by simp [v]); rw [Real.sinc_of_ne_zero ht]; exact div_ne_zero h ht
def floam:= ∏ k:Tang,Real.sinc (scar (o k) (i k)/2)^8
lemma floam_pos (p:Slab o):0 < floam o i:=Finset.prod_pos fun k _=> (Even.pow_pos (by decide:Even 8) (sx _ _ (p k).1 (p k).2)) -- tune
lemma sinc4 (p:1≤r)(q:r≤2): ‖Real.sinc (scar r j/2)^8‖ ≤ 256*gateL j:=by
 let a:=scar r j; let b:=(1+(snow j:ℝ)); have hb:0 < b:=(by unfold b; positivity); have hl:=conductor r j p q; have hy:a≠0:=by exact abs_pos.mp (hb.trans_le hl)
 let S:= Real.sinc (a/2); have hx:|S| ≤2/ b:= by
    unfold S; rw [Real.sinc_of_ne_zero (by exact (div_ne_zero hy (by norm_num))),abs_div]; apply le_trans (div_le_div_of_nonneg_right (Real.abs_sin_le_one _) (abs_nonneg _)) ?_; rw [abs_div,abs_of_pos (by norm_num:(0:ℝ)<2),_root_.div_le_div_iff₀ (by positivity) hb]; unfold a b; linarith
 have hv: (2/b)^8=256*b⁻¹^2*b⁻¹^6:=by field_simp; ring
 have hu:(b⁻¹)^6 ≤ 1:=pow_le_one₀ (by positivity) (inv_le_one_of_one_le₀ (by unfold b; simp only [le_add_iff_nonneg_right]; positivity))
 rw [Real.norm_eq_abs,abs_pow]; exact (pow_le_pow_left₀ (abs_nonneg _) hx _).trans (hv ▸ (show 256 * b⁻¹^2 * b⁻¹^6 ≤ _ from (by rw [inv_pow b]; exact mul_le_of_le_one_right (by positivity) hu))) -- tune
lemma floam_le (p:Slab o) : ‖floam o i‖ ≤ 256^3*billC i:= by
 unfold floam; rw [norm_prod]; let V:= Finset.prod_le_prod (s:=(univ:Finset Tang)) (fun i _=>norm_nonneg _) (fun i' _=> sinc4 _ (i i') (p i').1 (p i').2); simp_rw [Finset.prod_mul_distrib,prod_const,card_univ,show Fintype.card Tang=3 from Fintype.card_fin _] at V; exact V
end YM.CF.Window.Largo
