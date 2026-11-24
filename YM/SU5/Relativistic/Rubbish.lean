import YM.SU5.Relativistic.Windsail
import YM.SU5.Relativistic.Blush
import YM.CF.Fixed.PastBound
import YM.CF.BProof.PL
import YM.Work.E04
/-! # fuel for lemons at x universal. Clip price not symbols. -/
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 600000
noncomputable section
namespace YM.CF.Papyrus.Pharos
open Function Finset Filter MeasureTheory Lattice Wilson Precision RG
open Next.SectorChange
open Fixed.Pivots Fixed.Extensive
open Work.F03
open scoped Matrix BigOperators Topology ContDiff Matrix.Norms.Frobenius InnerProductSpace
variable (G : Gauge)(p:Clip){s C Λ:ℝ}
open Pressure (temp radiusB)
open BProof
lemma proof_t : Tendsto temp atTop (𝓝 0):= coin_purchases (a:= -1/2) (b:=1) (c:=0) (by norm_num) |>.congr' ((eventually_gt_atTop (0:ℝ)).mono fun i h=> thresh_eq h)
private lemma crane:PL (fun i=>(radiusB i:ℝ)):=PL.ceil (PL.log_y.pow 2) (Eventually.of_forall fun i=>sq_nonneg _)
theorem tempest {P₀:ℝ→ℝ}(i:ℕ)(f:PL P₀)(r:ℝ)(p:0<r) :∀ᶠ x:ℝ in atTop, |P₀ x| ≤ r*x*temp x^2:=by
 obtain ⟨a,h⟩:= f; filter_upwards [h,eventually_gt_atTop (0:ℝ),coin_budget (a:=0) (b:=0) (c:=a) (d:=0) (e:=2) (f:=0) (by norm_num) 1 r p] with x t u v; rw [one_mul] at v; refine t.trans (v.le.trans_eq ?_); rw [← thresh_eq u]; unfold BProof.thresh; rw [coin_pow]; rw [mul_assoc,show x*coin x (-1/2*(↑(2:ℕ):ℝ)) (1*(↑(2:ℕ):ℝ)) (0*(↑(2:ℕ):ℝ))=coin x 0 2 0 from ?_] -- tune
 · nth_rw 1 [← coinY u]; rw [coin_mul]; norm_num

def hose (y:ℝ) : ℕ:= (radiusB y+radiusB y+1)^4
lemma windPL: PL (fun i=> (hose i:ℝ)):=by unfold hose; push_cast; exact (((crane.add crane).add (PL.const 1)).pow 4)
private lemma breeze : Tendsto (fun i=>2*i*temp i^3) atTop (𝓝 0):=by
 have hp:=coin_purchases (a:= -1/2) (b:=3) (c:=0) (by norm_num); have he:=hp.const_mul 2; rw [mul_zero] at he; refine he.congr' ?_
 filter_upwards [eventually_gt_atTop (0:ℝ)] with i h; rw [←thresh_eq h]; unfold thresh; rw [mul_assoc]; congr 1; nth_rw 2 [← coinY h]; rw [coin_pow,coin_mul]; norm_num
-- note `Pays` for x,y role.E at cutoff p.threshold
open SectorNext.Vacuum (draught chord_z)
def husk (b k:ℝ)(y:G.El):= Real.exp (k-(Real.sqrt b*k)*G.chord y)
lemma husk_int(k:ℝ)(q:0<k)(g: ChartRatio G)(h:LocalRatio g) : ∃ C:ℝ,1≤C∧∀ᶠ b:ℝ in atTop,(∫ x:G.El,husk G b k x∂G.probHaar)≤ C*Next.SectorChange.spare g b:=by
 obtain ⟨L,u,w⟩:= chord_z g h k q
 let V:=(Real.sqrt (2*Real.pi))^Fintype.card G.ColorIndex*g.scale; have he:0<V:=mul_pos (pow_pos (Real.sqrt_pos.mpr (by positivity)) _) h.scale
 let c:=Real.exp k*L/V; refine ⟨max 1 c,le_max_left ..,?_⟩
 filter_upwards [Real.tendsto_sqrt_atTop.eventually_ge_atTop 1,eventually_gt_atTop (0:ℝ)] with b p q'
 let t:=Real.sqrt b
 have hy:= w t p; let n:= Fintype.card G.ColorIndex; have hf:Module.finrank ℝ G.Color=n:=by simp [Gauge.Color,n] -- tune
 have hs: t^n>0:=pow_pos (Real.sqrt_pos.mpr q') _
 have hp: (∫ x:G.El,husk G b k x∂G.probHaar)=Real.exp k*(∫ x:G.El,draught (t*k) x ∂G.probHaar):=by
    rw [← integral_const_mul]; apply integral_congr_ae (Eventually.of_forall _); intro i; unfold husk draught t; rw [← Real.exp_add,neg_mul,sub_eq_add_neg]
 rw [hp]; apply le_trans _ (mul_le_mul_of_nonneg_right (le_max_right ..) (spare_pos _ h q').le)
 have ht:V=Next.SectorChange.spare g b*t^n:=by unfold Next.SectorChange.spare V n coupling; rw [Real.sqrt_mul (by positivity : 0≤2*Real.pi),Real.sqrt_sq (by positivity),mul_pow,inv_pow]; unfold t; field_simp
 apply le_of_mul_le_mul_right _ hs; rw [mul_assoc c,← ht,show c*V=Real.exp k*L from div_mul_cancel₀ _ he.ne']; rw [hf] at hy; exact le_trans (le_of_eq (by ring)) (mul_le_mul_of_nonneg_left hy (Real.exp_nonneg k)) -- tune

lemma fuelGauge(C Λ r f t ξ k:ℝ)(fr:0<r)(hk:0<k)(sk:k ≤ r*p.linear/2)(f':0≤f)(v:0≤t)(c:0<C∨C=0)(pΛ:0≤Λ)(g:0<ξ) :∀ᶠ x:ℝ in atTop,∀ β∈ Set.Icc (x/2) (2*x),
  0<x ∧ 0<β∧ 0< temp x ∧ 5*(f+t*hose x)≤ r*β*(p.linear*temp x^2)∧ k≤(r*β)*(p.direct*(coupling β)^2/2) ∧ k≤(r*β)*(p.linear*temp x*coupling β) ∧ ∀ n:Side, Graph.taxY n β (temp x) C Λ ≤ ξ*n.val^4:=by
 have hp:= p.tail_pos; have ht:Tendsto (fun x=> C*(2*x*temp x^3)*(1+temp x)+Λ*temp x^2) atTop (𝓝 0):=by simpa using! (((breeze.const_mul C).mul (proof_t.const_add 1)).add ((proof_t.pow 2).const_mul Λ)) -- tune
 let P(x):=5*(f+t*(hose x:ℝ))
 filter_upwards [eventually_gt_atTop (0:ℝ),tempest (P₀:=P) 0 ((PL.const _).mul ((PL.const _).add ((PL.const t).mul windPL))) (r*p.linear/2) (by positivity), ht.eventually (ge_mem_nhds g)] with x hB hT v' β h
 have hu:=h.1; have hs:=h.2; have hf:0 < β:=by linarith
 let s:=temp x; let z:= coupling β; have hz:0<z:=coupling_pos hf; have hb:β*z^2=1:=by rw [← by_coupling hf]; exact inv_mul_cancel₀ (pow_pos hz 2).ne'
 have hw:0<s:= show 0<temp x from (by rw [←thresh_eq hB]; exact coin_pos ..)
 refine ⟨hB,hf,hw,?_,?_,?_,?_⟩
 · exact ((le_abs_self (P x)).trans hT).trans (by linarith only [mul_le_mul_of_nonneg_left hu (show 0≤r*(p.linear*s^2) by positivity)]) -- reducible tune linarith
 · have ht:=p.kink; have hA:=mul_lt_mul_of_pos_left ht fr; apply sk.trans; change _ ≤ _*(p.direct*z^2/2); rw [show (r*β)*(p.direct*z^2/2)= r*p.direct*(β*z^2)/2 from by ring,hb,mul_one]; linarith
 · -- s≥ g/2 even worst case
   have hm:z/2≤ s:=by
      have hm: (Real.sqrt x)⁻¹ ≤ s:= le_mul_of_one_le_right (by positivity) (Real.one_le_exp (sq_nonneg _)); apply le_trans _ hm
      have hv:Real.sqrt x≤2*Real.sqrt β:=by nlinarith [Real.sq_sqrt hB.le,Real.sq_sqrt hf.le,Real.sqrt_pos.mpr hf]
      rw [show z/2=(2*Real.sqrt β)⁻¹ from by unfold z coupling; field_simp]; exact inv_anti₀ (Real.sqrt_pos.mpr hB) hv
   apply sk.trans; change _≤ (r*β)*(p.linear*s*z); have hr:= mul_le_mul_of_nonneg_left hm (show 0≤r*β*p.linear*z by positivity); nlinarith only [hr, show r*p.linear*β*z^2=r*p.linear from (by rw [mul_assoc (_*_) β,hb,mul_one])]
 intro n; unfold Graph.taxY; change β*((n.val:ℝ)^4*(C*s^3+C*s^4))+(n.val:ℝ)^4*(Λ*s^2) ≤ _; change C*(2*x*s^3)*(1+s)+Λ*s^2 ≤ _ at v'
 have hz': 0≤ C:= c.elim le_of_lt fun t=> by rw [t] -- tune binder
 linarith only [mul_le_mul_of_nonneg_left v' (show 0≤(n.val:ℝ)^4 by positivity),mul_le_mul_of_nonneg_right hs (show 0≤(n.val:ℝ)^4*(C*s^3+C*s^4) by positivity)]
end YM.CF.Papyrus.Pharos
#print axioms YM.CF.Papyrus.Pharos.fuelGauge
