import Risa.Workshop
import Risa.Commodore
import Risa.Snag
import Risa.Variance
import Risa.Leaves
import Risa.Clamp
import Risa.Aurora
import YM.SU5.Regis.Hospitality
import Taffeta.Stigma
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
namespace Risa
open Regis ProbabilityTheory
open _root_.YM.Regis.Head AnalyticBridge.VerifiedReset StressFlux Lattice.PlaqAxes Virgo _root_.YM.CF.Scree
open Almanac CF.BProof
variable (Qh:Hike) (y:ℝ)(R₀:Rules G)(Lc:Side)
local notation "φ"=>scaleY
private lemma port_flux (x:ℝ)(p:0<x)(t:x/2 ≤ β)(g:β≤2*x)(q:Clip)(Q:Hike)(a:ℝ)(u:0 ≤ a)(y:ℝ)(y':0 ≤ y): ∃ M:ℝ, 0≤ M :=⟨1,zero_le_one⟩ -- skip
abbrev towerC(G:Gauge)(q:Clip):ℝ:=ridges*2*Etch.rays q 2 * Fintype.card Stitch * Fintype.card Signed -- horizon
lemma gainC (G:Gauge)(q:Clip)(X:Hike){a:ℝ}(h:|a|≤2) : limitRay (G:=G) (q:=q) X a ≤ towerC G q * X.cost:=by
 have hc: (X.cost:ℝ)≥0:=X.safe.le
 unfold limitRay Etch.lensLimit towerC; change (((ridges:ℝ)*2*X.cost)*Etch.rays q a)*_*_ ≤_
 have hg:Etch.rays q a ≤ Etch.rays q 2:=by unfold Etch.rays; rw [abs_of_pos (show (0:ℝ)<2 by norm_num)]; gcongr; all_goals first|positivity|assumption
 calc
 _ ≤ (((ridges:ℝ)*2*X.cost)*Etch.rays q 2)*(Fintype.card Stitch)*(Fintype.card Signed):= by gcongr
 _ = _ := by ring
-- uniform rate. F^24h enormous
lemma revenueα (q:Clip)(A:ℕ) : ∀ᶠ x:ℝ in atTop,∀ V:BudgetPoint,V.threshold=temp x →∀ β:ℝ,x/2 ≤ β→β ≤2*x→
 0 ≤ sock A x ∧ 4*sock A x*tempRate V (hatch A x) (Real.sqrt x)^2 ≤ 1 ∧ sunFee (hatch A x) R₀ (Real.sqrt x) V (v:=tuition Lc x) ≤ 1 ∧ ∀ T:ℕ,rebate G R₀ (hatch A x) β (sock A x) (Real.sqrt x) V (tuition Lc x) q (T*capacityS A x)≤2*T :=by
 -- given P≥etc.
 let M:ℝ:=max 4 (max (trend) (max (2*(ridges:ℝ)+2) (towerC G q+1)))
 filter_upwards [eventually_gt_atTop (0:ℝ),foliage R₀ Lc A,summitG.eventually_ge_atTop M] with x hp hf hM p r β s t
 let z:=φ x; let k:=sock A x; let N:ℝ:= capacityS A x; let η:=hatch A x; let h:=heightH A; let d:=gradM p (Real.sqrt x)
 let w:=z^h; let Y:=Real.sqrt x*coupling β
 have a:= (le_max_left 4 _).trans hM -- recursive max
 have a1:4 ≤ z:= a; have hv:=summitT x; change 1 ≤ z at hv; have hz:0<z:=zero_lt_one.trans_le hv
 have hi:1 ≤ h:=by unfold h heightH; omega
 have hW:z ≤ w:=le_trans (by simp : z≤ z^1) (pow_le_pow_right₀ hv hi)
 have hw0:1  ≤ w:=hv.trans hW; have h0:0<w:=zero_lt_one.trans_le hw0
 have nk:w^(24:ℕ)≤N:= (le_of_eq (show _=z^(24*h) from ((by rw [←pow_mul,Nat.mul_comm h]) : (z^h)^24=z^(24*h)))).trans (Nat.le_ceil _)
 have hn:0 < N:=by unfold N; exact_mod_cast reaches A x
 have hk:k*N=z^A:=by unfold k sock; change z^A/N*N=_; field
 have k0:0 ≤ k:=by unfold k sock; positivity
 have k':z^A ≤ w:=pow_le_pow_right₀ hv (show A ≤ h from (by unfold h heightH; omega))
 let f:=tempRate p η (Real.sqrt x)
 have hg:d=(ridges:ℝ)*z^2:=by unfold d gradM; rw [r,clockτ hp]
 have hr:(ridges:ℝ)+1 ≤ z:=by have h0:= (le_max_left ((2:ℝ)*ridges+2) (towerC G q+1)).trans ((le_max_right (trend) _).trans ((le_max_right 4 _).trans hM)); linarith only [h0,Nat.cast_nonneg (α:=ℝ) ridges]
 have hT:towerC G q ≤ z:= (le_add_of_nonneg_right zero_le_one).trans ((le_max_right ((2:ℝ)*ridges+2) _).trans ((le_max_right trend _).trans ((le_max_right 4 _).trans hM)))
 obtain ⟨h1,h2⟩:= Etch.railB s t hp; change _ ≤ Y at h1; change Y ≤_ at h2
 have hy: |Y|≤2:=by rw [abs_le]; constructor <;> linarith only [h1,h2]
 have hw: η.cost=w:= rfl
 have hY:limitRay (G:=G) (q:=q) η Y ≤ w^2:= (gainC G q η hy).trans (by rw [hw,pow_two]; gcongr; exact hT.trans hW)
 have he: f ≤ w^3:=by
    unfold f tempRate; rw [show gradM p (Real.sqrt x)=d from rfl,hg,hw]; have hv':(ridges:ℝ)+1 ≤ w:= hr.trans hW
    have hg0: (ridges:ℝ)*z^2 ≤ ridges*w^2:=by gcongr
    rw [max_eq_right hg0]; nlinarith only [mul_le_mul_of_nonneg_right hv' (sq_nonneg w), (show 1 ≤ w^(2:ℕ) from one_le_pow₀ hw0)]
 have h1f:= (rate_at (G:=G) η (Real.sqrt x) p).1 -- 1
 have hD:0 ≤ f:=zero_le_one.trans h1f
 have hΔ:d+1 ≤ z^3:=by rw [hg]; nlinarith only [(show 1 ≤ z^ (2:ℕ) from one_le_pow₀ hv),mul_le_mul_of_nonneg_right hr (sq_nonneg z)]
 let Qf:=sunFee η R₀ (Real.sqrt x) p (v:=tuition Lc x)
 have hσ: Qf*w≤1:=hf p r
 have he':z^A*2*(d+1)  ≤ w:=by
    calc
      _ ≤ z^A*z*z^3:=by gcongr <;> linarith
      _= z^(A+1+3):=by rw [pow_add,←pow_succ]; -- tune
      _ ≤ _:= pow_le_pow_right₀ hv (by unfold h heightH; omega)
 have hbb: 4*k*f^2 ≤1:=by
    have hP:w^2*w*w^6 ≤ w^24:=by rw [mul_assoc,←pow_succ',←pow_add]; exact pow_le_pow_right₀ hw0 (by norm_num)
    have htZ: (4:ℝ)  ≤ w := a.trans hW
    have hk'': k*N ≤ w:= hk.trans_le k'
    have h': (4*k*f^2)*N≤ w*w*w^6:=by
       rw [show (4*k*f^2)*N=4*(k*N)*f^2 by ring]; have hpS: f^2 ≤ w^6:=(pow_le_pow_left₀ hD he _).trans_eq (by ring); gcongr
    have hZ:w*w*w^6 ≤ w^24:= (show _=w^8 from by ring).trans_le (pow_le_pow_right₀ hw0 (by norm_num)); nlinarith only [(h'.trans hZ).trans nk,hn]
 refine ⟨k0,hbb, ?_,?_⟩
 · rcases le_total Qf 0 with q|q; · exact q.trans zero_le_one
   exact (le_mul_of_one_le_right q hw0).trans hσ
 intro T; let i:ℝ:=T
 unfold rebate; rw [Nat.cast_mul,mul_pow,Real.sq_sqrt (by positivity)]
 unfold portent; change k*(2*(d+1)*Qf)*(i*N)+trend*((2*k*f*limitRay (G:=G) (q:=q) η Y)^2*(i*N))≤2*i
 have hp: trend  ≤ w:= ((le_max_left trend _).trans ((le_max_right 4 _).trans hM)).trans hW
 have ho:0 ≤ trend:=by unfold trend; positivity
 have hg: trend*(2*k*f*limitRay (G:=G) (q:=q) η Y)^2*N≤1:=by
    have hg':0 ≤ limitRay η Y (G:=G) (q:=q):= xRay ..
    let C:=limitRay (G:=G) (q:=q) η Y
    have he: trend*(2*k*f*C)^2*N*N ≤ w*(w*w*w^3*w^2)^2:=by
       rw [show trend*(2*k*f*C)^2*N*N=trend*(2*(k*N)*f*C)^2 by ring]; have hr:k*N ≤ w:=hk.trans_le k'; gcongr; exact (show (2:ℝ)≤ w by linarith only [a1,hW]) -- gcongr auto? inspect
    have ht: w*(w*w*w^3*w^2)^2 ≤ w^24:=(show _=w^15 from by ring).trans_le (pow_le_pow_right₀ hw0 (by norm_num)); have hh:= (he.trans ht).trans nk; nlinarith only [hh, hn]
 have hs: k*(2*(d+1)*Qf)*N≤1:=by
    rw [show k*(2*(d+1)*Qf)*N=k*N*2*(d+1)*Qf from (by ring),hk]
    rcases le_total Qf 0 with q|q0
    · have he:0 ≤ d:=by unfold d gradM; positivity
      exact (mul_nonpos_of_nonneg_of_nonpos (by positivity) q).trans zero_le_one
    exact (mul_le_mul_of_nonneg_right he' q0).trans (by rwa [mul_comm])
 nlinarith only [mul_le_mul_of_nonneg_right hs (show 0 ≤ i by positivity),mul_le_mul_of_nonneg_right hg (show 0 ≤ i by positivity)]
#check one_le_pow₀
#print axioms revenueα
end Risa
end YM.Gleam.Luster
