import YM.CF.Ups.Beet
import YM.CF.Emu.Well
set_option autoImplicit false
noncomputable section
namespace YM.CF.Emu
open YM.CF.Onyx
open Function Filter Metric Fir Lattice Laurent Next.Free Bloch Finset Lat Ember Jill Kea Flare Rush Tulip Cube Fock SU Dial Thera
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix Matrix.Norms.L2Operator Kronecker
attribute [local instance] opCStarAlgebra
open YM.Stationary (Gaia)
open MeasureTheory Sods Girt Cube Pyx Py Scree Skye Graph
variable {N:Side}
variable {q:Wave (Single N)}
def σ_k(P:InkPS N)(Y:Pane N): Phys N:=∫ z:Ids N,P (Y,z)∂depot N
def gaugeMarg(P:InkPS N)(Y:Pane N):ℂ:= beamL N (σ_k P Y)
def full(P:InkPS N):Phys N:=∫ y,P y∂city N
-- collapse auxiliary book. covariance.V. rank tensor proof STILL scale0
private lemma factFan (g:Seat N→ E)(f:Orbit N→Phys N): (∫ y:Orbit N,f (gird g y) ∂city N)=∫ y,f y ∂city _:=by
 let T: MeasurableEquiv (Orbit N) (Orbit N):= ⟨⟨gird g,gird g⁻¹,gird_inv _,fun i=>by simpa only [inv_inv] using gird_inv g⁻¹ i⟩,(brace_ps g).measurable,(brace_ps g⁻¹).measurable⟩; exact (show MeasurePreserving T _ _ from brace_ps g).integral_comp' f
open RG
lemma boot_i {α:Type*} (P:InkPS N)(o:Opt (α:=α) N) (h:Hebi (fun i=> P i)) : ∀ g:Seat N→ E,effectK (tradew N g).val (full P)=full P :=by
 intro g; let Q:= (acts (quant (tradew N g).val)).restrictScalars ℝ; let S:=city N; let f(y:Orbit N):= P y; have hq:Integrable f S:= (Lp.memLp P).integrable (by norm_num)
 change Q (∫ y:Orbit N,f y ∂S)=_; rw [← Q.integral_comp_comm hq]; refine Eq.trans ?_ (factFan g f); apply integral_congr_ae; exact (h g).mono fun x t=> Eq.symm t -- cast full issue
variable {α:Type*}{a:α→TagT}(o:Site N)(i j:α)(R:ℝ)
local notation "Υ"=>Wilson.prior SU.group (More N)
set_option quotPrecheck false
include R
local notation "QJ"=> (show Opt (α:=α) N from ⟨o,R,[i,j],a⟩)
lemma poleH (P:InkPS N)(h:Hebi (fun i=> P i))(b: Integrable (fun x:Orbit N=> (plume QJ) x (P x)) (city _))(Z: Pane N→ℂ)(p:∀ᵐ i∂Wilson.prior SU.group (More N), σ_k P i=Z i • full P)(hi:signW (a i).2=true)(hj:signW (a j).2=false)(t:node (o+wrap N (a i).1)≠ node (o+wrap N (a j).1)) : Py.remark (plume QJ) P=0:=by
 let q:=full P; have hp (x:Pane N) : valA o x R a [i,j] q=0:=by
    have he:= tank o x R a [i,j] q 0; change _=∫ z:E, Emu.wall o x z R a [i,j] q 0∂_ at he; rw [mul_zero,sub_zero] at he; rw [he]; simp_rw [wall, fun y=>goLam o x y (q:=q) (boot_i P QJ h) a i j R hi hj t]; simp
 let f(x:Pane N):Phys N→L[ℂ]ℂ:= (innerSL ℂ (mateK N)).comp (acts (muni o x R a [i,j])); unfold Py.remark; rw [integral_prod _ b, ← show (∫ _x:Pane N,(0:ℂ)∂Υ)=0 from integral_zero ..]; apply integral_congr_ae
 have he:Integrable (fun x:Orbit N=>P x) (city N):=(Lp.memLp P).integrable (by norm_num); filter_upwards [p,he.prod_right_ae] with x h t; change (∫ i:Ids N,f x (P (x,i)) ∂_)=0; apply Eq.trans ((f x).integral_comp_comm t) -- tune aescales
 change f x (σ_k P x)=0; rw [h, map_smul, show f x (full P)=0 from hp x, smul_zero]
-- even rank-one product with arbitrary integrable scalar not possible
omit R
lemma relic(P:InkPS N)(h:Hebi (fun i=>P i))(W:Pane N→ℂ)(f:Phys N)(hv: ∀ᵐ x∂Wilson.prior group (More N),σ_k P x=W x • f)(hm:Integrable W (Wilson.prior group (More N)))(hs:Py.remark (fun _:Orbit N=>beamL N) P=1):∃ Z:Pane N→ℂ,∀ᵐ i∂Wilson.prior group (More N), σ_k P i=Z i • full P:=by
 have hY:Integrable (fun i:Orbit N=> P i) (city _):=(Lp.memLp P).integrable (by norm_num); have hp:= (beamL N).integral_comp_comm hY; have hx:beamL N (full P)=1:= hp.symm.trans hs -- syntax
 let c:=∫ y,W y∂Υ; have hh: full P=c • f:=by unfold full; change (∫ i:Orbit N, P i∂(Υ).prod (depot N))= _; rw [integral_prod _ hY]; change (∫ i,σ_k P i∂Υ)=_; rw [show _= (∫ y,W y • f ∂Υ) from integral_congr_ae hv, integral_smul_const]; -- tune Prod
 rw [hh] at hx; have he:c≠0:=fun p=>by rw [p,zero_smul,map_zero] at hx; exact zero_ne_one hx
 refine ⟨fun i=>W i/c,?_⟩; rw [hh]; filter_upwards [hv] with i h; rw [h,smul_smul,div_mul_cancel₀ _ he]
end YM.CF.Emu
