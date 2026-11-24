import WakeRoad.Saplings
import YM.UVNext.FREE_STRESS_CERTIFICATE.Diagonal
set_option autoImplicit false
set_option synthInstance.maxSize 26000
set_option maxHeartbeats 300000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark SatinVerification Vacancy Tapestry
open CF.Pannier.Chancel
open Preparation.Yoke EmberWind Jewel
open Lamour.Bridge.Celeste Morn
open Ballad
open SpinReceipt Shuttle
open Papal (Weaver household)
open WakeInvestment
open Gleam Gleam.Wake YM.WakeRoad CF.Hiro Hearth
open Precision Regis.Head.Brecht Regis.Circuit Exterior
namespace GramSignal
set_option quotPrecheck false
set_option linter.unusedSectionVars false
open ArborJet Preparation Yoke.ArborJet
open Dial Pressure Stationary Regis.Circuit
open Stationary CF.Onyx
variable (P:Spine)(r:ℕ→ℕ)
local notation "Y"=>P.run
local notation "Λ"=>P.par
local notation "R*" i:max=> ((moment P i):ℝ)
local notation "σ*" i:max=> stanceR P i
local notation "X*" i:max=>hat P.par.R.L P.par.x i
local notation "μ*" i:max=>Pressure.radiusB (hat P.par.R.L P.par.x i)
abbrev CardsT (s:ℕ):=Postcard (Pressure.radiusB (hat P.par.R.L P.par.x s)/10)
local notation "I*" i:max=> CardsT P i
open CF.Gingham.Ruff Spine.Gingham.VoyageB
lemma priced_epsilon : Tendsto (fun s:ℕ=>( (μ* s : ℝ)+2)/R* s) atTop (𝓝 0):=by
 open Pressure.Worth Pressure.Worth.Pays in
 have h:Pays 0 0 2 (fun x:ℝ=> (2*(radiusB x+2:ℝ))):=Pays.scale 2 (plus Worth.Pays.rising (Worth.Pays.merit (constant 2) (by norm_num [Worth.Earlier])))
 -- `open` scoped h only, tune
 open Pressure.Worth Pressure.Worth.Pays in
 have he:Tendsto (fun x:ℝ=> (2*(radiusB x+2:ℝ)) * BProof.coin x 0 (-12) 0) atTop (𝓝 0):= limit (times h (whole ..)) (Or.inr (.inl ⟨by norm_num,by norm_num⟩))
 apply squeeze_zero (fun _=>div_nonneg (by positivity) (by positivity)) _ (he.comp (turnover P.par))
 intro j
 let x:= X* j
 have t:= zoom_pos (P:=P) 12 j
 have hv : sPow P.par j 12 / 2 ≤ R* j := Nat.le_ceil _
 have hz: 0 < sPow P.par j 12:= BProof.coin_pos ..
 change _ ≤ _ * _
 refine le_trans (div_le_div_of_nonneg_left (by positivity) (half_pos hz) hv) (le_of_eq ?_)
 rw [div_div_eq_mul_div,div_eq_mul_inv,BProof.coin_inv]; simp; ring_nf; simp
private lemma flux_t (z:ℕ → Cover)(h:∀s,z s ∈Lattice.box (μ* s + 1)) :
 Tendsto (fun s=>riseX (2* R* s) (z s)) atTop (𝓝 0):=by
 let f(s:ℕ)(i:Axis):ℝ:=(z s i:ℝ)/(2* R* s)
 have t:Tendsto f atTop (𝓝 (0 : Axis → ℝ)):= tendsto_pi_nhds.mpr (fun i=>?_)
 swap
 · simp only [Pi.zero_apply]; rw [tendsto_zero_iff_norm_tendsto_zero]; refine squeeze_zero (fun _=> norm_nonneg _) (fun j=> ?_) (priced_epsilon P)
   have he := Lattice.box_test.mp (h j); have e:|(z j i:ℝ)| ≤ (μ* j:ℝ)+1:=by
     rw [abs_le]; exact_mod_cast (show -( ((μ* j)+1:ℕ):ℤ)≤ z j i ∧ z j i ≤ ( ((μ* j)+1:ℕ):ℤ) from ⟨he.1 i,he.2 i⟩) -- Nat.cast simplification plus
   let c:=R* j
   have hp:0 < c:=Nat.cast_pos.mpr (zoom_pos (P:=P) 12 j)
   change |f j i| ≤ _/c
   unfold f; rw [abs_div,abs_of_nonneg (show (0:ℝ)≤2*c by positivity)]
   gcongr <;> linarith
 have hc : Continuous (fun v: Axis→ℝ => moor v):=by unfold moor; exact PiLp.continuous_toLp ..
 exact (show moor 0 = (0:Gaia) from rfl) ▸ hc.continuousAt.tendsto.comp t
local notation "ζ"=> (Signed.mirror 3)
local notation "O" s:max => (2 • (stanceR P s) • (step (3:Axis):Cover))
abbrev adress (s:ℕ)(b:Bool)(x:Cover)(i:PlaqAxes):Cover:= if b then (ζ).act x+O s+ distal i else x
lemma compass_pose (s:ℕ)(n:Side)(b:Bool)(j:I* s): wrap (More n) (adress P s b j.1.1.val j.1.2)=ArborJet.taking (μ* s/10) (σ* s) b (N:=n) j:=by
 cases b; · rfl
 unfold ArborJet.taking adress; simp only [if_true]
 unfold town anis affine; rw [map_add,map_add, Lattice.wrap_signed]

private lemma clock_ok (X:∀ s,I* s) : Tendsto (fun s=> riseX (2* R* s) ((X s).1.1.val)) atTop (𝓝 0):=
 flux_t P _ (fun s=>by obtain ⟨a,b⟩:= Lattice.box_test.mp (X s).1.1.property; apply Lattice.box_test.mpr; constructor <;> intro i <;> specialize a i <;> specialize b i <;> omega)
private lemma peek_ok (X:∀ s,I* s)(a:PlaqAxes):Tendsto (fun s=>riseX (2* R* s) ((ζ).act (X s).1.1.val + distal a)) atTop (𝓝 0):=by
 apply flux_t; intro s; obtain ⟨v,t⟩:=Lattice.box_test.mp (X s).1.1.property
 apply Lattice.box_test.mpr; constructor <;> intro j <;> unfold distal <;> split <;>simp [Signed.act,Signed.mirror,step_apply] <;> specialize t j <;> specialize v j <;> split_ifs <;> omega

private lemma ruler_flux (A B:∀ s, I* s)(d:PlaqAxes) : Tendsto (fun s=> riseX (2* R* s) ((A s).1.1.val-adress P s true (B s).1.1.val d)) atTop (𝓝 (YM.basis 3)) := by
 have h:= (clock_ok P A).sub (peek_ok P B d); rw [sub_zero] at h
 have hx:= h.add_const (basis 3); rw [zero_add] at hx; refine hx.congr fun i=>?_
 ext v
 simp only [PiLp.add_apply,PiLp.sub_apply,basis_eq]; unfold riseX; -- above names
 unfold adress; simp only [if_true, Pi.add_apply,Pi.sub_apply]
 let h:ℝ:= (moment P i:ℝ); have hp:h≠0:= (Nat.cast_pos.mpr (zoom_pos (P:=P) 12 i)).ne'
 let a:=(A i).1.1.val v; let b0:=(ζ).act (B i).1.1.val v; let b:=b0+distal d v; let c:=(O i : Cover) v
 change (a:ℝ)/(2*h)-(b:ℝ)/(2*h)+(if v=3 then 1 else 0)= ((↑(a-(b0+c+distal d v)):ℝ))/(2*h)
 have hc:c=if v=(3:Axis) then -(2:ℤ)*↑(ArborJet.moment P i) else 0:= by unfold c; simp only [Pi.smul_apply, stanceR,step_apply]; split <;> simp
 unfold b; rw [hc]; split <;> push_cast <;> field_simp <;> unfold h <;> ring

open Gingham.Ruff Lifted
private def artificial (x:Cover)(v:PlaqAxes):Staff:=⟨0,0,(x,v),(0,0),Lattice.route (nodeC 0) x 1,route_end ..⟩
local notation "iₛ" i:max=>P.period (P.projection.rows (r i))
local notation "kₛ" i:max=>P.cutoff (P.projection.columns (r i))
local notation "nDoc" s:max i:max=>side P.run (iₛ i) s
local notation "Mₛ" s:max i:max=>P.par.V.L.H ((P.run).uv (kₛ i)-s)
local notation "Q"=> SU.group.ColorIndex
variable (p:StrictMono r)
include p
abbrev axialKernel (N:Side)(M:Bed)(x y:Cover)(v w:PlaqAxes)(i j:Q):ℂ:= coupon (Lattice.wrap (More N) x,v) (Lattice.wrap (More N) y,w) i j M
lemma purchase (A B:∀ s,I* s)(U D:PlaqAxes)(h k:Q):
 Tendsto (fun si:ℕ× ℕ=> ((↑(2* R* si.1):ℂ)^4)*axialKernel (nDoc si.1 si.2) (Mₛ si.1 si.2) (A si.1).1.1.val (adress P si.1 true (B si.1).1.1.val D) U D h k) stairs (𝓝 ((sch (G:=SU.group) h k:ℂ)* specter U D (YM.basis 3))):=by
 let W:=fun s=> artificial (A s).1.1.val U
 let V:=fun s=> artificial (adress P s true (B s).1.1.val D) D
 have e:= gauge_target (P:=P) (r:=ArborJet.moment P) (zoom_pos 12 (P:=P)) (zoom_grows P.par (show (0:ℝ)<12 by norm_num)) W V (a:=YM.basis 3) (fun u=>one_ne_zero (α:=ℝ) (by simpa using congrArg norm u)) (ruler_flux P A B D) p U D (fun _=>rfl) fun _=>rfl
 let I₀:ℂ:=Fintype.card SU.group.ColorIndex; let x:ℂ:=sch (G:=SU.group) h k; let K:ℂ:=x/I₀
 have hkn(y:ℂ): K*(I₀*y)=x*y:=by rw [←mul_assoc, div_mul_cancel₀ x (show I₀≠0 from prism_nonzero)]
 change Tendsto _ stairs (𝓝 (x*_))
 rw [←hkn]; apply (e.const_mul K).congr
 intro z; unfold gaugeCoupon axialKernel coupon; apply (mul_left_comm K _ _).trans; change (_ * (K *(I₀* _)) )= _
 rw [hkn];rfl
#print axioms purchase
