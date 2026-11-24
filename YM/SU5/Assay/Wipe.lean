import YM.SU5.Assay.Lamp
import YM.SU5.Assay.WickTest
import YM.SU5.Assay.RawTransfer
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4900
set_option maxHeartbeats 420000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance
namespace Spine
open Aria Set OS.Semigroup
variable (P:Spine)(j:Axis)(x:P.Spectrum0 j)
local notation "K"=> P.calibration
local notation "H"=> P.ColorHil j x
local notation "B"=> P.ManyF j x
local notation "X"=> (P.ColorHil j x).Op
local notation "Y"=> (P.ManyF j x).Op
local notation "Lag"=>ℝ→ℝ→(P.ManyF j x).Op
local notation "S"=> P.seasons j x
local notation "U"=> P.physicalEnergy j x
local notation "ω"=> (P.seasons j x).wax
local notation "W"=> P.cartage j x
local notation "θ"=> P.tableau j x
local notation "E"=> P.enter j x
local notation "R"=> P.wealth j x
local notation "Vac"=> P.colorZero j x
local notation "Ω"=> P.heaven j x
/-! Fixed-lag depletion before spatial projection. -/
variable {P j}{a b C g e:ℝ}{z:ℂ}
local notation "β"=>P.rawBase j x
local notation "τ"=>P.tock
local notation "φ"=> (P.physicalEnergy j x).wax
local notation "𝕞"=>P.meanBox j
local notation "μ"=>P.seenBox j x
local notation "σ"=>P.shifts j

lemma tock_nonneg (P:Spine)(s t:ℕ):0≤P.tock s t:=by rw [←P.tock_zero s,P.tock_le];omega
lemma tock_fades (P:Spine)(w:ℕ): Tendsto (fun s=>P.tock s w) atTop (𝓝 0):= by
 simpa only [tock_price,mul_zero] using P.macroStep_zero.const_mul ((w:ℤ):ℝ)
lemma tock_small (P:Spine)(w:ℕ){a:ℝ}(h:0<a):∀ᶠ s:ℕ in atTop,P.tock s w≤a:=
 ((P.tock_fades w).eventually (gt_mem_nhds h)).mono fun i h=>h.le
private lemma wick {D D':P.Apron}(s:ℕ)(p:D.s=s)(q:D'.s=s)(h:D.F=D'.F)(v:τ s (D.u j)≤a)(w:τ s (D'.u j)≤a): β D a a=β D' a a:=by
 rcases le_total (D.u j) (D'.u j) with r|r
 · rw [←engineAxle_widen x s p r w w,h,P.rawBase_engineAxle j x D',q]
 · rw [←engineAxle_widen x s q r v v,←h,P.rawBase_engineAxle j x D,p]

variable (j)
lemma down_wick {A A':P.Glaze}(h:A.F=A'.F)(r:0<a)(p:0≤g)(t:0<e)
    (v:∀ᶠ s in atTop,‖𝕞 s (A'.w+A'.w) (σ A'.w (1+z•A'.F))‖≤1+g):
    ∀ᶠ s in atTop,∀x:P.Spectrum0 j,∀u:P.ColorHil j x,(z*inner ℂ u (P.rawBase j x (A.apron s) a a u)).re ≤(e+g)*‖u‖^2:=by
 let Q:=A'.w+A'.w
 have hf:=A'.centers j; have hc:=P.shifts_keep j A'.w A'.color
 let J:=A'.w
 let f:=σ J A'.F
 have hu:0<Q:=add_pos A'.pos A'.pos
 have H₀:∀ᶠ s in atTop,∀x:P.Spectrum0 j,‖(P.physicalEnergy j x).wax (a-τ s J+(a-τ s J))-(P.physicalEnergy j x).wax (a+a)‖<e:=by
    have g':Tendsto (fun s=> a- τ s J) atTop (𝓝 a):=by simpa using tendsto_const_nhds (x:=a) |>.sub (P.tock_fades J)
    filter_upwards [wax_mod (g'.add g') (add_pos r r) t] with s v
    exact fun x=>v _
 filter_upwards [v,H₀,P.tock_small J r,P.tock_small A.w r] with s hs gs d w
 intro x
 specialize gs x
 let G:= P.seenBox j x s Q f
 have e': ‖(P.physicalEnergy j x).wax (τ s J+τ s J)+z•G‖≤1+g:=by
    rw [map_add,map_one,map_smul] at hs
    have ht :P.BEntry j Q 1:=BEntry.one _ _ hu -- tune
    have K₀:= (seenBox_pay s x (ht.add (hf.smul z))
      ((enclave K).add_mem (enclave K).one_mem ((enclave K).smul_mem hc z))).trans hs
    rw [seenBox_add s x ht (hf.smul z) (enclave K).one_mem ((enclave K).smul_mem hc z),seenBox_smul s x hf hc,P.seenBox_unit j x s hu, show Q=J+J from rfl,Nat.cast_add,P.tock_add] at K₀
    exact K₀
 apply wickTest (P.physicalEnergy j x) (P.tock_nonneg _ _) d p e' gs.le
 rw [wick x s rfl rfl (D':=A'.apron s) h w d,P.rawBase_engineAxle];rfl

namespace Glaze
-- Price centered sticker F − y • 1. Disposable wrapper in proof only.
def soot (A:P.Glaze)(y:ℂ):P.Glaze :=
   ⟨A.w,A.pos,A.S,A.F+(-y)•1,(bay ..).add_mem A.inlet ((bay ..).smul_mem (bay ..).one_mem _),
     (enclave K).add_mem A.color ((enclave K).smul_mem (enclave K).one_mem _),A.fits⟩
lemma static (A:P.Glaze): Glaze.Tiny (fun _=>A):=by
 unfold Tiny; simpa using P.macroStep_zero.const_mul (A.w:ℝ)
end Glaze
variable {A:P.Glaze}{y:ℂ}
lemma Taste.four (v:P.Taste A.F A.S y)(r:0<a)(t:0<e):
    ∀ᶠ s in atTop,∀x:P.Spectrum0 j,‖P.rawBase j x ((A.soot y).apron s) a a‖≤4*(2*e):=by
 let ε:=e/12; have ep:0<ε:=div_pos t (by norm_num)
 obtain ⟨c,u,h⟩:=v j _ ep
 let d:=min c (1/(6*ε)); have hd:0<d:=lt_min u (by positivity)
 let f:Finset ℂ:= {↑d,-↑d,Complex.I*↑d,-Complex.I*↑d}
 let g:= 2*(3*(ε*d)); have w: g+g=d*e:=by unfold g ε; ring
 have gp:0<g:=by positivity
 have K'(Z:ℂ)(q:Z∈f):∀ᶠ s in atTop,∀x:P.Spectrum0 j,∀u:P.ColorHil j x,(Z*inner ℂ u (P.rawBase j x ((A.soot y).apron s) a a u)).re≤d*e*‖u‖^2:=by
   have e': ‖Z‖=d:=by
     simp only [f,Finset.mem_insert,Finset.mem_singleton] at q;rcases q with rfl|rfl|rfl|rfl <;> simp [Real.norm_of_nonneg hd.le]
   obtain ⟨N,w₀,p₀,t⟩:=h Z (e'.symm ▸ hd) (e'.trans_le (min_le_left ..))
   have g₀: 3*(ε*‖Z‖) ≤1/2:=by
      rw [e']; have z:d≤1/(6*ε):=min_le_right ..
      nlinarith only [(le_div_iff₀ (by positivity:0<6*ε)).mp z]
   let T:=A.soot y
   let T':P.Glaze:=⟨N,w₀,T.S,T.F,T.inlet,T.color,p₀⟩
   rw [←w]
   apply down_wick j (A:=T) (z:=Z) (A':=T') rfl r gp.le gp
   refine t.mono (fun s u=>u.trans ?_)
   rw [e']; exact budget_exp_small _ (by positivity) (e' ▸ g₀)
 filter_upwards [(eventually_all_finite f.finite_toSet).mpr K'] with s h
 intro x
 exact wickTest_four d e hd t.le (fun z q=>h z q x)
lemma Taste.clean_rate (h:0<e) (v:P.Taste A.F A.S y)(p:0<a)(q:0<b):
  ∀ᶠ s in atTop,∀x:P.Spectrum0 j,‖P.rawBase j x ((A.soot y).apron s) a b‖<e:=by
 let d:=min a b
 let c:=e/9; have t:0<c:=div_pos h (by norm_num)
 have w:0<d:=lt_min p q
 filter_upwards [Taste.four j v w t,P.tock_small A.w w] with s u h₁
 intro x; specialize u x
 rw [ P.rawBase_step j x ((A.soot y).apron s) h₁ h₁ (min_le_left ..) (min_le_right ..)]
 apply ((sand_pay (P.physicalEnergy j x) ..).trans u).trans_lt
 unfold c;linarith
variable {j:Axis} in
lemma Taste.clean (x:P.Spectrum0 j)(v:P.Taste A.F A.S y)(p:0<a)(q:0<b):
  Tendsto (fun s=> P.rawBase j x ((A.soot y).apron s) a b) atTop (𝓝 0):=by
 rw [Metric.tendsto_nhds]
 intro e h; simpa using (Taste.clean_rate j h v p q).mono (fun s h=> h x)
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
