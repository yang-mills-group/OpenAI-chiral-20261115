import SatinThinVista
import ZecaFired
import ZecaPuff
import ZecaFlake
import YM.SU5.Six.Aprons
import YM.SU5.Cordial.Horizon
import YM.SU5.Cordial.Spritz
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 2000
set_option maxHeartbeats 280000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance
open Lamour.Bridge.Celeste
open Designs Twah Prototype
open YM.Stationary (Gaia) -- tune
open CF.Onyx (riseX moor)
open Lamour.Bridge.Celeste.Morn
namespace Spine
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000
set_option maxRecDepth 8000

open CF.Velvet CF.Pannier.Chancel
variable (P:Spine){K:P.Register} (Z:Lead.Clan)
def powderPay (s m w:ℕ) (e:ℝ):Prop:=
 ∀ (Z:Lead.Clan)(a:Axis)(x:P.Spectrum0 a)
 (T:(P.ColorHil a x).Op),
 P.Fired a x s (2*w)
     (P.shifts a w (P.frontMat Z m) - (purePrice Z:ℂ) • (1:P.Test)) T →
 ‖T‖ ≤ e


def fairFlurry (s m:ℕ)(e:ℝ):Prop:=
 ∃ w, (∀ j:Axis,P.probeClock m j≤w) ∧ w * P.macroStep s ≤ e ∧ P.powderPay s m w e
variable {X:Supplier}{v b:ℝ}(p:uniform P K X v b)(O:P.NightCop)
include p O
lemma feather_build {e:ℝ} (u:0<e):
 ∀ᶠ m in atTop, ∀ᶠ s in atTop,P.fairFlurry s m e:=by
 let y:=Real.exp 1
 have hy:0< y:=Real.exp_pos 1
 let d:= e/(2*y)
 have hd:0<d:=div_pos u (by positivity)
 have hd':2*(Real.exp 1*d)=e:=by
    change 2*(y*d)=_; unfold d; field_simp
 obtain ⟨_,_,_,_,_,_,t,_⟩:= p.1.paper
 filter_upwards [Filter.eventually_all.mpr (fun Z:Lead.Clan=> P.mist_clarity Z hd)] with m ht
 have h:=Filter.eventually_all.mpr
    (fun Z:Lead.Clan=> Filter.eventually_all.mpr
      (fun j:Axis=> Papal.crystal_law P.run P.large P.law P.history
          P.projection.clipped O j (P.room j) (P.mist_voice Z m) t p.2 p.1.nerve hd (ht Z)))
 obtain ⟨w,v',z⟩:=(h.and (Filter.eventually_all.mpr (fun j:Axis=>eventually_ge_atTop (P.probeClock m j)))).exists
 have t₀:=Filter.eventually_all.mpr (fun Z:Lead.Clan=> Filter.eventually_all.mpr (v' Z))
 have hl : Tendsto (fun s=>w * P.macroStep s) atTop (𝓝 (0:ℝ)):=by simpa using (P.macroStep_zero.const_mul (w:ℝ))
 filter_upwards [t₀,hl.eventually_le_const u] with s hg hk
 refine ⟨w,z,hk,?_⟩
 intro Z j x T F
 apply F.mean_le
 intro E p' t'
 apply le_trans _ hd'.le
 apply hg Z j
 let G:=P.frontMat Z m - (purePrice Z:ℂ) • (1:P.Test)
 have g:P.voxTest j s E.val=P.shifts j w G:=by
   unfold G; rw [map_sub,map_smul,map_one]; exact t'
 exact congrArg (fun a:P.Test => a.val) g
omit p O
/-- **schedule**. -/
def Snowy(c r:ℕ→ℕ):Prop:=∀ n,P.fairFlurry (c n) (r n) (keyV n)
include p O in
lemma schedule_ask (a:ℕ→ℕ) : ∃ z:ℕ→ℕ, a≤ z ∧ ∀ r:ℕ→ℕ,z≤r →
 ∃ b:ℕ→ℕ,∀ c:ℕ→ℕ,b≤ c → P.Snowy c r:=by
 choose f g using fun n=> eventually_atTop.1 (P.feather_build p O (keyV_positive n))
 refine ⟨fun i=> max (a i) (f i),fun i=>le_max_left .., ?_⟩
 intro r h
 choose b t using fun n=> eventually_atTop.1 (g n (r n) ((le_max_right ..).trans (h n)))
 exact ⟨b,fun M u n=>t n (M n) (u n)⟩

#print axioms Spine.schedule_ask
