import Aloft.Canon
import Ridgetop.Agenda
import Ridgetop.Origin
import Risa.Warehouse
import Preen.Chey
-- pilot price exactly zero, all. 
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 5000
set_option maxHeartbeats 360000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance
namespace Spine
namespace PledgeT
open Calico
open Aria Casting Set
open scoped Pointwise
namespace MiterT
open _root_.YM.Gleam.Luster.Risa CF.BProof AnalyticBridge.VerifiedReset
open Py.Rate.LocalLimit Py Py.Dyad Papal _root_.YM.CF.Pannier.Chancel Cliplet Precision
variable (P:Spine) (s A:ℕ)(o:Bool→ Cover)(b:Bool)
namespace Aloft
open Ridgetop
local notation "ρ" d:max=> ((girder P d):ℝ)
local notation "γ"=> (pollN P)
variable (m:ℕ)(e:1 ≤ m)
-- for any Enrolled selection param, any lag.Boot.boot.
include e
private lemma ranger {D K:ℕ→ℕ}(td:Tendsto D atTop atTop)(W:ℕ→ Cover)(t:∀i,Enrolled P (D i) (stairW (D i)) (W i))(hx:Tendsto (fun i=> led P m (D i) (W i)* CF.Ember.pinch (showF P (stackW (D i)) (K i))) atTop (𝓝 0)) : Tendsto (fun i=> ‖docket P (stackW (D i)) (K i) (blazeF P m (D i) (W i))‖*(led P m (D i) (W i))^8) atTop (𝓝 ‖Ridgetop.visible‖):=by
 let a(k):=led P m (D k) (W k); let S(k):=showF P (stackW (D k)) (K k)
 have hE:CF.Onyx.Yard S a:=⟨leader P m W t e,elevate P m W t e td,hx,fun i=>evenShow P _ _⟩
 let B:=P.par.V; let C0:=P.par.K; let f(n):=P.run.uv (P.cutoff (P.projection.columns (K n)))-stackW (D n)
 let z(i):= docket P (stackW (D i)) (K i) (blazeF P m (D i) (W i))
 have Ht:Tendsto (fun i=>(a i:ℂ)^8*z i) atTop (𝓝 Ridgetop.visible):= pulseLimit hE (lensΔ P m W t e td) (fun k=>(B.L.roof (f k)).1) C0.width (zero_lt_one.trans_le B.up) (fun k=>(B.L.roof (f k)).2.1 (S k))
 refine Ht.norm.congr fun k=>?_ ; change ‖(a k:ℂ)^8*z k‖=‖z k‖*_
 rw [norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,mul_comm]; rw [abs_of_pos (leader P m W t e _)]
open CF.Onyx
lemma ranged :∀ᶠ d:ℕ in atTop,∀ w:Cover,Enrolled P d (stairW d) w→∀ᶠ k:ℕ in atTop, let κ:=docket P (stackW d) k (blazeF P m d w); let a:= led P m d w;
 ‖Ridgetop.visible‖/2 ≤ ‖κ‖*(a)^8 ∧ ‖κ‖*a^8 ≤ 2*‖Ridgetop.visible‖:=by
 by_contra h; push Not at h; obtain ⟨D,t,C⟩:=extraction_of_frequently_atTop h
 choose W he hc using C
 let f(i):=blazeF P m (D i) (W i); let a(i):ℝ:=led P m (D i) (W i); let S(i):=stackW (D i); let v:=‖Ridgetop.visible‖
 let b(i k):= ‖docket P (S i) k (f i)‖*(a i)^8
 have hG (d:ℕ):Tendsto (fun k=>a d*CF.Ember.pinch (showF P (S d) k)) atTop (𝓝 0):=by
    have ht:= tendsto_inv_atTop_zero.comp ((tendsto_natCast_atTop_atTop (R:=ℝ)).comp (showF_grows P (S d))) |>.const_mul (a d*Real.pi); simpa [CF.Ember.pinch,div_eq_mul_inv,mul_assoc,Function.comp_def] using ht
 have hc' (i):∃ᶠ k:ℕ in atTop, ¬ (v/2 ≤ b i k ∧ b i k ≤2*v):=by apply (hc i).mono; intro k h p; exact h p -- await C
 choose K hx ht using fun i=>( (hc' i).and_eventually ((hG i).eventually (ge_mem_nhds (flowε_p i))) ).exists
 have hy:Tendsto (fun i=> a i* CF.Ember.pinch (showF P (S i) (K i))) atTop (𝓝 0):= squeeze_zero (fun i=> mul_nonneg (leader P m W he e i).le (CF.Ember.pinch_pos _).le) ht summers
 have hg:Tendsto (fun i=> b i (K i)) atTop (𝓝 v):=ranger P m e t.tendsto_atTop W he hy
 have hv:0<v:=norm_pos_iff.mpr Ridgetop.visibility
 obtain ⟨i,x,y⟩:= ((hg.eventually (le_mem_nhds (show v/2<v from half_lt_self hv))).and (hg.eventually (ge_mem_nhds (show v<2*v by linarith)))).exists; exact hx i ⟨x,y⟩
#print axioms ranged
end Aloft
end MiterT
end PledgeT
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
