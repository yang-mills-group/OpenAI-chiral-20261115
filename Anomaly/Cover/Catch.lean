import Anomaly.Cover.Locket
set_option autoImplicit false
set_option synthInstance.maxSize 26000
set_option quotPrecheck false
set_option maxHeartbeats 700000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase
     MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound
     Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker
     ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy
     Tapestry Germ Alliance Lamour.Bridge.Celeste Designs Twah Prototype
open YM.Stationary (Gaia)
open Lamour.Bridge.Celeste.Morn
open CF.Velvet CF.Pannier.Chancel
open Spine Pitching.Focus
open QuadClock Preparation.Yoke
open Swell Sonar StageQ Ione Vow Tapestry.StageW
namespace Spine
universe u
variable (P:Spine)(m:ℕ){R:ℕ→ℝ}{u:ℕ→ ℤ}{L U Q:ℕ→ℕ}{d t:ℝ}
private lemma awningBound (s:ℕ){x:Cover}(p:x∈ roomFox P s m) : let b:= (P.run.meter.a s).B+12+2*m; (1:ℤ)-(b:ℤ) ≤ x 3:=by
 intro b; change x∈ liner {nodeC 0} b at p; obtain ⟨i,h,w⟩:= mem_biUnion.mp p; rw [mem_singleton] at h; obtain ⟨k,v,rfl⟩:= mem_image.mp w; have hx:= (box_test.mp v).1 3; rw [h]; change (1:ℤ)-_ ≤ k 3+nodeC 0 3; simp only [nodeC, smul_zero,zero_add,Pi.one_apply]; omega
lemma overhead (X:Petro P R L U Q u d t) :∀ᶠ s:ℕ in atTop,Tower.region 3 (u s) P.calibration.ℓ (roomFox P s m):=by
 let ℓ':ℤ:= P.calibration.ℓ
 let f(i:ℕ):=Onyx.riseX (R i) (nodeC (0:Cover)-reel (u i) (nodeC (0:Cover))); have he:Tendsto (fun i=> f i (3:Axis)) atTop (𝓝 t):=by
    rw [show t=(t • YM.basis 3) 3 from (by simp [basis_eq])]
    exact ((EuclideanSpace.proj (𝕜:=ℝ) (3:Axis)).continuous.continuousAt).tendsto.comp X.flow.opposite -- typo rw t all, modifies f
 have hx(i): f i (3:Axis)=(2-2*(u i:ℝ))/R i:=by
    unfold f; change (((nodeC 0 - reel (u i) (nodeC 0)) (3:Axis):ℤ):ℝ)/R i = _ -- specify
    have h: ∀ j x, reel j x = (plane 3 j).motion x:=fun _ _=>rfl
    simp [h,fling_move,nodeC]; ring
 let v(i):= ((12+ 2*m+P.calibration.ℓ:ℕ):ℝ)/(R i); have hz:Tendsto v atTop (𝓝 0):= tendsto_const_nhds.div_atTop X.flow.growing; let sh(i):= ((U i:ℝ)/R i+v i); have hS:Tendsto sh atTop (𝓝 0):=by simpa only [add_zero] using X.flow.bulk.add hz
 have hp:=X.flow.angle; filter_upwards [hS.eventually (gt_mem_nhds (show 0 < t/4 by positivity)), he.eventually (lt_mem_nhds (show t/2<t by linarith)), X.fits] with s' p q u x e
 have hc:= X.flow.pos s'; let b:= (P.run.meter.a s').B; have ht:= awningBound P m s' e; have hh:(b:ℝ) ≤ U s':=by
    apply Nat.cast_le.mpr; have ht:b=Pressure.radiusB (hat P.par.R.L P.par.x s') := (P.run.meter.boot s').2.1; omega
 change t/2 < f s' (3:Axis) at q; rw [hx,lt_div_iff₀ hc] at q; change sh s'< t/4 at p; unfold sh v at p; rw [←add_div,div_lt_iff₀ hc] at p
 -- adjust hp.u shadow
 change _ + (P.calibration.ℓ:ℤ)≤ x 3; apply le_trans ?_ ht; apply Int.cast_le (R:=ℝ)|>.1; push_cast at p ⊢; change (_:ℝ)+_ ≤ 1-((b:ℝ)+12+2*m); linarith only [hh,p,q]
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
