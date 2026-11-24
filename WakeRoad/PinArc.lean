import WakeRoad.Rehome
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 3000
set_option maxHeartbeats 200000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical ContDiff
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance Lamour.Bridge.Celeste Designs Twah Prototype
open Lamour.Bridge.Celeste.Morn
open Spine
open CF.Velvet CF.Pannier.Chancel
open QuadClock
open Aria Casting MacroGrid Preparation.Yoke Yoke.Travel
open SatinNucleus Six DoseTravel Set
open OS.Semigroup YM.OS.Semigroup.Gingham
open Boundary Probe
namespace Spine.NativeSeam
open YM.OS YM.OS.Semigroup SatinRegistration YM.Velour YM.SatinMacro
variable (P:Spine)(x:P.Spectrum0 3)
local notation "jₓ"=> (3:Axis)
local notation "ξ"=> P.advocate 3 x jₓ
local notation "G"=> P.ManyF jₓ ξ
local notation "ℰ"=> P.seasons jₓ ξ
local notation "Ω"=> P.heaven jₓ ξ
local notation "W"=>carry P x
local notation "T"=>(ℰ).E
local notation "q*"=> foldSpace
open EmberWind
open Hiro Papal Lamour.Bridge.Celeste Regis.Head.Brecht
open EmberWind GramSignal
variable (I:ℝ)(i:ℕ)
open Twah (DirSpin)
open SpinReceipt
open Preparation.Yoke Jewel WakeInvestment Dial Pressure
local notation "K"=>P.calibration
local notation "b"=>ruler P.par.block
local notation "Rz"=> zoomR P.par I
abbrev chair (p:0<I)(k:Fin 2):= (GramSignal.Morning.pinM P I p).tests i k
abbrev eye (k:Fin 2):Cover:= if k=0 then (2:ℤ) • P.rosemary (Rz i) else 0
lemma eye_value (p:0<I)(k:Fin 2): b • eye P I i k= (2:ℕ) • chair P I i p k :=by
    fin_cases k
    · change b • ((2:ℤ) • P.rosemary (Rz i))= (2:ℕ) • (b • P.rosemary (Rz i)); rw [ruler_two]; simp
    change b • (0:Cover)= (2:ℕ) • 0; simp
lemma sky_abs(p:Cover):∀ x∈ skyDeck (nodeC p) 12, ∀ k:Axis, |x k-nodeC p k|≤ (12:ℤ):=by
    intro x z k; obtain ⟨a,y⟩:= (pav_v ..).mp z k
    change nodeC p k-(12:ℤ) ≤ x k at a
    change x k≤ nodeC p k+(12:ℤ) at y
    rw [abs_le]; omega
local notation "A" p:max=> GramSignal.Morning.pinM P I p
abbrev tag (p:0<I)(a:Fin 2):= skyDeck (nodeC (chair P I i p a)) (4+8)
variable (p:0<I){β:ℕ→ℝ}
-- legal for even any beta. P. prices from WakeInvest.
lemma readtag{V:GramSignal.Morning P I}(n:ℕ)(k:Fin 2): V.ask β k n∈ enclave P.calibration ∧ V.ask β k n∈ bay P.calibration (skyDeck (nodeC (V.tests n k)) 12) true:=by
    let f:= localStaff (V.tests n k) 0 (V.faces k); have hf:= ready_local (V.tests n k) (0:DirSpin) (V.faces k); let y:=staffWeight (Rz n)
    let g:= choiceWeave P β f 4 n; let h:=f.letterBudget (κFix β n) K (temp (hat P.par.R.L P.par.x n)) hf
    have u:= f.registration (κFix β n) (temp (hat P.par.R.L P.par.x n)) K hf
    refine ⟨(enclave_spec K).mpr (fun j m x=>?_), (Tapestry.locates ..).2 (.smul _ h)⟩
    change y • g _ _= twist _ (y • (g _ _)); rw [twist_scalar, (show g _ _=_ from u j m x)]; rfl
noncomputable def chairCap (β:ℕ→ℝ)(k:Fin 2) :P.Apron:= fitting P i (tag P I i p k) (eye P I i k) (chair P I i p k) ((A p).ask β k i) (readtag P I i k).2 (readtag P I i k).1 (eye_value P I i p k) (sky_abs _)
local notation "N"=> chairCap P I i p β
local notation "v" d:max=>eye P I i d
lemma worn (k:Fin 2): P.issuing i (N k) (v k)= (A p).ask β k i:=wearing P i _ _ _ _ _ _ _ _
local notation "w"=> (reWidth P:ℝ)*P.spotMesh i
lemma width_mass(k:Fin 2)(y:Axis): (N k).realWidth P y=w:=rewidth P i _ _ _ _ _ _ _ _ y
lemma navies (k:Axis): P.gridSpot i (v 1) k + 6 * (w) < P.gridSpot i (v 0) k:=by
    rw [P.gridSpot_mul,P.gridSpot_mul]
    have hp:(v 1)=0:=rfl
    rw [hp,Pi.zero_apply,Int.cast_zero,zero_mul,zero_add]
    apply lt_of_le_of_lt (Eq.le (mul_assoc 6 ..).symm)
      (mul_lt_mul_of_pos_right _ (P.spotMesh_pos ..))
    rw [eye,if_pos rfl,Pi.smul_apply]; change 6*((reWidth P:ℕ):ℝ)<↑((2:ℤ)*(P.rosemary (Rz i) k))
    exact_mod_cast (show (6:ℤ)*reWidth P < _ from (by
      unfold reWidth; push_cast; have h:= P.rosemary_hi (Rz i) k; unfold Spine.platterWidth at h; push_cast at h; omega))
lemma width_pos : 0<(w):=by unfold reWidth; have h:=P.spotMesh_pos i; positivity
private lemma hpass (k:Axis): P.gridSpot i (v 1) k+ 2 * (w)< P.gridSpot i (v 0) k:= by
    linarith only [navies P I i k,width_pos P i]
lemma seam_price (e:(A p).covPct P I β x jₓ i≠0)(J:P.Ellis 3 x):
    P.bodyPair x (N 1) (N 0) (P.gridSpot i (v 1)) (P.gridSpot i (v 0))≠ native P x (N 1)*native P x (N 0):=by
    let V₀:= P.gridSpot i (v 0); let V₁:= P.gridSpot i (v 1)
    let S:=N 0; let D:= N 1; let M:=P.singleState 3 i x
    have h₁(k:Axis): D.realWidth P k=(w):= width_mass P I i p 1 k
    have h₀(k:Axis): S.realWidth P k=(w):= width_mass P I i p 0 k
    have ht(k:Axis): V₁ k+D.realWidth P k<V₀ k-S.realWidth P k:=by rw [h₁,h₀]; unfold V₀ V₁; linarith only [hpass P I i k]
    have hv: V₀-V₁∈ P.forwardPair D S 3:=by change D.realWidth P 3+ _ <V₀ (3:Axis)-V₁ (3:Axis); linarith only [ht jₓ]
    rw [P.bodyPair_fwd x _ _ 3 _ _ J hv, show V₀=P.meshPose i (v 0) from rfl,show V₁=P.meshPose i (v 1) from rfl,← local_pair P x D S J i (v 1) (v 0) (show D.s ≤ i ∧ S.s ≤ i from ⟨le_rfl,le_rfl⟩) ht] -- likely dw mismatch
    have he(k:Fin 2) := native_on P x i _ _ _ ((A p).ask β k i) (readtag P I i k).2 (readtag P I i k).1 (eye_value P I i p k) (sky_abs _) J
    change ∀ k,native P x (N k) = _ at he
    rw [worn,worn,he,he,mul_comm, mul_comm (P.singleState 3 i x ((A p).ask β 1 i))]
    unfold GramSignal.Morning.covPct at e; dsimp only at e; simp_rw [P.single_agrees] at e
    exact sub_ne_zero.mp e
lemma springball (e:(A p).covPct P I β x jₓ i≠0)(J:P.Ellis 3 x): ∃ F V:SampleDose,∃ δ:ℝ,Ballast P x (N 0) (N 1) F V δ:=by
    obtain ⟨p',q',u,h⟩:= skimming P x (N 1) (N 0) (P.gridSpot i (v 1)) (P.gridSpot i (v 0)) (w) J (fun j=>⟨width_mass P I i p 1 j,width_mass P I i p 0 j⟩) (hpass P I i) (navies P I i 0) (seam_price P x I i p e J)
    obtain ⟨x,q⟩:= springtide P x (N 1) (N 0) J u h; obtain ⟨n,δ,g⟩:= q.exists
    exact ⟨_,_,δ,ribbons P _ _ _ _ _ _ J g⟩
#print axioms springball
end Spine.NativeSeam
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
