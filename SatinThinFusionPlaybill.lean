import SatinFixedContrastNovember4
import SatinThinFusionTrumpets
/-! # Earn pointwise convergence of every jet prescription (strict positive heat) with bona fide marked families in the same resolution scaling, simultaneously use front stamps of any of the six species. Test against ground and against zero-energy spectral projection, BOTH in unprojected and projected Hilbert with their given heat systems. -/
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 3000
set_option maxHeartbeats 400000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance Lamour.Bridge.Celeste Designs Twah Prototype
open Lamour.Bridge.Celeste.Morn
namespace Spine
open Aria Casting Six OS.Semigroup OS.Semigroup.Balloon
open MacroGrid SatinNucleus SatinJets
variable (P:Spine)(x:P.Spectrum0 3)
local notation "ξ"=> P.advocate 3 x 3
local notation "H"=> P.ColorHil 3 ξ
local notation "G"=> P.ManyF 3 ξ
local notation "S"=> P.physicalEnergy 3 ξ
local notation "Ε"=> P.seasons 3 ξ
local notation "V"=> P.wealth 3 ξ
variable (A:P.Apron)(w:Prism)
local notation "Λ"=> P.aTuba w A
abbrev burst (P:Spine)(s:ℕ):ℝ≥0:= whenly (timeMesh P.par) s 1
lemma burst_p (s:ℕ): 0<P.burst s:= when_pos _ _ 1 (by decide)
lemma burst_zero : Tendsto P.burst atTop (𝓝 0):=NNReal.tendsto_coe.mp (P.macroStep_zero.congr fun i=>by
 change P.macroStep i= ↑(whenly _ i 1); unfold macroStep; simp only [whenly]; simp) -- may need nested Ico; proof tuning
local notation "d"=> P.burst A.s
section tools
private lemma heat_flip_price {X:Hilbert}(E: OS.Semigroup X 3)(s t:ℝ≥0)(x:X) : E.E t (E.E s x)= E.E s (E.E t x):= by rw [←ContinuousLinearMap.comp_apply (E.E t), ←ContinuousLinearMap.comp_apply (E.E s),←E.time,←E.time,add_comm]
private lemma heat_mask_price {X:Hilbert}(E:OS.Semigroup X 3)(s t:ℝ≥0)(x:X): E.E t (prism_on E w s x)=prism_on E w s (E.E t x):= by
 have he: Commute (E.E t) (mesh_diff E s) := (show Commute (E.E t) (E.E s) from (show E.E t*E.E s=E.E s*E.E t from (E.time t s).symm.trans ((add_comm t s) ▸ E.time s t))).sub_right (Commute.one_right _) |>.smul_right _
 exact DFunLike.congr_fun (Commute.sum_right w.support (fun i=> w i • (mesh_diff E s)^(i+1)) _ (fun i _=> (he.pow_right (i+1)).smul_right _)|>.eq) x
private lemma ghostMask {H₁ G₁:Hilbert} (S₁:OS.Semigroup H₁ 3)(S₂:OS.Semigroup G₁ 3)(φ:H₁.space →L[ℂ] G₁.space)(s:ℝ≥0)(p:H₁)(hx:∀ q,φ (S₁.E s q)=S₂.E s (φ q)): φ (prism_on S₁ w s p)=prism_on S₂ w s (φ p):= by
 have he (i:ℕ): φ ((mesh_diff S₁ s^i) p)=(mesh_diff S₂ s^i) (φ p):=by
    induction i with
    | zero=>rw [pow_zero,pow_zero]; rfl
    | succ i h=> rw [pow_succ',pow_succ']; change φ (mesh_diff S₁ s _) = mesh_diff S₂ s _; rw [mesh_step,mesh_step,map_smul,map_sub,hx]; change _⁻¹ • (S₂.E s (φ ((mesh_diff S₁ s^i) p)) - φ ((mesh_diff S₁ s^i) p))=_; rw [h]; rfl
 unfold prism_on; rw [_root_.sum_apply,_root_.sum_apply,map_sum]; exact sum_congr rfl fun i _=> (map_smul (φ) (w i) _).trans (congrArg (w i • ·) (he _))
end tools
variable (a:P.birthF 3 A.s A.F)
local notation "B"=> P.thinOrigin x A a
local notation "f"=> P.plays_birth w A a
local notation "Y"=> P.thinOrigin x (Λ) (f)
local notation "F"=> prism_on (S) w d
local notation "R"=> prism_on (Ε) w d
lemma tuba_quenches (s:ℝ) : P.cradleH x (Λ) (f) s=(S).E d (prism_on (S) w d (P.cradleH x A a s)):= by
 exact ((congrArg ((S).E _) (P.trumpet_cost w A ξ a)).trans (heat_flip_price _ _ s.toNNReal _)).trans (congrArg ((S).E _) (heat_mask_price w _ _ _ _))
lemma tuba_cont_price : V (Y)=(Ε).E d (R (V B)):= ((congrArg (V) (P.trumpet_cost w A ξ a)).trans (P.bankHeat ..)).trans (congrArg ((Ε).E _) (ghostMask w (S) (Ε) (V) d B (P.bankHeat 3 ξ d)))
lemma tuba_quenchesG (s:ℝ) : P.cradleG x (Λ) (f) s=(Ε).E d (prism_on (Ε) w d (P.cradleG x A a s)):= by
 exact ((congrArg ((Ε).E _) (P.tuba_cont_price x A w a)).trans (heat_flip_price _ _ s.toNNReal _)).trans (congrArg ((Ε).E _) (heat_mask_price w _ _ _ _))
abbrev projectionDark (X:Hilbert)(S':OS.Semigroup X 3)(x:X):Prop:= S'.orth x=0 ∧ S'.ℚmeasure.region YM.Six.night x=0
lemma tuba_prep_dark : projectionDark H (S) Y ∧ projectionDark G (Ε) (V Y) := by
 have he(u:Hilbert)(S':OS.Semigroup u 3)(y:u):projectionDark u S' (S'.E d (prism_on S' w d y)):=by
    rw [heat_mask_price]; exact ⟨prism_on_dark ..,prism_on_night ..⟩ -- order maybe scope
 rw [P.tuba_cont_price x A w a]; constructor
 · change projectionDark _ (S) (P.viewF 3 ξ A.s _); rw [P.trumpet_cost w A ξ a]; exact he H (S) _
 exact he G (Ε) _
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.tuba_prep_dark
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.tuba_quenches
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.tuba_quenchesG
