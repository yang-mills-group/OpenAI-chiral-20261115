import YM.SU5.SatinWard.Resolution.Aviator
import YM.SU5.SatinWard.Resolution.Synod
import Velour.Crepe.Rent
set_option synthInstance.maxSize 28000
set_option maxHeartbeats 700000
set_option maxRecDepth 8000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase
open MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound
open Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker
open scoped ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy
open Tapestry Germ Alliance Lamour.Bridge.Celeste Designs Twah Prototype
open Lamour.Bridge.Celeste.Morn
open CF.Velvet CF.Pannier.Chancel
open Spine Pitching.Focus QuadClock Ione Vow Swell
open _root_.Zephyr.Chern
universe uΩ


open Papal CF.Papyrus.Franc.SatinForce CF.Pannier.Chancel Checkers

open CF.Papyrus.Franc.Loaves
-- CP3 package. PUBLIC, no topology/order changes
open Moon
open Horizons FoliageP BareProgram Moonlit Moonlit.SwitchC
open _root_.YM.Regis.Head.Brecht _root_.YM.Regis.Circuit _root_.YM.Regis.Circuit.SpringDay
open SlabMark VelourBoard Papal.SkyTax Cygnet VelourWiggle
open YM.Stationary (Gaia)
open SwitchC.Garland SwitchC.Garland.Terrace SwitchC.Garland.Terrace.Juniper
open Abacus CheckerFlag SlopeCharge Maxwell
open scoped RealInnerProductSpace ContDiff
namespace Fame
variable {P:Spine}{K:P.Register}{b C:ℝ}{t σ}{W:ℕ→ HorizonLens→ HorizonLens→ℝ}{β:ℕ→ℝ}
variable (T: CouncilGrant P K b C t σ W β)(H:PublicKernel P σ W)(F D: PlaqAxes)
variable {s:ℕ}(a b' c d:ℝ)
open BProof Pressure
namespace Regulator
local notation "Ω" s:max=> hat P.par.R.L P.par.x s
local notation "K'"=> P.calibration
local notation "τ" s:max=> Pressure.temp (hat P.par.R.L P.par.x s)
open _root_.YM.Gleam.Luster.Almanac Grade
open Papal.SkyTax
open _root_.YM.Regis.Head
open _root_.YM.Gleam.Luster.Almanac Grade
open _root_.YM.CF.Py.Rate.LocalLimit.Preparation _root_.YM.CF.Py.Rate.LocalLimit.Preparation.Tabletop Shrine Ione.Clock Moto
local notation "Γ"=>P.run
variable (P:Spine)
local notation "W★"=>P.calibration
local notation "Ω★"=>P.run.meter
variable (s:ℕ) {g:ℕ} (i:Cover) (X:Moto.Skate) (q:payable P s 2)
def bumper (P:Spine)(s:ℕ)(I:Cover): Moto.Skate→ₗ[ℝ] Buffered.Family P.calibration:= (lapQ P.run s) • LinearMap.pi (fun m:Side=> temple (P.run.meter.a s) (wrap (More (P.calibration.c m)) I))
lemma bumpC (n:Side): bumper P s i X n=temple ((Ω★).a s) (wrap _ i) (lapQ P.run s • X):=by rw [map_smul]; rfl
lemma bumpRoot (j:ℕ) (x:Site (side P.run j s))(h: node x=wrap _ i): exhibit P.run P.large s j (bumper P s i X)= glowMark P.run j s X x:=by
 unfold glowMark; rw [h]; change arrange _ _ _ (bumper P s i X (momentm P.run j s))= _; rw [bumpC]; apply across
where across (u v:Side)(p:u=v): arrange _ _ p ((temple (P.run.meter.a s) (wrap (More u) i)) (lapQ P.run s • X))=temple (P.run.meter.a s) (wrap (More v) i) (lapQ P.run s • X):=by subst v; rfl -- p budget `_`
noncomputable abbrev tollηw (P:Spine)(φ:ℕ→ℝ)(s:ℕ):ℝ:= (lapQ P.run s)*((Pressure.temp (hat P.par.R.L P.par.x s))^2*φ s)⁻¹
lemma bump_scaled (φ:ℕ→ℝ)(b:0< φ s) : bumper P s i (cloverKey a b')= (↑(tollηw P φ s):ℂ) • (aptLabel P φ a b' s i q).val:=by
 let y:=φ s; let t:=Pressure.temp (hat P.par.R.L P.par.x s); let V:= Fintype.card Axis;
 funext m; rw [bumpC,Pi.smul_apply]; let E:= wrap (More ((W★).c m)) i
 -- `summer_green` at (κ.c m=mid?): c fits? requires shape mid n B.Journey.c. look. use cashK not pointK.
 change _=(↑(tollηw P φ s):ℂ) • summer a b' (Real.sqrt y) t i (W★) m
 rw [coPay]; funext U
 let Γ':=(Ω★).a s; let θ:=lapQ P.run s; let ht: Γ'.threshold=t:=(P.run.meter.boot s).1; have hz:0< Γ'.threshold:=Γ'.threshold_pos
 change Shrine.bookValue Γ' (θ • cloverKey a b') E U.1 • (1:Fock.FC _)= _
 unfold Shrine.bookValue; change Set.indicator _ (kerP E Γ' _) U.1 • _= (↑(θ* (t^2*y)⁻¹):ℂ) • ((if pingS t (halo 10 {E}) U.1 then (Real.sqrt y)^2 • arm a b' E U.1 else 0) • (1:Fock.FC _)); unfold Set.indicator; by_cases w:pingS Γ'.threshold (halo 10 {E}) U.1
 · rw [if_pos (show _∈_ from w), if_pos (ht ▸ w),point_scale, cashK,Real.sq_sqrt (show 0≤y from b.le), Complex.coe_smul, ←smul_assoc (θ*_), smul_smul,smul_smul,ht]
   have hy:0<y:=b; have h:0<t:=hz.trans_eq ht; rw [show θ*(t^2)⁻¹=(θ*(t^2*y)⁻¹)*y from by field_simp]

 rw [if_neg (show _∉_ from w),if_neg (ht ▸ w),zero_smul,smul_zero]
lemma bump_mirror (j:Axis)(z:ℤ) : mirror P.calibration j z (bumper P s i X)=bumper P s ((plane j z).motion i) (localFace (Signed.mirror j) X):=by funext k; unfold mirror; simp only [bumpC]; rw [temple_mirror,Shape.anno,locale_smul]
lemma bump_tilt (D:Tilted.Ramp): D.cuspF P.calibration (bumper P s i X)= bumper P s (D.plan.motion i) (localFace D.s X):=by funext k; unfold Tilted.Ramp.cuspF; simp only [bumpC]; rw [temple_tilt,Shape.anno, locale_smul]
-- pay support rotation at output. any notch 
lemma bump_inv (p:Tilted.Ramp): bumper P s i (localFace p.s X)= p.cuspF P.calibration (bumper P s (p.plan.motion i) X):=by rw [bump_tilt, p.modes_m]
lemma local_pav (p:Tilted.Ramp)(D:ℕ): p.survey (pavilion (p.plan.motion i) D) ⊆ pavilion i D:=by
 let s:= p.s; intro z h; unfold Tilted.Ramp.survey at h; obtain ⟨v,w,rfl⟩:= mem_image.mp h; rw [pav_v (p.plan.motion i) _ D] at w; rw [pav_v i _ D]
 intro j; obtain ⟨j,rfl⟩:= p.s.perm.surjective j; specialize w j; let t':= p.modes_m i; rw [p.mode_motion, Signed.act_at]; have ht:=congrFun t' (p.s.perm j); rw [p.mode_motion, Signed.act_at] at ht; by_cases hf:p.s.flip j=true; · rw [if_pos hf] at ht ⊢; rw [←ht]; omega
 rw [if_neg hf] at ht ⊢; rw [←ht]; exact w
include q
lemma bump_owns (D:Option Tilted.Ramp) (X₁:Moto.Skate) (u:X₁=(D.elim (cloverKey a b') (fun p=>localFace p.s (cloverKey a b')))):
 InTest P.calibration true (pavilion i petalD) false (bumper P s i X₁)∧ (∀ m, covariant ((bumper P s i X₁) m)):=by
 let E:= (cloverKey a b'); let G:= bumper P s; let φ:= (1:ℕ→ℝ); let Z:=(↑(tollηw P φ s):ℂ)
 have hh(i:Cover): InTest P.calibration true (pavilion i petalD) false (bumper P s i E)∧ (∀ m,covariant ((bumper P s i E) m)):=by
    unfold E; rw [bump_scaled a b' P s i q φ zero_lt_one]; let A:=aptSingularity (P:=P) a b' q i φ; exact ⟨A.1.smul _, fun m=> (enclave_spec P.calibration).1 ((enclave P.calibration).smul_mem A.2.1 Z) m⟩
 subst X₁; cases D; exact hh i
 next p=>
    change InTest _ _ _ _ (bumper P s i (localFace p.s E)) ∧_ ; change _∧ ∀ m,covariant ((bumper P s i (localFace p.s E)) m); rw [bump_inv]; let h:= hh (p.plan.motion i); exact ⟨(p.faces _ h.1).mono (local_pav i p _),p.keeps_color _ (aux_test h.1) h.2⟩
#print axioms bump_owns
end Regulator
end Fame
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
