import YM.SU5.Registration.Ink.Potential
import YM.SU5.Registration.Rasp.UncutStunt
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 3000
set_option maxHeartbeats 700000
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
open Spine
open CF.Velvet CF.Pannier.Chancel
open QuadClock
open Aria Casting MacroGrid Preparation.Yoke Yoke.Travel
open SatinNucleus Six DoseTravel Set

namespace Spine
open _root_.YM.CF.Buffered.Afterglow.Hierarchy
open _root_.YM.CF.Buffered.Afterglow.Hierarchy.LyraBill.Chiffon.Sesame.FlakeNight
open FirstWindows FirstWindows.Chambers FirstWindows.LightBudget

open Aria Casting Six OS.Semigroup OS.Semigroup.Balloon
open MacroGrid SatinNucleus SatinJets DoseTravel Set

open _root_.YM.SatinEdge.RealSheet Boundary Probe
open SatinRegistration
-- Seld valise etc.
open scoped CF.Buffered.Afterglow.Hierarchy.Seld
variable (P : Spine) (x : P.Spectrum0 3)
local notation "ξ" => P.advocate 3 x 3
local notation "H" => P.ManyF 3 ξ
local notation "S" => P.seasons 3 ξ
local notation "D" => radial (P.seasons 3 ξ)
local notation "G" => bands (P.seasons 3 ξ)
local notation "Ω" => P.vacuumEntry x
local notation "ζ" => P.heaven 3 ξ
local notation "κ" => Lead.Clan
open Swatch SatinWFixed
open _root_.YM.Boundary.Probe
open Finsupp
section free
variable {J:Type*}(Q:J→P.Swatch)
 -- use Bool pair: avoids global WPermit for allowed partners separately
abbrev epaulets (J:Type*):= (J × Bool) →₀ ℂ
abbrev school (t : J × Bool) : P.Swatch := if t.2 then Q t.1 else (Q t.1).turn 3
noncomputable abbrev pupil {J:Type*}(j : J × Bool): epaulets J:= Finsupp.single j 1
lemma praise (t:J×Bool)(u:∀ i,(Q i).WPermit x 3) : (P.school Q t).WPermit x 3:=by unfold school; split; exact u _; exact (u t.1).reflector ..
-- powers and cost on linear module
variable (u:∀ i,(Q i).WPermit x 3)
noncomputable def fiscal (s:ℝ≥0): epaulets J →ₗ[ℂ] (H).Op:= Finsupp.linearCombination ℂ (fun t=> (P.praise x Q t u).atHeat s)
local notation "U" j:max=> P.praise x Q j u
lemma axial_fiscal (j:J×Bool)(s:ℝ≥0) : P.fiscal x Q u s (pupil j)= (U j).atHeat s:=by rw [pupil, fiscal,Finsupp.linearCombination_single,one_smul]
private lemma pad_income {H':Hilbert}{B:ℝ≥0→ H'.Op} {m n:ℕ}{c:ℝ}(u:m≤n)(t:PadBound B m c) : PadBound B n c:=fun p q h=>(mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one (show (0:ℝ)≤(p:ℝ) from q.le) (show (p:ℝ)≤(1:ℝ) from h) u) (norm_nonneg _)).trans (t p q h)
private lemma counted {H':Hilbert}{F K:ℝ≥0→ H'.Op}(t:PadPaid F)(p:PadPaid K): PadPaid (fun s=> F s+ K s):=by
 obtain ⟨m,c,s,u⟩:=t; obtain ⟨n,d,r,t⟩:=p; refine ⟨max m n,c+d,add_nonneg s r,fun i p e=>?_⟩; refine (mul_le_mul_of_nonneg_left (norm_add_le ..) (by positivity)).trans (?_); rw [mul_add]; exact add_le_add (pad_income (le_max_left ..) u _ p e) (pad_income (le_max_right ..) t _ p e)
private lemma shaded_bill {H':Hilbert}{A:ℝ≥0→ H'.Op}(p:PadPaid A)(c:ℂ): PadPaid (fun t=> c • A t):=by
 obtain ⟨k,Qf,v,t⟩:=p; refine ⟨k,‖c‖*Qf,mul_nonneg (norm_nonneg _) v,fun i u e=>?_⟩; rw [norm_smul,mul_left_comm]; exact mul_le_mul_of_nonneg_left (t i u e) (norm_nonneg _)
lemma fiscal_coherent (v:epaulets J) : SatinRegistration.Sound (S) (fun s=> P.fiscal x Q u s v):=by
 induction v using Finsupp.induction_linear with
 | zero=> intro s t r; simp
 | add i k h t=>
    simp_rw [map_add]; intro s p r; rw [mul_add,add_mul]; exact congrArg₂ (· + ·) (h _ p r) (t _ p r)
 | single j m=>
    intro s p r; simp_rw [fiscal,Finsupp.linearCombination_single]; rw [Algebra.mul_smul_comm,Algebra.smul_mul_assoc]; exact congrArg (m • ·) ((U j).delivery.isSound _ p r)
lemma fiscal_paid (v:epaulets J): PadPaid (fun t=> P.fiscal x Q u t v):=by
 induction v using Finsupp.induction_linear with
 | zero=> refine ⟨0,0,le_rfl,fun i u p=> ?_⟩; simp only [map_zero,norm_zero,mul_zero,le_refl]
 | add i k h t=> simp_rw [map_add]; exact counted h t
 | single i c=> simp_rw [fiscal,Finsupp.linearCombination_single]; exact shaded_bill ( (U i).delivery.paid) c
noncomputable def store : Carton (P.seasons 3 (P.advocate 3 x 3)) (epaulets J):=
 { bar s:= P.fiscal x Q u s
   coherent := P.fiscal_coherent x Q u
   price := P.fiscal_paid x Q u
   omega := ζ
   size := P.stone_norm ..
   hot := fun _=> P.heaven_hot ..
   stay := fun _=> P.roll_static .. }
local notation "S'"=> P.store x Q u
lemma scroll_pupil (t:J×Bool) (s:ℝ≥0) : (S').bar s (pupil t)= (U t).atHeat s:= P.axial_fiscal x Q u t s
lemma pupil_field (i:J×Bool) : (S').operator (pupil i)= P.temporalField x 3 _ (U i):=by
 let h:(fun s=>(S').bar s (pupil i))=(U i).atHeat:= funext (fun s=> P.scroll_pupil x Q u i s)
 change SatinRegistration.field _ (fun _=> _) ((S').coherent (pupil i)) ((S').price (pupil i))=SatinRegistration.field _ (U i).atHeat (U i).delivery.isSound (U i).delivery.paid; congr
abbrev turned (J:Type*) : Equiv.Perm (J×Bool):= Equiv.prodCongr (Equiv.refl J) Equiv.boolNot -- check mathlib
noncomputable def r_star (J:Type*) : SatinWFixed.JMap (epaulets J):= {
 toFun v:= equivMapDomain (turned J) (Finsupp.mapRange star (star_zero ℂ) v)
 map_add' v w:=by ext k; simp [equivMapDomain_apply,Finsupp.mapRange_apply]
 map_smul' c v:=by ext k; simp [equivMapDomain_apply,Finsupp.mapRange_apply]
}
lemma r_rate (j:J×Bool) (v:ℂ) : r_star J (Finsupp.single j v)= Finsupp.single (turned J j) (star v):=by
 unfold r_star; change Finsupp.equivMapDomain _ _ = _; rw [mapRange_single,equivMapDomain_single]
lemma flips_twice (J:Type*) (x:J×Bool): turned J (turned J x)=x:= by rcases x with ⟨x,i⟩; cases i <;> rfl
lemma pupil_companion (i:J×Bool) : r_star J (pupil i)= pupil (turned J i):=by rw [pupil,r_rate,star_one]
lemma retains (j:J×Bool)(s:ℝ≥0) : ((S').bar s (pupil j)).adjoint=(S').bar s (pupil (turned J j)):=by
 rw [P.scroll_pupil x Q u j s, P.scroll_pupil]; rcases j with ⟨j,i⟩; cases i
 · have t:=P.turn_ticket x 3 (Q j) (u j) ((u j).reflector ..); change (((u j).reflector ..).atHeat s).adjoint=(u j).atHeat s; simp only [t,ContinuousLinearMap.adjoint_adjoint]
 exact ((congrFun (P.turn_ticket x 3 (Q j) (u j) ((u j).reflector ..)) s)).symm
lemma preserves_income : Remembers (S') (r_star J):=by
 refine ⟨fun v=>?_,fun s v=>?_⟩
 · induction v using Finsupp.induction_linear with
   | zero=> simp
   | add f g hf hg=> simp only [map_add,hf,hg]
   | single i c=> rw [r_rate,r_rate,star_star,flips_twice]
 induction v using Finsupp.induction_linear with
 | zero=> simp
 | add f g h t=> simp only [map_add,h,t]
 | single i c=>
    have hv(j:J × Bool)(c:ℂ): Finsupp.single j c=c • pupil j:=by simp [pupil]; -- tune
    rw [r_rate,hv,hv,map_smul,map_smul,ContinuousLinearMap.adjoint.map_smulₛₗ,P.retains x Q u i]; try rfl
end free
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open YM.CF.Buffered.Afterglow.Tower.VacuumSelection
#print axioms Spine.preserves_income
#print axioms Spine.pupil_field
