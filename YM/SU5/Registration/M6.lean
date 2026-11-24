import YM.SU5.Registration.Rise.SolarWage
import YM.SU5.Registration.SpinePad
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
open _root_.YM.SatinRegistration
open Regis.Head Regis.Head.Brecht
open Aria Casting MacroGrid Preparation.Yoke Yoke.Travel

/-!
# Existence of M4 gauge estimate and first operator application

Hold THIS `c r n V X w` & clearance F U. The bounds in project/Tower can also
be used for all n-way etc where licensed at their own supports. Here make a
width-point purchase (H gauge prices), qualify M5 on the projected G on these
(gauge) fields; this is a new actual relative operator-norm & strong* convergence
estimate, for the clover stamps with THEIR continuum widths. Does not claim it
for the sewn (i.e. mixed/Satin) stamps in the same ledger: still need to pay moving
Fermi letters at the seam.
-/
variable (P:Spine)(x:P.Spectrum0 3)
variable {A:ℕ→ P.Apron}{n:ℕ→ℕ}
local notation "ξ"=> P.advocate 3 x 3
local notation "Ω"=> P.heaven 3 ξ
local notation "H'"=> P.ManyF 3 ξ
local notation "S"=> P.seasons 3 ξ
local notation "D"=> radial S

lemma honestBridge (A:P.Apron)(s t:ℝ≥0): P.manageBoth x A s t=P.stageG 3 ξ A s t:=by
 unfold manageBoth stageG stageH priceWidth; rw [A.width_real P 3,Real.toNNReal_coe,P.bank_both]; unfold realTable tableau; rw [neg_zero,P.cart_zero]; rfl
lemma has_widths (F:P.Funding x A) :∀ j:Axis,Tendsto (fun i=> (A i).realWidth P j) atTop (𝓝 0) :=by intro j; simp_rw [Apron.width_real]; exact NNReal.tendsto_coe.mpr (F.ft j)
lemma Funding.backed (F:P.Funding x A) : P.CapReady x A:=by
 refine ⟨P.has_widths x F,fun t p=> ?_,?_⟩
 · simp_rw [manage,P.honestBridge]; exact F.travels 3 [] t p
 obtain ⟨k,C,v,u⟩:= F.price 3 []; refine ⟨k,C,v,fun t p q=>?_⟩; simp_rw [manage,P.honestBridge]; exact (u t p q).mono fun i t=> (mul_le_mul_of_nonneg_left (P.toG_cost ..) (by positivity)).trans t
-- gauge price on the same V. include point equality not reading Y.
variable (V:∀ j:Axis, List Axis→ℝ→ P.ColorHil j (P.advocate 3 x j)) (t:Radiates P x A V) (F:P.Funding x A)
lemma beam_cost (D₁:P.Apron)(s:ℝ≥0): P.manage x D₁ s Ω = P.beam 3 x D₁ s :=by
 let w:= P.priceWidth D₁; let τ:= (P.seasons 3 ξ).E (s-w)
 unfold manage manageBoth realTable; change (P.seasons 3 ξ).E _ (P.tableau 3 _ _ _ ((P.seasons 3 ξ).E _ Ω))=_; rw [P.heaven_hot,P.tableMaps,P.cart_zero, ContinuousLinearMap.id_apply]; unfold beam; rw [NNReal.sub_def,P.price_exact]; rfl
include t F in
lemma local_gauge_vac (s:ℝ≥0)(p:0<s): P.managed x A (F.backed P x) s Ω = P.wealth 3 ξ (V 3 [] s):= tendsto_nhds_unique ((P.delivery_cap x A (F.backed P x)).accepted s p Ω) (((t.port 3 [] (show (0:ℝ)<(s:ℝ) from p) tendsto_const_nhds)).congr fun i=> (P.beam_cost x ..).symm)

/-- Select by authority of the earlier M4 stock. NOT universal estimates for
an arbitrary M4 tuple; existential here since we co-purchase on this one. -/
theorem funded_sunlit : ∃ (P : Spine) (K : P.Register) (c r : ℕ→ℕ) (x : P.Spectrum0 3) (R : P.Ellis 3 x)
    (i₀ : ℕ) (F U : SampleDose) (A : ℕ → P.Apron) (n : ℕ→ℕ) (w : Lead.Clan → Prism)
    (V : ∀ j : Axis, List Axis → ℝ → P.ColorHil j (P.advocate 3 x j)) (g h : ℕ)
    (X : P.HandleWith x c r A n)
    (Y : Lead.Clan → Test4 →L[ℂ] P.ManyF 3 (P.advocate 3 x 3)) (Z : Lead.Clan → Lead.Clan → Boundary.Distn E4),
    M4Tuple P K c r x R i₀ F U A n w V g h X Y Z ∧ P.Funding x A := by
 -- Mirror PoweredElection-EdgeLab-Sunlit; pay Tq (from ShelterCost....)
 let Y:Supplier := fun _ _ _ _ _ _ _ _ _ _ _ _ => 0
 obtain ⟨n,P,K,e,π₀,h0,h1,h2,h3,h4,G,C,ec,q,H,A,a,season,c,r,h,b,β,ρ⟩:= powered_century (fun _ _ _ _ _ _=>0) Y 1 1 zero_lt_one 1 zero_lt_one id
 obtain ⟨s,_,t⟩:=ρ.exists
 obtain ⟨x,R,_,p,v,a',q',S'⟩:=t (fun _=>True) (Eventually.of_forall fun _=>True.intro)
 obtain ⟨X,V,qX,pX,hX,B⟩:= P.appointed_camera x K R c r _ _ a' v h0 ⟨P.par.R.L.val/2,by omega⟩ ((P.treasury_plot A C H a).mono fun s p=> p (s+1) (by omega) (s+1) le_rfl) β p q' S'
 obtain ⟨N,f'⟩:= P.panel_sales x c r X p.setup; obtain ⟨i₀,w,F,U,Y,Z,z⟩:= (P.packages_rows x K R c r _ _ e p.setup X V qX pX hX N f').exists
 exact ⟨P,K,c,r,x,R,i₀,F,U,X,N,w,V,P.pointEra s,s,f',Y,Z,z,B⟩
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open YM.CF.Buffered.Afterglow.Tower.VacuumSelection
#check Spine.funded_sunlit
#print axioms Spine.Funding
#print axioms Spine.funded_sunlit
#print axioms Spine.honestBridge
#print axioms Spine.Funding.backed
#print axioms Spine.local_gauge_vac
