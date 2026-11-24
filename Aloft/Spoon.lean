import Aloft.Frugal
import Aloft.ZL
import Aloft.Canon
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
open Py.Dyad Keeping Py.Rate.Pitching.Focus
open _root_.YM.Preen
local notation "j0"=> (3:Axis)
variable (M:Morn P.par.K)(α:ℝ)(F:ℕ)(C D:ℕ→ℕ→ℝ)(x:P.Spectrum0 3)(p:∀ s,F ≤ s→ Accordance P M F s (C s) (D s))(u:RobeRoad P F C D x)(v:Jones P M α F C D x)
local notation "ξ"=>P.otherSpectrum 3 3 x
local notation "Ω"=>P.heaven 3 ξ
local notation "Ψ"=> P.seasons 3 ξ
local notation "H"=>P.ManyF 3 ξ
local notation "ζ"=>P.wealth 3 ξ
local notation "A₀"=>paster (Ω)
local notation "U"=>P.cartage 3 ξ
local notation "Lq" z:max=> asset P x (A₀ z)
#check amber
set_option synthInstance.maxHeartbeats 350000 in
private lemma crown_ag(j:ℕ)(y:H)(z:(P.ColorHil 3 ξ).space) : crownL P x j y z=adsorption (G:=H) (Lq y) (A₀ (ζ z)):=rfl
private lemma sailto {i a:ℕ}(t:(P.calibration.ℓ:ℤ)+22 ≤ nodeC (orbitB P.par.R.L (cellar P F a) (i-a)) 3) : A₀ (ζ (sparrow P F ξ i a))=amber P x 0 i (orbitB P.par.R.L (cellar P F a) (i-a)) t:=rfl
-- ask for pure price lens on all z. bind.
private lemma sparrow_cost (j:ℕ)(y:H){d k:ℕ}{a:ℝ}(t:(P.calibration.ℓ:ℤ)+22 ≤ nodeC (orbitB P.par.R.L (cellar P F (hikeV d)) (hikeV d+k-hikeV d)) 3)(hp:‖crownL P x j y (sparrow P F ξ (hikeV d+k) (hikeV d))‖≤a): ‖adsorption (G:=H) (Lq y) (amber P x 0 (hikeV d+k) (orbitB P.par.R.L (cellar P F (hikeV d)) (hikeV d+k-hikeV d)) t)‖≤a:=by
 let ht:= Eq.trans (crown_ag P x j y (sparrow P F ξ (hikeV d+k) (hikeV d))) (congrArg (fun k:(H)=>adsorption (G:=(H)) (Lq y) k) (sailto P F x t))
 exact (le_of_eq (congrArg (fun k:(H)=>‖k‖) ht.symm)).trans hp
-- choose coords first, spontaneous raw norm, general measure lemma.
private def finask(d k:ℕ){Lμ:ℕ→(H).space→ℝ}(a:ℝ):Prop:= ∃ w:Cover, ∃ e:Enrolled P d k w, ∃ z:(H).space, (∃ g:Vantage, U g z=amber P x 0 (hikeV d+k) w e.clock.1)∧ (Lμ (hikeV d+k) z ≤ a)
set_option maxHeartbeats 650000 in
private lemma juice(d k:ℕ)(o:Cover){f:ℕ→(H).space→ℝ}{a:ℝ}(hp:(P.calibration.ℓ:ℤ)+22 ≤ nodeC o 3 ∧ nodeC o 3 ≤ (P.par.R.L.val:ℤ)^k*reachQ P (hikeV d))(q:f (hikeV d+k) (amber P x 0 (hikeV d+k) o hp.1) ≤ a): finask P x d k (Lμ:=f) a:= enroll (shifted P (hikeV d+k) x o hp.1) q
where enroll (θ: ∃ y:Cover, ∃ h:nodeC y 3=nodeC o 3, (∀i:Axis,i≠3→0 ≤nodeC y i ∧ nodeC y i ≤ (ruler P.par.block)) ∧ ∃ g:Vantage,amber P x 0 (hikeV d+k) y (hp.1.trans_eq h.symm)=U g (amber P x 0 (hikeV d+k) o hp.1))(q:f (hikeV d+k) (amber P x 0 (hikeV d+k) o hp.1) ≤ a):finask P x d k (Lμ:=f) a:=by
        obtain ⟨y,e,g,z,r⟩:=θ
        have hE:Enrolled P d k y:= ⟨g,e.symm ▸ hp⟩
        exact ⟨y,hE,amber P x 0 (hikeV d+k) o hp.1,⟨z,r.symm⟩,q⟩
abbrev fell(d k:ℕ):Cover:=orbitB P.par.R.L (cellar P F (hikeV d)) (hikeV d+k-hikeV d)
lemma toad(d k:ℕ): let w:=fell P F d k; (P.calibration.ℓ:ℤ)+22≤ nodeC w 3 ∧ nodeC w 3 ≤ (P.par.R.L.val:ℤ)^k*reachQ P (hikeV d):=by
 intro w; let jw:=hikeV d; let o:=cellar P F jw; have hx:= dutyT o P.par.R.L P.par.R.odd_side (hikeV d+k-hikeV d)
 have hc: nodeC w 3=(P.par.R.L.val:ℤ)^k*nodeC o (3:Axis):=by unfold w fell; rw [hx]; rw [Nat.add_sub_cancel_left]; simp
 have ht:1 ≤(P.par.R.L.val:ℤ)^k:=by exact_mod_cast (show 1 ≤ P.par.R.L.val^k from Nat.one_le_of_lt (pow_pos P.par.R.L.property _))
 exact ⟨(by rw [hc]; have he:=fresh P F jw; change _ ≤ nodeC o 3 at he; nlinarith only [he,ht,Int.natCast_nonneg P.calibration.ℓ]),by rw [hc]; exact mul_le_mul_of_nonneg_left (recess P F jw|>.2) (zero_le_one.trans ht)⟩
set_option maxHeartbeats 440000 in
lemma spoonLX(j:ℕ)(y:H)(h:PeriodS P F C D x j y)(q:FiniteDimensional ℂ (Lq y))(p:∀ s,F ≤ s→ Accordance P M F s (C s) (D s))(u:RobeRoad P F C D x)(v:Jones P M α F C D x):∀ᶠ d in atTop,∀ k:ℕ, ∃ w:Cover, ∃ e:Enrolled P d k w, ∃ z:H,
  (∃ g:Vantage, U g z=amber P x 0 (hikeV d+k) w (show (P.calibration.ℓ:ℤ)+22 ≤ _ from e.clock.1)) ∧ ‖adsorption (G:=H) (Lq y) z‖ ≤ thresholdU P M α d k:=by
 filter_upwards [post P M α F C D x p u v j y h q] with d hd k
 exact juice P x d k _ (f:=fun _ z=>‖adsorption (G:=H) (Lq y) z‖) (toad P F d k) (sparrow_cost P F x j y (toad ..|>.1) (hd k))
#print axioms spoonLX
end Aloft
end MiterT
end PledgeT
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
