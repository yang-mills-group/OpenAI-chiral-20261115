import Verts.DotFeed
import AuroraB.Clot
import Minnow.Younger
import Acacia.Loom
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4500
set_option maxHeartbeats 650000
set_option quotPrecheck false
noncomputable section

open Filter Function Set Metric MeasureTheory
open scoped Topology InnerProductSpace NNReal ComplexOrder BigOperators
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance
open Lamour.Bridge.Celeste
open Designs Twah Prototype
open YM.Stationary (Gaia)
open CF.Onyx (riseX moor)
open Lamour.Bridge.Celeste.Morn
namespace Spine
open Aria Casting Six
namespace Habitat
variable {P:Spine} {x:P.Spectrum0 3} {c r:ℕ→ℕ} {K:P.Register} {J:P.Ellis 3 x}
variable (B:P.Experiment K c r x J)(Z:Lead.Clan)
local notation "ξ"=> P.otherSpectrum 3 3 x
local notation "ω"=> P.colorZero 3 (P.otherSpectrum 3 3 x)
local notation "Ω"=> P.heaven 3 ξ
local notation "H"=> P.ManyF 3 ξ
local notation "G"=> P.ColorHil 3 (P.otherSpectrum 3 3 x)
namespace Hemlock
open PledgeT MiterT Broker Aloft
open Py.Rate.Pitching.Focus (Morn)
namespace AuroraB.Verts
open Calico _root_.Yoland
variable (d:ℕ)(C D:ℕ→ℕ→ℝ)
local notation "φ" s:max=> (P.macroStep s:ℂ)
local notation "χ" t:max=>P.singleState 3 t x
local notation "isp" v:max=>aislePt (3:Axis) v
local notation "kd" s:max=> offer_update P d C D s B Z
local notation "Τ" s:max => agent P d C D s B Z
local notation "X" s:max t:max n:max U:max=> schema B Z d C D s t n U
local notation "Ψ"=> P.seasons 3 ξ
local notation "Λ"=> P.wealth 3 ξ
open DoseTravel
-- packaging linearity w arbitrary real sample.Su.S.E.
def combine(U V:SampleDose)(r:ℝ):SampleDose where
 val:=fun i=> r * U.val i+ V.val i
 smooth:=(U.smooth.const_smul r).add V.smooth
 budget:= (U.budget.mul_left (f:=fun _:Vantage=>r)).add V.budget
variable {w:ℝ}(U V: SampleDose)(u:claimV w U)(v:claimV w V)(r:ℝ)
include u v
lemma combine_support : claimV w (combine U V r):=by
 let M: Set Vantage:= tsupport U.val ∪ tsupport V.val
 have h: tsupport (combine U V r).val ⊆ M:=closure_minimal (fun i p=>?_ ) ((isClosed_tsupport _).union (isClosed_tsupport _))
 · intro i hp; obtain h'|h':=h hp; exact u _ h'; exact v _ h'
 by_cases h':U.val i=0
 · right; by_contra hp
   have hv:V.val i=0:=by by_contra ht; exact hp (subset_closure ht)
   exact p (by simp only [combine,h',hv,mul_zero,add_zero])
 left; exact subset_closure h'
variable (x)(m:ℕ)
local notation "J" z:max=> (fieldLimit x d C D m z)
local notation "R" z:max=> (zoomV x d C D m z)
omit u v
lemma combine_eq (h:Integrable fun i:Vantage=> (U.val i:ℂ) • zoomV x d C D m i) (h':Integrable fun i:Vantage=> (V.val i:ℂ) • zoomV x d C D m i): J (combine U V r)= (r:ℂ) • (J U)+J V:=by
 exact qv (Y:= (H)) _ _ _ _ h h'
where qv{Y:Hilbert}(g:Vantage→Y)(a b:SampleDose)(r:ℝ)(u:Integrable (fun i:Vantage=> (a.val i:ℂ) • g i))(v:Integrable (fun i:Vantage=>(b.val i:ℂ) • g i)) : (∫ i:Vantage,((combine a b r).val i:ℂ) • g i)=(r:ℂ) • (∫ i:Vantage,(a.val i:ℂ) • g i)+(∫ i:Vantage,(b.val i:ℂ) • g i):=by
       have he(i:Vantage): ((combine a b r).val i:ℂ) • g i= (r:ℂ) • ((a.val i:ℂ) • g i)+(b.val i:ℂ) • g i:=by simp only [combine,Complex.ofReal_add,Complex.ofReal_mul,add_smul,mul_smul]
       simp_rw [he,Complex.coe_smul r]
       calc
       _ = (∫ i:Vantage,r • (a.val i:ℂ) • g i)+(∫ i:Vantage,(b.val i:ℂ) • g i):= integral_add (u.smul r) v
       _ = _ :=by rw [integral_smul]
def silent:SampleDose:= {val:=fun _=>0,smooth:=contDiff_const,budget:=HasCompactSupport.zero}
lemma zenith0 (x:P.Spectrum0 3)(m:ℕ):fieldLimit x d C D m silent=(0:(P.ManyF 3 (P.otherSpectrum 3 3 x)).space):=by
 let V₀:=zoomV x d C D m
 exact zeroV (R₀:=P.ManyF 3 (P.otherSpectrum 3 3 x)) V₀
where zeroV{R₀:Hilbert}(f:Vantage→R₀):(∫ i:Vantage, (silent.val i:ℂ) • f i)=(0:R₀):=by simp only [silent,Complex.ofReal_zero,zero_smul]; simp
lemma zero_pose(w':ℝ):claimV w' silent:= by intro i h; have e:silent.val=0:=rfl; rw [e] at h; simpa using h
#check HasCompactSupport.smul_left
#check HasCompactSupport.smul_right
#check HasCompactSupport.mul_left
#print axioms combine_support
#print axioms combine_eq
end AuroraB.Verts
end Hemlock
end Habitat
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
