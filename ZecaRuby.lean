import SatinThinBank
import ZecaArch
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4500
set_option maxHeartbeats 500000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry

open TopologicalSpace
namespace Spine
open Lamour.Bridge.Celeste
open Lamour.Bridge.Celeste.Morn
open Py.Rate.LocalLimit.Papal (Weaver household)
open TopologicalSpace Tapestry.Exhibition
variable (P:Spine)(R : P.Register)(j:Axis)
local notation "φ"=> P.groundZero j
local notation "μ"=> P.pillars j
local notation "W"=> P.calibration
local notation "Q"=> P.par.block
local notation "ℓ"=> P.calibration.ℓ
open Papal Regis.Head Gleam
/-! # Price of ensemble-of-trips. Exactly composed on printed test level before estimation. -/
open Clock Clock.Hookah Clock.Hookah.Blaze
open Preparation.Yoke Yoke.Travel Regis.Head.Garland
open QuadClock Again Pressure
variable {s t f r v i k:ℕ}
local notation "Λ"=> P.par
local notation "L"=> P.par.R.L
local notation "H"=>P.large
local notation "N" s:max i:max => Journey.side P.run i s
/-! # Buy height and travel together. Keep both actual calibration and rank resolution schedule. -/
open CF.Pannier.Chancel CF.Py.Rate.LocalLimit.Preparation.Yoke
open Worth Pays CF.BProof
open Real (log)
open Aria Casting MacroGrid
local notation "z'" => witnessZ
open Regis.Head.Etch Push.Local AnalyticBridge.VerifiedReset
local notation "Δ" t:max x:max => P.tariffQ z' t x
variable (x : P.Spectrum0 3)

local notation "ξ"=> P.advocate 3 x j
local notation "EH"=>P.physicalEnergy j ξ
local notation "M"=> P.ColorHil j ξ
local notation "Ω"=> P.colorZero j ξ
local notation "Μ"=> timeMesh P.par


-- infrastructure Prop, accepts reindex. scalar clamp defined whole
local notation "Pair'"=>ℕ × ℕ
def orbitRent(R:ℝ)(P:Spine)(r:ℕ):ℝ:=(|R|+1)*4*zoomC P.par.R.L^r
lemma orbitRent_pos(R:ℝ)(P:Spine)(r:ℕ):0<orbitRent R P r:=by
 have h:0<zoomC P.par.R.L:=zero_lt_one.trans_le (zoomC_p _)
 unfold orbitRent; positivity
structure Engaged (P:Spine)(f k:ℕ)(A C:ℝ)(u:ℕ→ℕ)(y:ℕ→(ℕ × ℕ)→ℝ):Prop where
 early:f<k
 post:StrictMono u
 earn(i:ℕ) : k≤ u i∧ ∃ c w,Workforce A C f (u i) P c (y i) w

def rateQR (f k:ℕ)(c:ℝ)(t:ℕ)(a:Pair'→ℝ)(q:Pair'):ℝ:=
 if k ≤ q.1 ∧ q.1 < q.2 ∧ q.2 ≤ t then
   c * a (f,k) / a q else 0
variable {u:ℕ→ℕ}{y:ℕ→Pair'→ℝ}{A C c:ℝ}
local notation "q'" r:max=>orbitRent c P r
local notation "e" i:max=>c*(y i (f,k))
local notation "ζ" n:max p:max=>rateQR f k c (u n) (y n) p

namespace Engaged
variable {P}(g:Engaged P f k A C u y)
include g
lemma wages (p:k≤ s)(h:s<r)(q:r ≤ u i):
 e i = ζ i (s,r) * y i (s,r) ∧
 |ζ i (s,r)| ≤ q' r ∧
 ∃ δ z, lender A C s r (u i) δ (y i (s,r)) z P :=by
 have hp:chargeSpan f (u i) (f,k):=⟨le_rfl,g.early,(g.earn i).1⟩
 have ht:chargeSpan f (u i) (s,r):=⟨g.early.le.trans p,h,q⟩
 obtain ⟨_,o,t,d⟩:=g.earn i
 have lt:= d.career (f,k) (s,r) hp ht (p.trans h.le)
 unfold rateQR
 rw [if_pos (show k ≤ (s,r).1 ∧ (s,r).1<(s,r).2 ∧ (s,r).2≤ u i from ⟨p,h,q⟩)]
 refine ⟨?_,?_, ⟨_,_,d.plans _ ht⟩⟩
 · by_cases ho:y i (s,r)=0
   · rw [ho,abs_zero,mul_zero] at lt
     rw [abs_nonpos_iff.mp lt,ho,mul_zero,mul_zero]
   exact (div_mul_cancel₀ _ ho).symm
 by_cases ho:y i (s,r)=0
 · rw [ho,div_zero,abs_zero]; exact (orbitRent_pos ..).le
 rw [abs_div,abs_mul,div_le_iff₀ (abs_pos.mpr ho)]
 apply (mul_le_mul_of_nonneg_left lt (abs_nonneg c)).trans
 unfold orbitRent

 simp only [← mul_assoc]
 have l:0<zoomC P.par.R.L:=zero_lt_one.trans_le (zoomC_p _)
 gcongr <;> first | exact zoomC_p _ | positivity | omega | linarith
lemma wages_cap {p:Pair'} :
 |ζ i p| ≤ q' (p.2):=by
 cases p with
 | mk a r=>
    by_cases h:k ≤ a ∧ a<r ∧ r≤ u i
    · exact (g.wages h.1 h.2.1 h.2.2).2.1
    unfold rateQR
    rw [if_neg h,abs_zero]
    exact (orbitRent_pos ..).le
lemma step {el:ℕ→ℕ}(h:StrictMono el):Engaged P f k A C (u ∘ el) (y ∘ el):=
 ⟨g.early,g.post.comp h,fun i=>g.earn (el i)⟩
end Engaged
structure Skyways (P:Spine)(f k:ℕ)(A C c:ℝ)(u:ℕ→ℕ)(y:ℕ→(ℕ × ℕ)→ℝ):Prop extends Engaged P f k A C u y where
 sold(q:ℕ × ℕ):∃ d:ℝ,Tendsto (fun i:ℕ=> rateQR f k c (u i) (y i) q) atTop (𝓝 d)

lemma raise_skyways (g:Engaged P f k A C u y) (c:ℝ):
 ∃ el:ℕ→ℕ,StrictMono el ∧ Skyways P f k A C c (u ∘ el) (y ∘ el):=by
 let cost:=fun p:Pair'=>orbitRent c P p.2
 have hv:= isCompact_pi_infinite
     (fun i:Pair'=>isCompact_Icc (a:=-cost i) (b:=cost i))
 let v':= fun i (p:Pair')=> rateQR f k c (u i) (y i) p
 have hn:∃ᶠ i:ℕ in atTop,∀ p:Pair',v' i p∈ Set.Icc (-cost p) (cost p):=
    (Eventually.of_forall (fun i p=> abs_le.mp g.wages_cap)).frequently
 obtain ⟨z,t,el,h,d⟩:=hv.isSeqCompact.subseq_of_frequently_in hn
 exact ⟨el,h,g.step h,fun p=>⟨z p,tendsto_pi_nhds.mp d p⟩⟩
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
