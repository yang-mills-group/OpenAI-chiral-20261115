import YM.SU5.Assay.Flock
import YM.SU5.Assay.Die
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4900
set_option maxHeartbeats 420000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance
namespace Spine
open Aria Set OS.Semigroup
variable (P:Spine)(j:Axis)(x:P.Spectrum0 j)
local notation "K"=> P.calibration
local notation "H"=> P.ColorHil j x
local notation "B"=> P.ManyF j x
local notation "X"=> (P.ColorHil j x).Op
local notation "Y"=> (P.ManyF j x).Op
local notation "Lag"=>ℝ→ℝ→(P.ManyF j x).Op
local notation "S"=> P.seasons j x
local notation "U"=> P.physicalEnergy j x
local notation "ω"=> (P.seasons j x).wax
local notation "W"=> P.cartage j x
local notation "θ"=> P.tableau j x
local notation "E"=> P.enter j x
local notation "R"=> P.wealth j x
local notation "Vac"=> P.colorZero j x
local notation "Ω"=> P.heaven j x
local notation "φ"=>P.rawUnit j x
open Ballad Six
local notation "ℭ"=>P.experimentBody
/-! Also stamp and cool the ORIGINAL insertions at every resolution. Mere
 successive native rebilling (same normalized ruler, same n and increment)
 washes them away. -/
variable {P j}{f:P.Test}{y:ℂ}{D:Finset Cover}
lemma Taste.replica {Q:ℕ→P.Apron}(h:P.Fades Q)(e:∀s,(Q s).s=s)(t:∀s,(Q s).F=f)
 (q:f∈bay K D true)(p:P.Taste f D y): P.RawNormal j x Q (fun _=>0) 0 (y•φ):=by
 obtain ⟨w,v,z⟩:=((P.eventually_BFits D).and (eventually_ge_atTop 1)).exists
 let A:P.Glaze:= ⟨w,z,D,f,q,(t 0) ▸ (Q 0).realM,v⟩
 have u:P.RawNormal j x (Glaze.serial (fun _=>A)) (fun _=>0) 0 (y•φ):=
   ⟨A.static.fades,tendsto_const_nhds,fun a p₁ b p₂=>by
      simp only [P.align_zero];exact Taste.fixed x (A:=A) p p₁ p₂⟩
 exact u.changeStamp h e t
lemma Taste.sticker (q:f∈bay K D true)(t:f∈enclave K)(p:P.Taste f D y): Tendsto (fun s=>P.singleState j s x f) atTop (𝓝 y):=by
 rw [Metric.tendsto_nhds]
 intro a h
 exact (Taste.watch q t p j (a/2) (half_pos h)).mono fun s u=>by rw [dist_eq_norm];exact (u x).trans_lt (half_lt_self h)

open Lamour.Bridge.Celeste
-- Support and occurrence of every assignment; coin = front; reverse requires index gap.
variable (P)(Z:Lead.Clan)(n:ℕ)
local notation "b"=>P.sidesPerTick
local notation "Q"=>P.flash n
local notation "Π"=>P.frontMat Z n
lemma front_film (h:P.calibration.ℓ<n)(s:ℕ):Π∈P.Beam s (Q).patio Z.2 ∧ P.Wove (some Z.2) (Q).patio Π (P.stockFolio Q Z):=by
 have hp:=Finset.disjoint_left.mp (P.pin_disjoint _ _ _ (P.pocket_gap 0 n h)) (Finset.mem_singleton_self _)
 refine ⟨Beam.of_sensed ?_,P.stock_prices Q Z (fun t=>hp (Finset.mem_singleton.mpr t))⟩
 exact Submodule.subset_span (show _∈_ from ⟨_,_,(Q).patio,Finset.union_subset
   (Finset.singleton_subset_iff.mpr (porchBorn (P.flash n))) (Finset.singleton_subset_iff.mpr (porchGone _)),fun _ h=>h,
     P.pocket_gap s n h,P.front_charge Z n,P.front_real Z n⟩)
def bookPair :P.Folio:= (P.stockFolio Q Z) ++ (((P.stockFolio Q Z).transcribe (P.shifts 3 (P.laterPulse n))).ink (-1))
lemma experiment_first (s:ℕ)(h:P.calibration.ℓ<n): P.FirstDress (P.experimentBody Z s n) Z.2 (P.bookPair Z n):=by
 obtain ⟨u,w⟩:=P.front_film Z n h s
 constructor
 · change Π-P.shifts 3 (P.laterPulse n) Π ∈ P.Beam s (P.measureStencil n) Z.2
   exact (P.Beam ..).sub_mem (Beam.mono Finset.subset_union_left u) (Beam.mono Finset.subset_union_right (Beam.shift u _ _))
 change P.Wove _ _ (Π-P.shifts 3 (P.laterPulse n) Π) _
 rw [sub_eq_add_neg,←neg_one_smul ℂ]
 exact (Wove.mono Finset.subset_union_left w).staple ((Wove.mono Finset.subset_union_right (w.slide ..)).smul _)
lemma experiment_cost (x:P.Spectrum0 3)(s:ℕ):P.singleState 3 s x (P.experimentBody Z s n).F=0:=by
 change P.singleState 3 s x (Π-P.shifts 3 (P.laterPulse n) Π)=_ -- adjust
 rw [map_sub,P.slide_single,sub_self]
lemma experiment_small:P.Fades (fun s=>P.experimentBody Z s n):=fun _=> P.tock_fades _
/-- Keep `n` fixed as in a single successful old two-probe experiment; now repeat
 the true old charges on the finer unaged hosts. -/
lemma experiment_wash (p:Tasting.Paid P.par)(h:P.calibration.ℓ<n):
 P.RawNormal j x (fun s=>P.experimentBody Z s n) (fun _=>0) 0 0 :=by
 let A:=P.experimentBody Z 0 n
 have v:A.F∈bay K A.S false:=(P.experiment_first Z n 0 h).2.aperture
 have q:A.S.Nonempty:=⟨_,Finset.mem_union_left _ (porchBorn _)⟩
 obtain ⟨y,u⟩:= P.hasTaste p q v A.realM
 let z:P.Spectrum0 3 :=P.advocate j x 3
 have w:y=(0:ℂ):= tendsto_nhds_unique ((Taste.sticker z A.bay A.realM u).congr (P.experiment_cost Z n z)) tendsto_const_nhds
 simpa only [w,zero_smul] using Taste.replica x (f:=A.F) (P.experiment_small Z n) (fun _=>rfl) (fun _=>rfl) A.bay u

-- The front itself (singlet), with dosage and clearance purchase
-- subsequent. No centering, and raw price includes literal stock
-- coefficient.
def coin :P.Glaze:= ⟨P.eider n,by unfold eider;omega,(Q).patio,Π,P.visibility Z n,P.front_real Z n,P.eider_paid _⟩
lemma coin_first (s:ℕ)(h:P.calibration.ℓ<n): P.FirstDress ((P.coin Z n).apron s) Z.2 (P.stockFolio Q Z):=P.front_film Z n h s
lemma Company.coin_ms {M:P.Menagerie}{a:ℝ}(p:P.Company n M a):
 P.RawNormal j x (Glaze.serial (fun _=>P.coin Z n)) (fun _=>0) 0 (P.electro M Z •φ):=
 (Medal.gained x (M Z)).scale (P.coin Z n).static.fades (fun _=>rfl) (fun _=>by
    change Π= _ • (M Z).bright.F
    rw [electro_front,p.clock Z])
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
