import YM.SatinExist.Policed
import YM.SatinExist.Shield
import YM.SatinExist.Cameo
import YM.SatinExist.Hall
import YM.SatinExist.Fence
import SatinThinRampart
import SatinThinAngle
import YM.SatinExist.Glacis
import SatinThinSegno

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
local notation "Y"=> P.run
local notation "Λ"=> P.par
local notation "L"=> P.par.R.L
local notation "H"=>P.large
/-! # Train cost comparison on elected printed heights. -/
-- support of tested pair. Need dSpacing condition eventually at roots. Using real checkpoint geometry. Only prices here. 
variable (X:Cover){C e A:ℝ}
open CF.Pannier.Chancel CF.Py.Rate.LocalLimit.Preparation.Yoke
local notation "aK"=>P.nomadic
local notation "bK"=>P.engine
set_option linter.unusedSectionVars false
open Aria Casting MacroGrid
variable (N₁:P.NightCop) (x:P.Spectrum0 3)(A0:ℝ) (B0:ℝ)(b':ℝ)
local notation "T"=> ℕ × ℕ
variable (v:ℕ→ℕ)(a:ℕ→ (ℕ×ℕ)→ℝ)
lemma ScoutAnthem.further (V: ScoutAnthem P x A0 B0 f r b' v a) {τ:ℕ→ℕ} (h:StrictMono τ): ScoutAnthem P x A0 B0 f r b' (v∘τ) (a ∘ τ):=by
 let y:= h.tendsto_atTop; obtain ⟨R,t⟩:= V.station
 refine ⟨⟨R,t.fast.comp h,fun i=> t.up _,fun i=>t.cruise _, t.price,fun i=>t.main _,fun n=> y.eventually (t.extra n)⟩,fun j l e t=> ?_⟩
 obtain ⟨a,h⟩:= V.earns j l e t; exact ⟨a,y.eventually h⟩
variable {τ:ℕ→ℕ}
-- ratio denominator unknown outside; test only valid at tail
local notation "t₀"=> ((f,r):ℕ×ℕ)
structure Aglomerate (f r:ℕ)(v:ℕ→ (ℕ×ℕ)→ ℝ):Prop where
 caught (p:T)(a:p.1≥f)(b:p.2>p.1)(c:p.2≥r):∃ y:ℝ,Tendsto (fun i=> v i (f,r)/v i p) atTop (𝓝 y)
lemma children {u:ℕ→Pedal P f}(V:AtMile P A0 B0 f r x b' v a u) (h:f<r):∃ τ:ℕ→ℕ,StrictMono τ∧ Aglomerate f r (a ∘ τ):=by
 let b(p:T):= 4*zoomC P.par.R.L^(p.2-r)
 let Pcr(i:ℕ)(p:ℕ×ℕ):= if f ≤ p.1 ∧ p.1<p.2 ∧ r ≤p.2 ∧ p.2≤v i then a i (f,r)/a i p else 0
 have hp(i:ℕ)(p:ℕ×ℕ):Pcr i p∈ Set.Icc (-b p) (b p):=by
    apply abs_le.mp; unfold Pcr; rcases V.cruise i with ⟨W',e,t⟩; split; rename_i hv
    · by_cases u:a i p=0; · rw [u,div_zero,abs_zero]; unfold b; have hu:= zoomC_p P.par.R.L; positivity
      rw [abs_div]; exact (div_le_iff₀ (abs_pos.mpr u)).mpr (t.career (f,r) p ⟨le_rfl,h,V.up i⟩ ⟨hv.1,hv.2.1,hv.2.2.2⟩ hv.2.2.1)
    rw [abs_zero]; unfold b; have hu:=zoomC_p P.par.R.L; positivity
 obtain ⟨a',g,l,hk,ht⟩:= (isCompact_pi_infinite (ι:=T) (X:=fun _=>ℝ) (fun (p:T)=>isCompact_Icc (a:=-b p) (b:=b p))).isSeqCompact.subseq_of_frequently_in ((Eventually.of_forall (fun i=> (show ∀ j:T,Pcr i j∈ Set.Icc (-b j) (b j) from hp i))).frequently)
 refine ⟨l,hk,⟨fun p u q c=>⟨a' p,?_⟩⟩⟩
 refine (tendsto_pi_nhds.mp ht p).congr' ((hk.tendsto_atTop.eventually (V.fast.tendsto_atTop.eventually (eventually_ge_atTop p.2))).mono fun i y=>?_); change (if _ then _ else _)=_; exact if_pos ⟨u,q,c,y⟩ -- change tactic maybe stuck
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
