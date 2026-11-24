import SatinThinVista

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
local notation "Ω"=>P.Hil j
local notation "φ"=> P.groundZero j
local notation "μ"=> P.pillars j
local notation "W"=> P.calibration
local notation "Q"=> P.par.block
local notation "ℓ"=> P.calibration.ℓ
local notation "Ξ"=> household W
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
local notation "F" s:max=>hat P.par.R.L P.par.x s
local notation "N" s:max i:max => Journey.side P.run i s
/-! # Train cost comparison on elected printed heights. -/
/-! # Fix ranks independently of layout and period. Extract for every *fixed* v from very same P (no law mutation). -/
local notation "aK"=>P.nomadic
local notation "bK"=>P.engine
variable {A C U:ℝ}
abbrev cradle (P:Spine)(r v:ℕ)(b:ℝ): Prop:= |b|≤ 2*fareMax P.par.R.L (v-r) ∧ (1:ℝ)≤ (2*fareMin P.par.R.L (v-r))*|b|
variable (p:f≤r)(q:r≤v)
abbrev fundsDay (i:ℕ)(κ:ℝ): Prop:= ∃ b z t:ℝ, |z-1|≤1/4 ∧ ReadDensity P.run (P.nomadic i) (P.engine i) A p q b z t∧ κ=z*b
lemma crests_mark {z:ℝ}(u: Premier L (v-r) U)(t:|z-1|≤1/4): P.cradle r v (z*U):=by
 obtain ⟨a,m⟩:=abs_le.mp t; have h:0 ≤ z:=by linarith
 let b:=fareMax L (v-r); let t':=fareMin L (v-r); have hz: (1:ℝ)≤ t'*|U|:=by
    have e: 0 < |U| := abs_pos.mpr u.nz; exact (div_le_iff₀ e).mp ((one_div _).trans_le ((abs_inv _).symm.trans_le u.small))
 have h':0≤ t':=by unfold t' fareMin; positivity
 unfold cradle; rw [abs_mul,abs_of_nonneg h]; constructor
 · nlinarith only [a,m,u.big,abs_nonneg U, h,show 0≤fareMax L (v-r) from (abs_nonneg U).trans u.big] -- maybe generate z*U bound;
 have hc: t'*|U|≤2*z*(t'*|U|):= le_mul_of_one_le_left (mul_nonneg h' (abs_nonneg _)) (by linarith)
 exact le_trans hz (hc.trans_eq (by unfold t'; ring))
structure treasury (A C:ℝ) (P:Spine)(f r v:ℕ):Prop where
 price:f<r
 step:r≤v
 room:∀ᶠ i:ℕ in atTop, PaysTilt P.run (P.nomadic i) (P.engine i) f r v A ∧ ShelterCost C P.run f (P.nomadic i) (P.engine i)
lemma treasury_plot (A C:ℝ)(Y0:∀ᶠ f:ℕ in atTop, ∀ᶠ i:ℕ in atTop, ∀ k:ℕ, (P.run.voyage i).kick ≤ k→f ≤ P.run.uv k→ShelterCost C P.run f i k)(Y1:Chronicle P.run A):
 ∀ᶠ f:ℕ in atTop,∀ r:ℕ, f<r→ ∀ v:ℕ,r≤v→ treasury A C P f r v:=by
 filter_upwards [purchase_series P.run Y1,Y0] with f Pq H0 r w v t
 refine ⟨w,t,?_⟩; filter_upwards [P.history.finance v,P.stockGo.eventually (Pq r w v t), P.stockGo.eventually H0] with i u t' H1
 exact ⟨t' _ u.depth u.enters,H1 _ u.depth (le_trans (w.le.trans t) u.enters)⟩
variable (T:treasury A C P f r v)
structure lender (A C:ℝ)(f r v:ℕ)(b:ℕ→ℝ)(a:ℝ)(l:ℕ→ℕ)(P:Spine):Prop where
 treasury:treasury A C P f r v
 cape:P.cradle r v a
 earn: StrictMono l
 pays: ∀ᶠ i:ℕ in atTop,P.cradle r v (b i) ∧ P.fundsDay (A:=A) treasury.price.le treasury.step i (b i)
 future: Tendsto (b ∘ l) atTop (𝓝 a)
include T
lemma penny_p : ∃ (b:ℕ→ℝ)(a:ℝ)(l:ℕ→ℕ), lender A C f r v b a l P:=by
 let t(i:ℕ)(b:ℝ):= P.cradle r v b ∧ P.fundsDay (A:=A) T.price.le T.step i b; let pr:=T.step
 let c(i:ℕ):ℝ:= if h:∃ b,t i b then h.choose else 1; have hv:∀ᶠ i:ℕ in atTop,t i (c i):=by
    filter_upwards [T.room] with i h; obtain ⟨g, p,vQ⟩:=h.1.reading -- ordering
    obtain ⟨z',v,x,l,f,u⟩:=vQ; have ht:t i (p*g):= ⟨P.crests_mark x.aims v, _,_, z', v,f,rfl⟩
    unfold c; rw [dif_pos ⟨p*g,ht⟩]; apply Exists.choose_spec
 let g:ℝ:=2*fareMax L (v-r); obtain ⟨z,vq,l,t',he⟩:= (isCompact_Icc (α:=ℝ) (a:=-g) (b:=g)).isSeqCompact.subseq_of_frequently_in ((hv.mono fun i h=> show c i∈Set.Icc _ _ from abs_le.mp (show P.cradle r v _ from h.1).1).frequently)
 have h: P.cradle r v z:= ⟨abs_le.mpr vq, ge_of_tendsto (he.abs.const_mul _) ?_ ⟩ -- use ge_of_tendsto; tuning
 · exact ⟨c,z,l,T,h,t',hv,he⟩
 exact (t'.tendsto_atTop.eventually hv).mono fun _ h=>h.1.2
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.penny_p
