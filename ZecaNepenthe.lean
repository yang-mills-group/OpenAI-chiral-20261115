import ZecaFeathers
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
local notation "F" s:max=>hat P.par.R.L P.par.x s
local notation "N" s:max i:max => Journey.side P.run i s
/-! # Buy height and travel together. Keep both actual calibration and rank resolution schedule. -/
open CF.Pannier.Chancel CF.Py.Rate.LocalLimit.Preparation.Yoke
open Worth Pays CF.BProof
open Real (log)
open Aria Casting MacroGrid
open YM.Stationary (Gaia)
open CF.Onyx (riseX moor)

local notation "z'"=> Yoke.witnessZ
local notation "κ"=>P.sidesPerTick
local notation "κz"=> (P.sidesPerTick:ℤ)

variable (f)(p q:Plume_LocalFieldBounds)(a b:Cover)(W₀:5∣P.par.R.L.val)
lemma planned_heatCost (v:ℝ)(h:8*P.depthCap < v):
 Tendsto (fun r:ℕ=> (P.jetR r)^8/trailℓ v (F r)) atTop (𝓝 0):=
    P.planning_size_go κ 0 (by simpa using P.sides_pos) v h |>.congr fun _=> by unfold travelF jetR; rw [Nat.add_zero]

variable {C:ℝ}
 (A₀:∀ᶠ s in atTop,∀ᶠ i in atTop,∀ k:ℕ,(P.run.voyage i).kick ≤ k → s ≤ P.run.uv k → ShelterCost C P.run s i k)

include W₀ A₀
lemma bending_go :
 Tendsto (fun r:ℕ=>∫ x,P.bendMiss f p q a b r x∂P.pillars 3) atTop (𝓝 0):=by
 let t:=8*P.depthCap+1; have hp:=P.depthCap_pos; let A:=14+2*t; let v:= P.depthCap+6*A+2*t+1
 have ht:0<t:=by unfold t; linarith only [hp]
 have hV:P.depthCap < v:=by unfold v; unfold A; linarith only [ht]
 exact P.mistake_go 3 z' A t v A₀ P.jetR_pos P.jetR_go (P.bend f p q a b W₀) (tendril_live p q)
    (P.bending_cost f p q a b W₀ hV) (P.planned_heatCost t (lt_add_one _))
    (by unfold A; linarith) ht (by unfold v; linarith only [hp])

omit W₀ A₀
private lemma junExtraction {U:Type}[TopologicalSpace U][CompactSpace U][MeasurableSpace U][OpensMeasurableSpace U]
 (V:Measure U) [IsFiniteMeasure V]
 (d0:ℕ→ℕ→U→ℝ)(hc:∀ i n,Continuous (d0 i n))(hn:∀ i n x,0≤d0 i n x)
 (h:∀ i,Tendsto (fun n:ℕ=>∫ x,d0 i n x∂V) atTop (𝓝 0)):
 ∃ y:ℕ→ℕ,Tendsto y atTop atTop ∧ ∀ᵐ x∂V,
    ∀ i,Tendsto (fun n=>d0 i (y n) x) atTop (𝓝 0):=by
 let a:= (1/2:ℝ)
 let d(m n:ℕ)(x:U):= ∑ i ∈ Finset.range m,d0 i n x
 have C'(m n):Continuous (d m n):=continuous_finsetSum _ (fun i _=>hc i n)
 have hp(m n x):0≤d m n x:= Finset.sum_nonneg (fun i _=> hn i n x)
 have hz(m:ℕ): Tendsto (fun n=>∫ x,d m n x∂V) atTop (𝓝 0):= by
    have l:= tendsto_finsetSum (Finset.range m) (fun i (_:i∈Finset.range m)=>h i)
    simp only [Finset.sum_const_zero] at l
    refine l.congr (fun n=> (integral_finsetSum _ (fun i _=>
       (hc i n).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))).symm)
 have ha:0<a:=one_half_pos
 have hex(m):∃ n,m≤n ∧ (∫ x,d m n x∂V)≤a^m:=
   ((eventually_ge_atTop m).and ((hz m).eventually (ge_mem_nhds (pow_pos ha m)))).exists
 choose e h0 h1 using hex
 have hg:Tendsto (fun m=>∫ x,d m (e m) x∂V) atTop (𝓝 0):=
    squeeze_zero (fun m=>integral_nonneg (hp _ _)) h1
       (tendsto_pow_atTop_nhds_zero_of_lt_one ha.le (show a<1 from by norm_num [a]))
 let f(m:ℕ):=d m (e m)
 have ht(m):Integrable (f m) V:=
    (C' _ _).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
 have dx:TendstoInMeasure V f atTop 0:=by
    apply tendstoInMeasure_of_tendsto_eLpNorm (p:=1) one_ne_zero
     (fun m=> (ht m).aestronglyMeasurable) (aestronglyMeasurable_zero)
    have hx:Tendsto (fun m=>ENNReal.ofReal (∫ x,f m x∂V)) atTop (𝓝 (ENNReal.ofReal 0)):=
       ENNReal.continuous_ofReal.continuousAt.tendsto.comp hg
    rw [ENNReal.ofReal_zero] at hx
    refine hx.congr fun m=>?_
    change ENNReal.ofReal (∫x,f m x∂V)= eLpNorm (f m-0) 1 V
    rw [sub_zero,eLpNorm_one_eq_lintegral_enorm, ofReal_integral_eq_lintegral_ofReal (ht m)
       (Eventually.of_forall (hp _ _))]
    exact lintegral_congr (fun x=> by rw [← ofReal_norm_eq_enorm,Real.norm_of_nonneg (show 0≤f m x from hp _ _ _)])
 obtain ⟨n,ns,r⟩:=dx.exists_seq_tendsto_ae
 refine ⟨e ∘ n,(tendsto_atTop_mono (f:=id) h0 tendsto_id).comp ns.tendsto_atTop,r.mono fun x u i=>?_⟩
 refine squeeze_zero' (Eventually.of_forall (fun _=>hn _ _ _)) ?_ u
 filter_upwards [ns.tendsto_atTop.eventually_gt_atTop i] with m t
 exact Finset.single_le_sum (f:=fun j=> d0 j (e (n m)) x)
   (fun j _=>hn _ _ _) (Finset.mem_range.mpr t)

-- record simultaneous. includes condition Q₀ by election separately.
structure Nepenthe (P:Spine)(seq:ℕ→ℕ)(x:P.Spectrum0 3):Prop where
 sky:Tendsto seq atTop atTop
 poses:∀(f:ℕ)(p q:Plume_LocalFieldBounds)(a b:Cover),
  Tendsto (fun i=> P.bendMiss f p q a b (seq i) x) atTop (𝓝 0)

include W₀ A₀
lemma elect_nepenthe :
 ∃ seq:ℕ→ℕ, ∀ᵐ x∂P.pillars 3,P.Nepenthe seq x:=by
 haveI: Nonempty Plume_LocalFieldBounds:= ⟨⟨0,fun _=>1,by norm_num⟩⟩
 obtain ⟨L₀,t⟩:=exists_surjective_nat (ℕ × Plume_LocalFieldBounds × Plume_LocalFieldBounds × Cover × Cover)
 let v(m):= P.bendMiss (L₀ m).1 (L₀ m).2.1 (L₀ m).2.2.1 (L₀ m).2.2.2.1 (L₀ m).2.2.2.2
 obtain ⟨s₀,l,h⟩:= junExtraction (P.pillars 3) v
    (fun i n=> P.mistake_live 3 z' n _ _ _ _) (fun _ _ _=> norm_nonneg _)
    (fun i=>P.bending_go _ _ _ _ _ W₀ A₀)
 refine ⟨_,h.mono (fun x u=> ⟨l,?_⟩)⟩
 intro f p q a b
 obtain ⟨i,b'⟩:= t (f,p,q,a,b)
 have hi:= u i
 unfold v at hi; rw [b'] at hi; exact hi

#print axioms Spine.elect_nepenthe
