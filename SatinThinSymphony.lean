import SatinFixedContrastNovember4

import SatinThinCoalition

/-! # CP12 Symphony: one true shrinking gauge kernel (all axes) -/
set_option autoImplicit false
set_option maxHeartbeats 350000
set_option synthInstance.maxSize 28000
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
namespace Spine
open Aria Casting Six OS.Semigroup.Balloon
open MacroGrid Aria Casting Six OS.Semigroup.Balloon
open SatinNucleus
section constitution
variable (P:Spine)(x:P.Spectrum0 3)
-- expose x-first for beam average applications
structure Radiates (T:ℕ→P.Apron)(Y:∀ j:Axis,List Axis→ℝ→ P.ColorHil j (P.advocate 3 x j)):Prop where
 slender:∀ j, Tendsto (fun i=> (T i).realWidth P j) atTop (𝓝 0)
 cash:∀ j l t,0<t → Tendsto (fun i=>P.beamRaw j x ((T i).pivot P l) t) atTop (𝓝 (Y j l t))
-- x influences via Beam etc. continuity of heat
local notation "H" j:max=> P.ColorHil j (P.advocate 3 x j)
local notation "S" j:max=> P.physicalEnergy j (P.advocate 3 x j)
local notation "κ" j:max=> P.wealth j (P.advocate 3 x j)
variable (T:ℕ→ P.Apron)(Y:∀ j:Axis,List Axis→ℝ→ P.ColorHil j (P.advocate 3 x j))
lemma heat_both (L:Hilbert)(j:Axis)(U: OS.Semigroup L j): Continuous (fun x:ℝ≥0 × L=> U.E x.1 x.2):= by
 exact continuous_iff_continuousAt.mpr fun x : ℝ≥0 × L=> firmly (fun x:ℝ≥0 × L=> U.E x.1) zero_le_one (Eventually.of_forall (fun _ => U.shrinks _)) (((U.continuousE _).comp continuous_fst).continuousAt) (continuous_snd.continuousAt)
variable {P x T Y}
lemma Radiates.kiss (e:Radiates P x T Y)(j:Axis)(l:List Axis) : Tendsto (fun i=> ((T i).pivot P l).realWidth P j) atTop (𝓝 0):= (e.slender j).congr (fun _=> (Apron.pivot_w j P _ _).symm)
lemma Radiates.choir (e:Radiates P x T Y)(j:Axis)(l:List Axis){t r:ℝ}(p:0<t)(w:t ≤ r): Y j l r=(S j).E (r-t).toNNReal (Y j l t):=by
 let U:= (S j).E (r-t).toNNReal; refine tendsto_nhds_unique (e.cash j l _ (p.trans_le w)) (((U.continuous.tendsto _).comp (e.cash j l t p)).congr' ?_)
 exact ((e.kiss j l).eventually (gt_mem_nhds p)).mono fun i v=> (P.raw_twice j x _ (show ((T i).pivot P l).realWidth P j ≤ t from (show _ < _ from v).le) w).symm
lemma Radiates.heated_cont (e:Radiates P x T Y)(j:Axis)(l:List Axis){t:ℝ}(p:0<t): ContinuousAt (Y j l) t:=by
 let q:= t/2; let U:=fun r:ℝ=>(S j).E (r-q).toNNReal (Y j l q); have hp:q<t:= half_lt_self p
 have h: U=ᶠ[𝓝 t] Y j l:= (lt_mem_nhds hp).mono fun x t=> (e.choir j l (half_pos p) (show q < x from t).le).symm
 exact ((S j).continuousE _|>.comp (continuous_real_toNNReal.comp (continuous_id.sub continuous_const))|>.continuousAt (x:=t)).congr h -- h direction
lemma Radiates.vary {u:ℕ→ℝ}(e:Radiates P x T Y)(j:Axis)(l:List Axis){t:ℝ}(p:0<t)(d:Tendsto u atTop (𝓝 t)): Tendsto (fun i=>P.beamRaw j x ((T i).pivot P l) (u i)) atTop (𝓝 (Y j l t)):=by
 let q:= t/2; have h:0<q:= half_pos p; have hu:q<t:=half_lt_self p; rw [e.choir j l h hu.le]; have ht:Tendsto (fun i=> (u i - q).toNNReal) atTop (𝓝 (t-q).toNNReal):= (continuous_real_toNNReal.tendsto _).comp (d.sub tendsto_const_nhds)
 refine (((heat_both _ j (S j)).tendsto _).comp (ht.prodMk_nhds (e.cash j l q h))).congr' ?_; filter_upwards [(e.kiss j l).eventually (gt_mem_nhds h),d.eventually (lt_mem_nhds hu)] with i v w; exact (P.raw_twice j x _ (show ((T i).pivot P l).realWidth P j ≤ q from (show _<_ from v).le) (show q ≤ u i from (show _<_ from w).le)).symm
lemma Radiates.port {u:ℕ→ℝ}(e:Radiates P x T Y)(j:Axis)(l:List Axis){t:ℝ}(p:0<t)(d:Tendsto u atTop (𝓝 t)): Tendsto (fun i=>P.beam j x ((T i).pivot P l) (u i)) atTop (𝓝 ((κ j) (Y j l t))):= (((κ j).continuous.tendsto _).comp (e.vary j l p d)).congr (fun _=> (P.beam_bank ..).symm)
end constitution
section election
variable (P:Spine)(x:P.Spectrum0 3)(v:ℕ→ℕ)(u:StrictMono v)(a:ℕ→ (ℕ×ℕ)→ℝ){A C b:ℝ}(f r:ℕ)
local notation "a₀" => fun i=> a i (f,r)
local notation "Ts" s:max => fun i=>P.pleading x f r i (s i) v a₀ u
local notation "X" j:max=> P.ColorHil j (P.advocate 3 x j)
local notation "Z!" j:max l:max t:max k:max=> P.beamRaw j x ((P.basePlay x f (v k)).pivot P l) t
lemma radiated (w:ScoutAnthem P x A C f r b v a): ∃ (s:ℕ→ Coalition) (Y:∀ j:Axis,List Axis→ℝ→ X j), Radiates P x (Ts s) Y:=by
 let R:=P.rewardK f r
 let Y'(j:Axis)(l:List Axis)(p:ℝ)(k:ℕ):= (R:ℂ) • ((a₀) k:ℂ) • Z! j l p k
 obtain ⟨g,e⟩:=exists_surjective_nat (Axis × List Axis × ℕ)
 let ψ(i:ℕ):= P.macroStep i
 let U(i:ℕ):= (g i).1
 let E(i:ℕ):= X (U i)
 let F'(i:ℕ)(k:ℕ): E i:= Y' (U i) (g i).2.1 (ψ (g i).2.2) k; have he(i:ℕ):∃ B:ℝ,∀ᶠ k:ℕ in atTop, ‖F' i k‖≤B:=by
    obtain ⟨B,p⟩:= w.earns (U i) (g i).2.1 (ψ (g i).2.2) (P.macroStep_pos _); refine ⟨‖(R:ℂ)‖*B, p.mono fun k h=> ?_⟩; unfold F' Y'; rw [norm_smul]; exact mul_le_mul_of_nonneg_left h.2 (norm_nonneg _)
 obtain ⟨s,h⟩:=Coalitions E F' he; let T:= Ts s
 have ht:Tendsto (fun i=> P.roomy * ψ (v i)) atTop (𝓝 0):=by simpa only [mul_zero,Function.comp,ψ] using (P.macroStep_zero.comp u.tendsto_atTop).const_mul (P.roomy:ℝ)
 have wz(j:Axis): Tendsto (fun i=> (T i).realWidth P j) atTop (𝓝 0):= ht.congr fun i=> (P.pleading_w ..).symm
 have W(j:Axis)(l:List Axis)(i:ℕ):∃ y:X j, Tendsto (fun k=> P.beamRaw j x ((T k).pivot P l) (ψ i)) atTop (𝓝 y):=by
    obtain ⟨n,hp⟩:=e (j,l,i)
    suffices YF: ∃ y:X (g n).1, Tendsto (fun k=> P.beamRaw (g n).1 x ((T k).pivot P (g n).2.1) (ψ (g n).2.2)) atTop (𝓝 y) by rw [hp] at YF; exact YF -- shadow tune
    obtain ⟨y,p⟩:= h n; refine ⟨y,p.congr' ?_⟩
    filter_upwards [ht.eventually (gt_mem_nhds (P.macroStep_pos (g n).2.2))] with i d; unfold T
    rw [P.pleading_p _ _ _ _ _ _ _ u _  _ _ (le_of_lt d)]; refine sum_congr rfl fun i z=> ?_; unfold F' Y'; rw [Complex.ofReal_mul,Complex.ofReal_mul, mul_smul, mul_smul]
    -- simp done?
 have F(j:Axis)(l:List Axis)(t:ℝ)(p:0<t):∃ y:X j, Tendsto (fun i=>P.beamRaw j x ((T i).pivot P l) t) atTop (𝓝 y):=by
    obtain ⟨k,hk⟩:= (P.macroStep_zero.eventually (gt_mem_nhds p)).exists
    obtain ⟨y,c⟩:= W j l k; have he:ψ k<t:= hk; let H:= (P.physicalEnergy j (P.advocate 3 x j)).E (t-ψ k).toNNReal
    refine ⟨H y, ((H.continuous.tendsto _).comp c).congr' ?_⟩; filter_upwards [(wz j).eventually (gt_mem_nhds (P.macroStep_pos k))] with i g
    exact (P.raw_twice j x _ ((Apron.pivot_w j P _ l).le.trans (show (T i).realWidth P j < ψ k from g).le) he.le).symm
 choose! Y h using F; exact ⟨s,Y,wz,h⟩
end election
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.radiated
