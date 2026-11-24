import YM.SU5.WakeInvestment.CarryRead
import YM.SU5.WakeInvestment.Reappoint
/-!
# Receipt through the actual pillars of the unselected history, admitting same x for all listed
appointments. No descent product. At q_-test Gram the Mark coordinates need not yet buy
real rotations/refinement: these are in-lease actual Dome registrations, at scale $s$ itself.
Selection along common A after universal physical encounters in the volume i limit.
-/
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option synthInstance.maxSize 24000
set_option quotPrecheck false
set_option maxRecDepth 2500
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance
open Lamour.Bridge.Celeste
open Morn
open YM.Stationary (Gaia)
open Spine Ballad SpinReceipt Yoke Shuttle
variable (P:Spine) {E v A : ℝ} (Q: Investment P.par E v) (U:Dispatchers P.par)(R:Meritorious P.par)
variable {χ d:ℝ}{I:Type*} [Fintype I] (z:ℕ→ I→ Cover)(l:List I)(u:I→Lead.Clan)(y:I→Gaia)
local notation "WA"=>wakeSum y l u 0
local notation "μ"=>P.pillars (3:Axis)
local notation "F_" s:max=>pillJar P.par u (z s) 0 A s l
-- estimated inlection including Mark test carrier
abbrev readPill (u:I→ Lead.Clan)(G:List I)(x:I→ Cover)(A:ℝ)(s:ℕ): P.Test:= P.tuneK (vocalP u G s (fun _=> x) P.par A)
local notation "Ζ_" s:max=>readPill P u l (z s) A s

include Q U R
theorem realPoseP (p:0<A)(h:∀ i, Appoint P.par A (fun s=> z s i) (y i))(t:∀ i j, y i=y j →∀ᶠ s:ℕ in atTop, z s i=z s j)(c:0<χ):
   ∀ᶠ s:ℕ in atTop,(∫ x:P.Spectrum0 3, ‖P.singleState 3 s x (Ζ_ s) - WA‖^2 ∂μ) < χ := by
 obtain ⟨n,v,e⟩:= saba u l P.run P.large P.law P.history y Q U R p h t χ c
 filter_upwards [v,e] with s p e; let z':=WA; let G:= F_ s; let H:= vocalP u l s z P.par A; let g:=changeT G z'; let Y:=(H.sub ((Voice.one _).hushed z')); let T:=P.tuneK Y
 have hT:T=(Ζ_ s)-z' • (1:P.Test):=Subtype.ext rfl
 have hy(x:P.Spectrum0 3): P.singleState 3 s x (Ζ_ s) - WA=P.singleState 3 s x T:=by rw [hT,map_sub,map_smul]; rw [show P.singleState 3 s x 1=1 by simp [single_state],smul_eq_mul,mul_one]
 simp_rw [hy]; exact lt_of_le_of_lt (P.credit_delivers 3 Y s _ p) e

-- General class. Parameter `A_post` & κ & tests need not wait for x. All with strictly ascending heights (per mayQuota later). Preserve any initiated extraction (e.g. through projection arcs), expects payout beyond maturity.
omit Q U R
structure WakePoll (P:Spine) (f:ℕ→P.Test)(z:ℂ) :Prop where
 candidate (χ:ℝ)(p:0<χ) : ∀ᶠ s:ℕ in atTop,(∫ x:P.Spectrum0 3,‖P.singleState 3 s x (f s)-z‖^2 ∂P.pillars 3) < χ
variable {n:ℕ}{F:ℕ→P.Test}{Z:ℂ}
lemma poll_see (c:WakePoll P F Z) : Tendsto (fun s=>(∫ x:P.Spectrum0 3,‖P.singleState 3 s x (F s)-Z‖^2 ∂P.pillars 3)) atTop (𝓝 (0:ℝ)) := Metric.tendsto_nhds.mpr fun ε t=> (c.candidate ε t).mono fun i h=> by rw [Real.dist_eq,sub_zero,abs_of_nonneg (integral_nonneg (fun _=>sq_nonneg _))]; exact h
-- don't require every x on one subsequence free of choosing heights (separately later register)
theorem schedule_poll {I:ℕ→Type}[∀ n,Fintype (I n)](F:(n:ℕ)→ I n→ℕ→P.Test)(Z: ∀ n,I n→ℂ)(ε:ℕ→ℝ)(p:∀ i,0<ε i)(H:∀ i (j:I i), WakePoll P (F i j) (Z i j)) :
    ∃ f:ℕ→ℕ, ∀ q:ℕ→ℕ,f≤q→
     (∀ᵐ x:P.Spectrum0 3 ∂μ,∀ᶠ i in atTop,∀ (j:I i)(a:Axis), ‖P.singleState a (q i) (P.otherSpectrum 3 a x) (F i j (q i))-Z i j‖< ε i) := by
 choose z hz using fun n:ℕ=> (stablePrice (I n) n (p n)).exists; let A(n:ℕ):= basePrice (z n); have he(n):0<A n:=by have h:= (hz n).1; change 0 < 4*Real.exp 1*(4*z n); positivity
 choose g hg using fun n=> eventually_atTop.mp (Filter.eventually_all.mpr fun i:I n=> (H n i).candidate (A n) (he n))
 refine ⟨g,fun q t=>?_⟩; let U(n:ℕ)(i:I n)(x:P.Spectrum0 3):=‖P.singleState 3 (q n) x (F n i (q n))-Z n i‖^2; filter_upwards [prognosis U A (fun n i=> (((P.chi_joint 3 (P.reading 3 (q n) (F n i (q n)))).sub continuous_const).norm).pow _) (fun _ _ _=>sq_nonneg _) ε p (fun i a=>(hg i (q i) (t i) a).le) (fun i=>(hz i).2.2.2)] with x hx
 filter_upwards [hx] with i a j k; rw [P.single_agrees]; exact (pow_lt_pow_iff_left₀ (norm_nonneg _) (p i).le (by omega:2≠0)).mp (a j)

-- simultaneous along prior-extraction, common x *a.e.*, give finite homogeneous suite; for countables use I n= Fin(sup n). Extend proof.
variable (b:ℕ→ℕ)
lemma polls_calendar {I:Type}[Countable I](F:I→ℕ→P.Test)(Z:I→ℂ)(p:∀ i,WakePoll P (F i) (Z i))(u:StrictMono b): ∃ c:ℕ→ℕ,StrictMono c ∧
   ∀ᵐ x:P.Spectrum0 3 ∂μ,∀ i,Tendsto (fun r=> P.singleState 3 (b (c r)) x (F i (b (c r)))) atTop (𝓝 (Z i)) := by
 classical
 cases isEmpty_or_nonempty I with
 | inl v=> exact ⟨id,strictMono_id,Filter.Eventually.of_forall fun _ i=> isEmptyElim i⟩
 | inr v=>
    obtain ⟨g,hg⟩:= exists_surjective_nat I; let A(n:ℕ)(i:Fin (n+1)):= F (g i.val); let h(n:ℕ):ℝ:= (2:ℝ)⁻¹^n; have ht:Tendsto h atTop (𝓝 0):=tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    obtain ⟨z,hz⟩:= P.schedule_poll A (fun n (i:Fin (n+1))=> Z (g i.val)) h (fun _=> by unfold h; positivity) (fun i j=> p _)
    let c:ℕ→ℕ:= Nat.rec (z 0) (fun i v=> max (z (i+1)) (v+1)); have hZ(n:ℕ):z n ≤ c n:=by induction n with|zero=> rfl|succ i h=> exact le_max_left ..
    refine ⟨c,strictMono_nat_of_lt_succ (fun n=> by have hp:c (n+1)=max (z (n+1)) (c n+1):= rfl; rw [hp]; omega),?_⟩; have hr : ∀ (i:ℕ), i≤ b i:= u.id_le -- requires type?
    filter_upwards [hz (b∘c) (fun i=>(hZ i).trans (hr _))] with x hx i; obtain ⟨n,rfl⟩:= hg i
    refine Metric.tendsto_nhds.mpr fun ε t=>?_; filter_upwards [eventually_ge_atTop n,hx,ht.eventually (gt_mem_nhds t)] with i u q hx'; rw [dist_eq_norm]; have hp:= q (⟨n,by omega⟩:Fin (i+1)) 3; rw [P.single_agrees] at hp; exact (show ‖P.singleState 3 (b (c i)) x (F (g n) (b (c i)))-Z (g n)‖<h i from hp).trans hx'
#print axioms realPoseP
#print axioms polls_calendar
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
