import GaugeFieldConstruction.ClearShelfNX
import GaugeFieldConstruction.TimbersR
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 3000
set_option linter.unusedSectionVars false
set_option maxHeartbeats 130000
set_option quotPrecheck false
set_option linter.unusedSimpArgs false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance
open Lamour.Bridge.Celeste
namespace Spine
open Aria Set OS.Semigroup Ballad Six Glaze
open Papal FrameP Fock.Flux Gleam BProof.PricePort Gleam.Guide Gleam.clocks
open Lead Designs
variable (P:Spine){n:ℕ}(A B:BeaconNX n)(i:ℤ)
open RosterJ XGarden XGarden.MastTin XGarden.MastTin.ArtCart
private lemma regionBoxNX (j C:ℕ)(X:Lead n)(h: Laurent.size (nodeC X.birth) ≤ C)(g:2*n+C≤ j): X.patio⊆ cartO 0 j:=by
 intro v p; have he:=Extra.Iteration.along_size (nodeC X.birth) v _ (List.mem_toFinset.mp p)
 rw [X.costs] at he; have hp: Laurent.size v ≤ Laurent.size (v-nodeC X.birth)+C:= (show _ ≤ Laurent.size (v-nodeC X.birth)+ Laurent.size (nodeC X.birth) from by refine le_trans ?_ (Laurent.size_add ..); rw [sub_add_cancel]).trans (Nat.add_le_add_left h _)
 refine (cart_spec ..).2 fun i=>?_ ; rw [show (0:Cover) i=(0:ℤ) from rfl,sub_zero]; exact (show (v i).natAbs ≤ Laurent.size v from single_le_sum (f:=fun i => (v i).natAbs) (fun _ _=>Nat.zero_le _) (mem_univ _)).trans (hp.trans ((Nat.add_le_add_right he C).trans g)) -- tune name along_size
abbrev RootCoverNX (C:BeaconNX n):Cover := nodeC C.1.birth
lemma directionNNX (x:ℤ): Laurent.size (direction x)= x.natAbs:=by
 have he:∀ i:Axis,i≠3 → direction x i=0:=by intro i h; simp [direction,h]
 unfold Laurent.size; rw[sum_eq_single (3:Axis)]; swap; · intro i _ p; rw[he i p, Int.natAbs_zero]
 swap; · simp
 rw [show direction x 3=x from by simp [direction]]
local notation "δ" => ruler P.calibration.B
private lemma blueCoverNX :(RootCoverNX (P.postNowNX A i)) = RootCoverNX A+ direction (δ*i)∧ RootCoverNX (P.anteBNX B i) =RootCoverNX (flipBeaconNX B 3 0) - direction (δ*i):=by
 unfold RootCoverNX; rw [(P.marchAstNX ..).1,(P.bioAntsNX ..).1]; have h:(2:ℕ) • direction (P.crewB i) = direction (δ*i):=by rw [two_smul, direction, ← add_smul, ← two_mul,show 2*P.crewB i= δ*i from ruler_offset P.calibration i]; rfl
 unfold nodeC; change _∧ _=_+(1:Cover)-_
 rw[smul_add,smul_sub,h]; constructor
 · abel
 dsimp only [flipBeaconNX]; abel
variable (m:ℕ)(J:ℕ→ℤ)(p:Tendsto (fun i=> (Richm_R P m i)⁻¹*↑(ruler P.calibration.B*J i:ℤ)) atTop (𝓝 (1/2)))
include p
lemma marsLineNX : ∃ s:ℝ,∃ C,RunRate 0 s C ∧ ∀ᶠ i in atTop,∃ w:ℕ,0<w ∧ ∃ (σ:Cover)(k:ℕ)(j:ℤ), let U:=cartO 0 k
  (P.anteBNX A (J i)).1.patio⊆U∧(P.postNowNX B (J i)).1.patio⊆U∧SlabMark.Etch.House P.calibration w σ 0 (plow P.calibration 3 j U) ∧ σ 3=0∧ (SlabMark.Etch.ratio P.calibration.B w:ℝ)≤ C (P.urnMark (SportR P m i)):=by
 obtain ⟨f,t⟩:=costSum_R P m; let B':=P.calibration.B; let α(z:ℝ):= CapSum_R P m z; let R:= Richm_R P m
 let g(z:ℝ):=16*(B'.val:ℝ)* (8*α z); have ht:RunRate 0 f g:= (t.cmul 8).cmul _; have hp:= (ht.pow 4).cmul 128
 rw [zero_mul] at hp; refine ⟨_,_,hp,?_⟩
 let A':= flipBeaconNX A 3 0
 let a:ℕ:= Laurent.size (RootCoverNX A'); let b:= Laurent.size (RootCoverNX B)
 let c:= a+b+2*n; let H(i:ℕ):ℕ:=(δ*J i).natAbs; let k(i):=c+H i; let V':= P.calibration.ℓ
 have he:∀ᶠ i in atTop,(H i:ℝ) ≤ R i:=by
    have hz:∀ᶠ i in atTop,|(R i)⁻¹*↑(δ*J i:ℤ)| < 1:=p.abs.eventually (gt_mem_nhds (by norm_num : |(1:ℝ)/2|<1))
    filter_upwards [hz] with i h
    let X:= δ*J i; have hg: ((H i):ℝ)=|(X:ℝ)|:=by simp [H,X]
    rw [hg, ←mul_one (R i)]; apply (inv_mul_le_iff₀ (show 0 < R i from Richm_good ..)).mp -- ? RHS
    rw [← abs_of_nonneg (inv_pos.mpr (show 0 < R i from Richm_good ..)).le,←abs_mul]; exact h.le
 filter_upwards [cap_SumaR P m,he,(Richm_lit P m).eventually_ge_atTop ((c:ℝ)+V'+1)] with i h q U
 let d:=H i; let u:= k i+V'+1; let j:ℤ:=u
 refine ⟨2*u,Nat.mul_pos (by decide) (Nat.succ_pos _),fun m=>if m=(3:Axis) then 0 else -j,k i,j,?_,?_ ,?_ ,by simp,?_⟩
 · apply regionBoxNX (C:=a+H i); swap; · unfold k c; omega
   change Laurent.size (RootCoverNX (P.anteBNX A (J i))) ≤ _; rw [(P.blueCoverNX B A (J i)).2]; let u:=δ*J i; rw[sub_eq_add_neg]; apply le_trans (Laurent.size_add _ _); rw[Laurent.size_neg,directionNNX]
 · apply regionBoxNX (C:=b+H i); swap; · unfold k c; omega
   change Laurent.size (RootCoverNX (P.postNowNX B (J i))) ≤ _; rw [(P.blueCoverNX B A (J i)).1]; apply le_trans (Laurent.size_add ..); rw [directionNNX]
 · exact Heritor.mastHaus P (k i) 3 -- maybe w uses ℓ & h num
 unfold SlabMark.Etch.ratio SlabMark.Etch.pitch g α B'
 have hx:0 ≤(B'.val:ℝ):= Nat.cast_nonneg _
 push_cast; apply mul_le_mul_of_nonneg_left _ (by norm_num); apply pow_le_pow_left₀ (by positivity); apply mul_le_mul_of_nonneg_left _ (mul_nonneg (by norm_num) hx)
 unfold u k; push_cast; change _≤8*α (P.urnMark _); change R i ≤ α (P.urnMark _) at h; linarith only [h,q,U, Nat.cast_nonneg (α:=ℝ) c,Nat.cast_nonneg (α:=ℝ) V']
#print axioms marsLineNX
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
end
