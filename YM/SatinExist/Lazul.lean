import YM.SatinExist.Volt
import SatinProbeCompatibilityNovember6
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
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
namespace Spine
variable (P : Spine)
local notation "K" => P.calibration
local notation "Λ" => P.par
local notation "ι" => P.width
local notation "Y" => P.run
local notation "H" => P.large
local notation "ℒ" => P.law
local notation "π"=> P.history
local notation "Λ₁"=> Λ.R.L
open Afterglow.Hierarchy Hierarchy
open Chrono Hills
variable {C:Call P.par P.width}{W:Wicket P.par P.width}(R:Rolled P.run P.large P.period P.cutoff W C)
variable (j: Axis) (s : ℕ)
local notation "M₀"=> P.room j
open SalonG
variable (A' : ∀ j:Axis, Repertory P.run P.large P.law R j)
variable (x:P.Spectrum0 3)(f:Charm.W P.calibration)
local notation "U₁"=> A' j
local notation "W₀"=> route Y H s j ℒ R U₁
local notation "Ⅺ"=> (P.otherSpectrum 3 j x)
local notation "ρ"=> P.chi j Ⅺ
local notation "fβ" Q:max=> P.azureNativeInclusion Q
local notation "G"=> P.azureReadingOnSelectedVacuum x s
private lemma chosenAtAz (g:Charm.W P.calibration) : (G) g=P.singleState j s Ⅺ (fβ g):= (P.single_agrees ..).symm
include A'
private lemma goodAz (p:0 ≤ route Y H s j ℒ R U₁ f) : 0 ≤ (G) f := by
  rw [P.chosenAtAz j, P.single_state]; apply map_nonneg
  change 0 ≤ P.compressed j s (fβ f); exact P.pricedAz_op R j s U₁ f ▸ map_nonneg ((P.loungeIso R j U₁).conjStarAlgEquiv.toStarAlgHom) p
private lemma pocketAz
    (p:∀ v:Camera Y H j ℒ R U₁,0 ≤ inner ℂ v ((W₀) f v)) : 0 ≤ (G) f:= by
  exact P.goodAz R j s A' x f ((ContinuousLinearMap.nonneg_iff_isPositive _).2 (paidpositive p))
omit A' in
private lemma costMapAz (U V:Hilbert)(t:U≃ₗᵢ[ℂ]V)(x:U.Op) : ‖t.conjStarAlgEquiv x‖=‖x‖ :=
  StarAlgEquiv.norm_map (A:=U.Op) (B:=V.Op) t.conjStarAlgEquiv x
private lemma skyLens (g:Charm.W K) : ‖(G) g‖ ≤ ‖route Y H s j ℒ R U₁ g‖:=by
  rw [P.chosenAtAz j,P.single_state]
  let T:= P.reading j s (fβ g)
  have ht: ‖T‖=‖route Y H s j ℒ R U₁ g‖:=by
    let F:= (P.loungeIso R j U₁).conjStarAlgEquiv
    calc ‖T‖=‖F (route Y H s j ℒ R U₁ g)‖:= (congrArg (fun x=>‖x‖) (P.pricedAz_op R j s U₁ g)).symm
         _ = _:= costMapAz (Camera Y H j ℒ R U₁) (P.groundHil j) (P.loungeIso R j U₁) _
  change ‖(ρ) T‖≤_; rw [← ht]; exact NonUnitalStarAlgHom.norm_apply_le (ρ) _
-- copy / adapt to positive cone evaluation, all axes in due course
local notation "Kₜ" => P.calibration
local notation "M" i:max d:max f:max p:max=> Wedge Y H i j d ℒ R U₁ f p
local notation "ω"=>StructureH Y H j ℒ R U₁
local notation "Φ"=> Camera Y H j ℒ R U₁
lemma governAz (n:ℕ)(b:Decko P.run P.large j) : 0 ≤ (G) (helve (tent P.run P.large) j b.val (vectorT Y H j b n).val) ∧
    (G) (helve Kₜ j (vectorT Y H j b n).val (vectorT Y H j b n).val) ≤ (G) (helve Kₜ j b.val b.val):=by
  obtain ⟨S,p₁,v⟩:= b.property; obtain ⟨d,c,t⟩:= resident Y H S j _ p₁ v; have e:0 < n+d:= by omega
  let y:=vectorT Y H j b n; have p₁':Plan Y H j (n+d) y.val:= plan_steps Y H j d _ t (n:ℤ) (by positivity) (show (d:ℤ)+n≤↑(n+d) from by omega)
  let T' := tock Y H s ℒ R j j (U₁) n (fun _=> Nat.cast_nonneg' _)
  have hz : M s (n+d) p₁' e=T'*(M s d t c) := wicket_adv Y H s j d (n+d) b.val ℒ R (U₁) t c n rfl (show Plan Y H j (n+d) (clockW Kₜ j n b.val) from p₁')
  constructor
  · apply P.pocketAz R j s A' x _; intro u
    change 0 ≤ inner ℂ u ((W₀) (helve Kₜ j b.val y.val) u)
    rw [plate_score Y H s d (n+d) ℒ R A' b.val j t c _ y.val p₁' e,hz]; exact (tock_positive Y H s ℒ R j (U₁) n (Nat.cast_nonneg' _)).inner_nonneg_right _
  apply sub_nonneg.mp; rw [← map_sub (f:=G)]; apply P.pocketAz R j s A' x _; intro w
  change 0 ≤ inner ℂ w ((W₀) (_ - helve Kₜ j y.val y.val) w)
  rw [map_sub (W₀),_root_.sub_apply,inner_sub_right,sub_nonneg,
      plate_score Y H s d d ℒ R A' b.val j t c _ _ t c,plate_score Y H s (n+d) (n+d) ℒ R A' y.val j p₁' e _ _ p₁' e,hz]
  apply (moneyB _ _).mpr; exact (T'.le_opNorm _).trans (mul_le_of_le_one_left (norm_nonneg _) (toll_bound Y H s ℒ R j j (U₁) _ _))
lemma spreadAz (d:ℕ)(v:Plan Y H j d f)(c:0<d)(b:Decko Y H j):
    let y:=embark Y H j d v b
    let B:ℂ:= (↑‖Wedge Y H s j d ℒ R U₁ v c‖:ℂ)^2
    (G) (helve Kₜ j y.val y.val) ≤ B • ((G) (helve Kₜ j b.val b.val)):=by
  intro y B₁
  obtain ⟨S,p₁,v₁⟩:= b.property; obtain ⟨n,t₀,Q⟩:= resident Y H S j _ p₁ v₁
  let T':= M s d v c; let Z:= M s n Q t₀
  apply sub_nonneg.mp; rw [← map_smul (G) B₁, ← map_sub (f:=G)]
  apply P.pocketAz R j s A' x _; intro w
  let D:= couplePlan Y H j d n v Q; have hd:Plan Y H j (d+n) y.val:=D
  change 0 ≤ inner ℂ w ((W₀) _ w)
  rw [map_sub (W₀),map_smul (W₀),_root_.sub_apply, _root_.smul_apply, inner_sub_right,inner_smul_right,
      plate_score Y H s n n ℒ R A' b.val j Q t₀ _ _ Q t₀, plate_score Y H s (d+n) (d+n) ℒ R A' y.val j hd (by omega) _ y.val hd (by omega)]
  have he: M s (d+n) hd (by omega) = T'*Z:=(wedge_glues Y H s j d n ℒ R U₁ v c Q D t₀).symm; rw [he]; exact moneyA (T' (Z (cpo (ω).Unity w))) _ ‖T'‖ (norm_nonneg _) (T'.le_opNorm _)
theorem elected_sphere : Hills.Sphere Y H ℒ R A' (P.azureReadingOnSelectedVacuum x):=by
  refine ⟨fun s=>?_, fun s f=>?_,fun s a f z=>?_,fun s a z f=>?_,fun s a z S f t u=>?_,fun s a b n=> P.governAz R a s A' x n b,fun s a d b f p c=>P.spreadAz R a s A' x f d p c b,fun s x a=> P.skyLens R a s A' _ x⟩
  · change P.chi 3 x ((P.reading 3 s) (fβ (1:Charm.W K)))=_; rw [show (P.reading 3 s) (fβ (1:Charm.W K))=1 from P.reading_unit 3 s,map_one] -- defeq
  · have hx:fβ (Charm.next Y H s ℒ R f)=P.conveying s 1 (fβ f):= Subtype.ext (P.azure_advances s R f)
    change P.singleState 3 _ x (fβ _) =P.singleState 3 s x _
    rw [hx]; exact congrArg (P.chi 3 x) (P.carryReads ..)
  · simp_rw [P.chosenAtAz a,P.single_state]; exact congrArg (P.chi a _) (P.halfReads a s z (fβ f))
  · simp_rw [P.chosenAtAz a,P.single_state]; rw [← map_star]; exact congrArg (P.chi a _) (P.lightStar a s z (fβ f))
  rw [P.chosenAtAz a]; exact P.elevated a s _ (fβ f) z t u
#print axioms elected_sphere
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
