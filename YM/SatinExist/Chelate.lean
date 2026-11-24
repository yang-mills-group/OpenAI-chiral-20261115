import YM.SatinExist.Punch
import YM.SU5.Selected.MeshSym
/-! # BUDGET Aurora vs Unity. Odd notch discrepancy removed also for ground. -/
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
variable (A : Repertory P.run P.large P.law R j)
local notation "V"=> A.space
local notation "X"=> P.Hil j
local notation "ζ"=> P.history.circuit
local notation "F₀"=> P.foyerAz R j A
local notation "S₀" s:max=> store Y H s ℒ R j A
local notation "W₀"=> StructureH Y H j ℒ R A
local notation "G₀" s:max k:max t:max a:max=> sailV Y H ℒ s ζ j 0 false k a (M₀) t
local notation "V₀"=> Aurora Y H ℒ π j false (M₀)
local notation "Ε"=> advance Y H ℒ ζ j 0 false (M₀)
local notation "ϒ"=> clockdrive Y H ℒ ζ j 0 false (M₀)
include A
lemma azure_space (k:Axis)(v:k≠j)(z:ℤ)(x:A.space): (F₀) ((W₀).stepT s k z (fun h=>(v h).elim) x) = (G₀ s k z v) ((F₀) x) := by
  let G := (F₀).toContinuousLinearEquiv.toContinuousLinearMap
  let T := tock Y H s ℒ R j k A z (fun h=> (v h).elim)
  suffices h:G.comp T=(G₀ s k z v).comp G from DFunLike.congr_fun h x
  apply lens_ext Y H s ℒ R j A; intro i h y
  change (F₀) (T ((S₀ i) y))=(G₀ s k z v) ((F₀) ((S₀ i) y))
  unfold T; rw [earn_seed Y H s i ℒ R j k A y z _ h, P.azure_kin, P.azure_kin]
  unfold piece; rw [sailV_at Y H ℒ s ζ j 0 false k v (M₀) z i h]
  rfl
lemma azure_time (n:ℕ)(x:A.space): (F₀) ((W₀).stepT s j ↑n (fun _=>by positivity) x)= advance Y H ℒ ζ j 0 false (M₀) (P.halfTime s n) ((F₀) x):=by
  change _= P.euclOp j _ _; rw [←P.keel_along]
  let G := (F₀).toContinuousLinearEquiv.toContinuousLinearMap
  let T := tock Y H s ℒ R j j A n (fun _=> by positivity)
  suffices h:G.comp T=(P.Keeling j s n).comp G from DFunLike.congr_fun h x
  apply lens_ext Y H s ℒ R j A; intro i h y
  change (F₀) (T ((S₀ i) y))=P.Keeling j s n ((F₀) ((S₀ i) y))
  unfold T; rw [earn_seed Y H s i ℒ R j j A y n _ h,P.azure_kin,P.azure_kin,P.keel_at j s i n h]
  refine congrArg _ (Subtype.ext ?_)
  change chime K j (Heat.gaugeShift P.par.block _) y.val.val=chime K j (Heat.gaugeShift P.par.block _) y.val.val
  congr 2
omit A
-- Not obvious since s-even notch. But orientation independence in CAP already proves.
lemma sail_aurora (k:Axis)(v:k≠j)(z:ℤ)(x:X)(p:x∈P.vacuum j):(G₀ s k z v) x=x:=by
  -- Take cross inner products with late actors before ground projection
  apply Tower.all_voices Y H ζ j 0 false (M₀); intro i y
  let m:=max s i; have hs:= le_max_left s i; have hp:=le_max_right s i; rw [←join_actor Y H ℒ ζ j 0 false (M₀) i m hp y]
  let T:= G₀ s k z v; let U:= G₀ s k (-z) v
  let y':= Raise Y H ζ j 0 false i m hp y
  let l:=smill P.par s m (-z); let y'':=sail Y H m j 0 false k v l y'
  let w:=P.piece j m y'; let u:=P.piece j m y''
  have hw: U w=u:= by unfold U; rw [sailV_high Y H ℒ s ζ j 0 false k v (M₀) (-z) m hs]; unfold w u piece; rw [sailV_at Y H ℒ m ζ j 0 false k v (M₀) _ m le_rfl,smill_id]
  have h₁:T.comp U=ContinuousLinearMap.id ℂ (P.Hil j):=by unfold T U; rw [sailV_sum Y H ℒ,add_neg_cancel,sailV_source]
  have h₂:U.comp T=ContinuousLinearMap.id ℂ (P.Hil j):=by unfold T U; rw [sailV_sum Y H ℒ,neg_add_cancel,sailV_source]
  have hc: P.piZero j u=P.piZero j w:=by
    unfold w u; rw [← P.seed, ← P.seed]; refine congrArg (fun z:P.Ensemble j=>Subtype.val z (P.groundZero j)) (?_ : P.reading j m (P.voxTest j m y'')= P.reading j m (P.voxTest j m y'))
    apply (P.portals j k).injective; change (P.portals j k) _=(P.portals j k) _; rw [P.returns_reading,P.returns_reading]; rw [show P.voxTest j m y''=P.halfShift k l (P.voxTest j m y') from rfl]; exact P.halfReads k m l _ -- defeq?
  change inner ℂ w (T x) = inner ℂ w x
  let a: P.vacuum j:=⟨x,p⟩
  calc
    _= inner ℂ u x := by rw [← hw]; nth_rw 1 [← show T (U w)=w from DFunLike.congr_fun h₁ w]; apply inner_isoAux U _ h₂ (sailV_small Y H ℒ s ζ j 0 false k v (M₀) _) (sailV_small Y H ℒ s ζ j 0 false k v (M₀) _) -- order
    _= inner ℂ (P.piZero j u) a := (Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right a u).symm
    _= inner ℂ (P.piZero j w) a := by rw [hc]
    _=_:= Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right a w
where inner_isoAux {X₀:Hilbert}(g f:X₀.Op)(p:g.comp f=ContinuousLinearMap.id ℂ X₀)(u:‖f‖≤1)(v:‖g‖≤1)(x y:X₀):inner ℂ (f x) (f y)=inner ℂ x y:=by
        let D:X₀ →ₗᵢ[ℂ] X₀:={ f.toLinearMap with
            norm_map' := fun x=> le_antisymm ((f.le_opNorm x).trans (mul_le_of_le_one_left (norm_nonneg _) u)) (by
              change ‖x‖≤ ‖f x‖
              have ht:g (f x)=x:=DFunLike.congr_fun p x; nth_rw 1 [← ht]; exact (g.le_opNorm (f x)).trans (mul_le_of_le_one_left (norm_nonneg _) v)) }
        exact D.inner_map_map x y
-- full mismatch handled
include A
lemma azureFullFloor (x:A.space) : x∈ (W₀).Unity ↔ (F₀) x ∈ P.vacuum j:= by
  let y:= (F₀) x
  rw [(W₀).unityH]
  constructor
  · intro t; change y ∈ Aurora ..; rw [Aurora,Submodule.mem_iInf]; intro s
    apply (Vacancy.formal ..).mpr
    refine ⟨fun i=>?_,fun k z=>?_⟩
    · apply (ϒ).track_invariant y _ i; intro v u
      have ht:= congrArg (F₀) (t v j (↑(2*u):ℤ) (fun _=> by positivity)); rw [P.azure_time R j v A] at ht
      rw [show advance Y H ℒ ζ j 0 false (M₀) (P.halfTime v (2*u))=P.euclOp j (P.halfTime v (2*u)) from rfl, ← P.keel_along] at ht
      exact ht
    unfold y; rw [← P.azure_space R j s A,t]
  intro p s k z f
  apply (F₀).injective
  by_cases e:k=j
  · subst k; obtain ⟨n,rfl⟩:= Int.eq_ofNat_of_zero_le (f rfl)
    have ht:= P.azure_time R j s A n x
    refine ht.trans ?_
    exact Vacancy.floor_rise Y H ℒ π j false (M₀) ⟨y,p⟩ _
  rw [P.azure_space R j s A k e]; exact P.sail_aurora j s k e z y p
#print axioms azureFullFloor
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
