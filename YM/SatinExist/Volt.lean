import YM.SatinExist.Chelate
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
open SalonG
local notation "πg"=> (W₀).Unity -- token
local notation "F"=> Camera Y H j ℒ R A
local notation "Ω"=> P.groundHil j
include A
noncomputable def loungeIso : Camera Y H j ℒ R A ≃ₗᵢ[ℂ] P.groundHil j:= by
  let T:=(W₀).Unity
  let L:F→ₗᵢ[ℂ]Ω:= { toFun x:= (⟨(F₀) (cpo T x),(P.azureFullFloor R j A _).1 (among x)⟩:(P.vacuum j:Type)), map_add':= fun x y=> by apply Subtype.ext; exact map_add (F₀) _ _, map_smul':=fun c x=> by apply Subtype.ext; exact map_smul (F₀) _ _, norm_map':=fun x=> (F₀).norm_map (cpo T x)}
  apply LinearIsometryEquiv.ofSurjective L
  intro a
  let b:P.vacuum j:=a; obtain ⟨x,e⟩:=(F₀).surjective b.val; let t:T:=⟨x,(P.azureFullFloor R j A x).2 (e.symm ▸ b.property)⟩
  exact ⟨t,Subtype.ext e⟩
local notation "Λα"=> P.loungeIso R j A
lemma lounge_incl (x:Camera Y H j ℒ R A) : (P.inHil j) ((Λα) x)=(F₀) (cpo (W₀).Unity x):=rfl
lemma lounge_vacuum : (Λα) (Hills.orbitSeed Y H j ℒ R A)=P.groundZero j:=by
  have h:goldStar Y H ℒ R j A= (S₀ 0) 1:=by rw [Chrono.clapper,Chrono.seedling_one]
  apply Subtype.ext; change (P.inHil j) ((Λα) _) = P.floorVec j
  rw [P.lounge_incl,Hills.orbit_lift,h,P.azure_kin]; rfl
lemma lounge_cut (x:A.space): P.piZero j ((F₀) x)=(Λα) (dip (W₀).Unity x):=by
  apply ext_inner_left ℂ; intro y; obtain ⟨y,rfl⟩:=(Λα).surjective y
  rw [LinearIsometryEquiv.inner_map_map,sightR]
  calc
    _= inner ℂ ((P.inHil j) ((Λα) y)) ((F₀) x):= Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left ..
    _=_:=by rw [P.lounge_incl,LinearIsometryEquiv.inner_map_map]
omit A
include R
lemma azHigh (f:Charm.W K) (n:ℕ): (ascended Y H s ℒ R n f).val=(P.conveying s n (⟨f.val,f.property.1⟩:P.Test)).val:=by
  induction n with
  | zero=> rfl
  | succ n ih=> change (Charm.next Y H (s+n) ℒ R _).val = P.projection.refine (s+n) _; rw [P.azure_advances,ih]; rfl
variable (f:Charm.W P.calibration)(d:ℕ)(p:Plan P.run P.large j (2*d) f)
omit R
noncomputable def azureWagon : P.Card j s d:=by
  let g:= P.azureVox j s (⟨f,scoreP Y H j _ p⟩: Decko Y H j)
  refine ⟨g, p.choose,p.choose_spec.2,fun u z=> ⟨p.choose_spec.1.ahead u z,?_⟩⟩
  have hz: ((yard K (2*d):ℕ):ℤ) = ruler P.par.block*d:=by
      change (↑(8*P.par.block.val*(2*d)):ℤ)=16*P.par.block.val*d
      push_cast; ring
  exact (p.choose_spec.1.behind _ z).trans_eq hz
local notation "σ" => P.azureWagon j s f d p
include R A p
lemma foyer_wedge (q:0<d)(x:A.space) : (F₀) (Wedge Y H s j (2*d) ℒ R A p (by omega) x)= P.Box j s d q σ ((F₀) x) := by
  let V':= (F₀).toContinuousLinearEquiv.toContinuousLinearMap
  suffices h: V'.comp (Wedge Y H s j (2*d) ℒ R A p (by omega))=(P.Box j s d q σ).comp V' from DFunLike.congr_fun h x
  apply lens_ext Y H s ℒ R j A; intro i h x
  change (F₀) ((Wedge Y H s j (2*d) ℒ R A p (by omega)) ((S₀ i) x))= P.Box j s d q (σ) ((F₀) ((S₀ i) x))
  rw [P.azure_kin,SalonG.wedge_at Y H s i j (2*d) ℒ R A p x _ h, P.azure_kin]; unfold Box piece
  rw [snatch Y H ℒ s π P.projection.clipped j false (M₀) d σ q h]; apply congrArg (actor Y H i ζ j 0 false (M₀)); apply Subtype.ext
  change (ascended Y H s ℒ R (i-s) f).val * (chime K j (Heat.gaugeShift P.par.block (energyS Λ (2*d) (i-s):ℕ)) x.val.val) = (P.conveying s (i-s) (⟨f.val,f.property.1⟩:P.Test)).val* (chime K j (Heat.gaugeShift P.par.block (2*((amount Λ s i d:ℕ):ℤ))) x.val.val)
  rw [P.azHigh]
  have ht:((energyS Λ (2*d) (i-s):ℕ):ℤ)=2*(amount Λ s i d:ℕ):=by unfold energyS amount; push_cast; ring
  rw [ht]
omit p
lemma pricedAz (x:Camera Y H j ℒ R A) : (Λα) ((route Y H s j ℒ R A f) x)= P.compressed j s (⟨f.val,f.property.1⟩:P.Test) ((Λα) x) := by
  obtain ⟨d,e,z,g⟩:= house Y H j f; let f':=Chrono.clockW K j z f; let b:P.Test:= ⟨f'.val,f'.property.1⟩; let a:P.Test:= ⟨f.val,f.property.1⟩
  have ht:P.reading j s b=P.reading j s a:= P.halfReads j s z a; let p:= plan_larger Y H j d (2*d) f' (by omega) g
  let QP:= P.azureWagon j s f' d p
  change _= P.compressed j s a _
  rw [← show P.compressed j s b=P.compressed j s a from congrArg Subtype.val ht,
     ← Hills.stayP Y H s j j ℒ R A f z, Hills.route_formula Y H s j (2*d) ℒ R A p (by omega),show b=P.entryTest j s QP from rfl, P.compresses j s d e]
  change (Λα) (dip (W₀).Unity ((Wedge Y H s j (2*d) ℒ R A p (by omega)) (cpo (W₀).Unity x)))=P.piZero j (P.Box j s d e QP ((P.inHil j) ((Λα) x)))
  rw [←P.lounge_cut,P.foyer_wedge (f:=f') (q:=e),P.lounge_incl]
lemma pricedAz_op : (P.loungeIso R j A).conjStarAlgEquiv (route Y H s j ℒ R A f) = P.compressed j s (⟨f.val,f.property.1⟩:P.Test):=by
  ext1 x; obtain ⟨x,rfl⟩:= (Λα).surjective x; rw [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply,LinearIsometryEquiv.symm_apply_apply]; exact P.pricedAz R j s A f x
#print axioms pricedAz_op
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
