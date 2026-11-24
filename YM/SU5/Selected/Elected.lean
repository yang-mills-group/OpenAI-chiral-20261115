import YM.SU5.Selected.Lodestar
/-!
# One order-consistent trajectory/state across all axes, found inside the nonfactorizing opening

Existence on the paid signed election; no assumption of single ergodic state before selection.
Scope here: COMPATIBLE fixed-physical-scale resolution observables for asking `Parcel`, and
selected on ALL axis reconstructed slab algebras (extension including wide/non-neutral tests).
This does not by itself carry a relativistic construction (see log). The selected states include *uncompressed*
operators, for estimation of the actual fixed physical mixed-locus test as well as degeneration
checks in their own GNS. In other words, not just selecting a state that is extremal within a
made-to-order class of compressed moments.
-/
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
open CF.Pannier.Chancel FixedProbe
/-- Assert nonvacuity of the anchor convention: the stencil permits a strict separation
    and the whole Filigree-span component is made from words using such offsite pairs. -/
lemma fromWords (K : Calibration) (z:SU.Slot){m:ℕ}(b:Fin m→ Cover)(S:Finset Cover){x:Family K}
    (u : x ∈ Filigree K (Window.family z) b S) (v:x≠0) : ∃ (_:Fin m) (y:Cover), nodeC y∈ S ∧ ∀ i,y≠b i:=by
  let B:=Window.family z
  by_contra U
  apply v; clear v
  have h {L f}(p:CRow K B b S L f): L≠ [] → f=0:=by
    induction p with
    | gave=> simp
    | zip=> simp
    | fuse _ _ p q=> intro i; rw [p i,q i,add_zero]
    | glaze _ _ p=> intro i; rw [p i,smul_zero]
    | pair j y _ _ _ _ _ _ _ _ t _ e _ _=> exact (U ⟨j,y,t,e⟩).elim
  have ht: Lode K B b S ≤ ⊥:= by unfold Lode; apply Submodule.span_le.mpr; rintro f ⟨L,v,_,p⟩; exact (Submodule.mem_bot ℂ).mpr (h p v)
  have hu: Filigree K B b S ≤ ⊥:= by
    unfold Filigree; apply Submodule.span_le.mpr; rintro f ⟨w,p,e,t,rfl⟩; apply (Submodule.mem_bot ℂ).mpr; rw [(Submodule.mem_bot ℂ).mp (ht e),mul_zero]
  exact (Submodule.mem_bot ℂ).mp (hu u)

namespace Spine
variable (P : Spine) (j : Axis)
local notation "X"=> P.Spectrum0 j
local notation "W" k:max=> P.portion k
local notation "t'" k:max x:max=> P.otherSpectrum j k x
local notation "J" k:max=> P.jointTest k
/-- Bundle the phase tools already on the PRESENTATION. `stableTest` consumes *any* tile
    at *any* resolution. -/
structure LodestarStatus (x : P.Spectrum0 j) : Prop where
  accepted : P.lodestar j x
  state_unit (k : Axis) : P.portion k (P.otherSpectrum j k x) 1=1
  joint (k : Axis) : P.portion k (P.otherSpectrum j k x) (P.jointTest k)=1
  fixed0 (k : Axis) : let φ:= P.portion k (P.otherSpectrum j k x);
                        origin φ∈ rooted φ (P.jointTest k)
  actual0 (k : Axis) : let φ:= P.portion k (P.otherSpectrum j k x);
                        ∀ y : φ.GNS, y∈ rooted φ (P.jointTest k) ↔
                          (∀ s n, φ.gnsStarAlgHom (P.Eucl k (whenly (timeMesh P.par) s n)) y=y) ∧ ∀g,φ.gnsStarAlgHom (P.movesOf k g) y=y
  pinning (k : Axis) : let φ:= P.portion k (P.otherSpectrum j k x);
                        rooted φ (P.jointTest k)=Submodule.span ℂ {origin φ}
  separates (k : Axis) : pure0 (P.portion k (P.otherSpectrum j k x))
  normalized (k s x') (R:P.Register) : P.singleState k (s+1) (P.otherSpectrum j k x) (P.promote s R x')= P.singleState j s x x'
  feasible (k : Axis)(s : ℕ)(f : P.Test): ∃ b : P.Slabs k, b.val∈ P.tiles k ∧ P.portion k (P.otherSpectrum j k x) b=P.singleState j s x f ∧ P.shadow k b=P.reading k s f
  stableTest (k s w) (p : 0<w)(f : P.Card k s w) : P.singleState j s x (P.entryTest k s f)=
      P.portion k (P.otherSpectrum j k x) (P.atSide k s w p f)
  clusters (k : Axis) (b:P.Slabs k): let φ:= P.portion k (P.otherSpectrum j k x);
                                        Tendsto (fun n=> grain φ (P.jointTest k) n b) atTop (𝓝 (‖φ b‖^2))
lemma all_phases (x:X) (h:P.lodestar j x): P.LodestarStatus j x:= by
  refine ⟨h, fun k=> P.portion_unit k _,fun k=> P.portion_joint k _,fun k=>P.portion_root k _,fun k y=>?_,fun k=> P.rank_here k (h k), fun k=>P.extremal_here k (h k),?_,?_,?_,?_⟩
  · exact P.joint_ext k (show Hilbert from { space := ((W k) (t' k x)).GNS }) _ y
  · intro k s z R; rw [P.single_agrees,P.single_state,P.single_state,P.promotes_read]
  · intro k s f; obtain ⟨b,p,v⟩:= P.all_apartments k s f
    let y:P.Slabs k:=⟨b,P.blocks_admitted k p⟩; have ht:P.shadow k y=P.reading k s f:=Subtype.ext v
    refine ⟨y,p,?_,ht⟩; rw [P.portion_val,ht,← P.single_state,P.single_agrees]
  · intro k s w p f; rw [P.portion_val,P.boxes_here,← P.single_state,P.single_agrees]
  intro k b φ; rw [← (h k b)]
  exact grain_limit _ _ (P.testing_norm k) _
end Spine
/-- `Spine` includes Course and the E/I with its *actual joint ground projection*.
    Per slot, then EVERY sufficiently late rung (fix finally one!). The selection currently
    depends on the choice of test; not claiming same nonzero interaction in every slot of a
    common chosen component. `Retained` always asks `Parcel` on that history and functions;
    no implicit change to pure-gauge/dressed assignments. -/
theorem lodestar_purchase (ε η : ℝ) (p : 0<η) (o : Cover) (j : Axis):
    ∃ P : Spine, P.par.nominated (VolumeCape.Dream.Nimbus P.width) ∧ ε<P.par.x ∧ P.par.d ≤ η ∧
      ∃ (R : P.Register), SeasonCert P.run P.large R.exhibition ∧
      ∃ (q d w : ℕ) (Z C : ℝ), Papal.Cornet P.run P.large q d w C Z ∧
      ∀ z : SU.Slot, ∀ᶠ s : ℕ in atTop, let S := Sen o (payout d q w); let b:=booty o d q
                                         ∃ (F : FixedProbe.KernelTest P.run P.large) (f : P.Test) (N : ℕ), f.val=F.val ∧
      FixedProbe.AnchorGap (Λ:=P.par) s b S ∧ Carries P.run P.large P.law s P.projection F S N ∧
      f.val ∈ Filigree P.calibration (Window.family z) b S ∧ (∃ i y, nodeC y∈ S ∧ (∀ t, y≠b t) ∧
        0<dist (addressG P.par s (nodeC y)) (addressG P.par s (nodeC (b i)))) ∧
      1/4 ≤ ‖P.E s F.val‖ ∧ ∃ u : P.Spectrum0 j, P.LodestarStatus j u ∧ ∀ k: Axis, P.Retained k s
        (P.otherSpectrum j k u) b S z f := by
  obtain ⟨P,t,v,y,R,ℏ,q,d,w,Z,C,h⟩:= book ε η p; refine ⟨P,t,v,y,R,ℏ,q,d,w,Z,C,h,fun z=>?_⟩
  filter_upwards [(FixedProbe.current P.run P.large P.law P.projection h z o)] with s hs
  let S := Sen o (payout d q w); let b:=booty o d q
  obtain ⟨F,N,p,hx,e,g⟩:=hs; let f := P.art F.val F.property.1
  obtain ⟨u,r,c⟩:= P.approved_exists j R (P.aperture j s f g).1 (P.aperture j s f g).2
  have hv (k) : P.otherSpectrum j k u∈ P.opening k s f:= by
    change 1/8<‖P.singleState k s _ f‖; rw [P.single_agrees]; exact r
  refine ⟨F,f,N,rfl,p,e,hx,?_,g,u,P.all_phases j u c,fun k=> P.retention k s (P.otherSpectrum j k u) b S z (h.cents o) f hx e.firstPane (hv k)⟩
  have ha : f≠0:=by
    change (1:ℝ)/8<‖P.singleState j s u f‖ at r; intro ht; rw [ht,map_zero,norm_zero] at r; norm_num at r
  obtain ⟨i,y,t,hn⟩:=fromWords P.calibration z b S (x:=f.val) hx (fun h=> ha (Subtype.ext h)); exact ⟨i,y,t,hn,p.1.trans_le (p.2.2 i y t hn)⟩
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
#check @YM.CF.Buffered.Afterglow.Tower.VacuumSelection.lodestar_purchase
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.lodestar_purchase
