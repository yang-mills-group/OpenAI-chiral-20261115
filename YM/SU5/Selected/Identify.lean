import YM.SU5.Selected.Contrast

/-!
# Identify the transfer of the current ground history on the very same Tapestry election

Buy this by refining **before** purchasing the ground extension if necessary. No alternative
history from FiniteGaugeData manuscripts or other Season election, only Tapestry on this
Universal. The mixing `F` and estimates can already be gotten for the old subsequences
with the SAME I and E (on every slot); not transporting a proof about their ground spaces.
Use all along the new ground path for every fixed `(s,S)`. Equality of the limiting BLOCK
transfer also allows the compact-operator bill (on local Borel/Swatch norm) for every
refinement used in the ground conditioning. We need this for genuine vacuum selection.
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
open Tapestry.Exhibition
namespace Spine
variable (P : Spine) (j : Axis)
local notation "K" => P.calibration
local notation "Λ" => P.par
local notation "ι" => P.width
local notation "Y" => P.run
local notation "H" => P.large

/-- A Tapestry presentation, not inferred for arbitrary elections. The UV/period ladders,
    I,E, preparation and course are EXACTLY those of the Spine. -/
def Register := {p : (Tapestry.Rack P.par P.width) × (Tapestry.Clay P.par P.width) ×
      (ℕ→ℕ→Tapestry.Tariff) × (ℕ→Tapestry.Tariff) //
   Fashion P.run P.large P.period P.cutoff P.ultraviolet P.E p.1 p.2.1 p.2.2.1 p.2.2.2}
abbrev Register.row {P : Spine} (ρ : P.Register) := ρ.val.1
abbrev Register.loom {P : Spine} (ρ : P.Register) := ρ.val.2.1
theorem Register.exhibition {P : Spine} (ρ : P.Register) : Fashion P.run P.large P.period P.cutoff P.ultraviolet P.E ρ.row ρ.loom ρ.val.2.2.1 ρ.val.2.2.2:= ρ.property

variable (s : ℕ) (S : Finset Cover) (ρ : P.Register)
local notation "S₊" S:max=> followBox («Λ»:=P.par) (l:=P.width) S
lemma talks : Exhibition P.run P.large P.period P.cutoff P.ultraviolet P.E ρ.row ρ.loom:=
  ρ.exhibition.toExhibition
lemma certified_register : SeasonCert P.run P.large ρ.exhibition:=grantedCert ..
local notation "μ" n:max=> P.period (P.projection.rows n)
local notation "ν" n:max=> P.cutoff (P.projection.columns n)
local notation "π"=> P.history
abbrev stage (ρ : P.Register) (r : ℕ) : WedgeStage :=
  ⟨P.projection.rows r,P.projection.columns r,((P.talks ρ).status ..).1 (P.history.gate r)⟩
lemma native_match (n : ℕ) (F : Family K) : exhibit Y H s n F = distribute Y H s n F :=
  present_send ..
lemma block_matches (f : Swatch S) (n m : ℕ) (h : Spanned Y S s n m)
    (p : Tivoli (followBox («Λ»:=P.par) (l:=P.width) S) (P.calibration.c (momentm Y n (s+1)))) :
    block Y H s n m S (badge K S f).val =
      (badge K (S₊ S) (coupon Y H S s n m f)).val := by
  apply stationary_ext Y H (s+1) (S₊ S) n p.hosp (booked ..) (Tapestry.texture ..)
  rw [Tapestry.domTag,reserved Y H s S n m h.1 (Tapestry.texture S K f) p]; change
    ascender Y s n m (distribute Y H s n (render S K f))=
      distribute Y H (s+1) n (render _ K (coupon Y H S s n m f))
  rw [← native_match, ← native_match,← present_exhibit, ← present_exhibit,
    onSpanned Y H S s n m h]

-- takes ρ so `stage` construction is legal; actual q path from the single coherent history
-- NB Lean section inclusion mechanism.
lemma all_heights_here : Tendsto (P.stage ρ) atTop followStage :=
  tendsto_comap_iff.mpr P.history.growsA.tendsto_atTop
lemma limit_witness : Tendsto (fun z:ℕ => coupon P.run P.large S s (μ z) (ν z))
    atTop (𝓝 (ρ.loom S s)) :=
  (Exhibition.coneAdvance P.run P.large S s (P.talks ρ)).comp (P.all_heights_here ρ)

lemma evaluate_cont (m : Side) (x : Fields (P.calibration.c m)) :
    Continuous (fun f : Swatch S => render S K f m x) :=
  let T: Swatch S→ₗ[ℂ] FC (Single (P.calibration.c m)):= (LinearMap.proj (R:=ℂ) x).comp (appear S K m)
  (T.mkContinuous (spread S) (fun y=> renderLe S K m y x)).continuous

lemma block_convergence (f : Swatch S) (m : Side) (x : Fields (P.calibration.c m)) :
    Tendsto (fun z : ℕ => block P.run P.large s (μ z) (ν z) S (badge K S f).val m x) atTop
      (𝓝 ((badge K (S₊ S) (ρ.loom S s f)).val m x)) := by
  have U' : Tendsto (fun z:ℕ=> coupon P.run P.large S s (μ z) (ν z) f)
      atTop (𝓝 (ρ.loom S s f)) := cn_apply (X:=Swatch S) («Y»:=Swatch (S₊ S)) (P.limit_witness s S ρ) (tendsto_const_nhds (x:=f))
  have he:=((P.evaluate_cont (S₊ S) m x).continuousAt.tendsto.comp U')
  have hg:Tendsto (fun z:ℕ=>μ z) atTop atTop:=(P.law.pick.grow_i.comp P.history.growsA).tendsto_atTop
  refine he.congr' ?_
  filter_upwards [(P.all_heights_here ρ).eventually (Exhibition.cone_bill Y H S s (P.talks ρ)),
    hg.eventually (turning Y H (s+1) (S₊ S))] with n a b
  exact congrFun (congrFun (P.block_matches s S f _ _ a.1 b).symm m) x

lemma block_hist (F : Family K) (p : InTest K true S false F) (m : Side) (x : Fields (P.calibration.c m)) :
    Tendsto (fun z : ℕ => block P.run P.large s (μ z) (ν z) S F m x) atTop
      (𝓝 (P.projection.refine s F m x)) := by
  apply Metric.tendsto_nhds.mpr; intro ε e
  obtain ⟨u,h⟩:=valuation Y H p
  have ht : pay F u:=h; have hw:=pay_nonneg ht
  let v:= ε/(u+1); have hg: 0<v:=by dsimp [v]; positivity
  obtain ⟨_,_,f⟩:= P.history.implements s S
  filter_upwards [f v hg] with i hx; obtain ⟨_,_,t,_⟩ := hx F p u ht
  rw [dist_eq_norm]; refine lt_of_le_of_lt (t m x) ?_
  have he:v*(u+1)=ε:=div_mul_cancel₀ _ (by positivity); linarith
lemma identical_transfer (f : P.Test) : P.refineTest s f.val =
    (Tapestry.Exhibition.liftD P.run P.large s (P.talks ρ) f).val := by
  obtain ⟨S,u⟩:=findsBay K f
  obtain ⟨v,rfl⟩:= accolade K S f u
  rw [Tapestry.Exhibition.fromLocal]; funext m x
  exact tendsto_nhds_unique (P.block_hist s S (badge K S v).val (Tapestry.texture ..) m x)
    (P.block_convergence s S ρ v m x)
/-! Compact-operator bill now within the ground history. -/
lemma compact_lift : ∃ U : Swatch S→L[ℂ] Swatch (wingspan Λ ι S),
    U=ρ.loom S s ∧ IsCompactOperator U ∧ ∀ f : Swatch S, P.projection.refine s (badge K S f).val = (badge K (wingspan Λ ι S) (U f)).val := by
  refine ⟨_,rfl, Tapestry.Exhibition.compactBridge Y H S s (P.talks ρ), fun f=>?_⟩
  rw [show P.projection.refine=P.refineTest from rfl,P.identical_transfer s ρ,Tapestry.Exhibition.fromLocal]

abbrev promote : P.Test→ₗ[ℂ]P.Test:= Tapestry.Exhibition.liftD P.run P.large s (P.talks ρ)
lemma promotes_to (f : P.Test) : (P.promote s ρ f).val=P.projection.refine s f.val :=
  (P.identical_transfer s ρ f).symm
lemma gauge_promotion (u : GVertex) (f : P.Test) :
    P.promote s ρ (pennant K (parentGauge Λ u) f) = pennant K u (P.promote s ρ f):=
  Exhibition.pennantNatural ..
lemma promotes_read (f : P.Test) : P.reading j (s+1) (P.promote s ρ f)=P.reading j s f := by
  apply Subtype.ext; rw [at_label,at_label]
  unfold compressed
  have he : P.obs (P.promote s ρ f)=upward Y H P.history false (P.obs f) s ((s+1)-s) :=by
    apply Subtype.ext; rw [Nat.add_sub_cancel_left]; change (P.promote s ρ f).val=_; exact P.promotes_to s ρ f
  rw [he,cap_level Y H P.law s P.history P.projection.clipped j false (P.room j) (s+1) (by omega)]
lemma promotes_local (wide : Bool) (V : Set RSpace) {x : P.Test} (h : x∈ keep Λ P.width s K wide V) :
    P.promote s ρ x∈ keep Λ P.width (s+1) K true V := roofline _ _ _ wide _ (P.talks ρ) h
end Spine

-- Start directly from the joint election the question specifies, thinning at the allowed
-- place in its Universal and **retaining** all E and I; buy the dependent ground
-- extension after this.
theorem book (ε η : ℝ) (p : 0<η) : ∃ P : Spine,
    P.par.nominated (VolumeCape.Dream.Nimbus P.width) ∧ ε<P.par.x ∧ P.par.d ≤ η ∧
    ∃ (ρ : P.Register), SeasonCert P.run P.large ρ.exhibition ∧
      ∃ (q d w : ℕ) (Z C : ℝ), Papal.Cornet P.run P.large q d w C Z := by
  obtain ⟨Λ,l,Z,x,d,nom,H,Y,q,d',w,C,g,a,k,I,E,T,_,_⟩:=Papal.mixed_law_with_ground ε η p
  obtain ⟨u,v,L,B,T',t,h,e,W,A⟩:=chronicle Y H T
  let V:=W.univ_; obtain ⟨G⟩:= extend_ground Y H V; let P:Spine:=⟨Λ,l,Y,H,a∘u,k∘v,I,E,V,G⟩
  exact ⟨P,nom,x,d,⟨(L,B,T',t),W⟩,A,q,d',w,Z,C,g⟩
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.book
#check @YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.identical_transfer
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.identical_transfer
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.compact_lift
