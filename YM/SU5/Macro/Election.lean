import YM.SU5.Macro.Registration
import YM.SU5.Selected.PhaseRoad
import YM.SU5.Selected.Prag.Roof
import YM.SU5.Selected.Actress.Lode
import YM.SU5.Reconstruction.AlongHeat
/-!
# The very *chosen* Room, at any height formal construction, connected to the selected Hilbert

Sewing III: present the actual Slab GNS (`Selected.indoor`, hence CP-B) on the
chosen Root and eligibility; need not change price. These unitaries don't do Lorentz
rotation. See `the construction notes`. Batten of hypothesis exact at selection: internal
proof uses actual unitary here to port `Victory`. On FULL pre-spatial-C0 spaces.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 30000
set_option maxRecDepth 6000
set_option maxHeartbeats 440000
set_option quotPrecheck false
noncomputable section

namespace YM.CF.Buffered.Afterglow.Tower.Selection.Home
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark Vacancy SatinVerification
open Tapestry Tapestry.Altitude
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(H:Real.exp 1≤Λ.x)
local notation "K" => tent Y H
variable {i k:ℕ→ℕ}{I:ℕ→Family (tent Y H)→ℕ→ℂ}{E:ℕ→Family (tent Y H)→ℂ}
variable (V:Universal Y H i k I E) {D:ℕ→Family (tent Y H)→Family (tent Y H)} {a b:ℕ→ℕ}
    (Q:Coherent (i:=i) (k:=k) (E:=E) Y H D a b)(Qc:Clipped Y H (i∘a) (k∘b))
    (j:Axis)(r: Bool)(C : Arena Y H Q.circuit j 0 r)
open Tower.Selected
variable {χ:CapCharacter Y H V Q Qc j r C} (X:Birthplace Y H V Q Qc j r C χ)
local notation "P₀" => asDisplay Y H V Q Qc j r C χ
local notation "R₀" => indoor Y H V Q Qc j r C P₀
local notation "λ₀" i:max x:max=> markedActor Y H V Q Qc j r C X i x
local notation "λ₁" i:max x:max=> Selected.bud Y H V i Q Qc j r C P₀ x
local notation "φ" i:max => Tower.Field Y H i j 0 r
local notation "Ω₀" => Selection.vacuum Y H V Q Qc j r C X
local notation "Ω₁" => Selected.doorstep Y H V Q Qc j r C P₀
local notation:max "U" i:max t:max=> Raise Y H Q.circuit j 0 r i t

section
local notation "𝕋" => (Σ s:ℕ, Tower.Field Y H s j 0 r)
local notation "𝕋α" => (fun i:Σ s:ℕ, Tower.Field Y H s j 0 r => λ₀ i.1 i.2)
-- Avoid large elaborations matching the two dense-range pictures with membership in unions.

private lemma fibers {A:Type*}{X : ℕ → Type} [TopologicalSpace A] (f:(i:ℕ)→ X i→ A) (u:ℕ) (h:Dense (⋃ (i:ℕ) (_:u ≤ i), Set.range (f i))) : DenseRange (fun x:Σ s:ℕ, Σ' (_:u ≤ s), X s=> f x.1 x.2.2):= by
  refine h.mono ?_; intro x h; obtain ⟨i,v⟩:=Set.mem_iUnion.mp h; obtain ⟨p,z,e⟩:= Set.mem_iUnion.mp v; exact ⟨⟨i,p,z⟩,e⟩

private lemma fibers₀ {A:Type*}{X : ℕ→Type} [TopologicalSpace A] (f:(i:ℕ) → X i → A) (h:Dense (⋃ i:ℕ, Set.range (f i))) : DenseRange (fun x:Σ s:ℕ, X s=> f x.1 x.2):=by
  refine h.mono (fun x m=>?_); obtain ⟨i,z,e⟩:= Set.mem_iUnion.mp m; exact ⟨⟨i,z⟩,e⟩

private lemma fibers_t {A:Type*}{X : ℕ → Type} [TopologicalSpace A] (f:(i:ℕ)→ X i→ A) (u:ℕ) (h:Dense (⋃ (i:ℕ) (_:u ≤ i), Set.range (f i))) : DenseRange (fun x:Σ s:ℕ, X s=> f x.1 x.2):=
   (fibers f u h).mono (by rintro y ⟨⟨i,p,z⟩,rfl⟩; exact ⟨⟨i,z⟩,rfl⟩)
private lemma escorted : ∃ L : X.H.space ≃ₗᵢ[ℂ] (indoor Y H V Q Qc j r C P₀).space,
    ∀ i : Σ s:ℕ, Tower.Field Y H s j 0 r, L (λ₀ i.1 i.2)=λ₁ i.1 i.2:= by
  refine Selected.gram_impl (A:=X.H) (B:=R₀) (fibers_t (fun i x↦λ₀ i x) 0 (born_dense Y H V Q Qc j r C X 0)) (fibers₀ (fun i x↦ λ₁ i x) (stroll_dense Y H V Q Qc j r C P₀)) ?_
  intro i k
  let w:= max i.1 k.1; let p:= le_max_left i.1 k.1; let q:= le_max_right i.1 k.1
  let x:= U i.1 w p i.2; let y:= U k.1 w q k.2
  have hx: λ₀ i.1 i.2=λ₀ w x := (Selection.path Y H V Q Qc j r C X i.1 w p i.2).symm
  have hy: λ₀ k.1 k.2=λ₀ w y := (Selection.path Y H V Q Qc j r C X k.1 w q k.2).symm
  have hr: inner ℂ (λ₀ w x) (λ₀ w y)=inner ℂ (λ₁ w x) (λ₁ w y):=(affirmation Y H V Q Qc j r C X w x y).trans (Selected.earns Y H V w Q Qc j r C P₀ x y).symm
  have ht:λ₁ w x=λ₁ i.1 i.2:= Selected.flourishes Y H V i.1 Q Qc j r C P₀ w p _
  have hu:λ₁ w y=λ₁ k.1 k.2:= Selected.flourishes Y H V k.1 Q Qc j r C P₀ w q _
  exact (congrArg₂ (fun (x y:X.H)=> inner ℂ x y) hx hy).trans (hr.trans (congrArg₂ (fun (x y:R₀)=> inner ℂ x y) ht hu))

/-- Unitary equating all actual vectors from any compatible `Birthplace` to the one character
at the physical common axis. If reading that axis from any other one, rebase the cap character
and use *this* unitary at the new axis (not choosing a new character implicitly and this
is not a unitary between those two Birthplaces at the two different axes of the theory). -/
def register : X.H.space ≃ₗᵢ[ℂ] (indoor Y H V Q Qc j r C P₀).space:= (escorted Y H V Q Qc j r C X).choose
end
local notation "J" => register Y H V Q Qc j r C X
lemma register_actor (s:ℕ)(x:φ s) : J (λ₀ s x)=λ₁ s x:= (escorted Y H V Q Qc j r C X).choose_spec ⟨s,x⟩
lemma register_vac : J Ω₀=Ω₁ := (register_actor Y H V Q Qc j r C X 0 (unity Y H j 0 r 0)).trans (Selected.root Y H V 0 Q Qc j r C P₀)

local notation:max "Pπ" a:max=> Selected.procession Y H V Q Qc j r C P₀ a
/-- one density argument, any later resolving height. -/
lemma register_at (F:X.H.Op)(Z:(R₀).Op) (s:ℕ) (p:∀ t≥s, ∀ x:φ t, J (F (λ₀ t x))=Z (λ₁ t x)) (x:X.H) : J (F x)=Z (J x):= by
  have ht : Continuous (fun x:X.H=> J (F x)) := (J).continuous.comp F.continuous
  have hu : Continuous (fun x:X.H=> Z (J x)) := Z.continuous.comp (J).continuous
  have hi:= (fibers (fun i x↦ λ₀ i x) s (born_dense Y H V Q Qc j r C X s)).equalizer ht hu
  refine congrFun (hi ?_) x
  funext a
  exact (p a.1 a.2.1 a.2.2).trans (congrArg Z (register_actor Y H V Q Qc j r C X a.1 a.2.2).symm)

lemma register_width (s w:ℕ)(x:Entry Y H s j r w)(p:0<w)(z:X.H) :
    J (Actress.incubate Y H V Q Qc j r C X s w x p z)= Pπ (entrance Y H V s Q Qc j r C x p) (J z):=by
  let A:= Actress.incubate Y H V Q Qc j r C X
  refine register_at Y H V Q Qc j r C X (A s w x p) _ s ?_ z; intro t v y
  let x':= furnished Y H s Q j r w x t v; let w':= Λ.R.L.val^(t-s)*w; have vp:0 < w':= Nat.mul_pos (pow_pos Λ.R.L.property _) p
  let y':= slabT Y H t j r w' x' y
  have h : A s w x p (λ₀ t y)=λ₀ t y' := (DFunLike.congr_fun (Actress.sets Y H V Q Qc j r C X s w x p t v) _).trans (Actress.thrills Y H V Q Qc j r C X t w' x' vp y)
  exact (congrArg J h).trans ((register_actor Y H V Q Qc j r C X t y').trans (Selected.slot_high Y H V s Q Qc j r C P₀ x p t v y).symm)
lemma register_label (A:Actress.Label Y H j r)(x:X.H):
    J (Actress.Label.money Y H V Q Qc j r C X A x)= Pπ (entrance Y H V A.count Q Qc j r C A.appraise A.paid) (J x) := register_width ..

open OS.Semigroup MeshClock
local notation "Λ₀"=> timeMesh Λ
local notation "Vα"=> Diary.jetTime Y H V Q Qc j r C X
local notation "Vρ"=> Selected.ride Y H V Q Qc j r C P₀
lemma register_heat (k:ℝ≥0)(x:X.H) : J ((Vα).E k x)= (Vρ).E k (J x):=by
  let P:= Vα; let R:=Vρ
  have hu : Continuous (fun t:ℝ≥0=> J (P.E t x)):= (J).continuous.comp (P.continuousE _)
  refine congrFun ((fills (timeMesh Λ)).denseRange_val.equalizer hu (R.continuousE (J x)) ?_) k
  funext t; dsimp only [Function.comp_apply]; obtain ⟨s,i,e⟩:= MeshClock.split _ t.property
  let y:= whenly Λ₀ s i
  let G(u):= J (P.E u x); let F(u):= R.E u (J x)
  have h : G y = F y:=by
    refine register_at Y H V Q Qc j r C X (P.E y) (R.E y) s ?_ x; intro t v z
    let i':= MeshClock.acts Λ₀ s t i
    let y':= whenly Λ₀ t i'
    let u:= tick Y H t j 0 r (2*i') z
    have he : y'= y:= matchR Λ₀ s t i v
    have hp0: P.E y = walking Y H V Q Qc j r C X t (2*i'):= (congrArg P.E he.symm).trans ((journey Y H V Q Qc j r C X).track_even t i')
    have h' : P.E y (λ₀ t z)= λ₀ t u := (DFunLike.congr_fun hp0 (λ₀ t z)).trans (tempo_now Y H V Q Qc j r C X t (2*i') z)
    have hp : R.E y (λ₁ t z)= λ₁ t u := (congrArg (fun u=> R.E u (λ₁ t z)) he.symm).trans (Selected.ride_ticks Y H V t Q Qc j r C P₀ z i')
    exact (congrArg J h').trans ((register_actor Y H V Q Qc j r C X t u).trans hp.symm)
  exact (congrArg G e.symm).trans (h.trans (congrArg F e))

lemma register_edge (t:ℝ)(x:X.H) : J ((Vα).edge t x)= (Vρ).edge t (J x):= (Vα).intertwines_edge (Vρ) (J).toContinuousLinearEquiv.toContinuousLinearMap (register_heat Y H V Q Qc j r C X) x t
lemma register_complex (z:ℂ)(x:X.H)(h:0<z.re) : J ((Vα).F z x)= (Vρ).F z (J x):= (Vα).intertwines_F (Vρ) (J).toContinuousLinearEquiv.toContinuousLinearMap (register_heat Y H V Q Qc j r C X) x h
lemma register_balcony (z:ℂ)(x:X.H) : J (_root_.YM.Spectral.Alps.balcony (Vα) z x) = _root_.YM.Spectral.Alps.balcony (Vρ) z (J x):=by
  let a:= z.im.toNNReal; let b:=(Vα).E a
  exact (register_edge Y H V Q Qc j r C X z.re (b x)).trans (congrArg ((Vρ).edge z.re) (register_heat Y H V Q Qc j r C X a x))
local notation "Θ₀"=> Summer.Polaris Y H V Q Qc j r C X
local notation "Θ₁"=> Selected.turnstile Y H V Q Qc j r C P₀
lemma register_space (v:Trans j) (u:marks Λ₀)(x:X.H):
    J (((Θ₀).crew v).play u x)=((Θ₁).crew v).play u (J x):=by
  obtain ⟨s,i,e⟩:= notch_exists Λ₀ u
  let a:=(Θ₀).crew v; let b:=(Θ₁).crew v
  refine register_at Y H V Q Qc j r C X (a.play u) (b.play u) s ?_ x; intro t q z
  let i':= MeshClock.castor Λ₀ s t i; let w':= notch Λ₀ t i'; have he:w'=u:= (notch_up Λ₀ s t q i).trans e
  let V':= sail Y H t j 0 r v.val v.property (2*i') z
  have hx: a.play u (λ₀ t z)=λ₀ t V' := ((DFunLike.congr_fun ((congrArg a.play he.symm).trans (Summer.source_z Y H V Q Qc j r C X v t i')) _)).trans (travel_step Y H V Q Qc j r C X t v (2*i') z)
  have hb: b.play u (λ₁ t z)=λ₁ t V' := (DFunLike.congr_fun (congrArg b.play he.symm) _).trans (Selected.turnstile_in Y H V t Q Qc j r C P₀ z v i')
  exact (congrArg J hx).trans ((register_actor Y H V Q Qc j r C X t V').trans hb.symm)

open YM.SelectionAnalysis
local notation "Θ"=> bottom Y H V Q Qc j r C X
local notation "ρ"=> Selected.procession Y H V Q Qc j r C P₀
local notation "Φ"=> Selected.atCharacter Y H V Q Qc j r C P₀
local notation "ℓ"=> Selected.traveller Y H V Q Qc j r C
local notation "ε"=> YM.SelectionAnalysis.joint (ℓ) (ρ)
lemma register_joint (x:X.H): x∈ Θ ↔ J x ∈ ε:=by
 refine (Diary.staves Y H V Q Qc j r C X x).trans ((?_ : _ ↔ Selected.RealJoint Y H V Q Qc j r C P₀ (J x)).trans (Selected.true_joint Y H V Q Qc j r C P₀ _).symm)
 constructor
 · intro p; let z(v:Trans j)(u:marks Λ₀) : ((Θ₀).crew v).play u x=x:=
      let h:= notch_exists Λ₀ u; let s:= h.choose; let t:= h.choose_spec; let i:= t.choose; have e : u = notch Λ₀ s i:= t.choose_spec.symm;
      (DFunLike.congr_fun ((congrArg ((Θ₀).crew v).play e).trans (Summer.source_z Y H V Q Qc j r C X v s i)) _).trans (p.2 s v i)
   exact ⟨fun t=> (register_edge Y H V Q Qc j r C X t x).symm.trans (congrArg J (p.1 t)), fun v u=> (register_space Y H V Q Qc j r C X v u x).symm.trans (congrArg J (z v u))⟩
 · intro h
   exact ⟨fun i=> (J).injective ((register_edge Y H V Q Qc j r C X i x).trans (h.1 i)), fun i v u=>
     let w:= notch Λ₀ i u; have t : ((Θ₀).crew v).play w x=x:= (J).injective ((register_space Y H V Q Qc j r C X v w x).trans (h.2 v w)); (DFunLike.congr_fun (Summer.source_z Y H V Q Qc j r C X v i u) x).symm.trans t⟩

/-- The uniqueness hypothesis ports BOTH ways, not because all notions of
extremality buy Victory here but by our literal unitary intertwining. -/
theorem register_seal : LoneVac Y H V Q Qc j r C X ↔ Victory Y H V Q Qc r j C P₀:=by
  constructor
  · intro p
    have hp : SingleGround (Φ) (ℓ):= by
      intro i h
      let i': R₀ := i
      let k:= (J).symm i'
      have he0:J k=i':=(J).apply_symm_apply i'
      have hi: J k ∈ ε:= (congrArg (fun x:R₀=> x∈ε) he0).mpr h
      have hg := le_of_eq (show Θ = Submodule.span ℂ {Ω₀} from p) ((register_joint Y H V Q Qc j r C X k).2 hi)
      obtain ⟨z,e⟩:= Submodule.mem_span_singleton.mp hg
      have hu: z • Ω₁=J k:= ((congrArg (fun x:R₀=> z • x) (register_vac Y H V Q Qc j r C X).symm).trans (map_smul (J) z Ω₀).symm).trans (congrArg J e)
      exact ⟨z,hu.trans he0⟩
    exact ⟨hp,YM.SelectionAnalysis.single_is_extreme _ _ (Selected.travellers Y H V Q Qc j r C) (Selected.setupState Y H V Q Qc j r C P₀) hp⟩
  intro u
  refine le_antisymm ?_ (Submodule.span_le.mpr ?_)
  · intro x hx
    have hh:∃ i:ℂ,i • Ω₁=J x:= Selected.firm_door Y H V Q Qc j r C P₀ u _ ((register_joint Y H V Q Qc j r C X x).mp hx)
    obtain ⟨i,e⟩ := hh
    have he:J (i • Ω₀)=J x:= ((map_smul (J) _ _).trans (congrArg (fun x:R₀=> i • x) (register_vac Y H V Q Qc j r C X))).trans e
    exact Submodule.mem_span_singleton.mpr ⟨i,(J).injective he⟩
  exact Set.singleton_subset_iff.mpr (apt_floor Y H V Q Qc j r C X)
end YM.CF.Buffered.Afterglow.Tower.Selection.Home
open YM.CF.Buffered.Afterglow.Tower.Selection.Home
#print axioms register_heat
#print axioms register_edge
#print axioms register_complex
#print axioms register_balcony
#print axioms register_label
#print axioms register
#print axioms register_seal
