import YM.SU5.Selected.Identify
import Mathlib.Analysis.Normed.Operator.Banach
/-!
# Compact swatches really do parametrize the slab operators

Here S is any *fixed* local support at any fixed resolution. Even though wide
labels include arbitrary Borel inputs of the qualified kind, in particular spaces for which a
countable set of rational polynomials is not known to determine the reads, every real slab lifts
to the next fixed resolution with the SAME operator and with supported mark drawn from a relatively
compact set there (if on bounded balls here). Also the upper stage fits the new width! Thus we can
buy separability of the actual slab operator algebra in norm, using the compactness of the *step*
from the **same** signed election. No uniqueness of histories required.
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
lemma compactOp_separable {X Z : Type*}[NormedAddCommGroup X] [NormedSpace ℂ X]
    [NormedAddCommGroup Z] [NormedSpace ℂ Z] (T : X →L[ℂ] Z) (p : IsCompactOperator T) :
    IsSeparable (Set.range T) := by
  refine IsSeparable.mono (s:=⋃ n : ℕ, T '' closedBall 0 (n:ℝ)) ?_ ?_
  · apply IsSeparable.iUnion; intro n
    obtain ⟨K,h,s⟩:= (show IsCompactOperator T.toLinearMap from p).image_closedBall_subset_compact (n:ℝ)
    exact h.isSeparable.mono s
  rintro _ ⟨x,rfl⟩; obtain ⟨n,h⟩:=exists_nat_ge ‖x‖; exact Set.mem_iUnion.mpr ⟨n, x,by simpa using h,rfl⟩

namespace Spine
variable (P : Spine)(j : Axis)(s w : ℕ) (hw : 0<w)
local notation "K"=> P.calibration
local notation "π"=> P.history
local notation "V"=> P.law
local notation "Y"=> P.run
local notation "H"=> P.large
local notation "Qt"=> P.projection.clipped
local notation "L"=> P.par.R.L.val
local notation "C₀"=> P.room j
local notation "B" x:max=> P.Box j s w hw x
local notation "μ" t:max => L^(t-s)*w
local notation "κ" t:max => P.piece j t
local notation "T" p:max f:max=> slabT Y H _ j false _ (furnished Y H s π j false w f _ p)

lemma extend_box (f : P.Card j s w) (t : ℕ) (p : s≤ t) (z : P.Vox j t) :
    ((T p f) z).val = stream Y H P.projection.refine s (t-s) f.val.val *
      relocate K j ((μ t : ℕ) : ℤ) z.val := slab_eq ..

lemma box_linear (f g h : P.Card j s w) (a : ℂ) (p : h.val.val = a • f.val.val+g.val.val) :
    P.Box j s w hw h=a • P.Box j s w hw f+P.Box j s w hw g := by
  apply test_high Y H V s π j false C₀
  intro i l z
  change (B h) ((κ i) z)=a • (B f) ((κ i) z)+(B g) ((κ i) z)
  simp only [Box, snatch Y H V s π Qt j false C₀ w _ hw l z]
  have he : (T l h) z= a • ((T l f) z)+ ((T l g) z):=by
    apply Subtype.ext; change ((T l h) z).val = a • ((T l f) z).val+ ((T l g) z).val
    rw [P.extend_box,P.extend_box,P.extend_box,p,
      woven_add Y H P.history.circuit s _ ((test_entry Y H s j false f).scale a) (test_entry Y H s j false g),
      woven_smul Y H P.history.circuit s _ (test_entry Y H s j false f),add_mul, Algebra.smul_mul_assoc]
  -- rw with hidden reductions
  change (κ i) ((T l h) z)= a • ((κ i) ((T l f) z))+ (κ i) ((T l g) z)
  rw [he,P.piece_linear]

lemma box_zero (f : P.Card j s w) (h : f.val.val=0) : P.Box j s w hw f=0 := by
  have he := P.box_linear j s w hw f f f 1 (by rw [h]; module)
  simpa using he

variable (S : Finset Cover) (p : Between P.calibration j 0 (ruler P.par.block*w) S)
local notation "Z" t:max=> volumeAround P.par P.width (t-s) S
noncomputable def openingCard (x : Swatch S) : P.Card j s w :=
  ⟨P.positiveVox j s S (badge K S x) (locatesBadge ..) (fun i h=> (p i h).1), S,Tapestry.texture ..,p⟩
noncomputable def localBoxₗ : Swatch S →ₗ[ℂ] (P.Hil j).Op where
  toFun x:= P.Box j s w hw (P.openingCard j s w S p x)
  map_add' x y:=by
    let f:=P.openingCard j s w S p
    refine (P.box_linear j s w hw (f x) (f y) _ 1 ?_).trans ?_
    · rw [one_smul]; exact map_add (render _ K) x y
    rw [one_smul]
  map_smul' a x:=by
    let v:=P.openingCard j s w S p 0
    have gv:v.val.val=0:=map_zero (render _ _)
    refine Eq.trans (P.box_linear j s w hw (P.openingCard j s w S p x) v _ a ?_) ?_
    · rw [gv,add_zero]; exact map_smul (render S K) a x
    rw [P.box_zero j s w hw v gv, add_zero,RingHom.id_apply]


lemma signed_coeff (t : ℕ) (b : s ≤ t) (a x : P.Vox j t) : ∃ A : ℝ,
    ∀ f : Swatch S, ‖inner ℂ ((κ t) a) (P.localBoxₗ j s w hw S p f ((κ t) x))‖ ≤ A*‖f‖ := by
  let g:=mirror K j 0 a.val
  let y:=relocate K j ((μ t:ℕ):ℤ) x.val
  obtain ⟨G,h⟩:= (reflect_ok K j 0 (field_test Y H t j 0 false a)).paid
  obtain ⟨Y₀,q⟩:= (move_ok K j ((μ t:ℕ):ℤ) (field_test Y H t j 0 false x)).paid
  obtain ⟨C,c,Gf⟩:=fares Y H s π S (t-s)
  obtain ⟨_,u⟩ := (Gf 1 zero_lt_one).exists
  obtain ⟨Ca,ta⟩:= valuation Y H h; have ua : pay g Ca:= ta
  obtain ⟨Cx,tx⟩:= valuation Y H q; have ux : pay y Cx:= tx
  let Q:= G ∪ ((Z t) ∪ Y₀)
  let W:=toll Y H t Q
  refine ⟨W*(Ca*C*spread S*Cx),fun f=>?_⟩
  let F:=P.openingCard j s w S p f
  change ‖inner ℂ _ ((boxOp Y H V s π Qt j false C₀ w F hw) _)‖≤_
  rw [snatch Y H V s π Qt j false C₀ w _ hw b, P.seed_pairing, extend_box]
  let A:=stream Y H P.projection.refine s (t-s) F.val.val
  have hf: InTest K true S false F.val.val:= Tapestry.texture ..
  have hr : pay A (C*(spread S*‖f‖)) := (u _ hf (spread S*‖f‖) (fun i x=>renderLe S K i f x)).1
  have ha : InTest K true (Z t) false A:= (proceeds Y H P.history.circuit s (t-s) hf).1
  have ht : InTest K true Q false (g*(A*y)):= by
    have hh: InTest K true ((Z t) ∪ Y₀) false (A*y) := (ha.mono subset_union_left).mul (q.mono subset_union_right)
    exact (h.mono subset_union_left).mul (hh.mono subset_union_right)

  exact (E_bound Y H V t Q ht (pay_mul ua (pay_mul hr ux))).trans_eq (by unfold W; ring)


lemma basis_extₗ (D F : (P.Hil j).Op) (e : ∀ t, s ≤ t → ∀ x y : P.Vox j t,
    inner ℂ ((κ t) y) (D ((κ t) x)) = inner ℂ ((κ t) y) (F ((κ t) x))) : D=F := by
  apply test_high Y H V s π j false C₀
  intro t p x
  apply all_voices Y H P.history.circuit j 0 false C₀
  intro r y; let m:=max t r; let ht:=le_max_left t r; let hr:= le_max_right t r
  have hi := e m (p.trans ht) (Raise Y H P.history.circuit j 0 false t m ht x)
      (Raise Y H P.history.circuit j 0 false r m hr y)
  unfold piece at hi; rwa [join_actor Y H V,join_actor Y H V] at hi

noncomputable def pairing (t : ℕ) (x y : P.Vox j t) : (P.Hil j).Op →L[ℂ] ℂ :=
   (innerSL ℂ ((κ t) y)).comp (ContinuousLinearMap.apply ℂ (P.Hil j) ((κ t) x))

/-- No tacit assumption that the box map is controlled by a formal norm.
    Prove continuity from its full-domain linear existence and closed graph. -/
lemma bounded_insert : Continuous (P.localBoxₗ j s w hw S p) := by
  let D:= P.localBoxₗ j s w hw S p
  refine LinearMap.continuous_of_seq_closed_graph (𝕜:=ℂ) (E:=Swatch S) (F:=(P.Hil j).Op) D ?_
  intro u x y hx hy; apply P.basis_extₗ j s y (D x)
  intro t e a b
  let φ:= P.pairing j t a b
  let T0:= φ.toLinearMap.comp (P.localBoxₗ j s w hw S p)
  obtain ⟨f,h⟩:= P.signed_coeff j s w hw S p t e b a
  let Z': Swatch S →L[ℂ] ℂ := T0.mkContinuous f h
  exact tendsto_nhds_unique ((φ.continuous.tendsto _).comp hy) ((Z'.continuous.tendsto _).comp hx)
noncomputable def localBox : Swatch S →L[ℂ] (P.Hil j).Op where
  toLinearMap:= P.localBoxₗ j s w hw S p
  cont := P.bounded_insert j s w hw S p
abbrev carrying_w : ℕ := P.par.R.L.val^(s+1-s)*w
include p in
lemma expanded : Between K j 0 (ruler P.par.block*P.carrying_w s w) (wingspan P.par P.width S):=by
  let u:=expands_shape Y H p 1; unfold carrying_w; rw [Nat.add_sub_cancel_left,Nat.cast_mul,Nat.cast_pow,mul_left_comm]; exact u
include hw in
lemma carrying_pos : 0<P.carrying_w s w:=mul_pos (pow_pos P.par.R.L.property _) hw
variable (ρ : P.Register)
lemma represented (x : Swatch S) :
    P.localBox j s w hw S p x=P.localBox j (s+1) (P.carrying_w s w)
      (P.carrying_pos s w hw) (wingspan P.par P.width S) (P.expanded j s w S p) (ρ.loom S s x) := by
  let C:=P.openingCard j s w S p x; unfold localBox
  change B C=P.Box j (s+1) _ (P.carrying_pos s w hw) _
  rw [Box,refined_box Y H V s π Qt j false C₀ w C hw (s+1) (by omega)]
  apply congrArg (P.Box j (s+1) (P.carrying_w s w) (P.carrying_pos s w hw)); apply Subtype.ext; apply Subtype.ext
  obtain ⟨_,rfl,_,h⟩:= P.compact_lift s S ρ
  change stream Y H P.projection.refine s (s+1-s) (badge K S x).val=(badge K (wingspan P.par P.width S) (ρ.loom S s x)).val
  rw [Nat.add_sub_cancel_left]; exact h x
include ρ
lemma compact_boxes : IsCompactOperator (P.localBox j s w hw S p) := by
  let T0:= P.localBox j (s+1) (P.carrying_w s w) (P.carrying_pos s w hw) _ (P.expanded j s w S p)
  have h : P.localBox j s w hw S p=T0.comp (ρ.loom S s):=by ext1 i; exact P.represented j s w hw S p ρ i
  rw [h]; exact (Tapestry.Exhibition.compactBridge Y H S s (P.talks ρ)).continuous_comp T0.continuous
lemma boxes_separable : TopologicalSpace.IsSeparable (Set.range (P.Box j s w hw)) := by
  let D:= fun (S:Finset Cover)(h:Between K j 0 (ruler P.par.block*w) S) => Set.range (P.localBox j s w hw S h)
  have Hd(S:Finset Cover)(h:Between K j 0 (ruler P.par.block*w) S): IsSeparable (D S h):=
    compactOp_separable (X:=Swatch S) («Z»:=(P.Hil j).Op) (P.localBox j s w hw S h) (P.compact_boxes j s w hw S h ρ)
  have he: IsSeparable (⋃ (S:Finset Cover) (h:Between K j 0 (ruler P.par.block*w) S), D S h) :=
    IsSeparable.iUnion (fun S=>IsSeparable.iUnion (Hd S))
  refine IsSeparable.mono he ?_
  rintro y ⟨x,rfl⟩; obtain ⟨U,h,t⟩:=x.property
  obtain ⟨f,hf⟩:= Tapestry.rendered U K h
  have hi:P.openingCard j s w U t f=x:= Subtype.ext (Subtype.ext hf)
  exact Set.mem_iUnion.mpr ⟨U,Set.mem_iUnion.mpr ⟨t, f,congrArg (P.Box j s w hw) hi⟩⟩
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
#check @YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.represented
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.bounded_insert
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.represented
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.boxes_separable
