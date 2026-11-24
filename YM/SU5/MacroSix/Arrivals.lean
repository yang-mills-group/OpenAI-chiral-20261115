import YM.SU5.MacroSix.Stays

/-! # True positive-time Gram vectors

They can be priced all the way from the vacuum's projection space to the
positive-time `viewF` and `Portion` labels in the one character. Strong convergence
of the actual vectors for each such smear (before spectral multipliers). No positivity-space
claim for the mixed rectangle test; its prices come from the vacuum Schwinger kernel too
but not reflection Gram form.
-/

set_option autoImplicit false
set_option maxHeartbeats 420000
set_option maxRecDepth 4000
set_option synthInstance.maxSize 28000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory
  RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder
  InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance Aria
open _root_.YM.MacroSix
namespace Spine
variable (P : Spine) (R : P.Register) (s n t : ℕ) (Z : Window.Family) (x : P.Spectrum0 3)
local notation "M" => P.otherSpectrum 3 3 x
local notation "E" => (P.physicalEnergy 3 (P.advocate 3 x 3)).E
local notation "G" => P.ColorHil 3 M
local notation "B" => P.sixBody s n Z
local notation "K" => P.calibration
local notation "k" => P.viewF 3 M t
local notation "μ" => P.birthF 3 t
local notation "T" => P.openField s n Z x
local notation "m" => P.meshSize t
local notation "Ω" => P.heaven 3 M
local notation "ω" => P.colorZero 3 M
local notation "F₀" => P.sixWidth s n
local notation "w" => P.sixWidth s n 3
local notation "Λ" => P.par

lemma pane : P.enter 3 M (P.heaven 3 M)=P.colorZero 3 M ∧
    P.wealth 3 M (P.colorZero 3 M)=P.heaven 3 M ∧
    (P.enter 3 M).toContinuousLinearMap.comp (P.wealth 3 M)=(P.Viewers 3 M).starProjection :=
  ⟨rfl,P.stone_mark ..,P.visitors_op 3 M⟩

def inFuture (u : P.Test) (v : P.ColorHil 3 (P.advocate 3 x 3)) :=
  ∃ p : P.birthF 3 t u,P.viewF 3 (P.advocate 3 x 3) t p=v
local notation "A"=> P.inFuture t x
namespace inFuture
local notation "δ" => P.stateVoxLinear 3 M t
variable (u v:P.Test) (f g : P.ColorHil 3 (P.otherSpectrum 3 3 x))
lemma sum (p:A u f)(q:A v g): A (u+v) (f+g) := by
  let h:= p.choose; let d:=q.choose
  let a:= P.emmigrant 3 t h
  let b:= P.emmigrant 3 t d
  have hp : P.voxTest 3 t a.val=u:=P.documented 3 t h
  have hd : P.voxTest 3 t b.val=v:=P.documented 3 t d
  have h' : P.voxTest 3 t (a.val + b.val) = u+v:= congrArg₂ (· + ·) hp hd
  let c : P.naturalVox 3 t:= ⟨a.val+b.val,(enclave K).add_mem a.property b.property⟩
  have hv : μ (u+v):=⟨c,h'⟩
  let U:= P.gnsIn 3 M
  refine ⟨hv,(P.holdsF 3 M t hv c h').trans (U.injective ?_)⟩
  have hx : U f=δ a.val:= (congrArg U p.choose_spec.symm).trans (P.coincides 3 M a)
  have hg : U g=δ b.val:= (congrArg U q.choose_spec.symm).trans (P.coincides 3 M b)
  exact (P.coincides 3 M c).trans ((map_add δ a.val b.val).trans ((congrArg₂ (·+·) hx.symm hg.symm).trans
    (map_add U f g).symm))
lemma amp (p:A u f) (r : ℂ): A (r • u) (r • f) := by
  let h:= p.choose; let a:= P.emmigrant 3 t h
  let b:P.naturalVox 3 t:= ⟨r • a.val,(enclave K).toSubmodule.smul_mem _ a.property⟩
  have he : P.voxTest 3 t b.val = r • u := congrArg (fun v=> r • v) (P.documented 3 t h)
  have hd : μ (r • u):=⟨b,he⟩
  let U:= P.gnsIn 3 M; have hv: U f=δ a.val:= (congrArg U p.choose_spec.symm).trans (P.coincides 3 M a)
  refine ⟨hd,(P.holdsF 3 M t hd b he).trans (U.injective ?_)⟩
  exact (P.coincides 3 M b).trans ((map_smul δ r a.val).trans ((congrArg (fun x=> r • x) hv.symm).trans
    (map_smul U r f).symm))
lemma darkens : A 0 0 := by
  have p : A 1 ω:=⟨P.faceUnit ..,P.view_one ..⟩
  have he : A ((0:ℂ) • (1:P.Test)) ((0:ℂ) • ω) := amp P t x _ _ p 0 -- spacing
  simpa only [zero_smul] using he
variable {I : Type*} (r : Finset I) (U : I→P.Test)(V : I → P.ColorHil 3 (P.otherSpectrum 3 3 x))
lemma summing (h : ∀ i∈r, A (U i) (V i)) :
    A (∑ i∈r, U i) (∑ i∈r, V i) := by
  classical
  induction r using Finset.cons_induction with
  | empty => simpa using darkens P t x
  | cons a r e ih=>
    rw [sum_cons,sum_cons]; exact sum P t x _ _ _ _ (h _ (mem_cons_self ..))
      (ih (fun i t ↦ h i (mem_cons_of_mem t)))
end inFuture

variable (b : Cover) (p : s ≤ t)
include p
local notation "M₀"=> timeMesh P.par
local notation "F'"=> (P.fieldAt t B b)
local notation "f'"=> P.nativeLight s n t Z 0 x true b
local notation "L"=> P.pose t b
local notation "U"=> P.truck 3 M
local notation "τ" i:max=> Real.toNNReal i

lemma fieldAtFuture (h : (P.sixWidth s n 3:ℝ) ≤ P.pose t b 3) : P.inFuture t x F' (f') := by
  let Z₀:= ω
  let v:Unit → Cover:= fun _ ↦ b
  let Q : Unit → P.Apron:=fun _ ↦ B
  let O: Unit:= (); let d:= P.firstLeg 3 t Q v O
  let C:= P.vtile t b; let f:= P.vtile t ∘ v
  let D := P.fullScroll t Q v [O]; let g:= P.porchY 3 Q (P.laysM ∘ f) O
  let e:= E
  have hi : bell M₀ t d=g:= P.begins 3 Q v t O p
  have hg : g=P.pose t b 3-(w:ℝ):= by
    unfold g porchY Apron.time_panel Q
    rw [P.sixBody_width]; rfl
  have hw : bell M₀ t 0=0:= by unfold bell; rw [Int.cast_zero,zero_mul]
  have hp : 0 ≤ d:= (bell_le ..).mp ((hw.trans_le (hg ▸ sub_nonneg.mpr h)).trans_eq hi.symm) -- equality dir
  have hb : D= F':=mul_one _
  obtain ⟨g',u⟩:= P.vread 3 M t Q v [O] 0 (show _ from ⟨hp,trivial⟩) (fun _ _ ↦ p)
  have h' : P.shifts 3 (-0) D= F':=(show P.shifts 3 (-0) D=D by rw [neg_zero,P.shifts_zero]).trans hb
  have he : μ F':= h' ▸ g'
  refine ⟨he,(P.identical_F 3 M t he g' h'.symm).trans (u.trans ?_)⟩
  have hz:= P.transporting 3 M Q v t [O] 0 ⟨hp,trivial⟩ (fun _ _ ↦ p)
  apply hz.trans
  let J:= (B).engine P 3 M
  have hn(r : ℝ≥0) (v:G) : P.truck 3 M C ((e r) v)=(e r) (P.truck 3 M C v):=
    DFunLike.congr_fun ((P.voyageF 3 M).hard (look 3) ((P.physicalEnergy 3 M).E r)
      (fun i _ z ↦ P.colorMoveE 3 M i z r) (C ∘ Subtype.val)) v
  let a' : ℝ≥0:= (g - bell M₀ t 0).toNNReal
  let x':= timeWeight 0 L true
  have hj : a'+w=x' := by
    ext; push_cast; unfold x' timeWeight; rw [Real.coe_toNNReal,Real.coe_toNNReal]
    · simp only [hw,hg,if_true,sub_zero,sub_add_cancel]
    · have hj: 0 ≤ (w:ℝ) := NNReal.coe_nonneg _; change 0 ≤ if true=true then L 3-0 else 0-L 3 ; rw [if_pos rfl,sub_zero]; exact hj.trans h
    rw [hg,hw]; linarith
  let J':= (U) C
  change e a' (J' (J ((P.truck 3 M (-C)) Z₀))) = J' (e x' T)
  exact (congrArg (fun u:G ↦ e a' (J' u)) ((congrArg J (P.truck_empty 3 M (-C))).trans
    (P.bodyEngine_paid s n Z x))).trans ((hn a' ((e w) T)).symm.trans
      (congrArg J' ((HeatTwo.combine_heat G (P.physicalEnergy 3 M) T a' w).trans
        (congrArg (fun u : ℝ≥0 ↦ e u T) hj))))

omit p
-- API positive-time only and at unmasked x; apply with s,n(c i, r i) etc.
variable (f : Vantage→ℝ) (u : ∀ i∈ tsupport f, (P.sixWidth s n 3 : ℝ) ≤ i 3)(q : HasCompactSupport f)
local notation "W₀" r:max => P.smearField r f B
local notation "W'" r:max => P.weighLight s n r Z f 0 x true

include u q
lemma smoothFutures (p : s ≤ t) : P.inFuture t x (P.smearField t f B) (P.weighLight s n t Z f 0 x true) := by
  have he:= P.pose_finite t f q; let r:= he.toFinset
  unfold smearField weighLight
  rw [finiteTest_sum _ _ _ he.toFinset (by simp),finiteTest_sum _ _ _ he.toFinset (by simp)]
  refine inFuture.amp P t x _ _ (inFuture.summing P t x _ _ _ ?_) _
  intro i v; rw [Set.Finite.mem_toFinset] at v
  exact inFuture.amp P t x _ _ (P.fieldAtFuture s n t Z x i p (u _
    (subset_tsupport _ (show f (P.pose t i) ≠ 0 from v)))) _

lemma viewStrongLimit (J : P.Ellis 3 x) (h : Continuous f) :
    ∃ a : ℕ → P.ColorHil 3 M, (∀ t:ℕ, ∀ p:s≤t, P.inFuture t x (P.smearField t f B) (a t)) ∧
    Tendsto a atTop (𝓝 (P.enter 3 (P.advocate 3 x 3) (P.darkSmear s n Z f 0 x true))) :=
  ⟨fun i ↦ W' i,fun i p ↦ P.smoothFutures _ _ _ Z x f u q p,P.frameLight_limit s n Z f 0 x h q true J⟩
-- ↑ exactly `weighLight` at all t including pre-elected not necessarily p
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
#print axioms fieldAtFuture
#print axioms pane
#print axioms viewStrongLimit
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
