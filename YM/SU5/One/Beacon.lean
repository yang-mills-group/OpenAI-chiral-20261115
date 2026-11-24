import YM.SU5.One.Matter

/-!
# Identify the actual survival test with two gauge-invariant resolution-observable cells

Including physical locations, contact/advance interpretation. Nonproduct is
for the same reader, explained in `Refraction`. Not a clustering-failure
claim or the stronger Heisenberg/spacelike claims.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 30000
set_option maxRecDepth 6000
set_option maxHeartbeats 300000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.One
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Branch
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark Vacancy SatinVerification Tapestry PhaseChoice Altitude
open Selected

/-! Point on the rotor; always use same specified character. -/
variable {Λ : Preparation} {l : ℕ} (Y : Course Λ (VolumeCape.Dream.Nimbus l)) (H : Real.exp 1 ≤ Λ.x)
local notation "K"=> tent Y H
variable {i k:ℕ→ℕ} {I:ℕ→Buffered.Family (tent Y H)→ℕ→ℂ} {E:ℕ→Buffered.Family (tent Y H)→ℂ} (V: Universal Y H i k I E)
    (G: GroundExtension (i:=i) (k:=k) (E:=E) Y H) {L:Tapestry.Rack Λ l}{B:Tapestry.Clay Λ l}
    (D: Exhibition Y H i k I E L B)
variable (d : Axis) (S : ∀ j:Axis,Arena Y H G.history.circuit j 0 false)
local notation "𝔄" j:max=> displayAlgebra Y H V G.history G.clipped j false (S j)
variable (c : displayAlgebra Y H V G.history G.clipped d false (S d) →⋆ₐ[ℂ] ℂ)
local notation "C"=> SameCharacter.resident Y H V G d false (S d) c
local notation "Θ"=> onDrawing Y H V G D d S C
local notation "Mx"=> evaluate Y H V G d S C
local notation "r" j:max=> displacement Y H V G.history G.clipped d false (S d) c j (S j)
local notation "R" j:max t:max=> Selected.response Y H V t G.history G.clipped j false (S j) (r j)

lemma spinLoan (j:Axis) (n:ℕ) (f:Selected.Marks (tent Y H) false) :
    (R j n) f=Mx n f.val:=by
  rw [across_response]; exact (SameCharacter.sameReading Y H V G d false (S d) c n f).symm.trans (evaluates Y H V G d S _ n f).symm

lemma pinholeResponse (j:Axis) (n:ℕ)(f:Dome (tent Y H)): Θ (pinhole (Dome K) n f) =
    pigmentReading Y H V n G.history G.clipped j (S j) (r j) f.val:= by
  rw [plugged]
  let F:Selected.Marks K false:= observe (show TestFamily K true f.val from f.property)
  exact (spinLoan Y H V G d S c j n F).symm.trans (reads_color Y H V n G.history G.clipped j (S j) _ F).symm

/-- Beam of a strict mark. This pins HOW the limit polynomial corresponds to
its source mark for both actual evaluation and the transfer. -/
abbrev photograph (s:ℕ)(f:Marks (tent Y H) true) := pinhole (Dome (tent Y H)) s (resolutionProbe Y H f)
lemma negative_source {s:ℕ} {w:Bool}{W:Finset Cover}(f:Marks K true) (p:InTest K w W false f.val):
    photograph Y H s f∈ observatory Y H w s (cells Λ l s W):=
  oneSlotWell Λ K l w (handstamp (cells Λ l s W)) (Set.univ∩Set.Iic s) s
    (show s∈ Set.univ∩Set.Iic s from ⟨Set.mem_univ _, Set.mem_Iic.mpr le_rfl⟩)
    ((keeps ..).mpr ⟨_,(Tapestry.locates ..).mpr p,supported_cells Λ l s W⟩)
    -- CovCover is Neutral
    ((enclave_spec K).mpr (f.property.2 rfl))
lemma photos_multiply (s:ℕ)(f g: Marks (tent Y H) true): photograph Y H s (f*g)= photograph Y H s f * photograph Y H s g:=by
  unfold photograph; have he: resolutionProbe Y H (show Marks (tent Y H) true from f*g)= resolutionProbe Y H f * resolutionProbe Y H g:=rfl -- check obj expr
  rw [he,map_mul]
lemma photo_response (s:ℕ)(f:Marks (tent Y H) true)(j:Axis):
    Θ (photograph Y H s f)=(R j s) (bosonLabel K f):= (plugged ..).trans ((spinLoan Y H V G d S c j s (bosonLabel K f)).symm)

lemma photograph_stays {s:ℕ} (f:Marks K true)(t:ℕ): Θ (photograph Y H (s+t) (upward Y H G.history true f s t))= Θ (photograph Y H s f):= by
  rw [photo_response Y H V G D d S c _ _ d, photo_response Y H V G D d S c _ _ d]
  exact moves_up Y H V _ G.history G.clipped d false _ _ (bosonLabel K f) t

section stencil
variable {J:Calibration}{w:Bool}{f : Family J}{W : Finset Cover}
lemma cadTest (v:Cover)(p:List Axis)(h:InTest J w W false f):
    InTest J w (drivePlot v J p W) false (cad J p v f):=by
  induction p with | nil=> exact h | cons i t ih=> exact flow_port J i _ ih
end stencil

section display
open CF.Pannier.Chancel
variable (s:ℕ)(X₁:Finset Cover)(j:Axis)(p q:Cover)
local notation "Lw" a:max f:max=> relocateWorld Y H true a f
local notation "X₊"=> streetBox K q X₁
local notation "X₋"=> reflectedBox j 0 (streetBox K p X₁)
local notation "U"=> cells Λ l s X₊
local notation "W"=> cells Λ l s X₋
local notation "Θw" f:max=> mirrorInMarks Y H j true f
local notation "Θ₀" p:max f:max=> Θw (Lw p f)
variable (f : Marks (tent Y H) true)
local notation "m"=> Θ₀ p f
local notation "n"=> Lw q f
local notation "x"=> photograph Y H s m
local notation "y"=> photograph Y H s n
variable {u k₀ : ℕ}{o:Cover}{δ:ℝ}{z:SU.Slot}
local notation "Mk" v:max Q:max=> (show Marks K true from upward Y H G.history true Q s v)

-- cells supports at one fixed physical separation.
structure Lantern (δ:ℝ)(o:Cover)(u k₀:ℕ)(z:SU.Slot): Prop where
 sources : f.val∈ Filigree K (Window.family z) (booty o k₀ u) X₁
 aperture : (m).val∈ observ (tent Y H) (X₋) false ∧ (n).val∈ observ (tent Y H) (X₊) false
 tied : photograph Y H s ((m)*(n)) = x*y
 exposed : x∈ observatory Y H false s (W) ∧ y∈observatory Y H false s (U) ∧
   x*y ∈ observatory Y H false s (W∪U)
 local_support : IsCompact W ∧ IsCompact U ∧ Disjoint W U ∧ ∀ (a b : RSpace)(i:Axis),a∈ W → b∈ U → a i+δ≤ b i
 widened (t : ℕ) :
   SupportedPhysically Λ l (s+t) (volumeAround Λ l t X₊) U ∧
   SupportedPhysically Λ l (s+t) (volumeAround Λ l t X₋) W ∧
   x*y∈ observatory Y H true (s+t) (W∪U) ∧
   (Mk t m).val ∈ observ (tent Y H) (volumeAround Λ l t X₋) true ∧
   (Mk t n).val ∈ observ (tent Y H) (volumeAround Λ l t X₊) true
 paired (t:ℕ) : ((Mk t m)*(Mk t n):Marks K true).val = (Mk t (m*n)).val
 estimate (t:ℕ) : 1/32 ≤ ‖Θ (x*y)‖ ∧ (R j (s+t)) (bosonLabel K ((Mk t m)*(Mk t n):Marks K true))=Θ (x*y)
 -- Not a nonzero connected value claim. Pair witnesses this failure (would be exactly 0 for `RemoteSplit`, keeps >=1/32)
 fails : ¬ RemoteSplit j K p q X₁ (booty o k₀ u) (Window.family z) (Mx s)
 through : Exceeds Y H V s G.history G.clipped j (S j) (r j) δ f z X₁ o u k₀ p q

lemma observing_more {mm t : ℕ}{a:Bool} {V : Set RSpace} (h:t ≤ mm):observatory Y H a t V ≤ observatory Y H true mm V:=
 le_trans (wellWider Λ K l a (handstamp V) (Set.univ ∩ Set.Iic t)) (wellGrows Λ K l true (handstamp V) _ (Set.univ ∩ Set.Iic t) (Set.univ∩ Set.Iic mm) (fun i v=>⟨v.1,(le_trans (show i≤t from v.2) h)⟩) Set.Subset.rfl)

lemma displays (a : Exceeds Y H V s G.history G.clipped j (S j) (r j) δ f z X₁ o u k₀ p q)
    (b : f.val∈ Filigree K (Window.family z) (booty o k₀ u) X₁):
    Lantern Y H V G D d S c s X₁ j p q f δ o u k₀ z:= by
  let h:=a.shelf
  have he:= FilTest b
  have hv(t:Cover): InTest (tent Y H) false (streetBox K t X₁) false (Lw t f).val:=by rw [world_val]; exact cadTest t _ he
  have hu : InTest (tent Y H) false X₋ false (m).val:= axial K j 0 (hv p)
  have Hx:= negative_source Y H (s:=s) m hu; have Hy:= negative_source Y H (s:=s) n (hv q)
  have hx : (m).val∈ observ (tent Y H) (X₋) false:= (obs_in ..).2 ⟨hu,(m).property.2 rfl⟩
  have hY : (n).val∈ observ (tent Y H) (X₊) false:= (obs_in ..).2 ⟨hv q,(n).property.2 rfl⟩
  have Hw:= (observatory Y H false s (W∪U)).mul_mem (wellGrows Λ K l false (handstamp W) _ _ _ Set.Subset.rfl (Set.preimage_mono Set.subset_union_left) Hx) (wellGrows Λ K l false (handstamp U) _ _ _ Set.Subset.rfl (Set.preimage_mono Set.subset_union_right) Hy) -- names
  have hstar: Θ (x*y)= (R j s) (bosonLabel K ((m)*(n))) := by rw [←photos_multiply]; exact photo_response Y H V G D d S c s _ j
  have ht(t:ℕ): (Mk t m)*(Mk t n)=(Mk t (m*n)):= Subtype.ext (a.persisting t).1.symm
  refine ⟨b,⟨hx,hY⟩,photos_multiply ..,⟨Hx,Hy,Hw⟩,⟨compact_cells .., compact_cells .., cells_disjoint (h.span_positions j),fun a b i=> cells_apart (h.span_positions i)⟩,fun t=> ⟨(supported_cells Λ l s X₊).persists t,(supported_cells Λ l s X₋).persists t, observing_more Y H (show s ≤ s+t from Nat.le_add_right ..) Hw,?_, ?_⟩,fun t=> congrArg Subtype.val (ht t),fun t=> ?_,?_,a⟩
  · exact chroma Y H G.history.circuit s t ((obs_in ..).mpr ⟨hu.widen,(m).property.2 rfl⟩)
  · exact chroma Y H G.history.circuit s t ((obs_in ..).mpr ⟨(hv q).widen,(n).property.2 rfl⟩)
  · rw [hstar, ht]; exact ⟨h.consumption,moves_up Y H V s G.history G.clipped j false _ _ (bosonLabel _ (m*n)) t⟩
  intro u; apply h.paid
  suffices g : pigmentReading Y H V s G.history G.clipped j (S j) (r j)= (Mx s) by rw [g]; exact u
  funext x0
  by_cases ht : TestFamily K true x0
  · exact (reads_color Y H V s G.history G.clipped j (S j) (r j) (observe ht)).trans (spinLoan Y H V G d S c j s (observe ht))
  unfold pigmentReading evaluate; rw [dif_neg, dif_neg ht]; exact fun p =>ht p.1
end display
end YM.CF.Buffered.Afterglow.Tower.One
