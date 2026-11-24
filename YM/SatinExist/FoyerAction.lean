import YM.SatinExist.Foyer
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4000
set_option maxHeartbeats 350000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance Lamour.Bridge.Celeste Designs Twah Prototype
open Lamour.Bridge.Celeste.Morn
namespace Spine
open Aria Casting Six OS.Semigroup
open MacroGrid Set
variable (P : Spine) (x : P.Spectrum0 3) (j : Axis)
local notation "Y" => P.run
local notation "H" => P.large
local notation "Λ" => P.par
local notation "V" => P.law
local notation "G" => P.history
local notation "Gt" => P.projection.clipped
local notation "W" => timeMesh P.par
local notation "C" => P.room
local notation "ξ" => P.advocate 3 x j
local notation "ζ" => P.glasshouseCharacter 3 x
local notation "χ" => P.orientHouse x j
local notation "Hi" => P.GreatRoom x j
local notation "Hz" => P.PortionHil j ξ
local notation "Hc" => P.ColorHil j ξ
local notation "Bc" => P.stateVox j ξ
local notation "Bg" => P.greatBud x j
local notation "α" => P.foyer x j
local notation "β" => P.colorRoom x j
local notation "α'" => (α).toLinearIsometry.toContinuousLinearMap
local notation "Tg" => Selected.turnstile Y H V G Gt j false (C j) χ
local notation "R″" => Selected.ride Y H V G Gt j false (C j) χ
local notation "E₀" => P.physicalEnergy j ξ
local notation "E" => P.innerEucl j ξ
local notation "RepF" => P.stateSpace j ξ
local notation "RepF₀" => Selected.procession Y H V G Gt j false (C j) χ
local notation "Σ₀" A:max => (P.stateSpace j ξ) A

lemma high_wait (n r s:ℕ)(e:s ≤ r) (b:P.Vox j r) :
    α (E (whenly W s n) (Bc r b))=(R″).E (whenly W s n) (α (Bc r b)) := by
  rw [P.foyer_bud, ← matchR W s r n e, ← P.moves_p j ξ r, P.foyer_bud]
  exact (Selected.ride_ticks Y H V r G Gt j false (C j) χ b _).symm
lemma foyer_wait (t:ℝ≥0) : (α').comp (E t)=((R″).E t).comp α' := by
  apply ContinuousLinearMap.ext_on (P.preGram_dense x j)
  rintro _ ⟨⟨s,b⟩,rfl⟩
  let u:= Bc s b
  let f(r:ℝ≥0):= α (E r u); let g(r:ℝ≥0):=(R″).E r (α u)
  suffices hx : f=g from congrFun hx t
  apply (fills W).denseRange_val.equalizer ((α).continuous.comp (P.journey_cont j ξ u)) ((R″).continuousE (α u))
  funext w
  obtain ⟨m,n,h⟩ := MeshClock.split W w.property
  let k:=max s m; let e:=le_max_left s m
  change α (E w.val (Bc s b))=(R″).E w.val (α (Bc s b))
  rw [←P.refine_vox j ξ s _ e, ← h]
  exact P.high_wait x j n k m (le_max_right ..) _

lemma color_wait (t:ℝ≥0)(z:Hc) : β ((E₀).E t z)=(R″).E t (β z) := by
  let u := P.gnsIn j ξ
  have he : u ((E₀).E t z) = E t (u z) := P.warmTransit ..
  exact (congrArg α he).trans (DFunLike.congr_fun (P.foyer_wait x j t) (u z))

lemma color_live (t:ℝ)(z:Hc) : β ((E₀).edge t z) = (R″).edge t (β z) :=
  DFunLike.congr_fun (within_energy E₀ R″ (β).toLinearIsometry.toContinuousLinearMap
    (fun r => ContinuousLinearMap.ext fun i=> P.color_wait x j r i) t) z

lemma foyer_grid (m:ℕ)(v:ℤ)(k:Trans j) :
    (α').comp (RepF (P.movesOf j (m,v,k))) = (((Tg).crew k).play (notch W m v)).comp α' := by
  apply ContinuousLinearMap.ext_on (P.preGram_dense x j)
  rintro _ ⟨⟨s,x1⟩,rfl⟩
  let n:=max m s; let p:=le_max_left m s; let q:=le_max_right m s; let z:= castor W m n v
  let y :=Raise Y H P.history.circuit j 0 false s n q x1
  change α ((RepF (P.movesOf j (m,v,k))) (Bc s x1))= ((Tg).crew k).play (notch W m v) (α (Bc s x1))
  rw [←P.refine_vox j ξ s n q x1]; have he : P.movesOf j (m,v,k) = P.movesOf j (n,z,k) := by
    apply Subtype.ext; change (P.crew j k).play (notch W m v)=(P.crew j k).play (notch W n z)
    rw [show notch W m v= notch W n z from (notch_up W m n p v).symm]
  rw [he, show notch W m v=notch W n z from (notch_up W m n p v).symm,
    P.move_use, P.foyer_bud,P.foyer_bud]
  exact (Selected.turnstile_in ..).symm
lemma color_grid (k:Trans j)(v:marks W)(z:Hc) :
    β (((P.voyageF j ξ).crew k).play v z) = ((Tg).crew k).play v (β z) := by
  let u := P.gnsIn j ξ
  obtain ⟨m,y,rfl⟩ := notch_exists W v
  rw [P.meets]; exact (congrArg α (P.moveTransit j ξ (m,y,k) z)).trans
    (DFunLike.congr_fun (P.foyer_grid x j m y k) (u z))

local notation "A′" s:max w:max p:max b:max => P.atSide j s w p b
local notation "T₀" s:max B:max p:max => Selected.entrance Y H V s G Gt j false (C j) B p

lemma pushed_entry (s w:ℕ) (p:0<w)(b:P.Card j s w) (f:P.Vox j s) :
    (Σ₀ (A′ s w p b)) (Bc s f)=Bc s (slabT Y H s j false w b f) := by
  obtain ⟨v,q,f,rfl⟩:= P.fits j s f
  let z:=edit Y H s j false w v b f
  rw [P.from_entry j ξ s v q f,← show z.val=slabT Y H s j false w b f.val from
    Subtype.ext (by rw [slab_eq]; unfold z; rw [editor]),P.from_entry j ξ s (w+v) (by omega) z]
  let u:=P.emptyV j ξ
  let B:= A′ s w p b; let A:= A′ s v q f
  change (RepF B * RepF A) u = RepF (A′ s (w+v) (add_pos p q) z) u
  rw [←map_mul]; exact congrArg (fun a=>RepF a u) (P.concat ..)

lemma foyer_operator (s w:ℕ) (p:0<w)(b:P.Card j s w) :
    (α').comp (RepF (P.atSide j s w p b))=(RepF₀ (Selected.entrance Y H V s G Gt j false (C j) b p)).comp α' := by
  apply ContinuousLinearMap.ext_on (P.preGram_dense x j)
  rintro _ ⟨⟨t,f⟩,rfl⟩
  let k:=max s t; let e:=le_max_left s t; let q:=le_max_right s t
  change α ((Σ₀ (A′ s w p b)) (Bc t f)) = RepF₀ (T₀ s b p) (α (Bc t f))
  let bb:=furnished Y H s G j false w b k e
  rw [← P.refine_vox j ξ t k q f,P.upper_tab j s w p b k e, P.pushed_entry, P.foyer_bud, P.foyer_bud]
  exact (Selected.slot_high ..).symm
lemma color_entry (s w:ℕ) (p:0<w)(b:P.Card j s w)(h:P.voxTest j s b.val ∈ enclave P.calibration)
    (z:Hc) : β ((P.colorSpace j ξ) (P.door j s w p b h) z)= RepF₀ (T₀ s b p) (β z) := by
  let u:=P.gnsIn j ξ
  have he : u ((P.colorSpace j ξ) (P.door j s w p b h) z)= RepF (A′ s w p b) (u z) :=
    DFunLike.congr_fun (P.restrict_flight j ξ (P.door j s w p b h)) z
  exact (congrArg α he).trans (DFunLike.congr_fun (P.foyer_operator x j s w p b) (u z))

lemma color_view (s:ℕ){F:P.Test}(p:P.birthF j s F) :
    β (P.viewF j ξ s p)= Bg s (show P.Vox j s from p.choose.val) := by
  exact P.colorRoom_actor x j s _
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
