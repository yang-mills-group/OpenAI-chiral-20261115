import YM.SU5.Macro.Mixture
import YM.SU5.Reconstruction.Docket
/-!
# Persistence and continuum budget of the centered, masked exercise

Keeps price scope for each slot experiment. Does not replace mark-level products by
products of slab or ground-compressed readings. S & T concrete. For comparison in this system see
also the separate pricing handoff.
-/
set_option autoImplicit false
set_option maxHeartbeats 470000
set_option maxRecDepth 4500
set_option synthInstance.maxSize 24000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.Selection.Home
open Function Filter NormedSpace Metric SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark Vacancy SatinVerification
open Tapestry Tapestry.Altitude
open Tower.PhaseChoice Tower.Selected Tower.Reconstruction
open CF.SatinRotation CF.Pannier.Chancel.Attic.Cairn Buffered.Reliance Buffered.Reliance.ShortWave
open CF.Pannier.Chancel CF.Pannier.Chancel.Lantern CF.Pannier.Chancel.Lantern.Bulb
open Rubric Fern Fern.Planet
open OS.Semigroup MeshClock
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(H:Real.exp 1≤Λ.x)
local notation "K" => tent Y H
variable {i k:ℕ→ℕ}{I:ℕ→Family (tent Y H)→ℕ→ℂ}{E:ℕ→Family (tent Y H)→ℂ}
    {L: Rack Λ l} {B:Clay Λ l} {T:ℕ→ℕ→Tariff} {t:ℕ→Tariff} (D: Fashion Y H i k I E L B T t)
    (G:SatinVerification.GroundExtension (i:=i) (k:=k) (E:=E) Y H) (room : ∀ j:Axis,Arena Y H G.history.circuit j 0 false)
    (χ:CapCharacter Y H D.univ_ G.history G.clipped 3 false (room 3))
local notation "V" => D.univ_
local notation "Q" => G.history
local notation "Qt" => G.clipped
namespace Siam
open Giant
variable (s:ℕ) (M:Giant)
local notation "Φ" => Torrent.fare
local notation "A" => early M
local notation "S" => M.ascX
local notation "Wz" => wall M
local notation "Mρ" z:max u:max a:max b:max c:max => Rubric.Marble K z M.Zumba M.ascX M.ascY u a b c
local notation "k₀" f:max => phaseRead Y H V Q Qt 3 (room 3) χ s f
local notation "Γ" => sch Y H D G room (dial Y H D G room 3 χ 0)
variable {f g: Dome (tent Y H)}{z:Window.Family}{ε:ℝ}(p:Signal Y H D G room χ s M f g z ε)
namespace Signal
local notation "Ξ" => Dome K
local notation "X" => pinhole (Dome (tent Y H)) s f
local notation "W" => pinhole (Dome (tent Y H)) s g
local notation "U" => footprint Λ l s (early M)
local notation "U'" => footprint Λ l s M.ascX
local notation "d"=> whenly (timeMesh Λ) s 1
include p
lemma left : InTest K false A false f.val:= (show cameo 0 10=false from by decide) ▸ (Marble.assign p.young)
lemma right: InTest K false M.ascX false g.val:= (show cameo 10 0=false from by decide) ▸ (Marble.assign p.aged)
-- caps/either geometry
lemma paid_box : IsCompact U ∧ IsCompact U' ∧ (0:ℝ)<d ∧ Disjoint U U' ∧
    (∀ (x y:RSpace), x∈ U → y∈ U' → ∀ i:Axis,x i+d ≤ y i) ∧
    X ∈ PolAt Y H s U ∧ W∈ PolAt Y H s U' ∧ X*W ∈ PolAt Y H s (U∪U') := by
  let q:=p.seam
  have ht {h:Ξ}{L':Finset Cover}(v:h∈ enclave K)(w:InTest K false L' false h.val):pinhole Ξ s h∈PolAt Y H s (footprint Λ l s L'):=oneSlotWell Λ K l true _ _ s
    (Set.mem_inter (Set.mem_univ _) (Set.mem_Iic.mpr le_rfl)) (x:=h) ((keeps ..).mpr ⟨L', w.widen,has_footprint Λ l s L'⟩) v
  have hu:=ht p.gaugeEarly (p.left Y H D G room χ s M); have hv:=ht p.gaugeLate (p.right Y H D G room χ s M)
  exact ⟨footprint_compact ..,footprint_compact .., when_pos (timeMesh Λ) s 1 zero_lt_one, q.disjoint Y H s, q.separated Y H s,hu,hv, Subalgebra.mul_mem _ (isotone Y H (Set.subset_union_left (t:=U')) hu) (isotone Y H (Set.subset_union_right (s:=U)) hv)⟩

lemma connected : Φ < ‖Γ (X*W)‖ ∧ (Γ) W = 0 ∧
    Φ < ‖D.toExhibition.vistaTake Y H (X*W)‖ ∧ D.toExhibition.vistaTake Y H W=0:= by
  obtain ⟨u,c⟩:= Fern.Cloak.priced0 Y H V Q Qt 3 (room 3) s χ (bidding Y H g) p.cold
  rw [←map_mul (pinhole Ξ s), Exhibition.onVista, Exhibition.onVista, sch_hole,sch_hole]
  exact ⟨p.elector,c,p.first,u⟩

local notation "Vξ"=> phaseRead Y H V Q Qt 3 (room 3) χ
local notation "𝒮" i:max x:max=> stream Y H G.refine s i x
local notation "D'" i:max=> D.toExhibition.vistaFinish Y H (s+i)
local notation "P'" i:max=> volumeAround Λ l i
variable (n:ℕ)
-- tell comparing reader exactly what moved
omit p in
lemma one_high (x: Ξ) (h:x∈enclave K) : ((D' n) (pinhole Ξ s x)).val= 𝒮 n x.val :=
  let f' : Marks K true:= ⟨x.val,x.property,fun _=>show CovCover K x.val from h⟩
  Reconstruction.further_finish Y H V G D.toExhibition s n f'
lemma grows : footprint Λ l (s+n) ((P' n) A) ⊆ U ∧
    footprint Λ l (s+n) ((P' n) S) ⊆ U' ∧
    𝒮 n f.val ∈ observ K ((P' n) A) true ∧ 𝒮 n g.val ∈ observ K ((P' n) S) true ∧
    ((D' n) (X*W)).val = (𝒮 n (f*g).val) ∧
    (𝒮 n (f*g).val)=(𝒮 n f.val)*(𝒮 n g.val):= by
  have a:= (p.left Y H D G room χ s M).widen; have b:= (p.right Y H D G room χ s M).widen
  exact ⟨covers_footprint ..,covers_footprint ..,
    Tower.chroma Y H G.history.circuit s n ((obs_in ..).2 ⟨a,p.gaugeEarly⟩),
    Tower.chroma Y H G.history.circuit s n ((obs_in ..).2 ⟨b,p.gaugeLate⟩),by
      rw [←map_mul (pinhole Ξ s)]; exact one_high Y H D G s n (f*g) ((enclave ..).mul_mem p.gaugeEarly p.gaugeLate),
    woven_product _ _ (Q).circuit s n a b (p.seam.complete Y H)⟩
lemma larger_bill :
    E (s+n) ((𝒮 n f.val)*(𝒮 n g.val)) = E s (f.val*g.val) ∧
    Vξ (s+n) ((𝒮 n f.val)*(𝒮 n g.val)) = k₀ (f.val*g.val) ∧
    E (s+n) (𝒮 n g.val)=0 ∧ (Vξ (s+n) (𝒮 n g.val))=0 := by
  let t:=upward Y H Q false (bidding Y H (f*g)) s n
  let T':=upward Y H Q false (bidding Y H g) s n
  obtain ⟨a,b⟩:= Fern.Cloak.priced0 Y H V Q Qt 3 (room 3) (s+n) χ T' ((read_refines Y H V Q Qt 3 false (room 3) s n (bidding Y H g)).trans p.cold)
  have q:t.val=(𝒮 n f.val)*(𝒮 n g.val):= (p.grows Y H D G room χ s M n).2.2.2.2.2
  have w : Vξ (s+n) t.val= Vξ s (f.val*g.val):= (phase_read Y H V Q Qt 3 (room 3) (s+n) χ t).trans ((congrArg χ (read_refines Y H V Q Qt 3 false (room 3) s n (bidding Y H (f*g)))).trans (phase_read Y H V Q Qt 3 (room 3) s χ (bidding Y H (f*g))).symm)
  have ht:= inspected Y H V (s+n) Q Qt 3 false (room 3) (F:=t);
  rw [show cap Y H V (s+n) Q Qt 3 false (room 3) t= _ from
    (show _ = cap Y H V s Q Qt 3 false (room 3) (bidding Y H (f*g)) from
      congrArg Subtype.val (read_refines Y H V Q Qt 3 false (room 3) s n (bidding Y H (f*g))))] at ht
  rw [← q]
  exact ⟨ht.symm.trans (inspected Y H V s Q Qt 3 false (room 3)),w,a,b⟩
-- Actual cutoff. Window/geometry: both supports, physical regions, onCutoff E
local notation "P" => pinhole Ξ s
lemma finite_price :
    (Tendsto (fun r:ℕ=> Tapestry.taking Y H (i (G.rows r)) (k (G.columns r)) (P f * P g)) atTop
      (𝓝 (E s (f.val*g.val)))) ∧
    (∀ᶠ r:ℕ in atTop, Φ < ‖Tapestry.taking Y H (i (G.rows r)) (k (G.columns r)) (P f * P g)‖) ∧
    (∀ᶠ i:ℕ in atTop, ∀ (n k:ℕ), Pay Y (s+n) i k → breathing Y H (s+n) i k (P f*P g) =
       breathing Y H (s+n) i k X * breathing Y H (s+n) i k W) := by
  obtain ⟨c,e,_,h,_,g₀,g₁,v⟩:= p.paid_box Y H D G room χ s M
  let T':= D.toExhibition.vistaTake Y H
  have hx:Tendsto (fun r:ℕ=> Tapestry.taking Y H (i (G.rows r)) (k (G.columns r)) (P f*P g)) atTop (𝓝 (E s (f.val*g.val))) := by
    let a:= interpret_cuts Y H V G D
    have hd := a.converge (P f*P g) (Altitude.curve.mpr ⟨s,inside_budget Y H v⟩)
    rw [show T' (X*W)= E s (f.val*g.val) from
      (congrArg T' (map_mul (pinhole Ξ s) f g).symm).trans (Exhibition.onVista Y H s D.toExhibition)] at hd
    exact hd
  refine ⟨hx, hx.norm.eventually (lt_mem_nhds p.first),?_⟩
  let X' := interpret_cuts Y H V G D
  filter_upwards [X'.native_separated U U' h c.isBounded e.isBounded] with i v n k u
  have q {F₀:Cloud Ξ}{U₀:Set RSpace}(x': F₀∈ PolAt Y H s U₀) : F₀∈ jetty Λ l K true (handstamp U₀) (Set.Iic (s+n)):=by
    rw [←Set.univ_inter (Set.Iic (s+n))]; exact ((well_spec ..).1 (polAt_up Y H (Nat.le_add_right s n) x')).1
  exact v _ k u X W (q g₀) (q g₁)
-- Ferry/limit query, gives support preconditions to plug into CutInterpret.support
lemma eligible : X∈ jetty Λ l K true (handstamp U) (Set.Iic s) ∧ W∈ jetty Λ l K true (handstamp U') (Set.Iic s) ∧
    X*W∈ jetty Λ l K true (handstamp (U∪U')) (Set.Iic s) ∧
    X*W∈localEuclidean Λ l K true (U∪U') ∧ CutInterpret Y H G D:= by
  obtain ⟨c,e,_,_,_,a,b,t⟩:=p.paid_box Y H D G room χ s M
  refine ⟨?_,?_,?_,?_,interpret_cuts Y H V G D⟩
  · rw [←Set.univ_inter (Set.Iic s)]; exact ((well_spec ..).1 a).1
  · rw [←Set.univ_inter (Set.Iic s)]; exact ((well_spec ..).1 b).1
  · rw [←Set.univ_inter (Set.Iic s)]; exact ((well_spec ..).1 t).1
  exact local_at (c.union e) (show  X*W∈ circum Λ l (tent Y H) true (U∪U') (Set.Iic s) from Set.univ_inter (Set.Iic s) ▸ t)
end Signal
end Siam
end YM.CF.Buffered.Afterglow.Tower.Selection.Home
open YM.CF.Buffered.Afterglow.Tower.Selection.Home.Siam.Signal
#print axioms eligible
#print axioms finite_price
#print axioms larger_bill
#print axioms connected
#print axioms one_high
#print axioms grows
