import YM.SU5.MacroSix.Report
import YM.SU5.MacroSix.Ledger
import YM.SU5.Reconstruction.Berezin

/-!
# The chiral labels and single gauge data

No regulator-to-low-energy-chirality assertion in this construction: this identifies the
**source and prescribed operator** in the FiniteGaugeData history. `Stock` uses THESE precise chiral
labels (up create / down remove; down unbarred source if pricing Grassmann conventions
with the minus). Verified starting realization uses `st_price`—no need to append a coarse
Wilson-line recipe that isn't priced by this kernel. Top recognized on the joint Fock
system with actual Sea and mateK and summation; can use already verified writer /
Grassmann viewpoint `Reconstruction.action_at`. This is the *regulated* left-handed
`10 ⊕ 5̄` representation identification, as in `the construction notes` in the handoff.
Use also `Reconstruction.empty_symbol` (from `Berezin`, we restate part to fix the
precise minus-grading convention). Top density only on admitted links; not replacing
by a square determinant.

Below all the hypotheses on bare checks are those of the library's ACTUAL chiral
identification. Helps reading the paper to collect the same formulae at the supplied
course/heights. No new polarization assumptions here. Color-sector projection in the
selected, continuous space (entirely different projection!) later.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 30000
set_option maxRecDepth 4000
set_option maxHeartbeats 450000
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
open Reconstruction Dial Thera Scree Paige Reed
-- `Sources` separate from the ancestor namespace and from comparison's `Prices` annotations
namespace Spine
open Ballad Lamour.Bridge.Celeste
open ExTwo
variable (P : Spine) (g : ℕ) (t k s n : ℕ) (Z : Window.Family)
local notation "Λ" => P.par
local notation "Y" => P.run
local notation "H" => P.large
local notation "Γ" => P.calibration
local notation "m₀" => P.run.uv k
local notation "μ" => P.run.ir t
local notation "N" => Journey.side P.run t (P.run.uv k)
local notation "T₀" => (P.run.voyage t).CapeT m₀
local notation "V₀" => ((P.run.voyage t).X m₀).gram m₀
local notation "β" => (V₀).beta
local notation "S₀" => (P.run.meter.a m₀).threshold

-- projection statements investments
lemma largeSource (a : Fin 3) (i : SU.Ten) : (a,Sum.inl i)∈colors (a,true) := by simp [colors,family]
lemma smallSource (a : Fin 3) (i : SU.F) : (a,Sum.inr i)∈ colors (a,false) := by simp [colors,family]
lemma color_identity (v : SU.E) (a : Fin 3) : (matter v).val=triple (fund v) ∧
    (matter v).val=(1:Op (Fin 3)) ⊗ₖ (Join.both (wedgeOp (SU.fund v)) (cc (SU.fund v))) ∧
    (∀ i j : SU.Slot, family i ≠ family j → (matter v).val i j=0) ∧
    (∀ i j : SU.Ten, (matter v).val (a,Sum.inl i) (a,Sum.inl j) =
      SU.fund v i.val.1 j.val.1 * SU.fund v i.val.2 j.val.2 -
        SU.fund v i.val.1 j.val.2 * SU.fund v i.val.2 j.val.1) ∧
    (∀ i j : SU.F, (matter v).val (a,Sum.inr i) (a,Sum.inr j) = star (SU.fund v i j)) ∧
    Fintype.card Window.Family = 6 ∧ Fintype.card Ten=10 ∧ Fintype.card SU.Slot=45 ∧
    (colors Z).card=(if Z.2 then 10 else 5) := by
  refine ⟨rfl,rfl,fun i j ↦ neq_block v,?_,?_,?_,SU.pairs,SU.slots, colors_card _⟩
  · intro i j; simp [matter_matrix,triple,Join.both,SU.each,wedge_entry]
  · intro i j; simp [matter_matrix,triple,Join.both,SU.each,cc_apply]
  exact (show Fintype.card Window.Family=6 from (by decide))

-- Identify signs & index dictionary of both halves. (AP seam built in `frame` below.)
lemma ap_slots (x : Site (Journey.side P.run t (P.run.uv k))) (i : SU.Slot) (a : SpinIdx) :
    (((x,a),i)∈Tset (Journey.side P.run t (P.run.uv k)) ↔ a∈ plusHalf) ∧
    plusHalf={(0:SpinIdx),1} ∧ cutM plusHalf=(1/2:ℂ) • (1+grading) ∧
    (think (Tset (Journey.side P.run t (P.run.uv k)))).term ((x,a),i)=
      if a∈plusHalf then Fock.put ((x,a),i) else -Fock.takeF ((x,a),i) := by
  refine ⟨?_,?_,Lat.raising, microscopic_letter _ t k x a i.1 i.2⟩
  · exact mem_Tset x a i
  decide

structure SourceBill : Prop where
  -- inside the priceable link configurations (outside: density is zero)
  flags_ (a : Skye.Orbit (Journey.side P.run t (P.run.uv k))) :
    flags (S₀) a.1≠∅ → denZ (V₀) P.par.U (T₀) a=0
  like (a : Skye.Orbit (Journey.side P.run t (P.run.uv k))) (h : flags (S₀) a.1=∅) :
    T₀ a=a.1 ∧
    let F₀ := Lat.frame SU.matter (Cube.links a.1) (Lat.anticut (Journey.side P.run t (P.run.uv k)))
    let PS:= spar P.par.K.j babyM a.1
    Safe F₀.H ∧ PS=portW (Tulip.helix _).symm (projector F₀.H) ∧ Sea PS (changeM P.par.U a.1 babyM) ∧
    denZ (V₀) P.par.U (T₀) a= Complex.exp (-((β * basicP P.par.K.top.clip a.1 : ℝ):ℂ)) • changeM P.par.U a.1 babyM ∧
    F₀.overlap * projector F₀.H = cutM (Lat.upperP (Journey.side P.run t (P.run.uv k))) * projector F₀.H
  -- bra
  mate_ : Sea (cutM (Tset (Journey.side P.run t (P.run.uv k)))) (mateK (Journey.side P.run t (P.run.uv k)))
  -- calibration checks: representation and lattice projection on empty links
  slots (U : SU.E) : (matter U).val=(1:Op (Fin 3)) ⊗ₖ (Join.both (wedgeOp (SU.fund U)) (cc (SU.fund U))) ∧
    Fintype.card Window.Family=6 ∧ (∀ (Z : Window.Family), (colors Z).card = if Z.2 then 10 else 5)
  left_hand :
    let f := Lat.frame SU.matter (Cube.links (1:Pane (Journey.side P.run t (P.run.uv k)))) (anticut N)
    projector f.H=fourImage SU.Slot (Journey.side P.run t (P.run.uv k)) (fun k=>projector (latticeAtoms _ k).H) ∧
    f.H=fourImage SU.Slot N (fun k=>(latticeAtoms _ k).H) ∧
    projector (BZ.atom 0).H=1-(1/2:ℝ) • (1+grading) ∧
    (BZ.atom 0).overlap * projector (BZ.atom 0).H=0 ∧
    ∀ t : BZ.Mom, HasDerivAt (fun v:ℝ=> let W:=BZ.atom (v • t); W.overlap * projector W.H*(1-BZ.gPos))
      ((1/2:ℝ) • (BZ.symbolD t*(1-BZ.gPos))) 0

lemma source_bill : P.SourceBill t k := by
  refine ⟨fun a h ↦ ?_,fun a h ↦ ?_,(touchP (Journey.side P.run t (P.run.uv k))) ▸ tickB (Journey.side P.run t (P.run.uv k)),
    fun _ ↦ ⟨rfl,by decide,fun _ ↦ colors_card _⟩,?_⟩
  · rw [P.run.whole]; exact Set.indicator_of_notMem (s:={U|flags (S₀) U=∅}) h _
  · let e := top_system P.run t k a h
    exact ⟨e.1,e.2.1,e.2.2.1,e.2.2.2.1,e.2.2.2.2.1,e.2.2.2.2.2.1⟩
  let M := empty_symbol P.run t k
  exact ⟨M.1,M.2.1,M.2.2.2.1.1,M.2.2.2.1.2,M.2.2.2.2⟩

/-- Recheck availability of single chiral source interpretation even for the advanced, true
(link PAIR gauge contour) marks. With any singlet's true support and height. Important: NOT
asking that such a script be continuous in U, or selected matter at the continuum level
have identical tensor representation to this cutoff Sea. -/
lemma atTop_flavor {b : Set RSpace} (F : P.Effect) (p : F∈ PolAt Y H s b) (h : Pay Y s t k) :
    let u:=atCutoff Y H t k F
    ∃ S, PhaseChoice.SupportedPhysically P.par P.width (P.run.uv k) S b ∧
    AtSupport false (Satin.region S (Journey.side P.run t (P.run.uv k))) (toMark u) ∧ covariant (toMark u) ∧
    ∃ w: Pane (Journey.side P.run t (P.run.uv k)) → FC (Single N), Envelope w ∧
      Lattice.LocalOn (Satin.region S N) w ∧ ∀ z:Pane N, Absorb (modesIn N (Satin.region S N)) (w z) ∧
      Plain (w z) ∧ u z=(think (Tset N)).eval (w z) := atCutoff_script Y H t k p h

-- also stock at arbitrary implementing PE, incl observing s=t after the price. Confirms enclosurable sim.
local notation "S₁" => P.stockS Z (P.flash n)
local notation "S₂" => (P.flash n).birth
local notation "S₃" => (P.flash n).death
lemma flavor_bill : S₁ ∈ enclave (P.calibration) ∧ (S₁).val = (-(n:ℂ)^3/5) •
    ∑ p∈colors Z, ∑ q∈ colors Z,
      scalar P.calibration ((fun U : LinksC ↦ (matter (travel U (nodeC (P.flash n).birth)
        (List.replicate (2*n) (posDir 3)))).val p q) ∘ Prod.fst) *
      (removal P.calibration ((P.flash n).death) 2 q * creation P.calibration ((P.flash n).birth) 0 p) :=
  ⟨P.celebrity (flourish _ _), (P.st_price ..).2.2.2⟩
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
#print axioms ap_slots
#print axioms color_identity
#print axioms source_bill
#print axioms atTop_flavor
#print axioms flavor_bill
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
