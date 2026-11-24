import SU5SatinMarkedCurrentNovember7
import Quarry.Harvest

/-! # Cp1. Interior masked estimate, chiral jet, signed insertion loan.

 No additional SUS Ward, election, existence hypotheses. Scope of estimate:
 real Mark infrastructure on these regulators (incl per-location/torus
 full and birth bill at pinpr=Q scale for birth, NPL for full,
 implements in (2) numerator/denominator). Doesn't establish yet e.g. that
 such Marks can attain the price (133) plane reflection. See accompanying
 report/missing inequality. -/

set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxHeartbeats 700000
set_option maxRecDepth 3200
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase
open MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound
open Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker
open scoped ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy
open Tapestry Germ Alliance Lamour.Bridge.Celeste Designs Twah Prototype
open Lamour.Bridge.Celeste.Morn
open CF.Velvet CF.Pannier.Chancel
open Spine Pitching.Focus QuadClock Ione Vow Swell
open _root_.Zephyr.Chern
universe uΩ

-- keep a base appointment reusable for conjunctive later election
structure Rocky (P : Spine) (K : P.Register) (Mc : ℕ) : Prop where
  sizing : uniform P K blankSupplier 1 1
  ro : P.Roster
  night : P.NightCop
  tile : 8 ∣ P.par.M.val
  oddL : Odd P.par.R.L.val
  stepR : RateStamp P.run
  visa : Compass_sol P.run
  merit : Meritorious P.par
  slot : ∃ (Pay kc G : ℝ) (Tξ : Hove.Grant P.par.K.j 2) (n:ℕ),
    Sweepcraft P.run Tξ Pay kc G n Mc
  residence : ∃ A C:ℝ, Chronicle P.run A ∧
    ∀ᶠ i : ℕ in atTop, ∀ᶠ j : ℕ in atTop, ∀ k : ℕ,
      (P.run.voyage j).kick ≤ k → i ≤ P.run.uv k → Yoke.ShelterCost C P.run i j k

theorem rocky_now (Mc : ℕ) : ∃ (P : Spine) (K : P.Register), Rocky P K Mc := by
  -- same method as planetaryPolar (from the preliminary appointment)
  obtain ⟨n,h⟩ := exists_nat_gt ((2+(Mc:ℝ))*strive_E 6)
  have hz : 0 ≤ strive_E 6:=by unfold strive_E Jet.composeCost; positivity
  obtain ⟨P,K,q,r,H,⟨T,t⟩,mY,_,hv,hy,_,⟨C,_,_,p⟩,A,k⟩ :=
    bookedS n (le_trans (mul_le_mul_of_nonneg_right
      (le_add_of_nonneg_right (Nat.cast_nonneg _):(2:ℝ)≤2+Mc) hz) h.le)
      (fun _ _ _ _ _ _=>0) blankSupplier 1 1 zero_lt_one
  obtain ⟨Pay,kC,Γ,Tξ,u,v,s,Z,y,p1,p2,πx,m⟩:= T.fromCrew
  have ht : Odd P.par.R.L.val:= ⟨P.par.R.L.val/2,by omega⟩
  exact ⟨P,K,q,r,H,hy,ht,EarningsRate.atMask P.run (RateCover.stepRate m) r.prepared,
    visa_onPath P.run r.prepared t,mY,⟨Pay,kC,Γ,Tξ,n,
    bandRadius P.run ((RateCover.includes _ _ _ m).staysOn
      (by rw [P.par.kJ]; exact ⟨2,rfl⟩) P.par.kJ.ge u v Z s p1 p2 Mc
       ((mul_le_mul_of_nonneg_right (le_add_of_nonneg_left (by norm_num)) hz).trans h.le)) r.prepared⟩,
    A,C,k,p⟩

theorem Rocky.select {P:Spine}{K:P.Register}{n:ℕ} (H : Rocky P K n)(good : P.Spectrum0 3 → Prop)
    (h : ∀ᵐ x ∂P.pillars 3, good x) : ∃ x, good x ∧ JointTuple.{uΩ} P K x :=
  let ⟨_,_,g,q⟩ := H.residence
  reside P K H.sizing H.ro H.night H.oddL g q good h

abbrev rulerMatter (P : Preparation) : ℕ := 8*P.block.val

-- anchor of windmill is a matter site; by offsets `[-m+1,...,m]` on EACH axis,
-- windmill at root (-1) has center gauge 0.
structure CathedralQ (P : Spine) : Prop where
  prime : ∀ i k : ℕ, (((P.run.voyage i).X (P.run.uv k)).gram 0).beta = P.par.x
  mesh : let m:= rulerMatter P.par
         0 < m ∧ (2*m:ℕ)= (ruler P.par.block).toNat ∧
           ∀ s:ℕ,MeshClock.bell (timeMesh P.par) s 1= Selected.gaugeMesh P.par s*(2*(m:ℝ))
  paid (m : ℕ) (hm : m>0) : ∃ a c:ℝ, ∃ F D:ℝ→ℝ, 0<a ∧ 0<c ∧ BPress.NPL F ∧ BPress.NPL D ∧
    ∀ z:Cover, ∃ d:ℝ, 0<d ∧ ∀ᶠ s:ℕ in atTop, ∀ᶠ i:ℕ in atTop, ∀ k:ℕ,
    (P.run.voyage i).kick ≤ k → s < P.run.uv k →
    let R := RootBook P.run i k s
    let N := cell (P.run.ir i) P.par.block P.par.R.L s
    let x:=wrap N z
    let K := (P.run.voyage i).CapeT s
    let p:=R.p
    let w:=hat P.par.R.L P.par.x s
    let Q:=pinpr P.par.R.L w
    /- includes denominator at the compensated scale, including β calibration -/
    VLine P.run s i k (SectorNext.Remainder.Scales.merit P.par.R.L w) ∧
    ∃ J T X Z V, let Y:= mark128 p K x Q m J X
      let I:Buffered.Mark N := (stemS w:ℂ) • Y
      let A := colorsTest P z i k s X
      Counterfoil P.run s i k m a c (F w) (D w) x J T X Z V ∧
      RealStencil Y (Swell.port p x) ∧ Bud A ∧ d < (bud A 2).re ∧
      let D_ := partitionZ R P.par.U K
      D_ ≠ 0 ∧ D_ = markedRead (1: Mark N) K (denZ R P.par.U K) ∧
      (∀ (f:Buffered.Mark N) {S:Support (More N)}, AtSupport false S f → Disjoint (Swell.port p x) S →
        Integrable (Preparation.aisle P.run s i k V f) (city N) ∧
        Journey.compass P.run i k s (f*I)=(∫ u, Preparation.aisle P.run s i k V f u ∂city N)/D_)

lemma rulerOut (P : Spine) (s:ℕ) : MeshClock.bell (timeMesh P.par) s 1=
    Selected.gaugeMesh P.par s*(2*(rulerMatter P.par:ℝ)) := by
  rw [Reconstruction.Atlas.bell_norm]; simp only [mul_one,rulerMatter,ruler]
  push_cast; ring

lemma cathedral_buy {P: Spine}{K:P.Register}{n:ℕ}(p : Rocky P K n) : CathedralQ P := by
  constructor
  · exact terminalBeta P K p.sizing
  · refine ⟨Nat.mul_pos (by omega) P.par.block.property, by
      dsimp only [ruler,rulerMatter]; omega,rulerOut P⟩
  intro m hm
  obtain ⟨a,c,F,D,ha,hc,f,d,U⟩ := market129 P.run p.ro.prepared p.visa p.stepR m
  refine ⟨a,c,F,D,ha,hc,f,d,?_⟩; intro z
  obtain ⟨e,h,J⟩ := paid_turn P z m (SprigFee.paid P) hm a c ha
  refine ⟨e,h,?_⟩
  filter_upwards [U,J,line_merit P.run 1 zero_lt_one p.merit] with s h j v
  filter_upwards [h] with i v' k w c' R N x K0 p' y Q
  obtain ⟨J,T,X,Z,V,l⟩ := v' k c' x
  obtain ⟨q,u,a0,g⟩ := Counterfoil.aisleSolo P.run s i k m l w c'.le
  have hT := j i k l
  refine ⟨by simpa only [one_mul] using v i k w c'.le,J,T,X,Z,V,l,
    Counterfoil.realMask P.run s i k m l,hT.1,hT.2,u,a0,?_⟩
  intro f S p H
  let hx := Counterfoil.aisleSale P.run s i k m l w c'.le f p H
  exact ⟨hx.1,hx.2.2.2⟩

/-- One election with (124) and pricetag of (129) for **actual** single-root
 inputs and the top coefficient test on the REAL physical gauge payload of (128),
 also Mark & Y° agreement on all-support-you-can-supply disjoint spectators in
 the signed reading (2). Exact statement via `CathedralQ`, `Counterfoil`, `Opening`.
 (Pre-(84), does not itself price the RG continuation of that reading.) -/
theorem cp1 (Mc:ℕ) : ∃ (P : Spine) (K : P.Register) (x : P.Spectrum0 3),
    Rocky P K Mc ∧ JointTuple.{uΩ} P K x ∧ CathedralQ P := by
  obtain ⟨P,K,A⟩:= rocky_now Mc
  obtain ⟨x,_,H⟩:= A.select (fun _=> True) (.of_forall fun _ => trivial)
  exact ⟨P,K,x,A,H,cathedral_buy A⟩

#print axioms cp1
#print axioms Counterfoil.billed
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
