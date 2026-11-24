import Finch.Bill
import SU5SatinMarkedCurrentNovember7
/- CP1. -/
set_option autoImplicit false
set_option maxHeartbeats 380000
noncomputable section
set_option synthInstance.maxSize 28000
set_option maxRecDepth 2000

namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection

open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase
     MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound
     Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker
     ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy
     Tapestry Germ Alliance Lamour.Bridge.Celeste Designs Twah Prototype
open YM.Stationary (Gaia)
open CF.Onyx (riseX moor)
open Lamour.Bridge.Celeste.Morn

open CF.Velvet CF.Pannier.Chancel
open Spine Pitching.Focus

open QuadClock Preparation.Yoke

namespace Spine
universe u
-- For fixed finite number Mc of root-types available at each seat,
-- issue the OrbitPulse economics together with Reg.
open Ione Vow

-- definitions in scope of current branch
open Swell Sour Marks _root_.Zephyr.Chern
/-
For ACTUAL single-root openings. (Eventually s, eventually i, all k s<uv k):
X=P.par, x=hat X.R.L X.x s, τ=temp x, Q=pinpr X.R.L x.
FullInsertion seed at each center O on weighted MARK (not just a cylinder on flags or an
unpadded jet); within the lecture `integrates_full` gives its insertion meaning.
`engraves` is the affine stream test on that SAME masked gauge part, before Wick valuation.
NOT a statement of the two reflection estimates or budgets for feeding a Gap step.
-/
structure SingleRootFinance (P:Spine): Prop where
  each (m:ℕ) : ∃ a c:ℝ, ∃ q g:ℝ→ℝ, 0<a ∧ 0<c ∧ YM.CF.BPress.NPL q ∧ YM.CF.BPress.NPL g ∧ ∀ᶠ s:ℕ in atTop,∀ᶠ i:ℕ in atTop,∀ k:ℕ,s<P.run.uv k→
    let N:=age P.run i s
    let x:=hat P.par.R.L P.par.x s
    ∀ O:Site N,∃ J:Axis→ SOp N,∃ X:SOp N,∃ L:Sour.Bag N, SingleRootAccount P.run a c i k s m (q x) (g x) O J X L ∧
    ∀ (B:Tagged N)(U:Sa N), (∀ x, Fock.Sector (modesIn N U) false (B x)) → Disjoint (wardZone (RootBook P.run i k s).p O m) U → (P.run.voyage i).kick≤ k → RG.Envelope B →
       partitionZ (RootBook P.run i k s) P.par.U ((P.run.voyage i).CapeT s)≠0 ∧ Integrable (birthReading P.run i k s B L) (city N) ∧ Marks.ratio P.par.V P.par.U (RootBook P.run i k s) ((P.run.voyage i).CapeT s) (B*liftedOrbit (Ramp P.run i k s m O X J)) = (∫ x,birthReading P.run i k s B L x ∂city N)/(partitionZ (RootBook P.run i k s) P.par.U ((P.run.voyage i).CapeT s))
  engraves (a c:ℝ) (p:0<a)(x:Cover)(m:ℕ)(e:1≤ m) : ∃ β> (0:ℝ), ∀ᶠ s:ℕ in atTop,∀ i k,s<P.run.uv k→∀ (J:Axis→ SOp (age P.run i s)) (X:SOp (age P.run i s))(L:Sour.Bag (age P.run i s))(q g:ℝ), SingleRootAccount P.run a c i k s m q g (wrap _ x) J X L→ let N:=age P.run i s; let Z:= inkCost ((P.run.voyage i).CapeT s) (RootBook P.run i k s).p (wrap _ x) X; _root_.Zephyr.Chern.Bud (Z ∘ _root_.Zephyr.Chern.petals (_root_.Zephyr.Chern.stream N)) ∧ β < (_root_.Zephyr.Chern.bud (Z ∘ _root_.Zephyr.Chern.petals (_root_.Zephyr.Chern.stream N)) 2).re
lemma singleRootSupported(P:Spine)(K:P.Roster)(v:RateStamp P.run)(w:Compass_sol P.run)(f:SprigFee P): SingleRootFinance P:=by
 refine ⟨?_,concordance P f⟩; intro m
 obtain ⟨a,c,q,g,p,u,F,G,H⟩:= fundRoot P.run K.prepared v w m
 refine ⟨a,c,q,g,p,u,F,G,?_⟩
 filter_upwards [H] with s t; filter_upwards [t] with i Z k y; intro N x O
 obtain ⟨J,X,L,l⟩:= Z k y O
 exact ⟨J,X,L,l,fun B U h p w v=> integrates_full P.run l.actual128 h p w y.le v⟩

/-- Independent joint election (variant of planetaryPolar with additional receipts). -/
theorem planetaryMarked128 (Mc:ℕ) :
 ∃ (P : Spine)(K : P.Register)(x : P.Spectrum0 3), JointTuple.{u} P K x ∧
    8 ∣ P.par.M.val ∧ RateStamp P.run ∧ Compass_sol P.run ∧
    P.Roster ∧ Preparation.Post124 P.run ∧ Solstitial P.par ∧ Preparation.Heater P.par P.run ∧
    _root_.Zephyr.Chern.SprigFee P ∧ SingleRootFinance P ∧
    ∃ (Pay kc G : ℝ)(Tξ:Hove.Grant P.par.K.j 2)(n:ℕ),
      Sweepcraft P.run Tξ Pay kc G n Mc := by
  obtain ⟨n,h⟩:= exists_nat_gt ((2+(Mc:ℝ))*strive_E 6)
  have hz:0 ≤ strive_E 6:=by
      unfold strive_E Jet.composeCost; positivity
  obtain ⟨P,K,q,r,H,⟨T,t⟩,_,_,hv,hy,_,⟨C,_,_,p⟩,a,k⟩:=
    bookedS n (le_trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (Nat.cast_nonneg _):(2:ℝ) ≤ 2+Mc) hz) h.le) (fun _ _ _ _ _ _=>0) blankSupplier 1 1 zero_lt_one
  obtain ⟨Pay,kC,Γ,Tξ,u,v,s,Z,y,p1,p2,πx,m⟩:= T.fromCrew
  have ht : Odd P.par.R.L.val:= ⟨P.par.R.L.val/2,by omega⟩
  obtain ⟨x,_,E⟩:= reside.{u} P K q r H ht k p (fun _=>True)
    (Eventually.of_forall fun _=>True.intro)
  have hZ':= EarningsRate.atMask P.run (RateCover.stepRate m) r.prepared
  have A:= visa_onPath P.run r.prepared t
  have f:=RateCover.includes _ _ _ m
  let B':= _root_.Zephyr.Chern.SprigFee.paid P
  exact ⟨P,K,x,E,hy,hZ',A,r,Preparation.postpaid P.run f r.prepared,t,
    Preparation.warmDust P.run (InkCover.fuels f (by rw [P.par.kJ]; exact ⟨2,rfl⟩) P.par.kJ.ge u v Z s p1 p2) r.prepared,
    B', singleRootSupported P r hZ' A B', Pay,kC,Γ,Tξ,n,
    bandRadius P.run ((RateCover.includes _ _ _ m).staysOn (by rw [P.par.kJ]; exact ⟨2,rfl⟩) P.par.kJ.ge u v Z s p1 p2 Mc ((mul_le_mul_of_nonneg_right (le_add_of_nonneg_left (by norm_num)) hz).trans h.le)) r.prepared⟩

#check planetaryMarked128
#print axioms planetaryMarked128
#print axioms integrates_full
#print axioms fundRoot
#print axioms concordance
#print axioms traced_jet
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
