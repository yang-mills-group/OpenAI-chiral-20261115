import ExactRunning.Step.Record
import YM.CF.Vale.Oak

/-!
# The Gold stamps meet the comparison hypotheses
-/
set_option linter.unusedSectionVars false
noncomputable section
namespace ExactRunning
open YM Stationary Lattice Laurent Bloch RG
open Function Filter Finset Matrix
open scoped BigOperators ContDiff Topology ComplexConjugate Matrix


open Precision Wilson Exterior Tree
open CF.Vale CF

local notation "G5" => SU.group
variable {K : Pressure.Teller G5} {P : Patch} {R : ChartRatio G5} {W : Hom.Postal}
variable (B : Gold K P R W)

include B in
lemma cap_of_gold : 0 ≤ K.C := by
  let i := plaquette (⟨(0,1),by decide⟩:PlaqAxes)
  have h := (B.roof 0).1.2.1 i i
  exact (tsum_nonneg h.1).trans h.2.2

def goldPylon (F : ℕ→KindF G5) (h : ∀ i, Endpoint K.top.clip (B.path i) (F i)) (t : ℕ) :
    Pylon G5 :=
  let U := B.roof t
  ⟨K.top.clip,B.path t, F t,B.H t, K.η,W.parcel,K.C,K.top.width,K.top.paths,W.bar,
   K.width,W.reserve,cap_of_gold B,B.mood t,K.top.paths_pos.le,W.rental,
   U.1, U.2.1, B.tied t,U.2.2,h t⟩

lemma gold_ep :
    ∃ (F : ℕ→KindF G5), (∀ i, Endpoint K.top.clip (B.path i) (F i)) ∧
      ∃ a b : ℝ, 0≤a ∧ 0≤b ∧ (∀ i, Grounds a b (F i)) := by
  obtain ⟨a,b,ha,hb,X⟩ :=
    harvest G5 Thera.yet_one K.η W.parcel K.C K.top.clip.direct K.top.width K.top.paths
      K.width W.reserve (cap_of_gold B) K.top.clip.quadratic_pos.le K.top.width_pos K.top.paths_pos.le
  choose F g h using (fun t : ℕ => X _ _ _ _ (B.mood t) (B.tied t)
    (B.roof t).1.2.1 le_rfl (B.roof t).2.1 (B.roof t).2.2)
  exact ⟨F,g,a,b,ha,hb,h⟩

variable (F : ℕ→KindF G5) (h : ∀ i, Endpoint K.top.clip (B.path i) (F i))

lemma gold_blockTie (localChart : LocalRatio R) (t : ℕ) :

    ∃ Z : BlockTie (goldPylon B F h t) (goldPylon B F h (t+1)),
      Z.L=P.L ∧ Z.q = B.charge t := by
  let D := B.deed t
  have hi := B.sold t
  refine ⟨⟨(B.f t).patch, K.bind, (B.lent t).symm ▸ B.cloth, Thera.yet_one, B.Z t, B.charge t, R,localChart,K.η,K.C,W.rise,W.peak,W.gap,W.n,K.width,cap_of_gold B,W.large,W.slow,W.tame,?_,fun m =>D.link rfl,?_,?_⟩,B.lent_L t,rfl⟩
  · intro l h
    have := (B.f t).legal
    exact (D.pay.2.2.2 l (by omega)).1
  · intro m h
    let y := m * (B.f t).L
    let s : StepData m y := ⟨(B.f t).patch,K.bind,rfl⟩
    have e : y.val=m.val*P.L.val := by unfold y;rw [B.lent_L t];rfl
    have es : s = ⟨P,K.bind,e⟩ := by unfold s; congr; exact B.lent t
    change Bid.Larger s (G:=G5)
    exact es.symm ▸ B.robe.bound e h

  intro m hm s
  let Y := m * (B.f t).L
  let g := Classical.choice (select s.ratio (B.f t).odd)
  obtain ⟨u,a,b⟩ := hi.existP m Y rfl hm g
  have hw := hi.all m Y rfl hm g
  exact ⟨g,hw.1,u,a,b,(hw.2 _ a)⟩

end ExactRunning
