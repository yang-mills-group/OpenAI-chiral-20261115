import VerifiedSatinSelectedSectors
import YM.SU5.Reconstruction.NoWrap
set_option autoImplicit false
set_option synthInstance.maxSize 30000
set_option maxRecDepth 6500
set_option maxHeartbeats 440000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.Reconstruction
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory
  RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder
  InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark Vacancy SatinVerification
open Selected PhaseChoice PhaseChoice.SameCharacter PhaseChoice.Theory
open Tapestry Tapestry.Altitude Tapestry.Exhibition

/-! Multiplication of insertions on disjoint EUCLIDEAN compact regions works
also at microscopic all-paid levels, at sufficiently large scaled volume independently
of cutoff. Use for translating into bare correlation constraints. -/
open PiTensorProduct (tprod)
variable {Λ : Preparation} {l : ℕ} (Y : Course Λ (VolumeCape.Dream.Nimbus l)) (H : Real.exp 1 ≤ Λ.x)
local notation "K" => tent Y H
variable (A B : Set RSpace) (p : Disjoint A B) (S T : BillOfWork) (i k : ℕ)
local notation "Q" => tidalDressing Y H i k
local notation "U" n:max => frameBudget S Λ l n
local notation "V" n:max => frameBudget T Λ l n

lemma native_finish (x : sequenceOf (tent Y H)) (h : ∀ u,x u∈ bay K (S u) true)
    (n : ℕ) (t : Tapestry.Pay Y n i k) :
    AtSupport false (Satin.region (U n) (Journey.side Y i n)) (attire ((Q).finish n x)) := by
  obtain ⟨f,rfl⟩:= motif_represents K S x h
  exact wearSupport Y H i k n S f t

include p
lemma native_purchase (a : ∀ n, silhouette Λ l n (S n) ⊆ A)
    (b : ∀ n, silhouette Λ l n (T n) ⊆ B)
    (v : ∀ n : ℕ, FullDistances (frameBudget S Λ l n ∪ frameBudget T Λ l n) (Journey.side Y i n))
    (x y : sequenceOf (tent Y H)) (hx : ∀ u : ℕ, x u∈ bay K (S u) true)
    (hy : ∀ u : ℕ, y u∈ bay K (T u) true) (n : ℕ) (t : Tapestry.Pay Y n i k) :
    (Q).finish n (x*y) = (Q).finish n x * (Q).finish n y := by
  induction n with
  | zero=> exact map_mul ((Q).perceive 0) (x 0) (y 0)
  | succ n ih=>
    have Pq:Tapestry.Pay Y n i k := ⟨t.1,Nat.le_of_lt t.2⟩
    have hu:=native_finish Y H S i k x hx n Pq
    have hv:=native_finish Y H T i k y hy n Pq
    have hp:= separatedPhys (supported_iff.mpr (future_budget S a n))
      (supported_iff.mpr (future_budget T b n)) (Disjoint.preimage (fun x:RSpace=> fun j:Axis=> x j/2) p) -- order `.preimage _ p`, name
    have he: (Q).surge n ((Q).finish n x*(Q).finish n y)=(Q).surge n ((Q).finish n x)*(Q).surge n ((Q).finish n y) := by
        apply attireL_inj; -- unfold surge
        change attire (music Y n i k _)=attire (music Y n i k _*music Y n i k _)
        rw [music,flowing,attire_mul,attire_mul,flowing,flowing]
        exact ascendSep Y n i k t hu hv (fun x a y b=> distances_separate (v n) hp a b)
    simp only [Decking.finish,Pi.mul_apply,map_mul, ih Pq,he]; ac_rfl

lemma collect_native_pair (S T : BillOfWork) (a : ∀ n, silhouette Λ l n (S n) ⊆ A)
    (b : ∀ n, silhouette Λ l n (T n) ⊆ B)
    (v : ∀ n : ℕ, FullDistances (frameBudget S Λ l n ∪ frameBudget T Λ l n) (Journey.side Y i n))
    (x y : Cloud (Dome (tent Y H))) (n : ℕ) (hx : x∈ fountainHeads K S n)
    (hy : y∈ fountainHeads K T n) (t : Tapestry.Pay Y n i k) :
    breathing Y H n i k (x*y)= breathing Y H n i k x*breathing Y H n i k y := by
  apply boarded (P:={f| Officer (Set.Iic n) (fun z=> bay K (S z) true) f})
    (M:=fun x=>breathing Y H n i k (x*y)= breathing Y H n i k x * breathing Y H n i k y) ?_ ?_ ?_ ?_ hx -- force placeholders
  · intro f (g : Officer (Set.Iic n) _ f)
    apply boarded (P:={f| Officer (Set.Iic n) (fun z=> bay K (T z) true) f})
      (M:=fun y=>breathing Y H n i k ((tprod ℂ f)*y)= breathing Y H n i k (tprod ℂ f) * breathing Y H n i k y) ?_ ?_ ?_ ?_ hy
    · intro F (G : Officer (Set.Iic n) _ F)
      have a' := g.visible _ _ Set.Subset.rfl; have b' := G.visible _ _ Set.Subset.rfl
      unfold breathing
      rw [PiTensorProduct.tprod_mul_tprod, Decking.reckon_paid _ _ _ (a'.together b'),
        Decking.reckon_paid _ _ _ a', Decking.reckon_paid _ _ _ b']
      exact native_purchase Y H A B p S T i k a b v f F g.observes G.observes n t
    · simp
    · intro p q _ _ g h; rw [mul_add,map_add,g,h,map_add,mul_add]
    intro c y _ hy; rw [Algebra.mul_smul_comm (A:=Altitude.Cloud (Dome (tent Y H))) c _ _,map_smul,hy,map_smul,Algebra.mul_smul_comm]
  · simp
  · intro p q _ _ g h; rw [add_mul,map_add,g,h,map_add,add_mul]
  intro c y _ hy; rw [Algebra.smul_mul_assoc,map_smul,hy,map_smul,Algebra.smul_mul_assoc]

include H
lemma independent_insertion (a : Bornology.IsBounded A) (b : Bornology.IsBounded B) :
    ∀ᶠ i : ℕ in atTop, ∀ (n k : ℕ) (t : Tapestry.Pay Y n i k) (c d : Bool) (x y : Cloud (Dome (tent Y H))),
      x∈ jetty Λ l (tent Y H) c (handstamp A) (Set.Iic n) → y∈ jetty Λ l (tent Y H) d (handstamp B) (Set.Iic n) →
        breathing Y H n i k (x*y)= breathing Y H n i k x*breathing Y H n i k y := by
  filter_upwards [full_distances Y H (a.union b)] with i t n k p' c d x y hx hy
  obtain ⟨S,a,hx⟩ := uniform_support hx
  obtain ⟨T,b,hy⟩ := uniform_support hy
  refine collect_native_pair Y H A B p i k S T a b (fun m=> t m _ ?_) x y n hx hy p'
  intro u h; rcases Finset.mem_union.mp h with k| k
  · exact Or.inl ((supported_iff.mpr (future_budget S a m)).contains k)
  exact Or.inr ((supported_iff.mpr (future_budget T b m)).contains k)

lemma local_product_hierarchy {i k : ℕ → ℕ} {I : ℕ → Family (tent Y H) → ℕ → ℂ} {E : ℕ → Family (tent Y H) → ℂ}
    (V' : Universal Y H i k I E)
    (G : GroundExtension (i := i) (k := k) (E := E) Y H) {L : Rack Λ l} {B' : Clay Λ l}
    (D : Exhibition Y H i k I E L B') (d : Axis) (T : ∀ j : Axis, Arena Y H G.history.circuit j 0 false)
    (c : PhaseChoice.Theory.Resident (catalog Y H V' G d false (T d)))
    (a : Bornology.IsBounded A) (b : Bornology.IsBounded B) (x y : Cloud (Dome (tent Y H)))
    {e v : Bool} (t : x∈localEuclidean Λ l (tent Y H) e A) (u : y∈localEuclidean Λ l (tent Y H) v B) :
    ∃ s:ℕ, ∀ᶠ i in atTop, ∀ n:ℕ,s≤n →
      PhaseChoice.onDrawing Y H V' G D d T c (x*y)= PhaseChoice.evaluate Y H V' G d T c n
        ((vistaFinish Y H n D x).val * (vistaFinish Y H n D y).val) ∧
        ∀ k : ℕ, Tapestry.Pay Y n i k →
          attire (breathing Y H n i k (x*y))= attire (breathing Y H n i k x)*attire (breathing Y H n i k y) := by
  obtain ⟨s,U₀,h,a',e₀⟩:= t; obtain ⟨r,U',h',b',e'⟩:= u
  refine ⟨max s r,?_⟩
  filter_upwards [independent_insertion Y H A B p a b] with i hv n hn
  have hx : x∈ circum Λ l K e A (Set.Iic n):= circum_widens Y H a' (Set.Iic_subset_Iic.mpr ((le_max_left _ _).trans hn)) e₀
  have hy : y∈ circum Λ l K v B (Set.Iic n):= circum_widens Y H b' (Set.Iic_subset_Iic.mpr ((le_max_right _ _).trans hn)) e'
  refine ⟨endorse_window Y H V' G D d T c ((Set.inter_self (Set.Iic n)).symm ▸ hx) ((Set.inter_self (Set.Iic n)).symm ▸ hy) p,?_⟩ -- orientation ▸ check
  intro k q
  rw [hv n k q e v x y ((well_spec ..).1 hx).1 ((well_spec ..).1 hy).1]; exact attire_mul ..
end YM.CF.Buffered.Afterglow.Tower.Reconstruction
#print axioms YM.CF.Buffered.Afterglow.Tower.Reconstruction.local_product_hierarchy
