import YM.CF.Buffered.Mark
import YM.Corona.Spend

/-! # Forest locality and independence for advancement

NOT a tree gauge assumption. Address a forest by its `up` at vertices
(by parent cells). Include all height choices when independently averaging.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 16000
set_option maxHeartbeats 580000
noncomputable section
namespace YM.CF.Buffered.Advance
open Function Fock NormedSpace SU Lat Lattice Cube Finset MeasureTheory Branch Reflect Window Wilson Rush Peaks Scroll
open Phase Skye Pastry Tulip Dial Paige Push.SectorMeasure Scree RG Vault Fir Peaks Drapes Tap Precision Tree Next.SectorChange
open scoped Topology BigOperators InnerProductSpace ComplexConjugate Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
section
variable {c f : Side} {G : Ratio c f}
def sameForest (S : Support c) (F H : Forest G) := ∀ i, G.parent i ∈ S → F.up i=H.up i
noncomputable def stitchF (S : Support c) (F H : Forest G) : Forest G where
  up i := if G.parent i∈S then F.up i else H.up i
  height i:= if G.parent i∈ S then F.height i else H.height i
  bound i:=by split; exact F.bound i; exact H.bound i
  stays i h:=by split; exact F.stays i h; exact H.stays i h
  rise i h:=by
    by_cases p:G.parent i ∈ S <;> simp only [p,ite_true,ite_false,F.stays i h,H.stays i h] <;> first| exact F.rise i h| exact H.rise i h
lemma stitch_self (S : Support c) (F H : Forest G) : sameForest S (stitchF S F H) F := fun _ h=> if_pos h
lemma stitch_separate {S T : Support c} (F H : Forest G) (h : Disjoint S T) : sameForest T (stitchF S F H) H := fun _ k=> if_neg fun p=> Finset.disjoint_left.mp h p k
private lemma forest_ext {A B: Forest G} (h:A.up=B.up) (hz:A.height=B.height) : A=B := by cases A; cases B; congr
private lemma stitch_twice (S : Support c) (F H : Forest G) : stitchF S (stitchF S F H) (stitchF S H F) = F := by
  apply forest_ext <;> funext x <;> by_cases h : G.parent x ∈ S <;> simp [stitchF,h]
def stitchBoth (S : Support c) : Equiv.Perm (Forest G × Forest G) where
  toFun x:=(stitchF S x.1 x.2, stitchF S x.2 x.1)
  invFun x:=(stitchF S x.1 x.2, stitchF S x.2 x.1)
  left_inv x:= by dsimp only; rw [stitch_twice,stitch_twice]
  right_inv x:= by dsimp only; rw [stitch_twice,stitch_twice]

section mean
variable {X : Type*} [NormedRing X] [NormedAlgebra ℝ X]
def avgF (u : Forest G → X) := (Fintype.card (Forest G) : ℝ)⁻¹ • ∑ i, u i
-- Works even for empty indexing; mass-one needed separately.
lemma forest_product {S T : Support c} {u v : Forest G → X} (p : Disjoint S T)
    (h : ∀ F H, sameForest S F H → u F=u H) (k : ∀ F H, sameForest T F H → v F=v H) :
    avgF (u*v) = avgF u * avgF v := by
  by_cases n : Nonempty (Forest G); swap
  · letI:IsEmpty (Forest G):=not_nonempty_iff.mp n
    simp [avgF,Fintype.card_eq_zero]
  let s := Fintype.card (Forest G); have he : 0<(s:ℝ):= Nat.cast_pos.mpr Fintype.card_pos
  let f := fun x:Forest G=>u x*v x; let A(x:Forest G × Forest G) := f x.1
  have hx : (∑ i, u i) * ∑ i, v i = (s:ℝ) • ∑ i, f i := by
    have hw(z: Forest G × Forest G): A (stitchBoth S z)=u z.1*v z.2 := congrArg₂ (· * ·) (h _ _ (stitch_self S z.1 z.2)) (k _ _ (stitch_separate z.1 z.2 p))
    calc
      _ = ∑ i, ∑ j, u i * v j := by rw [sum_mul]; simp_rw [mul_sum]
      _ = ∑ i:(Forest G × Forest G), A i := by rw [←Equiv.sum_comp (stitchBoth S)]; simp_rw [hw,Fintype.sum_prod_type]
      _ = _ := by rw [Fintype.sum_prod_type]; simp only [A,sum_const,card_univ,s, smul_sum, Nat.cast_smul_eq_nsmul]
  unfold avgF; rw [Algebra.smul_mul_assoc,Algebra.mul_smul_comm,hx]; change (s:ℝ)⁻¹ • _= (s:ℝ)⁻¹ • ( (s:ℝ)⁻¹ • ((s:ℝ) • _)); rw [inv_smul_smul₀ he.ne']; rfl
end mean
lemma same_hike {S : Support c} {F H : Forest G} (p : sameForest S F H) {x} (h : G.parent x ∈ S) : F.hike x = H.hike x := by
  induction x using Forest.hike.induct F with
  | case1 i g ih=>
    rw [Forest.hike,dif_pos g]; conv_rhs=> rw [Forest.hike,dif_pos g]
    rw [←p i h, ih ((F.stays i g).symm ▸ h)]
  | case2 i g=> rw [Forest.hike,dif_neg g]; conv_rhs =>rw [Forest.hike,dif_neg g]
lemma hike_length (F : Forest G) (x y : Site f) (p : y ∈ visits x (F.hike x)) : separation x y ≤ 4*G.count.val := (Extra.Iteration.Shapes.visits_dist x y _ p).trans ((F.hike_lower x).trans (F.bound x))
end
section localities
variable {N P : Side} (G : Ratio N P)
local notation "g" => ratio G
local notation "L" => G.count.val
theorem seine_local (ho : Odd G.count.val) {S : Support (More P)} {F H : Forest (ratio G)} {V V' : Pane N} {W W' : Pane P}
    (w : Agrees (halo (4*L) S) W W') (v : Agrees (S.image ((ratio G).parent)) V V') (t : sameForest (S.image ((ratio G).parent)) F H) (q : Chi) (d : ℝ) :
    Agrees S (seine G F q d W V) (seine G H q d W' V') := by
  rintro ⟨i,j⟩ h k; change i∈ S at h; change i+step j ∈ S at k
  have he(x : Seat P) (hx : x ∈ S) : F.foldAt W x = H.foldAt W' x := by
    have hg := same_hike t (mem_image_of_mem ((ratio G).parent) hx)
    have hr(y : Seat P)(t': y∈ visits x (H.hike x)): y∈ halo (4*L) S:= halo_spec.mpr ⟨x,hx,hike_length H x y t'⟩
    unfold Forest.foldAt; rw [hg]; exact congr_arg Inv.inv (travel_local _ _ _ _ (fun i h k=> w i (hr _ h) (hr _ k)))
  have hz : Precision.replica (ratio G) V (i,j)=Precision.replica (ratio G) V' (i,j) := by
    unfold Precision.replica; split; rfl
    next hx =>
      have hr:= (ratio G).parents_hop ho i j; split at hr
      · exact v ((ratio G).parent i,j) (mem_image_of_mem _ h) (show (ratio G).parent i+step j∈ S.image _ from (hr ▸ mem_image_of_mem ((ratio G).parent) k))
      exact (hx hr).elim
  simp only [seine,portU,Lattice.gauge,Pi.inv_apply, he i h, he _ k,w (i,j) (halo_subset (4*L) S h) (halo_subset (4*L) S k), hz]
end localities
end YM.CF.Buffered.Advance
