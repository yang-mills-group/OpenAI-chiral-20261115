import YM.CF.Pastry.Pie
set_option linter.unusedSectionVars false

/-! Local support of a pie. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Pastry
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Topology
open Function Fock Finset NormedSpace Petal Branch
attribute [local instance] opCStarAlgebra
variable {n Y G D : Type*} [LinearOrder n] [Fintype n] [Fintype Y] [DecidableEq Y] [TopologicalSpace D]
-- Covariance from the actual support family
variable {K : Stage Y n D G} {s t z : Tag K} {W : Toll n} {A : Raw D n} {S : Seal Y}
lemma stiff (h : Ticket s t S W A) : W≠0→ Grove K.F S := by
  intro p; by_contra g; apply p; funext i j; change W i j=0; by_contra f; exact g (((h.expo i j).triggered f).1)
lemma stiff' (h : Ticket s t S W A) (p : ledgerV W≠0) : Grove K.F S := stiff h (fun l=>p (by simp [l,ledgerV]))
lemma whorl (u v : Bool) {A : Op n} {W : Toll n} (S : Finset (LeanV n)) (T : Finset n) (w : ∀ i j, ‖A i j‖≤W i j) (g : ∀ i j, W i j≠0→i∈T∧j∈T) (p : ∀ i∈T, ∀ b, (b,i)∈S) : Flour S (faceD u v A) := by
  unfold faceD twinD; refine Flour.sum _ (fun i _=> Flour.sum _ (fun j _=>?_))
  by_cases k:W i j=0
  · rw [norm_le_zero_iff.mp ((w ..).trans k.le),zero_smul]; exact Flour.trivial
  exact (Flour.putPut S (p _ (g i j k).1 u) (p _ (g i j k).2 v)).smul _
lemma ice_tier (u v : Bool) {A : Op n} {W : Toll n} (w : ∀ i j, ‖A i j‖ ≤ W i j) (H : ℝ) (h : 0≤H) : tier H (faceD u v A)≤ ledgerV W*H^2 := by
  unfold ledgerV; simp only [pow_two,sum_mul]; apply (tier_sum h ..).trans; apply sum_le_sum; intro i _; apply (tier_sum h ..).trans; apply sum_le_sum; intro j _; rw [whiteℂ]; exact mul_le_mul (w ..) (white_two H h) (pitch h _) ((norm_nonneg _).trans (w i j))
lemma twinC (u v : Bool) : Continuous (faceD u v (n:=n)) := by
  apply continuous_finsetSum; intro i _; apply continuous_finsetSum; intro j _; exact (show Continuous (fun A:Op n=>A i j) from (continuous_apply _).comp (continuous_apply _)).smul continuous_const
variable {B C : Raw D n} {U V : Toll n}
structure Linen (S : Seal Y) (A B C : Raw D n) (s : Tag K) (W U V : Toll n) : Prop where
  low : Ticket s.reverseV s S W A
  middle : Ticket s.reverseV s.reverseV S U B
  high : Ticket s s.reverseV S V C
namespace Linen
variable (h : Linen S A B C s W U V)
include h
def coins (W U V : Toll n) := ledgerV W+ ledgerV U+ledgerV U+ledgerV V
lemma coast : 0 ≤ coins W U V := by
  have he : 0 ≤ ledgerV W := sum_nonneg fun i _=> sum_nonneg (fun j _=>h.low.nonn i j)
  have hv : 0 ≤ ledgerV U := sum_nonneg fun i _=> sum_nonneg (fun j _=>h.middle.nonn i j)
  have hl : 0 ≤ ledgerV V := sum_nonneg fun i _=> sum_nonneg (fun j _=>h.high.nonn i j)
  unfold coins; positivity
lemma shore (v : coins W U V ≠0) : Grove K.F S := by
  by_cases g:ledgerV W=0
  · by_cases k:ledgerV U=0
    · exact stiff' h.high (by simpa [coins,g,k] using v)
    exact stiff' h.middle k
  exact stiff' h.low g
lemma fondant (g : Finset (LeanV n)) (k : ∀ i, K.home i ∈ S→ ∀ b,(b,i)∈g) (d : D) : hang (A d) (B d) (C d)∈stretch g := by
  apply (stretch_ok ..).mpr; unfold hang; dsimp only; unfold quilt; rw [sub_eq_add_neg]; apply Flour.smul; apply Flour.add
  let T := board K S; have he (i:n) (v : i∈T) : ∀ b, (b,i)∈g := k _ (mem_filter.mp v).2
  -- availability
  · have He (s t : Tag K) (A : Raw D n) (W : Toll n) (p : Ticket s t S W A) (u v : Bool) : Flour g (faceD u v (A d)) ∧ Flour g (faceD u v (A d)ᵀ) := by
      have hx i j (g : W i j≠0) : i∈ T ∧ j∈T := ⟨mem_filter.mpr ⟨mem_univ _, ((p.expo i j).triggered g).2.1⟩,mem_filter.mpr ⟨mem_univ _,((p.expo i j).triggered g).2.2⟩⟩
      exact ⟨whorl u v g T (fun i j=>(p.expo i j).bounded d) hx he, whorl u v g T (fun i j=>(p.expo j i).bounded d) (fun i j h=>(hx j i h).symm) he⟩
    apply Flour.add (Flour.add (He _ _ _ _ h.low _ _|>.1) (He _ _ _ _ h.middle _ _|>.1)); simpa using ((He _ _ _ _ h.middle true false).2.smul (-1))
  exact whorl true true g (board K S) (fun i j=> (h.high.expo i j).bounded d) (fun i j v=> by
    obtain ⟨h,k⟩:= ((h.high.expo i j).triggered v).2; simp [board,h,k]) (fun i p=>k i (mem_filter.mp p).2)
lemma pool_tier (x : D) (H : ℝ) (p : 0≤H) : tier H (hang (A x) (B x) (C x)).val ≤ coins W U V * H^2 := by
  have he (A : FC (LeanV n)) : tier H (-A)=tier H A := by simpa using whiteℂ H A (-1)
  unfold hang quilt; dsimp only; rw [sub_eq_add_neg,whiteℂ]; apply (mul_le_of_le_one_left (pitch p _) (by norm_num)).trans
  unfold coins; simp only [add_mul]; apply (tier_plus p ..).trans; refine add_le_add ((tier_plus p ..).trans (add_le_add ((tier_plus p ..).trans (add_le_add ?_ ?_)) ?_)) ?_
  · exact ice_tier false false (fun i j=> (h.low.expo i j).bounded x) H p
  · exact ice_tier false true (fun i j=> (h.middle.expo i j).bounded x) H p
  · rw [he]; have ht := ice_tier true false (A:=(B x)ᵀ) (W:=Function.swap U) (fun i j=> (h.middle.expo j i).bounded x) H p
    have hc : ledgerV (Function.swap U)=ledgerV U := sum_comm; rwa [hc] at ht
  exact ice_tier true true (fun i j=> (h.high.expo i j).bounded x) H p
lemma pivotC : Continuous (fun x=>hang (A x) (B x) (C x)) := by
  let g:= h.middle.cont; have he : Continuous (fun x=>(B x)ᵀ) := g.matrix_transpose
  exact (Continuous.subtype_mk (show Continuous (fun x=>quilt (A x) (B x) (C x)) from (continuous_const (y:=(2:ℂ)⁻¹)).smul (((((twinC false false).comp h.low.cont).add ((twinC false true).comp g)).sub ((twinC true false).comp he)).add ((twinC true true).comp h.high.cont))) _)
lemma pivotD (x y : D) (g : K.eval S x y=0) : hang (A x) (B x) (C x)=hang (A y) (B y) (C y) := by
  have he (s t : Tag K) (A : Raw D n) (W : Toll n) (p : Ticket s t S W A) : A x=A y := by
    ext i j; have ht := (p.expo i j).variation x y; rw [g,mul_zero] at ht; exact sub_eq_zero.mp (norm_le_zero_iff.mp ht)
  rw [he _ _ _ _ h.low,he _ _ _ _ h.middle, he _ _ _ _ h.high]
lemma gift (g : G) (x:D) : fold (n:=LeanV n) (closeV (s.run g)) (hang (A x) (B x) (C x))=hang (A (K.drive g x)) (B (K.drive g x)) (C (K.drive g x)) := by
  let y := K.drive g x; let U := (s.run g).val
  have he : star U=(cc U)ᵀ := (ccT _).symm
  have hv : star (cc U)=Uᵀ := by rw [←cc_star,cc,star_star]
  have ht : s.reverseV.run g=ccU (s.run g) := rfl
  rw [Uniform.run,h.low.frame.frame,h.middle.frame.frame,h.high.frame.frame]; change _= hang (cc U * _ * star U) (cc U * _*star (cc U)) (U *_ *star (cc U)); rw [he,hv]
end Linen
end YM.CF.Pastry
