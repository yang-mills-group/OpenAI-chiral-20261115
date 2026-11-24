import YM.CF.Cubes.Flag

/-! Simultaneously coning up to 6 edges to an assignment of values. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Cube
open Lattice Lat SU Finset
open scoped Matrix.Norms.L2Operator MatrixOrder Topology
attribute [local instance] opCStarAlgebra
variable {m B N : Side}

def broad : ℝ := (uniform_miss (6*budgetW)).choose
lemma broad_pos : 0 < broad := (uniform_miss _).choose_spec.1
def margin : ℝ := broad/2
lemma margin_pos : 0 < margin := half_pos broad_pos
lemma broad_margin : margin < broad := half_lt_self broad_pos
def ending (r : Finset Row) (j : Row) := ∀ i∈r, i < j
def capRow (s : ArrayF m) (j : Row) (u : Field m) : ArrayF m := fun a => if a.2=j then u a.1 else s a

lemma choose_tip (m B U) {I : Type} [DecidableEq I] (S : Finset I) (f : I → ArrayF m) (r : I → Finset Row) (j : Row) (h : S.card≤6)
    (a : Index m) : ∃ v : Ballot, ∀ i∈S, ∀ l∈permits m (a,j) (insert j (r i)), broad < ‖restrain margin (train m B U (f i) a l) v.val‖ := by
  classical
  let t := S.biUnion fun i=>(permits m (a,j) (insert j (r i))).image (fun x=>(i,x))
  have he : t.card≤6*budgetW := by
    apply (card_biUnion_le ..).trans
    apply le_trans (sum_le_sum (fun i hi => (card_image_le).trans (permits_cap m (a,j) (insert j (r i)))))
    simpa using Nat.mul_le_mul_right budgetW h
  let q (x : t) := train m B U (f x.val.1) a x.val.2
  have hk (x : t) : (q x).length<10 := by
    unfold q; rw [train_len]; obtain ⟨i,-,H⟩ := mem_biUnion.mp x.property; obtain ⟨l,g,y⟩ := mem_image.mp H
    rw [←y]; exact lt_of_le_of_lt (total_len (permits_iff.mp g).1) (by norm_num)
  choose v Hv using fun x=> normal (q x) (hk x)
  obtain ⟨w,H⟩ := (uniform_miss _).choose_spec.2 _ t he v
  refine ⟨w,?_⟩; intro i hi l hl
  let x : t := ⟨(i,l),mem_biUnion.mpr ⟨i,hi,mem_image_of_mem _ hl⟩⟩
  exact (H x).trans_le (strain_margin _ (q x) (v x) _ (Hv x))
lemma check_tip (m B U) {I : Type} [DecidableEq I] (S : Finset I) (f : I → ArrayF m) (r : I → Finset Row) (j : Row)
    (h : S.card≤6) (a : Index m) (w : Field m) : ∃ v : Ballot, ∀ i∈S, Check m B margin U (capRow (f i) j (Function.update w a v)) (insert j (r i)) (a,j) := by
  obtain ⟨v,H⟩ := choose_tip m B U S (fun i=>capRow (f i) j w) r j h a
  refine ⟨v,?_⟩; intro i hi l hl
  simp only [show capRow (f i) j (Function.update w a v) (a,j)=v by simp [capRow]]
  rw [train_eq m B U (capRow (f i) j w) a l _]; exact broad_margin.trans (H _ hi _ hl)
  rintro ⟨⟨b,g⟩,o⟩ hb
  have he : (b,g)≠(a,j) := (move_mem (permits_iff.mp hl).1 _ hb).2.2
  unfold capRow; dsimp only; split_ifs with hx
  · subst g; have hg : b≠a := fun h=>he (by rw [h]); rw [Function.update_of_ne hg]
  rfl
lemma row_dep (m B U s j r a e) {w v : Field m} (h : Check m B e U (capRow s j w) r (a,j))
    (he : ∀ b, Fits m b a → w b=v b) : Check m B e U (capRow s j v) r (a,j) := by
  intro l hl
  rw [train_eq m B U (capRow s j w) a l _, show capRow s j v (a,j)=capRow s j w (a,j) by simp [capRow,he a (fits_id m a)]]
  · exact h l hl
  rintro ⟨⟨b,g⟩,o⟩ hb
  have hb : Fits m b a := (move_mem (permits_iff.mp hl).1 _ hb).1; simp [capRow,he b hb]
lemma extensions (m B U) {I : Type} [DecidableEq I] (S : Finset I) (f : I → ArrayF m) (r : I → Finset Row) (j : Row)
    (h : S.card≤6) (he : ∀ i∈S, ending (r i) j) (hg : ∀ i∈S, Verified m B margin U (f i) (r i)) :
    ∃ v : Field m, ∀ i∈S, Verified m B margin U (capRow (f i) j v) (insert j (r i)) := by
  have q (k : ℕ) : ∃ v : Field m, ∀ a, degree m a < k → ∀ i∈S, Check m B margin U (capRow (f i) j v) (insert j (r i)) (a,j) := by
    induction k with
    | zero => exact ⟨fun _ => Classical.arbitrary Ballot,fun _ hi=> by omega⟩
    | succ k ih =>
      obtain ⟨w,hw⟩ := ih
      choose p H using fun a => check_tip m B U S f r j h a w
      let v : Field m := fun a=> if degree m a=k then p a else w a
      refine ⟨v,?_⟩; intro a ha i hi
      by_cases g : degree m a=k
      · apply row_dep _ _ _ _ _ _ _ _ (H a i hi); intro b hb; by_cases gx : b=a
        · subst b; simp [v,g]
        have hu := fits_degree hb gx; rw [g] at hu; simp [v,hu.ne,gx]
      apply row_dep _ _ _ _ _ _ _ _ (hw a (by omega) i hi); intro b hb
      have he : degree m b≤degree m a := card_le_card (fits_os hb)
      unfold v; rw [if_neg (by omega)]
  obtain ⟨v,H⟩ := q 5
  refine ⟨v,?_⟩; intro i hi ⟨a,t⟩ ht
  rcases mem_insert.mp ht with hq|hq
  · simp only at hq; subst t; exact H a (lt_of_le_of_lt (degree_le ..) (by norm_num)) i hi
  have hj : t < j := he i hi _ hq
  intro l hl; have G := permits_iff.mp hl
  have hr {x : Ramp m} (h : x∈l) : x.1.2 < j := lt_of_le_of_lt (move_mem G.1 _ h).2.1 hj
  have he : InRows (r i) l := fun x hx=>(mem_insert.mp (G.2 x hx)).resolve_left (hr hx).ne
  rw [show capRow (f i) j v (a,t)=f i (a,t) from if_neg hj.ne,train_eq m B U (f i) a l _]; exact hg i hi _ hq _ (permits_iff.mpr ⟨G.1,he⟩)
  exact fun x hx=>if_neg (hr hx).ne
lemma verified_restrict {s t : ArrayF m} {e U r u} (h : Verified m B e U s u) (g : r⊆u)
    (he : ∀ i : Spot m, i.2∈r → t i=s i) : Verified m B e U t r := by
  intro a ha l hl; have hp := permits_iff.mp hl
  rw [he a ha,train_eq m B U s _ _ _ (fun j hj=>he _ (hp.2 j hj))]
  exact h a (g ha) _ (permits_iff.mpr ⟨hp.1,fun i hi=>g (hp.2 i hi)⟩)
end YM.CF.Cube
