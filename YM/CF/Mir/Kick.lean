import YM.CF.Mir.Program

/-! Schedule check, for arbitrary coarse weight. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Mir
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Topology
open Function Fock Filter NormedSpace SU Lat Lattice Branch Cube Tenant MeasureTheory Phase Trip Finset
attribute [local instance] opCStarAlgebra
variable {m B : Side} {c : Phase.Part m B} {u v d : ℝ} {W : Scroll m B c}
def markHit {c : Phase.Part m B} (W : Scroll m B c) (d a : ℝ) (v : Index m) := ∑ k:FaceTerm m B, if v∈pavilion m B (driftK k) then rent a (pavilion m B (driftK k))*coinK W d k else 0
lemma pays_hit {a e : ℝ} (h : ∀ i,cellHit m B a (dust W d) i ≤ e) (x : Index m) : markHit W d a x ≤ e := by
  unfold markHit; rw [Fintype.sum_prod_type]
  let v := tariffR m; have he : 0<v := paid_t m
  have H (i : Trip m) : ∑ S:Stamp m B, (if x∈pavilion m B (driftK (i,S)) then rent a (pavilion m B (driftK (i,S)))*coinK W d (i,S) else 0) ≤ v⁻¹*e := by
    calc
      _ = v⁻¹*cellHit m B a (dust W d) (i⁻¹.adv x) := by
        unfold cellHit spotHit; rw [sum_filter,mul_sum]; refine sum_congr rfl ?_; intro S _; unfold driftK; dsimp only; rw [←pad_rot]
        have ht : Injective (adv i) := i.facesA.injective
        have hz : x∈Finset.image i.adv (pavilion m B S)↔ i⁻¹.adv x∈pavilion m B S := by
          rw [mem_image]; constructor; rintro ⟨j,h,p⟩; rw [←p,adv_back]; exact h
          intro h; exact ⟨_,h,adv_last ..⟩
        by_cases g:i⁻¹.adv x∈pavilion m B S
        · rw [if_pos (hz.mpr g),if_pos g]; unfold rent; rw [card_image_of_injective _ ht]; exact mul_left_comm ..
        rw [if_neg (fun p=>g (hz.mp p)),if_neg g,mul_zero]
      _ ≤ _ := mul_le_mul_of_nonneg_left (h _) (by positivity)
  apply (sum_le_sum (fun i (_:i∈univ)=>H i)).trans
  simp only [sum_const,card_univ,nsmul_eq_mul]; change v*(v⁻¹*e)≤_; rw [←mul_assoc,mul_inv_cancel₀ he.ne',one_mul]
structure RunsB (m B : Side) (a : Phase.Part m B) (W : Scroll m B a) (u v d e k ε : ℝ) : Prop where
  scaleK : ScaleK u v W
  budget : Budget B e d
  costs i : markHit W d k i ≤ ε

theorem schedule (k ε : ℝ) (hk : 0<k) (h : 0<ε) : ∃ u v:ℝ, 0<u ∧ 0<v ∧ ∃ n:ℕ, ∀ B:Side,n≤B.val→ ∃ r:ℝ, 0<r ∧ ∀ e:ℝ,0≤e→e≤r→ ∀ (m : Side) (a : Phase.Part m B), ∃ W : Scroll m B a, RunsB m B a W u v (quantile u B) e k ε := by
  obtain ⟨u,v,hu,hv,A⟩ := composeK; obtain ⟨n,H⟩ := lot_size hu hv hk h
  refine ⟨u,v,hu,hv,n,fun B g=>?_⟩; obtain ⟨r,e,p⟩ := H B g
  refine ⟨r,e,?_⟩; intro q h H m c; obtain ⟨W,Q⟩ := A m B c; obtain ⟨x,y,l⟩ := p q h H; exact ⟨W,Q,x,pays_hit (fun i=>kit hu hv Q x hk y l i)⟩
lemma cabin_g {e : ℝ} (H : ScaleK u v W) (b : Budget B e d) {x} (p:x∈payer m B e) (g) : cabin W (Lattice.gauge g x.1,partner m B g x.2)=cabin W x := sum_congr rfl fun i _=> twist_gate H b p g i
end YM.CF.Mir
