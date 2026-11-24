import YM.CF.Fock.InjectC

/-! Joint nonvanishing and continuous non-real Weyl line. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Fock
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators
open Finset
attribute [local instance] opCStarAlgebra
variable {n : Type*} [LinearOrder n] [Fintype n]
lemma self_t (s : Finset n) : (cutM s)ᵀ=cutM s := by simp [cutM]
lemma cut_real (s : Finset n) : cc (cutM s)=cutM s := by rw [cc,(cutM_idp s).isSelfAdjoint,self_t]
lemma cut_range (s : Finset n) (x : Ket n) (h : ∀ i∉s, x.ofLp i=0) : acts (cutM s) x=x := by
  apply PiLp.ext; intro i; rw [cut_apply]; split_ifs with g; rfl; rw [h i g]
def insertRows (z : Wave n) (t : Finset n) : Ket n := WithLp.toLp 2 fun j => (acts (put j) z).ofLp t
lemma pull_rows {C : Op n} (h : Cᵀ= -C) (t : Finset n) (i : n) :
    (acts (takeF i) (pairWave C)).ofLp t=(acts C (insertRows (pairWave C) t)).ofLp i := by
  rw [pull h,coupleRow,act_sum,WithLp.ofLp_sum,Finset.sum_apply,act_at]; simp_rw [act_smul]; rfl
lemma rows_support (z : Wave n) (t : Finset n) : acts (cutM t) (insertRows z t)=insertRows z t := by
  apply cut_range; intro i hi; change (acts _ _).ofLp t=0; rw [put_row,if_neg hi]
lemma top_present (s : Finset n) (C : Op n) (h : Cᵀ= -C) (g : Nonsing (cutM s) C) :
    (pairWave C).ofLp s≠0 := by
  intro he
  let P := cutM s; let H := P*C*P; let z := pairWave H
  have heq : z=acts (quant P) (pairWave C) := by rw [pair_cov,show Pᵀ=P from self_t _]
  have ht : Hᵀ= -H := by simpa only [self_t s,H,P] using skew_form (A:=cutM s) h
  have hs (t : Finset n) : z.ofLp t=if t ⊆ s then (pairWave C).ofLp t else 0 := by rw [heq,show quant P=cutM s.powerset from quantCut s,cut_apply]; simp
  have hx : ∀ (k : ℕ) (t : Finset n), t ⊆ s → s.card-t.card=k → z.ofLp t=0 := by
    intro k; induction k using Nat.strong_induction_on with
    | h k ih =>
      intro t hg hz; by_cases gt:t=s
      · rw [gt,hs]; simp [he]
      obtain ⟨j, hj, ej⟩ := not_subset.mp (show ¬ s ⊆ t from fun r => gt (Subset.antisymm hg r))
      let u := insert j t; have huo : u ⊆ s := insert_subset hj hg
      let w := insertRows z u
      have hew : acts P w=w := by
        apply cut_range; intro i hi; change (acts _ _).ofLp u=0; rw [put_row,if_neg (fun e => hi (huo e))]
      have hez : w=0 := by
        apply g w (by rw [cut_real]; exact hew)
        have hb : acts (P*C) w=acts H w := by unfold H; rw [act_mul (P*C) P,hew]
        change acts (P*C) w=0; rw [hb]; apply PiLp.ext; intro i
        change (acts H w).ofLp i=0; unfold w; rw [show z=pairWave H from rfl, ← pull_rows ht,take_row]
        change (if i∈u then 0 else parity i u*z.ofLp (insert i u))=0
        split_ifs with l
        · rfl
        by_cases ha : insert i u ⊆ s
        · rw [ih (s.card-(insert i u).card) _ (insert i u) ha rfl,mul_zero]
          have hi := card_le_card ha
          have hL : (insert i u).card=t.card+1+1 := by rw [card_insert_of_notMem l,show u.card=t.card+1 from card_insert_of_notMem ej]
          omega
        rw [hs,if_neg ha,mul_zero]
      have hm : parity j u*z.ofLp t=0 := by
        have hb : w.ofLp j=0 := by rw [hez]; rfl
        change (acts (put j) z).ofLp u=0 at hb; rw [put_row] at hb; simpa [u,ej] using hb
      rw [← one_mul (z.ofLp t),← parity_sq j u,mul_assoc,hm,mul_zero]
  have h0 := hx _ ∅ (empty_subset _) rfl
  unfold z at h0; rw [paired_vac] at h0; exact one_ne_zero h0

def filled (P C : Op n) : Wave n := acts (lineOp P) (pairWave C)
theorem filled_twist (U : UNI n) (P C : Op n) : filled (twist U P) (congrC U C)=acts (quantU U).val (filled P C) := by
  unfold filled; rw [congrC, ← pair_cov,line_twist,twist_formula,act_mul,act_mul]; congr 2; exact act_unit (quantU U) _
lemma nonemptyDiag (s : Finset n) (C : Op n) (h : Cᵀ= -C) (g : Nonsing (cutM s) C) : filled (cutM s) C≠0 := by
  intro ht; unfold filled at ht; rw [cutLine] at ht
  have hm : (acts (cutM {s}) (pairWave C)).ofLp s=0 := by rw [ht]; rfl
  rw [cut_apply,if_pos (mem_singleton_self _)] at hm; exact top_present s C h g hm
lemma nonemptyFill (P C : Op n) (e : IsStarProjection P) (h : Cᵀ= -C) (g : Nonsing P C) : filled P C≠0 := by
  obtain ⟨U,s,rfl⟩ := spot_projection P e
  intro he; let L := congrC (star U) C
  have hz : Lᵀ= -L := skew_form h
  have hc := g.twisted (star U); rw [twist_inv] at hc
  apply nonemptyDiag s L hz hc
  unfold L
  rw [← twist_inv U (cutM s),filled_twist (star U),he,map_zero]
/-- Joint lift onto determinant line. Singular when Nonsing fails may degenerate. -/
def anchored (P C : Op n) := ((‖filled P C‖ : ℂ)⁻¹) • filled P C
@[fun_prop] lemma filled_cont : Continuous (fun t : Op n × Op n => filled t.1 t.2) := by unfold filled; fun_prop
lemma anchor_cont (P C : Op n) (h : filled P C≠0) : ContinuousAt (fun t : Op n × Op n => anchored t.1 t.2) (P,C) := by
  have he : ContinuousAt (fun t : Op n × Op n => (‖filled t.1 t.2‖ : ℂ)⁻¹) (P,C) := (Complex.continuous_ofReal.comp (filled_cont (n:=n)).norm).continuousAt.inv₀ (by simpa using h)
  exact he.smul filled_cont.continuousAt
lemma anchor_g (U : UNI n) (P C : Op n) : anchored (twist U P) (congrC U C)=acts (quantU U).val (anchored P C) := by
  unfold anchored; rw [filled_twist,map_smul,act_unit_norm]
theorem anchorSea (P C : Op n) (e : IsStarProjection P) (h : Cᵀ= -C) (g : Nonsing P C) : Sea P (anchored P C) := by
  constructor
  · unfold anchored; rw [map_smul]; congr 1; unfold filled; rw [← act_mul,show lineOp P*lineOp P=lineOp P from (line_proj e).isIdempotentElem]
  unfold anchored; rw [norm_smul]; simp [nonemptyFill P C e h g]
end YM.CF.Fock
