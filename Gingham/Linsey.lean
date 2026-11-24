import Gingham.Excise
/-! # Vertical determinant transfer
Strengthens paid_move: simultaneity on real smears at spacelike gap,
even on ranking several measurements on the same pair of localized tests.
Costs for starting the matrix taken to already include election on both
marginals. -/
set_option autoImplicit false
set_option maxRecDepth 2000
set_option maxHeartbeats 600000
noncomputable section
namespace YM.OS.Semigroup.Gingham
open Function Set Filter Complex Paley
open scoped NNReal Topology InnerProductSpace ComplexOrder

def Reaches (b : Bool) (f : ℂ→ℂ):Prop :=
    (∃ C:ℝ,Paley.Air f C) ∧ (b = true→
      ∃ D≥ (0:ℝ), ∀z:ℂ, 0 ≤ z.im→ ‖f z-f z.re‖≤ D*z.im)
variable {b:Bool}{f g:ℂ→ℂ}

lemma Reaches.const (z:ℂ): Reaches b (fun _=>z):=
   ⟨⟨‖z‖,continuousOn_const,differentiableOn_const _,fun _ _=>le_rfl⟩,
   fun _=>⟨0,le_rfl,fun _ _=>by simp⟩⟩
lemma Reaches.add (h:Reaches b f)(q:Reaches b g):
    Reaches b (fun t=> f t+ g t):=by
   obtain ⟨C,hf⟩:=h.1
   obtain ⟨R,he⟩:=q.1
   refine ⟨⟨C+R,hf.connects.add he.connects,hf.straight.add he.straight,
     fun z e=>(norm_add_le ..).trans (add_le_add (hf.bounded z e) (he.bounded z e))⟩,
     fun a=>?_⟩
   obtain ⟨D,u,i⟩:=h.2 a
   obtain ⟨E,w,j⟩:=q.2 a
   refine ⟨D+E,by positivity,fun z t=>?_⟩
   rw [show f z+g z - (f z.re + g z.re) =
            (f z-f z.re)+(g z-g z.re) by ring,add_mul]
   exact (norm_add_le ..).trans (add_le_add (i z t) (j z t))

lemma Reaches.mul (h:Reaches b f)(q:Reaches b g):
    Reaches b (fun t=> f t* g t):=by
   obtain ⟨C,hf⟩:=h.1
   obtain ⟨R,he⟩:=q.1
   have p:=hf.rate; have _:=he.rate
   refine ⟨⟨C*R,hf.connects.mul he.connects,hf.straight.mul he.straight,
     fun z e=>?_⟩, fun a=>?_⟩
   · rw[norm_mul]
     exact mul_le_mul (hf.bounded z e) (he.bounded z e) (norm_nonneg _) p
   obtain ⟨D,u,i⟩:=h.2 a
   obtain ⟨E,w,j⟩:=q.2 a
   refine ⟨D*R+C*E,by positivity,fun z t=>?_⟩
   rw [show f z*g z-f z.re*g z.re=(f z-f z.re)*g z + f z.re*(g z-g z.re) by ring]
   refine (norm_add_le ..).trans ?_
   rw[norm_mul,norm_mul,add_mul,mul_assoc,mul_comm R,mul_assoc C,←mul_assoc D]
   exact add_le_add
      (mul_le_mul (i z t) (he.bounded z t) (norm_nonneg _) (by positivity))
      (mul_le_mul (hf.bounded (z.re:ℂ) (show 0 ≤ im (z.re:ℂ) by simp)) (j z t) (norm_nonneg _) p)

lemma does_sum {ι:Type} (w:Finset ι) (X : ι → ℂ → ℂ)
    (q:∀i,Reaches b (X i)):Reaches b (fun z=>∑i∈w,X i z):=by
 classical
 induction w using Finset.induction with
 | empty=> simpa using (Reaches.const 0 (b:=b))
 | insert i w p H=> simpa [p] using (q i).add H

lemma does_prod {ι:Type} (w:Finset ι)(X : ι → ℂ → ℂ)
    (q:∀i,Reaches b (X i)):Reaches b (fun z=>∏i∈w,X i z):=by
 classical
 induction w using Finset.induction with
 | empty=> simpa using (Reaches.const 1 (b:=b))
 | insert i w p H=> simpa [p] using (q i).mul H

variable {ι : Type} [Fintype ι] [DecidableEq ι]
/-- Ensures all diagonals light, as well as full rank -/
def ProofRank (M:Matrix ι ι ℂ) : ℂ := M.det * ∏i,M i i
lemma does_rank (M: ι → ι→ ℂ→ℂ)(q:∀i j, Reaches b (M i j)) :
    Reaches b (fun z=> ProofRank (Matrix.of fun i j=>M i j z)):=by
 classical
 refine Reaches.mul ?_ (does_prod Finset.univ _ (fun i=>q i i))
 simp_rw [Matrix.det_apply', Matrix.of_apply]
 exact does_sum Finset.univ
    (fun σ:Equiv.Perm ι=>fun z=> (Equiv.Perm.sign σ:ℤ)*∏i,M (σ i) i z) fun σ=>
       (Reaches.const _).mul (does_prod Finset.univ _ (fun i=> q _ i))

lemma rank_iff (M:Matrix ι ι ℂ):
    ProofRank M ≠ 0 ↔ M.det ≠ 0 ∧ ∀i,M i i ≠ 0 := by
   simp [ProofRank, Finset.prod_eq_zero_iff] -- tune

lemma rank_warm :Continuous (ProofRank (ι:=ι)) :=
   continuous_id.matrix_det.mul (continuous_finsetProd _ (fun i _=>
      continuous_id.matrix_elem i i))


variable {H:Hilbert}{a:Axis}(S:Semigroup H a)

lemma incandescent (v w:ι→H):
    Reaches false (fun z=>ProofRank (Matrix.of fun i j=>S.J 0 (v i) (w j) z)) :=
   does_rank _ (fun i j=>⟨⟨_,S.altitude 0 (v i) (w j)⟩,by simp⟩)

lemma luminary (v:ι→H)(w:ι→ S.muslin):
    Reaches true (fun z=>ProofRank (Matrix.of fun i j=>S.J 0 (v i) (w j).val z)) :=
   does_rank _ (fun i j=>
     ⟨⟨_,S.altitude 0 (v i) (w j).val⟩,fun _=>J_lift S (v i) (w j)⟩)


theorem move_rank (v:ι→H) (w:ι→S.muslin) {T : ℝ≥0} (u : 0 < T)
    {t : ℝ} (p : ProofRank (Matrix.of fun i j=>
        inner ℂ (v i) (S.edge t (S.E T (w j).val))) ≠ 0)
    {l r : ℝ} (y : l < r) :
    ∃ s ∈ Ioo l r, ProofRank (Matrix.of fun i j=>
      inner ℂ (v i) (S.unit.translation (s • basis a) (w j).val)) ≠ 0 := by
  by_contra! e
  let Z (z:ℂ):=ProofRank (Matrix.of fun i j=> S.J 0 (v i) (w j).val z)
  have h0 : ∀ s ∈ Ioo l r,Z (s:ℝ) = 0 := by
    intro s hs; unfold Z; simp_rw [veers,zero_add]; exact e s hs
  have h:Reaches true Z := luminary S v w
  obtain ⟨C,n⟩:=h.1
  obtain ⟨D,d,f⟩ := h.2 rfl
  have hv := Air.squared_interval n f y d h0
  apply p
  simpa only [Z,J,ray,S.unit.origin,ContinuousLinearMap.id_apply,Real.toNNReal_coe,
     Pi.zero_apply] using (hv (show (⟨t, T⟩ : ℂ) ∈ loft from u))


theorem shorter_rank (v w:ι→H) {T : ℝ≥0} (u : 0 < T)
    (p : ProofRank (Matrix.of fun i j=>inner ℂ (v i) (S.E T (w j))) ≠ 0)
    {l r : ℝ} (x : 0 ≤ l) (y : l < r) :
    ∃ t : ℝ≥0, (t:ℝ) ∈ Ioo l r ∧
      ProofRank (Matrix.of fun i j=> inner ℂ (v i) (S.E t (w j))) ≠ 0 := by
  by_contra! e
  let Z (z:ℂ):=ProofRank (Matrix.of fun i j=> S.J 0 (v i) (w j) z)
  have h0 : ∀ t : ℝ, t ∈ Ioo l r → Z ⟨0,t⟩ = 0 := by
    intro t ht
    have hs := Real.coe_toNNReal t (show 0 ≤ t from le_trans x ht.1.le)
    have hr := e t.toNNReal (hs.symm ▸ ht)
    exact by simpa only [Z,J,ray,S.unit.origin,S.birth,ContinuousLinearMap.id_apply] using hr
  obtain ⟨C,q⟩:=(incandescent S v w).1
  have hv := Air.heights q x y h0
  apply p
  exact by simpa only [J,ray,S.unit.origin,ContinuousLinearMap.id_apply,Real.toNNReal_coe,S.birth,
     Pi.zero_apply] using (hv (show (⟨0, T⟩ : ℂ) ∈ loft from u))

lemma downward_rank (ω:H)(A B:ι→ ℝ≥0→H.Op)(g:Ano S ω)
    (w:∀i,S.Covetails (A i))(c:∀j,S.Covetails (B j))
    {s t : ℝ≥0} (p : 0<s) (q : 0<t) (y : Cross a)
    (u : ProofRank (Matrix.of fun i j=>
          inner ℂ (jut ω (A i s)) (S.U y (jut ω (B j t)))) ≠ 0)
    (d : ℝ≥0) (h : 0<d) :
    ∃ r : ℝ≥0, 0<r ∧ r<d ∧ ProofRank (Matrix.of fun i j=>
      inner ℂ (jut ω (A i r)) (S.U y (jut ω (B j r)))) ≠ 0 := by
  let e := min d (min s t)/2
  have pe : 0<min d (min s t) := lt_min h (lt_min p q)
  have ke : 0<e := half_pos pe
  have he : e ≤ d/2 := by
    exact div_le_div_of_nonneg_right (min_le_left ..) zero_le_two
  have le := half_lt_self pe
  have lc : e<s := le.trans_le ((min_le_right ..).trans (min_le_left ..))
  have lt : e<t := le.trans_le ((min_le_right ..).trans (min_le_right ..))
  simp_rw [fun (i j:ι)=> jut_rebalance S ω _ _ g (w i) (c j) ke ke lc.le lt.le y] at u
  have x : 0 < s-e+(t-e) := add_pos (tsub_pos_of_lt lc) (tsub_pos_of_lt lt)
  obtain ⟨r,l,n⟩ := shorter_rank S (fun i=>jut ω (A i e)) (fun j=>S.U y (jut ω (B j e))) x u (le_refl _) (show (0:ℝ)<d from h)
  have rl : 0 < r := l.1
  have ru : r < d := l.2

  have er : e ≤ e+r/2 := self_le_add_right ..
  refine ⟨e+r/2,ke.trans_le er,?_,?_⟩
  · refine (add_lt_add_of_le_of_lt he ((div_lt_div_iff_of_pos_right (zero_lt_two' ℝ≥0)).mpr ru)).trans_eq (add_halves _)
  simp_rw [fun (i j:ι)=> jut_rebalance S ω _ _ g (w i) (c j) ke ke er er y, add_tsub_cancel_left, add_halves];exact n

open Boundary Probe
lemma sunup_rank (v : S.muslin) (g:Ano S v.val)
    (n : inner ℂ v.val v.val = 1)
    {Q₁ Q₂ : ι→ℝ≥0 → H.Op} {A B :ι→ S.Detector}
    (h :∀i, S.Instates (Q₁ i) (A i)) (k :∀j, S.Instates (Q₂ j) (B j))

    (f u : Test4) {A':ι→Module.End ℂ S.muslin} (e :∀i, S.Faces (A i f) (A' i))
    {t r : ℝ≥0} (w : 0<t) (z : 0<r) (l b : ℝ)
    (p : ProofRank (Matrix.of fun i j=>
          inner ℂ (age S l (jut v.val (S.rasp (Q₁ i t) f)))
                 (age S b (jut v.val (S.rasp (Q₂ j r) u)))) ≠ 0)
    (ε : ℝ) (y : 0<ε) :
    ∃ s : ℝ, |s| < ε ∧ ProofRank (Matrix.of fun i j=>
          rfault S v (A' i) (B j (ahead (s • basis a) u))) ≠ 0 := by
  have m(i j:ι):inner ℂ (age S l (jut v.val (S.rasp (Q₁ i t) f)))
                 (age S b (jut v.val (S.rasp (Q₂ j r) u))) =
     inner ℂ (rjut S v (A i f)).val
        (S.edge (-l+b) (S.E (t+r) (rjut S v (B j u)).val)):=by
   rw [age,age,real_vac S _ g.1 (h i) _ w, real_vac S _ g.1 (k j) _ z,
    ←ContinuousLinearMap.adjoint_inner_right, edge_star,
    ←ContinuousLinearMap.comp_apply (S.edge (-l)), S.send,
    ←ContinuousLinearMap.adjoint_inner_right, S.sym, ←age_heat,
    ←ContinuousLinearMap.comp_apply (S.E t), ←S.time]
  simp_rw [m] at p
  obtain ⟨s,js,q⟩ := move_rank S (fun i=>_) (fun j=> rjut S v (B j u)) (add_pos w z) p (neg_lt_self y)
  exact ⟨s,abs_lt.mpr js, by
    simp_rw [fun i=>rshines S n (e i), fun j=> real_loc S _ g.2 (k j)]
    exact q⟩

end YM.OS.Semigroup.Gingham
