import YM.CF.Dial.Bastion
/-! Sums of exponential connected trace bills on mixed sites. -/
set_option autoImplicit false
set_option synthInstance.maxSize 8000
noncomputable section
namespace YM.CF.Dial
open Function Filter Lattice Laurent Bloch Next.Free Metric Lat Finset Branch Cube Tenant SU Rush Drapes Fir Tulip Fock Peaks
open scoped Topology Matrix MatrixOrder BigOperators Matrix.Norms.L2Operator Kronecker InnerProductSpace
attribute [local instance] opCStarAlgebra
variable {ι:Type*}{L:Side}{P A K:Chop ι}
def noon (P A: Chop ι) (x y:TickZ): Chop ι:=fun i _ _ G f=>
 let W:= P i G f; let B:= P i G (chargeB f);
 W*laneC P A (i,y) G f*cc B*(zL P A (i,x) G f)⁻¹+(1-W)-1
abbrev Che (m a:ℕ):= berth m (min a m)
def termJ(m:ℕ)(a:ℕ): TickZ:=if h:m=0 then ⟨0,Set.left_mem_Icc.mpr zero_le_one⟩ else ⟨Che m a,⟨div_nonneg (by positivity) (by positivity),by
  rw [Che,berth,div_le_one (Nat.cast_pos.mpr (Nat.pos_of_ne_zero h))]; exact_mod_cast Nat.min_le_right a m⟩⟩
lemma term_eq(m:ℕ)(p:0<m)(a:ℕ)(h:a≤m):(termJ m a).val=berth m a:=by rw [termJ,dif_neg p.ne']; simp [Che,h]
lemma berth_diff (m:ℕ)(p:0<m)(a:ℕ): berth m (a+1)-berth m a=1/m:=by unfold berth; push_cast; ring
lemma berth_jump {m:ℕ}(p:0<m)(a:ℕ){s:ℝ}(h:s∈railZ m a):|s-berth m a|≤1/m := by rw [abs_of_nonneg (sub_nonneg.mpr h.1),←berth_diff m p a]; exact sub_le_sub_right h.2 _
lemma noontide(i:ι)(P A: Chop ι){N F:Side}(G:Ratio N F)(X:Sew N F)(x y:TickZ): noon P A x y i G (post X)= relay (P i G (post X)) (tonic P A i G (post X) x.val) (tonic P A i G (post X) y.val)-1:=by unfold noon relay tonic body; dsimp only; rw [charge_p,zL_at,lane_at,lane_at]
def earnings(P A:Chop ι)(m:ℕ): Chop ι:=fun i _ _ G z=>∑ l∈Finset.range m,(2:ℂ)⁻¹ • pencil (noon P A (termJ m l) (termJ m (l+1)) i G z)
namespace BoxD
lemma burs {u v: AxisT}:BoxD L u v (fun (_:ι) _ _ _ _=>0):=boxify (k:=0) (C:=0) (fun i _ _ G h v=> Crown.free) (show 0<(1:ℝ) from one_pos) (show 0<(1:ℝ) from one_pos)
lemma fundas {α:Type*}(S:Finset α)(X:α→ Chop ι){u v:AxisT} (p:∀ w∈S,BoxD L u v (X w)):BoxD L u v (fun i _ _ G x=>∑ j∈S,X j i G x):=by
  classical
  induction S using Finset.induction_on with
  | empty=> simp only [sum_empty]; exact burs
  | @insert a s ha ih => simp only [sum_insert ha]; exact (p a (by simp)).add (ih (fun w h=>p _ (by simp [h])))
end BoxD
namespace Land
variable(h: Land L P A K)(ho:Odd L.val){m:ℕ}
include h ho
lemma noon_b(x y: TickZ): BoxD L (false,true) (false,true) (noon P A x y):=by
  let T:= h.lay.corner ((h.crown ho).reindex (fun i=> (i,y))); exact ((T.chain ((h.helper ho).1.reindex (fun i=> (i,x)))).add (BoxD.one.sub h.lay)).sub BoxD.one
lemma stable(p:0<m)(g:Joy L P A m): BoxD L (false,true) (false,true) (earnings P A m):=by
  refine BoxD.fundas (Finset.range m) (fun l i N F G z=> (2:ℂ)⁻¹ • pencil (noon P A (termJ m l) (termJ m (l+1)) i G z)) ?_
  intro l hl; have he:l+1≤m:=mem_range.mp hl
  let x:=termJ m l; let y:=termJ m (l+1)
  refine (ink (h.noon_b ho x y) (show 0<(1:ℝ)/2 by norm_num) (by norm_num) ((show Still L _ from g).forward ?_)).scale _ _ fun i=>le_rfl -- tune type
  intro N F G hp U hv i; rw [noontide]
  apply (hv i x).2; unfold x; rw [term_eq m p _ (by omega),term_eq m p _ (by omega),berth_diff _ p]; rw [abs_of_nonneg (by positivity)]
lemma taxes(p:0<m)(g:Joy L P A m): Still L fun G x=>∀ i,
  let S:=P i G (post x); let B:=tonic P A i G (post x); let D:= earnings P A m i G (post x); let C:=squareD G false (post x); let V:=squareD G true (post x); let N:= A i G (post x)
  (D.trace=rockZ B S m m) ∧ Complex.exp (rockZ B S m m) • filled S C=filled S (N*V*Nᵀ) ∧ filled S C≠0 :=by
  apply (h.sky.plus g).forward; rintro N F G hG x ⟨f,h⟩ i S B D C V R
  have he:S= P i G (post x):=rfl; have ht: IsStarProjection S:=(f i).1
  have hz:Vᵀ= -V:=skew_square ..; have hk:Cᵀ= -C:=skew_square ..
  have hv:B= straightC S V C R:=rfl
  have hB: Stay S B m :=by
    intro a q t r
    let T:TickZ:=termJ m a; let y:TickZ:=⟨t,railIn m a q r⟩
    have ho:T.val=berth m a:=term_eq m p a q.le
    have hp:= (h i T).2 y (by rw [ho]; exact berth_jump p a r)
    exact ⟨straight_skew ht hk hz _,(h i y).1,ho ▸ hp.trans_lt (by norm_num)⟩ -- order
  refine ⟨?_,princess ht (f i).2.1 hB p,?_⟩
  · unfold D earnings rockZ; rw [Matrix.trace_sum]; apply sum_congr rfl; intro a ha; have hm:a<m:=mem_range.mp ha
    rw [Matrix.trace_smul,noontide,spark,term_eq m p a hm.le,term_eq m p (a+1) hm];
    let Y:=relay S (B (berth m a)) (B (berth m (a+1)))-1; have hg : ‖Y‖<1:=(hB a hm (berth m (a+1)) ⟨ber_m m (Nat.le_add_right ..),le_rfl⟩).2.2
    change (2:ℂ)⁻¹ * (pencil Y).trace=invoice Y/2; rw [tally_log hg]; ring
  have hf : B (berth m 0)= C:=by rw [berth0,hv]; simp [straightC]
  exact signs_nz ht hk (hf ▸ (hB 0 p (berth m 0) ⟨le_rfl,ber_m m (Nat.zero_le _)⟩).2.1)
end Land
end YM.CF.Dial
