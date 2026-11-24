import YM.SU5.Relativistic.Maha
import YM.SU5.Relativistic.Schist
/-! # True roots. Static alphabet. polynomial analysis. Gives actual Wick germs, ordered plot PW. -/
set_option autoImplicit false
set_option maxHeartbeats 320000
noncomputable section
namespace YM.CF.Papyrus.Franc.Loaves
open Function Set Filter NormedSpace Fock Finset Thera MeasureTheory Metric Lattice Cube Lat Fir Onyx Rush Ember SU Scroll Skye Tulip BPress.Spin.Blank Flare
open Laurent Bloch Dial Jill Crest Crest.Shore Crest.Sleet Buffered Emu
open Stationary (Gaia cartWeight boundsEarth exileE)
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators ComplexOrder NNReal ENNReal Kronecker
attribute [local instance] opCStarAlgebra
section
variable {I:Type*}[LinearOrder I][Fintype I][Nonempty I] {ι:Type*} (A F:ι→FC I)
lemma scone (k:Bool)(x y:Ket I): ‖creed k x-creed k y‖≤‖x-y‖:=by
 rw [show creed k x-creed k y= creed k (x-y) from (?_)]; exact cost_pe ..; rw [show x-y=x+ -y by abel,creed_a]; have hh:creed k (-y)= -creed k y:=by cases k <;> simp [creed,Fock.remove]
 rw [hh]; abel -- tune name
lemma normC(A:ι→FC I)(C:ℝ)(p:0<C)(L:List ι)(h:∀ i∈L,‖A i‖≤C): ‖rollC A L‖≤ C^L.length:=by
 induction L with| nil=> simp [rollC]| cons i l ih=> unfold rollC; rw [List.map_cons,List.prod_cons,List.length_cons,pow_succ']; exact (norm_mul_le ..).trans (mul_le_mul (h _ List.mem_cons_self) (ih fun i t=> h i (List.mem_cons_of_mem _ t)) (norm_nonneg _) p.le)
lemma normsDiff (C:ℝ)(p:1≤C)(e:ℝ)(v:0≤e)(L:List ι) (t:∀ i∈L,‖A i‖≤C)(g:∀ i∈L,‖F i‖≤C)(w:∀ i∈L,‖A i-F i‖≤e) : ‖rollC A L-rollC F L‖≤ L.length*e*C^L.length :=by
 induction L with| nil=> simp [rollC]| cons i l ih=>
   have hb(k:ι→Prop): (∀ a:ι,a∈ (i::l)→ k a) → ∀ i,i∈l→k i:= fun h i v=>h i (List.mem_cons_of_mem _ v) -- tune
   let X:=rollC A l; let Z:= rollC F l; change ‖A i*X-F i*Z‖≤ _
   rw [show A i*X-F i*Z=A i*(X-Z)+(A i-F i)*Z by noncomm_ring]
   apply (norm_add_le ..).trans; apply le_trans (add_le_add ((norm_mul_le ..).trans (mul_le_mul (t i List.mem_cons_self) (ih (hb _ t) (hb _ g) (hb _ w)) (norm_nonneg _) (by linarith))) ((norm_mul_le ..).trans (mul_le_mul (w i List.mem_cons_self) (normC _ _ (by linarith) l (hb _ g)) (norm_nonneg _) v)))
   rw [List.length_cons,pow_succ,Nat.cast_add_one]; nlinarith only [mul_le_mul_of_nonneg_right p (show 0≤e*C^l.length by have hc:=zero_lt_one.trans_le p; positivity)]
lemma pike_cross(A:FC I)(f:Wave I)(h:‖f‖=1):‖inner ℂ f (acts A f)‖ ≤ ‖A‖:= (norm_inner_le_norm ..).trans ((mul_le_mul_of_nonneg_left (Graph.spentS ..) (norm_nonneg _)).trans_eq (by rw [h,mul_one,one_mul]))
end
private lemma sock (L:List Bite) (ε:ℝ)(p:0<ε):∀ᶠ k:ℕ in atTop,∀ (N:Side)(M:Jill.Male),IsStarProjection (spar 4 M (1:Pane N))→∀ v:ℕ,k ≤ v→ ‖earnK (N:=N) M v L-earnK (N:=N) M k L‖≤ε:=by
 obtain ⟨C,g,h⟩:=stilt_h; let q:=1+C; let l:=L.length; let D:=(l+1:ℝ)*q^l; let δ:=ε/D; have ht:1 ≤ q:=le_add_of_nonneg_right g.le; have hD:0<D:=by unfold D; positivity
 have hδ:0<δ:=div_pos p hD
 filter_upwards [stilt_p hδ] with k H N M p' v a
 let P:=spar 4 M (1:Pane N); let F(i:ℕ):Bite→Reader0 (Single N):= stilt i P; obtain ⟨x,b⟩:=phoz p'; rw [bandN v _ p' x b,bandN k _ p' x b,stamps, stamps, ←inner_sub_right,←act_sub]
 let G(i:ℕ):=ton∘F i; apply le_trans (pike_cross _ x b.2)
 have hu(i:ℕ)(j:Bite): ‖G i j‖ ≤ q:= by apply (cost_pe ..).trans; exact (h N M p' i j).trans (le_add_of_nonneg_left zero_le_one)
 apply (normsDiff (G v) (G k) q ht δ hδ.le L (fun i _=> hu ..) (fun i _=> hu ..) (fun i _=>(scone i.hand _ _).trans (H N M p' v a i))).trans
 conv_rhs => rw [← div_mul_cancel₀ ε hD.ne']
 change (l:ℝ)*δ*q^l≤δ*D
 have hf:0<q^l:=by positivity
 unfold D; nlinarith only [mul_nonneg hδ.le hf.le]
private lemma tallT : ∃ (N:ℕ→Side)(M:ℕ→Jill.Male), Tendsto (fun i=>(N i).val) atTop atTop ∧ Tendsto (fun i=>(M i).val.val) atTop atTop ∧ (∀ i,Even (N i).val) ∧ ∀ i,IsStarProjection (spar 4 (M i) (1:Pane (N i))):=by
 obtain ⟨z,h,p,t⟩:= Tulip.funde_q 4 (by decide); let N(i:ℕ):Side:=⟨2*(i+1+p), by omega⟩; let M(i:ℕ):Jill.Male:=⟨⟨2*i+1,by omega⟩,i,rfl⟩
 refine ⟨N,M,tendsto_atTop_mono ?_ tendsto_id,tendsto_atTop_mono ?_ tendsto_id,fun i=>⟨i+1+p,(by unfold N; dsimp; omega)⟩,fun i=>?_⟩ -- tune λ infer
 · intro i; change i ≤ 2*(i+1+p); omega
 · intro i; change i ≤ 2*i+1; omega
 exact t (M i) (N i) (by change p≤2*(i+1+p);omega) 1 (guard0 h.le)
lemma toes (L:List Bite): ∃ u, Tendsto (billW L) atTop (𝓝 u):=by
 apply cauchySeq_tendsto_of_complete; apply Metric.cauchySeq_iff.mpr; intro ε e
 obtain ⟨k,h⟩:= (sock L (ε/3) (by positivity)).exists; obtain ⟨N,M,g,p,q,P⟩:= tallT
 have he(x)(y:k≤x): ‖billW L x-billW L k‖≤ε/3:= le_of_tendsto' (((forge_to g p q P L x).sub (forge_to g p q P L k)).norm) (fun i=>h _ _ (P i) _ y)
 refine ⟨k,fun m x n y=>?_⟩ -- tune
 refine (dist_triangle_right _ _ (billW L k)).trans_lt ?_; simp only [dist_eq_norm]; linarith only [he m x,he n y,e]
def zTariff (L:List Bite):ℂ:= (toes L).choose
lemma gift (L:List Bite)(ε:ℝ)(e:0<ε) : ∀ᶠ k:ℕ in atTop,∃ n:ℕ,∀ N:Side, n ≤ N.val → Even N.val→∀ M:Jill.Male,n ≤ M.val.val→ IsStarProjection (spar 4 M (1:Pane N))→ ‖earnK (N:=N) M k L - zTariff L‖≤ ε:=by
 filter_upwards [Metric.tendsto_nhds.mp (toes L).choose_spec (ε/2) (half_pos e)] with k h
 change dist _ (zTariff L)<_ at h
 by_contra! v; choose N hx hg M hf hp ht using v
 have hh:= le_of_tendsto_of_tendsto' tendsto_const_nhds (((forge_to (W:=N) (tendsto_atTop_mono hx tendsto_id) (tendsto_atTop_mono hf tendsto_id) hg hp L k).sub_const (zTariff L)).norm) (fun i=> (ht i).le)
 rw [dist_eq_norm] at h; linarith
end YM.CF.Papyrus.Franc.Loaves
