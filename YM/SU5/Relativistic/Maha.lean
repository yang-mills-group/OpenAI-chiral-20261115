import YM.SU5.Relativistic.Katsu
/-! # every packed word, Neumann limit after density. limits independent winding sheets. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 240000
noncomputable section
namespace YM.CF.Papyrus.Franc.Loaves
open Function Set Filter NormedSpace Fock Finset Thera MeasureTheory Metric Lattice Cube Lat Fir Onyx Rush Ember SU Scroll Skye Tulip BPress.Spin.Blank Flare
open Laurent Bloch Dial Jill Crest Crest.Shore Crest.Sleet Buffered Emu
open Stationary (Gaia cartWeight boundsEarth exileE)
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators ComplexOrder NNReal ENNReal Kronecker
attribute [local instance] opCStarAlgebra
variable {N:Side}{M:Jill.Male}{j k:ℕ}(u r:Bite){P:Op (Single N)}(p:IsStarProjection P)
include p in
private lemma tow(x y:Staff) (w:Staff) : let A:=tickA N;let X:=acts (x.stem A P) (u.loc N);let Y:=acts (y.stem A P) (r.loc N); inner ℂ X (acts (w.stem A P) Y)=inner ℂ (u.loc N) (acts ((x.flip.mul (w.mul y)).stem A P) (r.loc N)):=by
 intro A X Y; have h:IsStarProjection A:=by unfold A; rw [←t_comp]; exact cutM_idp _
 unfold X Y; rw [Staff.stem,Staff.stem, Staff.flip_p A P _ p h,act_mul,act_mul,←act_inner (star (x.stem A P)),star_star]
private abbrev fTar (k:ℕ)(P:Op (Single N))(u w:Bite):= tooth P (stilt k P u) (stilt k P w)
def agt (x y:Bite)(S:Staff):=zCost x.root y.root x.spin y.spin x.cost y.cost S
def billJ(k:ℕ) (u w:Bite): ℂ:= let X:=Loaves.colors k u.hand; let Y:=Loaves.colors k w.hand; if u.hand=w.hand then 0 else if u.hand then agt u w (X.flip.mul ((Staff.one.add (.neg .pay)).mul Y)) else agt w u (Y.flip.mul (.mul .pay X))
variable {W N0:ℕ→Side}{G:ℕ→Jill.Male}(g:Tendsto (fun i=>(W i).val) atTop atTop)(t:Tendsto (fun i=>(G i).val.val) atTop atTop)(e:∀ i,Even (W i).val)(pB:∀ i,IsStarProjection (spar 4 (G i) (1:Pane (W i))))
include g t e pB
lemma fundJ(k:ℕ)(u w:Bite): Tendsto (fun i=> fTar k (spar 4 (G i) (1:Pane (W i))) u w) atTop (𝓝 (billJ k u w)):=by
 let a:= Loaves.colors k u.hand; let b:=Loaves.colors k w.hand
 let q(i:ℕ):=spar 4 (G i) (1:Pane (W i)); let W'(s:Staff)(x y:Bite)(i:ℕ):= inner ℂ (x.loc (W i)) (acts (s.stem (tickA _) (q i)) (y.loc (W i)))
 have hw(n x y): Tendsto (W' n x y) atTop (𝓝 (agt x y n)):= supplier x.root y.root x.spin y.spin x.cost y.cost g t e n pB -- tune
 generalize he:billJ k u w=c; subst c
 unfold fTar tooth; simp only [show ∀ i m (P:Op (Single m)),(stilt k P i).1=i.hand from fun _ _ _ =>rfl]; unfold billJ; split -- inside Tendsto 
 next h =>exact tendsto_const_nhds
 next h =>
   split
   next hT =>let Y:=(Staff.one.add (.neg .pay)); refine (hw (a.flip.mul (Y.mul b)) u w).congr fun i=> Eq.symm ?_; have hx:= tow u w (pB i) a b Y; let T:= tickA (W i); change inner ℂ (acts (a.stem T (q i)) _) (acts (1 + -(q i)) _) = _ at hx; rw [←sub_eq_add_neg] at hx; exact hx -- let's
   next hT => exact (hw (b.flip.mul (Staff.pay.mul a)) w u).congr fun i=> (tow w u (pB i) b a .pay).symm
abbrev earnK {N:Side} (M:Jill.Male) (k:ℕ)(L:List Bite) :ℂ:=runes (fTar k (spar 4 M (1:Pane N))) L
def billW (L:List Bite)(k:ℕ):ℂ:=runes (billJ k) L
lemma forge_to (L:List Bite)(k:ℕ) : Tendsto (fun i=>earnK (N:=W i) (G i) k L) atTop (𝓝 (billW L k)):= offer_v _ _ (fundJ g t e pB k) _
omit g t e pB
lemma bandN (k:ℕ)(L:List Bite)(p:IsStarProjection (spar 4 M (1:Pane N)))(v:Wave (Single N))(h:Sea (spar 4 M (1:Pane N)) v) : earnK (N:=N) M k L=inner ℂ v (acts ((Saber (B:=tickA N) p k).glow (chartP N L)) v) :=by
 rw [stamps]; exact (choral p _ _ h).symm
lemma phoz (h:IsStarProjection P) : ∃ v, Sea P v:=by
 obtain ⟨U,s,g⟩:= spot_projection P h; let x:= acts (quantU U).val (basisKet s); refine ⟨x,?_,by unfold x; rw [act_unit_norm]; simp [basisKet]⟩; rw [g,line_twist, cutLine]; unfold x; rw [←Fock.swivel,cut_basis, if_pos (mem_singleton_self s)]
lemma stilt_h :∃ C> (0:ℝ), ∀ (N:Side)(M:Jill.Male)(p:IsStarProjection (spar 4 M (1:Pane N))),∀ (k:ℕ)(i:Bite), ‖(stilt k (spar 4 M (1:Pane N)) i).2‖≤C:=by
 obtain ⟨C,h,u⟩:= columnC 4 (by decide)
 refine ⟨1+C,by positivity,fun N M p k i=>?_⟩; let Q:=spar 4 M (1:Pane N); let B:=tickA N; let V:=i.loc N; let X:=Comb B Q k; have hc:‖V‖=1:=i.normP _
 have hB:IsStarProjection B:=by unfold B; rw [←t_comp]; exact cutM_idp _
 have hm(T:Op (Single N))(h:∀ i,‖acts T (basisKet i)‖≤C): ‖acts T V‖≤ C:=by unfold V Bite.loc Lifted.basisC; rw [map_smul,norm_smul]; unfold Lifted.winding Rush.fee; simp; exact h _
 unfold stilt Loaves.colors; dsimp only; split
 · next _=> change ‖acts (1 + -((Staff.ice k).stem B Q)) V‖ ≤_; rw [←sub_eq_add_neg,Staff.ice_at,act_sub,act_one]; exact (norm_sub_le ..).trans (add_le_add hc.le (hm X (fun i=>(u N M p k i).1)))
 change ‖acts (1 + (Staff.ice k).flip.stem B Q) V‖ ≤_; rw [Staff.flip_p _ _ _ p hB, Staff.ice_at,act_add,act_one]; exact (norm_add_le ..).trans (add_le_add hc.le (hm (star X) (fun i=>(u N M p k i).2)))
lemma stilt_p {ε:ℝ}(p:0<ε):∀ᶠ k:ℕ in atTop,∀ (N:Side)(M:Jill.Male)(p':IsStarProjection (spar 4 M (1:Pane N)))(j:ℕ),k ≤ j → ∀ i:Bite, let P:=spar 4 M (1:Pane N); ‖(stilt j P i).2-(stilt k P i).2‖≤ε:=by
 filter_upwards [net_c 4 (by decide) ε p] with k h N M p' j u i Q
 let B:=tickA N; let Y:=i.loc N; let X(k'):=(Staff.ice k').stem B Q; have hb:IsStarProjection B:=by unfold B; rw [←t_comp]; exact cutM_idp _
 have he(i:Single N): ‖acts (X j-X k) (basisKet i)‖ ≤ ε ∧ ‖acts (star (X j-X k)) (basisKet i)‖≤ε:=by unfold X; rw [Staff.ice_at,Staff.ice_at]; exact h N M p' j u i
 have hm(T:Op (Single N))(h:∀ z,‖acts T (basisKet z)‖≤ε): ‖acts T Y‖ ≤ ε:=by unfold Y Bite.loc Lifted.basisC; rw [map_smul,norm_smul]; unfold Lifted.winding Rush.fee; simp; exact h _
 unfold stilt Loaves.colors; dsimp only; split_ifs
 · change ‖acts (1 + -(X j)) Y-acts (1 + -(X k)) Y‖ ≤ ε; rw [←act_sub,show 1 + - X j-(1+ - X k)= -(X j-X k) by abel,act_neg,norm_neg]; exact hm _ fun z=>(he z).1
 change ‖acts (1+(Staff.ice j).flip.stem B Q) Y - acts (1+(Staff.ice k).flip.stem B Q) Y‖ ≤ _; rw [←act_sub,Staff.flip_p _ _ _ p' hb, Staff.flip_p _ _ _ p' hb,add_sub_add_left_eq_sub,←star_sub]; exact hm _ fun z=>(he z).2
end YM.CF.Papyrus.Franc.Loaves
