import YM.CF.BProof.Stave.Mould
/-! ε-filler, on ambient affordable. Base dimension ≤3. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Mesh.Stave
open Function Filter Topology Set NormedSpace Metric Extension
open scoped Matrix Matrix.Norms.Frobenius Topology BigOperators NNReal ComplexConjugate Classical
variable {I:Type*}[Fintype I]
variable {X:Type*}[NormedAddCommGroup X][NormedSpace ℝ X][FiniteDimensional ℝ X]
private lemma monarch (p:Module.finrank ℝ X≤3){s t:Set X}{R:ℝ}{f:X→SU.E} (g:Tame s (SU.fund ∘ f))(e:s ⊆ t)(c:0<R)(h:t ⊆ closedBall 0 R): ∃ F:X→ SU.E,Tame t (SU.fund ∘ F) ∧ EqOn f F s := by
 by_cases hz:s.Nonempty
 · obtain ⟨A,hA,H⟩:=frame_extend 4 R ((g.choose:ℝ)+1) c (by positivity) p
   obtain ⟨w,V,w',B⟩:= H t s (SU.fund ∘ f) h e hz (fun x _=> ⟨SU.fund_U _,SU.fund_det _⟩) (g.vein.mono (Subset.refl _) (by simp))
   let F(x:X):SU.E:= if h:x∈t then ⟨⟨w x,(w' x h).1⟩,(w' x h).2⟩ else 1
   have hg (x:X)(hx:x∈ t):SU.fund (F x)=w x:= by unfold F; rw [dif_pos hx]; rfl
   exact ⟨F,(monk hA.le V).copy (fun x hx=> (hg x hx).symm),fun x hx=>SU.group.mat_injective ((B hx).trans (hg x (e hx)).symm)⟩
 exact ⟨fun _=>1,⟨_,(LipschitzWith.const _).lipschitzOnWith⟩,fun x hx=> (hz ⟨_,hx⟩).elim⟩
lemma dough (d:ℝ)(h:0<d): ∃ u:ℝ,0<u∧ u≤d ∧ ∀ (t s:Set X)(R:ℝ)(F:X→plate I)(A:plate I),Module.finrank ℝ X≤3→ t⊆s → s ⊆ closedBall 0 R → 0<R → A∈ King I → (∀ x∈t, Like u A (F x)) → Tame t F → ∃ G:X→plate I,Tame s G ∧ EqOn F G t ∧ ∀ x∈s, Like d A (G x):=by
 obtain ⟨L,r,hr,K⟩:= Mesa.nickel SU.group; let u:= min (r/4) (d/7); have hu:0<u:= lt_min (by positivity) (by positivity); have he:7*u≤ d:=by have g:u≤d/7:=min_le_right ..; linarith
 have ht:3*u<r:=by have z:u≤r/4:=min_le_left ..; linarith
 refine ⟨u,hu,by linarith, fun t S R F A p e U k kA w W=>?_⟩
 let f(x:X):= podium A (F x); have hf:Tame t (SU.fund ∘ f):=lift_price W kA w ht K
 obtain ⟨g,tg,hg⟩:=monarch p hf e k U
 let V(x:X):= roll (F x) (f x)⁻¹; have hX : Tame t V:= W.rollZ ⟨_,Mesa.bolt_back (A:=f) hf.li⟩ (show 0≤3+u by positivity) (fun x hx=>size_like (w x hx) kA) -- tune gauge G
 have hp (x:X)(hx:x∈ t): ‖V x-A‖ ≤ d:=by rw [← dist_eq_norm,← roll_dist _ _ (f x)]; unfold V; rw [roll_mul,inv_mul_cancel,roll_one,dist_comm]; exact (podium_meets kA (w x hx)).trans he
 obtain ⟨G,vG,hT,B⟩:=weak_fill h hX hp
 refine ⟨fun x=> roll (G x) (g x), (vG.subset (subset_univ S)).rollZ tg (show 0≤d+3 by positivity) (fun x _=> (norm_le_norm_sub_add _ A).trans (add_le_add (B x) (king_le kA))),fun x hx=> ?_,fun x _=> ⟨g x,?_⟩⟩
 · dsimp only; rw [← hT hx, ← hg hx]; unfold V; rw [roll_mul,inv_mul_cancel,roll_one]
 dsimp only; rw [roll_dist,dist_comm,dist_eq_norm]; exact B x
end YM.CF.BProof.Mesh.Stave
