import YM.CF.Mesa.Gerund
/-! Extend from the scaled discrete faces, through ambient Lipschitz & SU tube. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Mesa
open Function Set Filter Metric Matrix
open scoped Topology NNReal BigOperators InnerProductSpace Matrix.Norms.Frobenius
variable {G:Gauge}{d:ℕ} {E:Type*}[MetricSpace E]
lemma finite_real {s:Set E}{K:ℝ≥0}(h:s.Finite)(f:E→ℝ)(hf:LipschitzOnWith K f s): ∃ F:E→ℝ,LipschitzWith K F∧EqOn F f s:=by
  classical
  by_cases H:s.Nonempty
  · let S:=h.toFinset; have hs:S.Nonempty:= ⟨_,h.mem_toFinset.mpr H.choose_spec⟩
    let g (x y:E) := f y+K*dist x y
    let F (x:E):= S.inf' hs (g x)
    have hb (x y:E)(hy:y∈s): F x≤g x y:=Finset.inf'_le _ (h.mem_toFinset.mpr hy)
    choose y hy he using fun x:E=> Finset.exists_mem_eq_inf' hs (g x)
    have hG (x z:E): F x-F z ≤ K *dist x z:=by
      have hj:= (dist_triangle x z (y z)); have hu:=hb x (y z) (h.mem_toFinset.mp (hy z));
      have hH:=he z; change F z=g z (y z) at hH; unfold g at *; nlinarith [K.coe_nonneg]
    refine ⟨F,LipschitzWith.of_dist_le_mul (fun x z=>?_),fun x hx=>?_⟩
    · rw [Real.dist_eq,abs_le]; exact ⟨by have hx:=hG z x; rw [dist_comm] at hx; linarith,hG x z⟩
    apply le_antisymm (by simpa [g] using hb x x hx); rw [show F x=g x (y x) from he x]
    have ht:=hf.dist_le_mul x hx _ (h.mem_toFinset.mp (hy x)); rw [Real.dist_eq,abs_le] at ht; unfold g; linarith [ht.2]
  refine ⟨fun _=>0,(LipschitzWith.const 0).weaken (bot_le (a:=K)),fun _ hx=> (H ⟨_,hx⟩).elim⟩
lemma finite_axis (Y:Type*)[NormedAddCommGroup Y][NormedSpace ℝ Y][FiniteDimensional ℝ Y] (K:ℝ≥0) : ∃ L,∀ (s:Set E), s.Finite →∀ f:E→Y, LipschitzOnWith K f s→∃ F:E→Y,LipschitzWith L F∧EqOn F f s:=by
  let Z : Y ≃L[ℝ] (Fin (Module.finrank ℝ Y)→ℝ):= ContinuousLinearEquiv.ofFinrankEq (by simp)
  let A := ‖Z.toContinuousLinearMap‖₊; let B := ‖Z.symm.toContinuousLinearMap‖₊
  refine ⟨B*(1*(A*K)), fun s hs f h=>?_⟩
  choose L hL he using fun i:Fin _=> finite_real hs (fun x=> Z (f x) i) ((LipschitzWith.eval i).comp_lipschitzOnWith (Z.lipschitz.comp_lipschitzOnWith h))
  let v:=fun x i=>L i x; have ht : LipschitzWith (1*(A*K)) v:=by exact LipschitzWith.of_dist_le_mul (fun x y=> (dist_pi_le_iff (by positivity)).mpr (fun i=> (hL i).dist_le_mul x y))
  refine ⟨Z.symm ∘ v,Z.symm.lipschitz.comp ht,fun x hx=> ?_⟩
  rw [Function.comp_apply, show v x=Z (f x) from funext fun i=>he i hx,Z.symm_apply_apply]

def nick (G:Gauge)(A:G.Mat):G.El:= (G.nearest_exists A).choose
lemma nick_fix (G:Gauge)(x:G.El): G.mat (nick G (G.mat x))=G.mat x := by
  have ht : G.Nearest (nick G (G.mat x)) (G.mat x) := (G.nearest_exists _).choose_spec
  have hx:= ht x; rw [sub_self,norm_zero] at hx; exact (sub_eq_zero.mp (norm_le_zero_iff.mp hx)).symm
lemma nickel (G:Gauge): ∃ L:ℝ≥0, ∃ r:ℝ, 0<r ∧ LipschitzOnWith L (G.mat ∘ nick G) (⋃ v:G.El, ball (G.mat v) r):=by
  obtain ⟨K,t,hT,hk⟩:= (G.focus_diff.of_le (by exact le_top : (1:WithTop ℕ∞)≤(⊤:WithTop ℕ∞))).exists_lipschitzOnWith
  obtain ⟨r,hR,H⟩:= Metric.mem_nhds_iff.mp (inter_mem hT G.nearest_is_focus)
  let b:=Real.sqrt (G.repDim:ℝ)
  obtain ⟨n,hn⟩:= exists_nat_gt (4*b/r)
  refine ⟨K+n,r/2,by positivity,LipschitzOnWith.of_dist_le_mul ?_⟩
  intro x hx y hy; obtain ⟨v,hv⟩:= mem_iUnion.mp hx; change dist x _ < _ at hv
  have hS (z) (h:dist z (G.mat v)<r): G.mat v⁻¹*z∈t∧ G.focus (G.mat v⁻¹*z)=v⁻¹*nick G z:=by
    have he : G.mat v⁻¹*z∈ ball 1 r :=by rw [mem_ball,←G.mat_one,← inv_mul_cancel v,G.mat_mul,dist_eq_norm,←mul_sub,Gauge.mul_frob_eq _ _ (G.mat_star_mul _),← dist_eq_norm]; exact h
    exact ⟨(H he).1, ((H he).2 _ ((G.nearest_left v⁻¹ (nick G z) z).mpr ((G.nearest_exists z).choose_spec))).symm⟩
  by_cases h:dist x y<r/2
  · obtain ⟨ha,hA⟩:= hS x (by linarith); obtain ⟨hb,hB⟩:= hS y (by have hz:=dist_triangle y x (G.mat v); rw [dist_comm y x] at hz; linarith)
    have hg:= hk.dist_le_mul _ ha _ hb; rw [hA,hB,bolt'] at hg
    simp only [Function.comp_apply]; refine hg.trans ?_
    rw [dist_eq_norm,← mul_sub,Gauge.mul_frob_eq _ _ (G.mat_star_mul _),← dist_eq_norm]; gcongr; simp
  simp only [Function.comp_apply]; rw [dist_eq_norm]; apply (norm_sub_le ..).trans
  rw [Gauge.unitary_frob (G.mat_mul_star _), Gauge.unitary_frob (G.mat_mul_star _)]
  change b+b≤ _; push_cast
  rw [div_lt_iff₀ hR] at hn; push Not at h; nlinarith [K.coe_nonneg,dist_nonneg (x:=x) (y:=y)]
lemma lav {d:ℕ}(hd:d≤3)(K:ℝ≥0) : ∃ r:ℝ, ∃ L,0<r∧∀(s:Set (Board d)), s⊆ Peri _ → s.Finite → (∀ x∈Peri (Board d),∃ y∈s,dist x y ≤ r) →∀ f:Board d→ SU.E,LipschitzOnWith K (SU.group.mat ∘ f) s→∃ F:Board d→SU.E, LipschitzOnWith L (SU.group.mat ∘ F) (terrace _)∧ EqOn F f s :=by
  obtain ⟨J,P⟩:= finite_axis (E:=Board d) SU.group.Mat K
  obtain ⟨V,t,ht,W⟩:= nickel SU.group
  obtain ⟨C,H⟩:= moment hd (V*J)
  let r:=t/(J+1:ℝ); have hr:0<r:=by positivity
  refine ⟨r,C,hr,fun s hs ho hp f hf=> ?_⟩
  obtain ⟨Y,hY,he⟩:= P s ho _ hf
  have hk : MapsTo Y (Peri _) (⋃ v:SU.E, ball (SU.group.mat v) t):=by
    intro x hx; obtain ⟨y,hy,k⟩:= hp x hx; refine mem_iUnion.mpr ⟨f y,?_⟩
    have hm:=hY.dist_le_mul x y; rw [he hy] at hm; change dist (Y x) _<_; refine hm.trans_lt ?_
    have he : r*(J+1:ℝ)=t:=div_mul_cancel₀ _ (by positivity)
    nlinarith [J.coe_nonneg]
  obtain ⟨F,hF,h⟩:= H (nick SU.group ∘ Y) (W.comp hY.lipschitzOnWith hk)
  refine ⟨F,hF,fun x hx=>?_⟩
  rw [h (hs hx), Function.comp_apply,he hx]; exact SU.group.mat_injective (nick_fix ..)
end YM.CF.Mesa
