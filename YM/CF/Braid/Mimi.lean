/- This file incorporates modified third-party source. See the source attributions in notices/. -/ import YM.CF.Braid.Pane
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Braid
open Function Lattice RG Exterior Bloch Laurent Filter Finset Asymptotics Stationary
open Matrix (transpose mulVec of)
open scoped Matrix Topology ContDiff BigOperators
open Work.F06
variable {α ξ:Type}[Fintype α][DecidableEq α][Fintype ξ] {σ τ A C : ℝ}{M N r t:ℕ}
lemma twist0 : twist (axes (0:Axis→ℝ)) (t:=t)=missing:=funext fun _=>by simp [twist,show axes (0:Axis→ℝ)=0 from funext fun i=>by simp [axes]]
lemma pure (f:SheetLeg (Keys (t+1)) ξ r) (ha:0≤ A)(hf:Board M A f) {U} (hU:Uniforms _ _ (stick t) U)(h:wall U f)(hc:Cycles missing r f)(hp:r≠0∨∀ p:Corn (Keys (t+1)),missing p=0→ f (axes p)=0){s:ℕ}(hj:JetWall s f): ∃ B: SheetLeg (Keys (t+1)) ξ (r+1),Board (peak t M) (A*liftCost t M) B ∧ JetWall (s-1) B ∧ wall U B ∧ ∀ p:Corn (Keys (t+1)),f (axes p)=cob r missing B (axes p):=by
 rw [← twist0]; exact drift f 0 ha hf hU h (by rw [twist0]; exact hc) (hp.imp_right fun H p hx=> H p (by simpa [twist] using hx)) (Or.inl rfl) hj
abbrev Mimi(M:ℕ):= peak 0 M + rowDr 0 (peak 0 (1+peak 0 M))
abbrev puff(a:ℕ):ℝ:=4*a
def handC(M:ℕ):ℝ:= liftCost 0 M+liftCost 0 M * topG 0*liftCost 0 (1+peak 0 M)*puff (peak 0 (1+peak 0 M))*topG 2
theorem twoP (M:ℕ):
    ∀ A s (f : Run 2 → Space 1 → ℂ), 0 ≤ A → (∀ i, Pond M A (f i)) → Contractible (t:=1) f →
      (∀ i, Rays (s+2) (f i ∘ axes)) →
      ∃ g : CurRun 2 → Space 1 → ℂ, (∀ i, Pond (Mimi M) (A*handC M*mate 1 (Mimi M)) (g i)) ∧
        (∀ i, Rays s (g i ∘ axes)) ∧ ∀ (p : Corn (Keys 1)) b,
          fromCurl (plotted (axes p)) (fun i => g i (axes p)) b=f b (axes p) := by
  intro A s f ha hh hu hy
  obtain ⟨X,HX,Hj,Hw,Ht⟩ := pure (clauses (t:=1) f) ha (fun i b => hh _) line_uniform
    (fun i j => ((seal_tail i _).1 (hu.loci.2 i j)).1) hu.loci.1 (Or.inl (by norm_num)) (s:=s+2) (fun i b => hy _)
  have hv : Cycles missing 2 (headPress X) := by
    intro p; rw [← press_cob]
    funext a x; unfold headPress; rw [← Ht]
    exact ((seal_tail p _).1 (hu.loci.2 p a)).2 x
  let T : Corn (Keys 1) → Submodule ℂ (Run 0 → ℂ) := fun p => locus0 (clipVars p)
  have hU : Uniforms (Run 0) _ (stick 0) T := var_uniform fun _ _ he => by unfold T; rw [he]
  have hJ : JetWall (s+2) (headPress X) := press_jet Hj
  obtain ⟨Y,hY,yJ,Hy,Hs⟩ := pure (headPress X)
    (mul_nonneg (mul_nonneg ha (by unfold liftCost; positivity)) (by unfold topG; positivity)) (pressP HX (mul_nonneg ha (by unfold liftCost; positivity))) hU (press_wall Hw) hv
    (Or.inl (by norm_num)) hJ
  have h₁ : JetWall (s+1) Y := yJ
  obtain ⟨D,hD,Hd,HD,hp⟩ := press_pref Y (mul_nonneg (mul_nonneg (mul_nonneg ha (by unfold liftCost; positivity)) (by unfold topG; positivity)) (by unfold liftCost; positivity)) hY h₁ Hy (by
      intro p hr
      have hh : p=0 := funext fun ⟨i,k⟩ => by
        rw [show i=0 from @Subsingleton.elim (Fin 1) _ _ _]; exact congr_fun hr k
      subst p; funext i x
      exact (rays_at_zero ((hY i x).analytic.analytic_real _)).1 ((h₁ i x).weaker (Nat.succ_le_succ s.zero_le)))
  let V := X-cob 2 missing D
  have Vp p : cob 1 missing V (axes p) = clauses f (axes p) := by unfold V; rw [cob_sub,cob_zero,sub_zero, Ht]
  let β:=(A*liftCost 0 M*topG 0)*liftCost 0 (1+peak 0 M)
  have hb:0≤ β:=by unfold β liftCost topG; positivity
  have hV:Board (Mimi M) (A*handC M) V:=by
    have hB := too (0:Axis→ℝ) hD (mul_nonneg hb (by positivity))
    rw [twist0] at hB
    apply Board.mono (Board.sub (Board.mono HX le_rfl (show _ ≤ Mimi M from Nat.le_add_right ..)) (Board.mono hB le_rfl (show _ ≤ Mimi M from Nat.le_add_left ..))) _ le_rfl
    exact le_of_eq (by unfold handC puff; ring)
  have Vj : JetWall (s+1) V := fun i x => (Hj i x).sub (miss_jet Hd i x)
  have Hv : wall locus0 V := by
    intro p a; apply (seal_tail p _).2; refine ⟨(lineTail p).sub_mem (Hw p a) (wall_cob missing HD p a),fun i => ?_⟩
    change headPress V (axes p) a i=0
    rw [show V=X-_ from rfl, press_sub,press_cob]
    simp only [Pi.sub_apply]; apply sub_eq_zero.mpr
    rw [Hs]; unfold cob; rw [hp]
  choose W hZ hq hw' using fun i => solo 1 (Mimi M) (Embedding.refl (Keys 1)) (A*handC M) (s+1) (fun b p => V p i b) (mul_nonneg ha (by unfold handC liftCost topG puff; positivity))
    (hV i) (Vj i) (fun p => Hv p i)
  refine ⟨fun b => W (b 0) (Fin.tail b), fun i => ?_,fun i => hq _ _,fun p i => ?_⟩
  · exact hZ _ _
  rw [fromCurl_cons]
  simp only [Fin.cons_zero,Fin.tail_cons,plotted]
  rw [show (fun i => projected (strand i) (axes p)) = strands (Embedding.refl (Keys 1)) (axes p) from rfl]
  simp_rw [hw']; change cob 1 missing V (axes p) _ _=_
  rw [Vp]; simp [clauses]
end YM.CF.Braid
