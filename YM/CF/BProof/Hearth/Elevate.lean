import YM.CF.BProof.Hearth.Road

/-! Uniform in all configurations satisfying holes. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Hearth
open Function Filter Fock Finset Branch Tenant Cube SU Tulip Lat Lattice Dial Spin Stint Fig Align
open scoped Topology BigOperators Matrix MatrixOrder InnerProductSpace Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {N:Side}{a b l r d c:ℝ}
lemma cut_value(x y:Piles N)(i j:Single N)(u:Bool): ‖bandCut x u i j - bandCut y u i j‖ ≤ dots (badgeOf i) x y:=by
 by_cases h:i=j; subst j; simp only [dots,badgeOf,spot_spec,bandCut,cutM,Matrix.diagonal_apply_eq]; by_cases p:i∈bandSites x u <;> by_cases g:i∈bandSites y u <;> simp only [p,g, ↓reduceIte] <;> (rw [mem_band] at p g) <;> split_ifs <;> norm_num <;> tauto
 rw [bandCut,bandCut,cutM,cutM,Matrix.diagonal_apply_ne _ h,Matrix.diagonal_apply_ne _ h,sub_zero,norm_zero]; exact dots_pos .. -- tune
lemma cutsBudget : ∃ p:Pay,∀ (N:Side)(a d:ℝ)(u:Bool), let b:= apron N a d; Earn p b.mark b.mark (fun i=> bandCut i.2 u):=by
 let q:= quota*((↑(0:ℕ):ℝ)+1)^4 * Real.exp (1*(quota*((↑(0:ℕ):ℝ)+1)^4))*1; have hx:=Spin.quota_p; refine ⟨⟨1,q,one_pos,(by unfold q; positivity)⟩,?_⟩; intro N a d u b; let D:=Counter (More N) d × Piles N; let X(i:D):= bandCut i.2 u; refine row_earn (F:=X) (m:=0) b.cap hx.le zero_le_one ?_ ?_ zero_le_one ?_ ?_ ?_
 · intro g i; exact blockG ..
 · exact continuous_of_discreteTopology (f:=fun i:Piles N=>bandCut i u)|>.comp continuous_snd
 · intro x i j t; have ht:i≠j:=fun h=>by rw [h,b.st.F.reflex] at t; omega
   exact Matrix.diagonal_apply_ne _ ht -- tune
 · intro i j x; exact (norm_entry (X x) i j).trans ((cutM_idp _).norm_le _)
 intro i j x y; rw [one_mul]; refine (cut_value x.2 y.2 i j u).trans ((le_trans ?_ (b.st.includeV (singleton_subset_iff.mpr ((bay_mem _).mpr (by rw [b.st.F.reflex]))) x y))) ; change _≤ _+∑ l∈({badgeOf i}:Seal _), dots l x.2 y.2; rw [sum_singleton]; exact le_add_of_nonneg_left ((iron N a d).st.pos _ x.1 y.1)
variable {j:ℕ}{P:Ready j a b l r}{F:Core j a b l r N} (h:Age P F d)
-- all Guard fields with Board; persist covariance when Mark rotations and placements.
abbrev PitH (F:Core j a b l r N)(X:Bkg (More N))(S: Support N)(t:ℝ):= floorH (F.θ X 1) (bandCut S true) (bandCut S false) t
def gapE (F:Core j a b l r N)(X:Bkg (More N))(S: Support N)(B:Quilt N)(t:ℝ):= (1-PitH F X S t)* pair B* cc (PitH F X S t)
lemma tablePrice (P: Ready j a b l r)(h:0<c): ∃ v: Pay, ∀ {N d}{F:Core j a b l r N}(t: Age P F d) (u:ℝ), ‖u‖≤1 → let b:= HScope.palette (t.beam c) 3; Earn v b.mark b.mark.reverseV (fun i=> gapE F i.1.val.1.val i.1.val.2 i.2.val u):=by
 obtain ⟨p,T⟩:= Core.earnsθ P; obtain ⟨q,Q⟩:= cutsBudget; let k:= Pay.simple; obtain ⟨l,E⟩:= HScope.buys (by norm_num : (1:ℝ)≤3); obtain ⟨s,a,b,v,w,W⟩:= Stint.sphere _ _ Spin.quota_p.le h p q q (k.wage 1); refine ⟨(((k.add v).mul l).mul v),?_⟩; intro n d F t u g b; let f:= t.beam c; let U:=HScope.skid f 3; let V:= t.beamSkid c; let A(x:InRoad F d c):= F.θ x.val.1.val 1; let X(i:Bool)(x:InRoad F d c):= bandCut x.val.2 i; have he:Earn p f.mark f.mark A:= V.mark ((kiln ..).mark (T F t.minN t.shelter)); have hp(i:Bool): Earn q f.mark f.mark (X i):= V.mark (Q ..); have H:= (W.applies f.cap (hp true) (hp false) he (τ:=fun _=>u) ((Earn.one f.mark).wage g) (fun _=>g) (fun i=>i.property)).2.2.2.1; have hx:= U.mark H; exact (((Earn.one b.mark).minus hx).times (E f)).times hx.ccUp
end YM.CF.BProof.Hearth
