import YM.SU5.May.TorqueMirror
set_option autoImplicit false
set_option maxHeartbeats 450000
set_option synthInstance.maxSize 30000
set_option maxRecDepth 3000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.May.TorqueBeam
open Function Filter Finset Fir Lattice Laurent Next.Free Bloch Lat Ember Jill Rush
open scoped Topology BigOperators ContDiff InnerProductSpace Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator Classical
attribute [local instance] opCStarAlgebra
open Onyx Fock SU Flare Kea Sods Emu Dial Cube Tulip Spire Scroll Thera
open Fock Reflect
open Lamour (lakeP lakeK)
open Hygrometry Personality PriceCliff
open RG Wilson Phase Mir Vale Vale.Grace Peaks Paige Vault
open Stationary (Gaia)
open Buffered.Lifted Buffered.Afterglow.Tower.Tilted
open scoped ComplexOrder
local notation "Ω" => Complex.I
open May.Floe
open Buffered Buffered.Advance Buffered.Advance.Whorl May.Arctic
variable {α:Type*}(b:α→ℂ)(f x:α⊕α→α⊕α→ℂ)
lemma gradedEnough {j:ℕ}(h:1≤j):∃ C:ℝ,0<C∧∀ N:Side,Even N.val→∀ M:Jill.Male, ‖ledger N j M‖ ≤ C*N.val:=by
 obtain ⟨b,B,g,q,H⟩:= Onyx.soul j h; refine ⟨B/Real.pi,by positivity,fun N e M=>?_⟩
 rw [ledger_as_lake h e]; apply markQ _ (by positivity); rintro ⟨i,a⟩; have ht:= H M (pm i) (Velvet.mass_valid i) 1 zero_lt_one
 rw [show lakeP N j M (i,a)=dip j M (tmap (pm i)) from ?_]
 · have hx:pinch N ≤‖pm i‖:=by have hx:= tall_p i; unfold Jill.tall at hx; simpa using (le_div_iff₀ (pinch_pos _)).mp hx
   exact ht.2.trans ((div_le_div_of_nonneg_left q.le (pinch_pos _) hx).trans_eq (by unfold pinch; ring_nf; rw [inv_inv]; ring_nf)) -- ring_nf may need inverse inv cast.
 have h0:=Lamour.align_b (j:=j) M e a i; rw [show glen (zeroF N) i=pm i from add_zero _,trackF,show Emu.rake (too N) i a=(i,a) from (by simp [Emu.rake,too])] at h0; exact h0
variable {I:Type*}[LinearOrder I][Fintype I][Nonempty I] (U:UNI I)(L:Op I) (δ ρ:ℝ)
variable (X:α→ Reader0 I)
noncomputable abbrev bag : α⊕α → Reader0 I:= Sum.elim (send U ∘ X) X
noncomputable abbrev focusL (j k:α⊕α):ℂ:= rankG L (bag U X j) (bag U X k)
private lemma cap_vote (h:0≤ρ)(x y:Reader0 I) (f:‖x.2‖≤ρ)(w:‖y.2‖≤ρ): ‖rankG L x y‖ ≤ ‖L‖*ρ^2:=by
 unfold rankG; split; simp; positivity; -- split branches bullet better
 split <;> (first| rw [norm_neg]|skip) <;> apply (norm_inner_le_norm (𝕜:=ℂ) ..).trans
 · exact (mul_le_mul f ((opy ..).trans (mul_le_mul_of_nonneg_left w (norm_nonneg _))) (norm_nonneg _) h).trans_eq (by ring)
 exact (mul_le_mul w ((opy ..).trans (mul_le_mul_of_nonneg_left f (norm_nonneg _))) (norm_nonneg _) h).trans_eq (by ring)
lemma focusCharge (p:0≤ρ)(h:∀ i,‖(X i).2‖≤ρ)(x y:α⊕α): ‖focusL U L X x y‖ ≤ ‖L‖*ρ^2:=by
 have hv(k:α⊕α) : ‖(bag U X k).2‖≤ρ:=by
    cases k with | inl i=>change ‖-acts U.val (X i).2‖≤ρ; rw [norm_neg,act_unit_norm]; exact h i | inr i=>exact h i
 exact cap_vote L ρ p _ _ (hv x) (hv y)
noncomputable def focusBig (j k:α⊕α):ℂ:= match j,k with
 | .inl i,.inr l=>(Complex.I*costal (X i))⁻¹* promoted U L δ (X i) (X l)
 | j,k=> focusL U L X j k
omit [Nonempty I] in
lemma costal_ne (x:Reader0 I): costal x≠0:= norm_pos_iff.mp (by rw [costal_f]; positivity)
lemma subsidy (d:0≤δ)(p:0≤ρ)(h:∀ i,‖(X i).2‖≤ρ)(x y:α⊕α): ‖focusBig U L δ X x y - focusL U L X x y‖ ≤ δ*ρ^2:=by
 rcases x with x|x <;> rcases y with y|y
 all_goals first | (solve| simp only [focusBig, sub_self, norm_zero]; positivity) | skip
 let B:=Complex.I*costal (X x); have he:‖B‖=1:=by unfold B; rw [norm_mul,costal_f]; simp
 have hz: B≠0:= norm_pos_iff.mp (he.symm ▸ (show (0:ℝ)<1 from by norm_num))
 rw [focusBig, show focusL U L X (.inl x) (.inr y)= B⁻¹* promoted U L 0 (X x) (X y) from ?_]; change ‖B⁻¹*_-B⁻¹*_‖ ≤ _; rw [←mul_sub,norm_mul,norm_inv,he,inv_one,one_mul]; exact (normRise U L δ d _ _).trans (mul_le_mul_of_nonneg_left (by rw [sq]; exact mul_le_mul (h _) (h _) (norm_nonneg _) p) d)
 rw [fromRank, show Ω * costal (X x)= B from rfl, ←mul_assoc, inv_mul_cancel₀ hz,one_mul]; rfl
omit [Nonempty I]
variable [LinearOrder α][Fintype α]
lemma treasury : income (costal ∘ X) (focusBig U L δ X) = Matrix.of fun i j=> promoted U L δ (X i) (X j) := by
 ext i j; change (Complex.I*costal (X i))* ((Complex.I*costal (X i))⁻¹*_)=_; rw [←mul_assoc,mul_inv_cancel₀ (mul_ne_zero Complex.I_ne_zero (costal_ne _)),one_mul]; rfl
#print axioms gradedEnough
#print axioms subsidy
end YM.CF.May.TorqueBeam
