import YM.SU5.Relativistic.Bonbon
/-! # Lifting costs to one actual sensor. Vectors with AP seam signs. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Crest.Sleet.Sorcerer
open Function Set Filter Topology NormedSpace MeasureTheory Metric Real Finset Lattice Cube Next.Free
open Laurent Bloch Fir Jill Ember Shore Cuest Lat Fock Nacre Skye Scroll Rush Dial Tulip Pannier.Chancel UpStart Buffered
open Lifted (nodeC basisC node_of)
open scoped Topology BigOperators Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace Kronecker
attribute [local instance] opCStarAlgebra screen_fin
local notation "I"=>Complex.I
local notation "φ"=> 2*Real.pi
local notation "Φ"=> Set.Icc (-π) π
variable {a:ℝ}
lemma mint_patch {v:Cover}{d:ℕ}(e:2≤d) {C:ℝ}(t:0 < C)(A:ℕ)(R:Waxy) (h:∀ k∈backPane,∀ u∈Φ, ‖timbre A R k u-Minty v d (tack k u)‖≤C):
    ∀ᶠ N:ℕ in atTop,∀ (M:Jill.Male),N≤ M.val.val → ∀ n:Side,∀ (f:SU.Slot)(o:Cover), let X:=strum n o A R f; ‖acts (spar 4 M (1:Pane n)) X-X‖≤3*C:=by
 obtain ⟨N,w⟩:= junebug v d e _ t; filter_upwards [eventually_ge_atTop N] with D vQ M hm n f o X
 rw [←act_unit_norm (star (ear n))]; change ‖acts (star (ear n).val) _‖≤ _; rw [prime_fourier n M,map_sub, twist_formula, act_mul,act_mul,show acts (star (ear n).val) X= _ from (show _=shellV n f (snap n o A R) from wake_kernel n o A R f)] -- ordering `act_mul` goes star outer? after map_sub
 let H:= snap n o A R
 rw [act_unit,shell_bands,shell_sub]
 let g:= (fun i=>acts (bar 4 M.val (mel i)) (H i))
 apply shellBound _ f _ (by positivity); intro i
 let S:= bar 4 M.val (mel i); have he: S= UpStart.mana M (flowE n i) (flowL n i):= by unfold S mel mana; rw [flow_meet]
 have ht := here_s n i; let U:=timbre A R (flowE n i) (flowL n i); let Y:=Minty v d (tack (flowE n i) (flowL n i))
 have hb:‖acts S Y-Y‖ ≤ C := he.symm ▸ w M (vQ.trans hm) (flowE n i) ht.1 (flowL n i) ht.2
 have hu: ‖U-Y‖≤C:=h (flowE n i) ht.1 (flowL n i) ht.2
 have hw:‖acts S U -acts S Y‖ ≤ C:=by rw [←map_sub]; exact (((acts S).le_opNorm _).trans (mul_le_of_le_one_left (norm_nonneg _) (he.symm ▸ spiritShrink _ _ ht.1 ht.2 M))).trans hu
 change ‖acts S (mode (mel i) (-o) • U)-mode (mel i) (-o) • U‖≤ _; rw [map_smul,←smul_sub,norm_smul,mode_real _ _ (mel_h i).1,one_mul]
 rw [norm_sub_rev U Y] at hu
 linarith only [hu,hb,hw,norm_sub_le_norm_sub_add_norm_sub (acts S U) (acts S Y) Y,norm_sub_le_norm_sub_add_norm_sub (acts S U) Y U]
lemma muster {k d:ℕ}(p:2*(1+(k+8))+2 ≤ 2*d)(v:Cover):
   ∃ C:ℝ,0<C∧ (∀ A n o j,‖strum n o A (Lilt v d A) j‖≤C)∧ ∀ A:ℕ,∀ᶠ N:ℕ in atTop,∀ (M:Jill.Male),N≤ M.val.val → ∀ n:Side,∀ f:SU.Slot,∀ o:Cover, let X:=strum n o A (Lilt v d A) f; ‖acts (spar 4 M (1:Pane n)) X-X‖≤C*boxOrder k A:=by
 let g(u:Behind×ℝ):= Minty v d (tack u.1 u.2); have he:Continuous g:= (mint_smooth v d (by omega)).comp tack_c
 obtain ⟨D,H⟩:= ((isCompact_univ_pi fun _: Fin 3 => (isCompact_Icc : IsCompact Φ)).prod (show IsCompact Φ from isCompact_Icc)).exists_bound_of_continuousOn he.continuousOn
 obtain ⟨C,t,u⟩:= gala (v:=v) p; let X:= 3*C+|D|; have hx :0<X:=by unfold X; positivity
 refine ⟨X,hx,fun A n o j=>?_,fun A=>?_⟩
 · rw [←act_unit_norm (star (ear n))]; change ‖acts (star (ear n).val) _‖≤ _; rw [wake_kernel n]; apply shellBound _ _ _ hx.le; intro i; let k':=flowE n i; let x:=flowL n i; unfold snap; rw [norm_smul,mode_real _ _ (mel_h i).1,one_mul]; apply (norm_le_norm_sub_add _ (g (k',x))).trans; rw [norm_sub_rev]; apply le_trans (add_le_add (u A k' x) (H _ (here_s n i))); have ht:boxOrder k A≤1:=inv_le_one_of_one_le₀ (one_le_pow₀ (show 1 ≤ (A:ℝ)+1 from le_add_of_nonneg_left (by positivity))); unfold X; nlinarith only [ht,t,le_abs_self D]
 apply (mint_patch (by omega:2≤d) (mul_pos t (boxOrder_p k A)) A (Lilt v d A) (fun i _ a _=> (norm_sub_rev ..).trans_le (u A i a))).mono; intro n r M t i f o; apply (r M t i f o).trans; rw [←mul_assoc]; exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (abs_nonneg _)) (boxOrder_p k A).le
lemma drink {j d A:ℕ}(v:Cover)(s:ℝ)(e:chipPay (damper d) v≠0) (x:A<j): ∀ D: Finset WalkA, ∑ z∈D, ‖Lilt v d A 2 0 ((j:ℤ) • z)-(if z=0 then 1 else 0)‖^2 ≤ s^2:=by
 intro D; rw [sum_eq_zero]; exact sq_nonneg _
 intro i t; rw [feast_s]; by_cases g:i=0
 · subst i; simp only [smul_zero]; have ht:tack (0:WalkA) 0=0:=by funext i; induction i using Fin.lastCases <;> simp only [tack,Fin.lastCases_last,Fin.lastCases_castSucc] <;> rfl
   rw [ht,if_pos (by apply box_test.mpr; simp), payoff e]; simp
 rw [if_neg (show tack ((j:ℤ) • i) 0 ∉ Lattice.box A from ?_),if_neg g]; simp
 intro q; obtain ⟨a,p⟩:= Function.ne_iff.mp g; obtain ⟨t,u⟩:= box_test.mp q; specialize t a.castSucc; specialize u a.castSucc; simp only [tack_left,zsmul_eq_mul,Pi.mul_apply,Pi.intCast_apply,Int.cast_id] at t u; change i a≠ 0 at p; rcases lt_or_gt_of_ne p with w|w
 · have he:= mul_le_mul_of_nonneg_left (show i a≤(-1:ℤ) from by omega) (show 0≤(j:ℤ) by positivity); omega
 have he:= mul_le_mul_of_nonneg_left (show 1 ≤ i a from w) (show 0≤(j:ℤ) by positivity); omega
lemma casing(v:Cover)(d A:ℕ){i:SpinIdx}{j:ℤ}{x:WalkA}(p:x∈(Lilt v d A i j).support): tack x j∈box A:= boxMeal v d A i j x p -- syntax
lemma garnishing(v:Cover)(d A:ℕ){i:SpinIdx}(h:i∈plusHalf){j:ℤ}{x:WalkA}(p:x∈(Lilt v d A i j).support): tack x j+v∈ box d:=by
 apply upperBill i h; have he:=Finsupp.mem_support_iff.mp p; change Lilt v d A i j x≠0 at he; exact (show chipPay (mintedK v d i) (tack x j)≠ 0 from (by have ht:Lilt v d A i j x=chipPay _ (tack x j):= (feast_s v d A i j x).trans (if_pos (casing v d A p)); rwa [ht] at he)) -- named args tune
end YM.CF.Crest.Sleet.Sorcerer
#print axioms YM.CF.Crest.Sleet.Sorcerer.muster
