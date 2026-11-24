import YM.CF.Newt.Amp
import YM.Push.STATIONARY_UNIFORM.Paths
set_option autoImplicit false
noncomputable section
namespace YM.CF.Newt
open Function Filter Set Matrix Lattice Wilson RG Precision Pressure Tree Exterior Finset MeasureTheory
  Push Push.Uniform
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius InnerProductSpace
variable {G:Gauge} {c f:Side} {d k n l:ℕ}{q:Clip}{R:PathData G}{σ C a:ℝ}
def rodE:ℕ ≃ Stationary.PairsIndex:=by haveI : Nonempty PlaqAxes:= ⟨⟨(0,1),by decide⟩⟩; exact Classical.choice nonempty_equiv_of_countable
def rod (R:PathData G)(l:ℕ):ℕ→ Atom G 2:= farther (wink R l) (Stationary.gramPath R) ∘ rodE
def haste (m:ℕ)(A:ℕ→Atom G k):=farther (fun i=>(A i).length ≤ m) A
abbrev tollE(σ:ℝ)(m:ℕ):= Real.exp (-(σ/2)*m)
lemma hurry (h:R.Bounds q σ C a)(m:ℕ) : SumBudget (fun i=>(rod R m i).budget (σ/2)) (tollE σ m * Stationary.gramCost G C):=by
 have hp :=Stationary.gram_budget R h.rows
 let U:= wink R m; let g i:= (farther U (Stationary.gramPath R) i).budget (σ/2); have he: SumBudget g (tollE σ m*_):= farm (fun i hx=> by unfold U wink at hx; rw [Stationary.gram_size]; omega) hp h.width.le
 exact ⟨fun i=>he.1 _, rodE.summable_iff.mpr he.2.1,(rodE.tsum_eq g).trans_le he.2.2⟩
lemma pastA (A:ℕ→Atom G k)(h:0<σ)(p:SumBudget (fun i=>(A i).budget σ) C)(m:ℕ): SumBudget (fun i=>(haste m A i).budget (σ/2)) (tollE σ m*C):=farm (fun i hx=> (Nat.le_of_not_ge hx)) p h.le
lemma uncut_pair (p:R.Bounds q σ C a)(m:ℕ)(x:Site f)(U: Config G f):
 (∑' i,(rod R m i).unmasked U x)= (∑ j, ‖R.ell U (x,j)‖^2/2)-∑ j, ‖(grainA R m).ell U (x,j)‖^2/2:=by -- scope parentheses!
 let T:=grainA R m; let K: ℝ:= Stationary.gramCost G C; let A j:=(Stationary.gramPath R j).unmasked U x; let B j:=(Stationary.gramPath T j).unmasked U x
 have ht (j): ((farther (wink R m) (Stationary.gramPath R)) j).unmasked U x=A j-B j:=by
    have he : B j=inner ℝ (T.ellTerms (x,j.1) j.2.1 U) (T.ellTerms (x,j.1) j.2.2 U)/2:= Stationary.gram_eval T _ _ _
    have ha : A j=inner ℝ (R.ellTerms (x,j.1) j.2.1 U) (R.ellTerms (x,j.1) j.2.2 U)/2:= Stationary.gram_eval R _ _ _
    unfold farther; split
    next hv=> rw [dimU, he, ha]; simp_all [wink,T,grainA,PathData.ellTerms]
    next hv=> rw [he]; unfold wink at hv; by_cases hx:(R.row j.1 j.2.1).2.length≤m
              · have hh : ¬(R.row j.1 j.2.2).2.length≤m:= fun h=> hv ⟨hx,h⟩; simp only [T,grainA,PathData.ellTerms,if_neg hh, zero_smul, inner_zero_right, zero_div, sub_zero]
                rfl
              simp only [T,grainA,PathData.ellTerms,if_neg hx, zero_smul, inner_zero_left, zero_div, sub_zero]; rfl
 rw [← aimed p.rows p.width x U,← aimed (amo p m) p.width x U]
 change (∑' i,(farther (wink R m) (Stationary.gramPath R) (rodE i)).unmasked U x)=(∑' j,A j)-(∑' j,B j)
 rw [rodE.tsum_eq (fun j=>(farther _ _ j).unmasked U x)]
 simp_rw [ht]; exact Summable.tsum_sub (asume _ p.width (Stationary.gram_budget R p.rows) x U) (asume _ p.width (Stationary.gram_budget T (amo p m)) x U)
lemma uncut_high (A:ℕ→Atom G k)(h:0<σ)(p:SumBudget (fun i=>(A i).budget σ) C)(x:Site f)(U:Config G f)(m:ℕ):
 (∑' i,(haste m A i).unmasked U x)=(∑' i,(A i).unmasked U x)-∑' i,(if (A i).length≤m then A i else dimA (A i)).unmasked U x:=by
 have ht i : (haste m A i).unmasked U x = (A i).unmasked U x-(if (A i).length ≤ m then A i else dimA (A i)).unmasked U x:=by unfold haste farther; dsimp only; split <;> simp [dimU]
 have he:=asume _ h p x U; simp_rw [ht]; apply Summable.tsum_sub he; refine Summable.of_norm_bounded he.norm fun i=>?_
 split
 · exact le_rfl
 rw [dimU,norm_zero]; positivity
section actual
variable {S:StepData c f}
-- group assignment gauge kernel remains one. Full action through specific short replacement, unmasked.
lemma tail_exact (h:R.Bounds q σ C a)(m:ℕ)(F:Forest S.ratio)(k:S.Choices)(x: Positions (Joint F G)):
 (Push.Uniform.priced F k q R-Push.Uniform.priced F k q (grainA R m)) x = Patch.average fun s:Signed=>
 uncut (rod R m) (signedFine F x s)+uncut (haste m R.cubic) (signedFine F x s)+uncut (haste m R.quartic) (signedFine F x s):=by
 let T:= grainA R m; change (mainTerm q R _+noiseTaylor _ _ _ _)-(mainTerm q T _+noiseTaylor _ _ _ _) =_
 rw [add_sub_add_right_eq_sub]
 unfold mainTerm Patch.average; rw [← mul_sub, ← Finset.sum_sub_distrib]; congrm _ * ?_
 refine Finset.sum_congr rfl fun i _=> ?_
 let V:=signedFine F x i
 change quadratic q R V+uncut R.cubic V+uncut R.quartic V-(quadratic q T V+uncut T.cubic V+uncut T.quartic V)=_
 unfold quadratic uncut; simp_rw [Fintype.sum_prod_type, Finset.sum_add_distrib, uncut_pair h, uncut_high _ h.width h.three, uncut_high _ h.width h.four, Finset.sum_sub_distrib]; dsimp only [V,signedFine,T,grainA]; abel
end actual
end YM.CF.Newt
