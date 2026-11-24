import YM.CF.Vol.Pallas
import YM.Push.LOOP_COEFFICIENT.LogDet
import YM.CF.Pec.Sine
/-! Trace-delta norms for true thermal. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Souk
open Function Filter Set Matrix Lattice Wilson RG Precision Pressure Tree Exterior MeasureTheory Metric
 AnalyticBridge.MarginalMultiplier3b1d AnalyticBridge.LocalGaussianLaws AnalyticBridge.SectorAffine Char Jet Newt Hors Neige
open Push.SectorMeasure AnalyticBridge.RelativeLogdet.Ink
open Push
open Push.Uniform (curve Slope meetVar Positions upperCol lowerCol block meet_derivative bolt address Primary tint Multiplicity countCost)
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius InnerProductSpace
variable {P:RG.Patch}{G:Gauge}{c f:Side}{S:StepData c f}{T:Tube G S}{K:Teller G}{F:Forest S.ratio}{X E B:Type}[NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup B][NormedSpace ℝ B]{t x s D A C Q V r:ℝ}{i n l:ℕ}
variable {ι τ:Type} [Fintype ι][Fintype τ] [DecidableEq τ]
section matrix
variable {X Y Z W:Neige.Shelf τ}
abbrev notesP(X:Neige.Shelf τ):ℝ:= ∑ i,∑ j, |X i j|
lemma row_S (X:Neige.Shelf τ)(i:τ):∑ j,|X i j| ≤ ‖paintO X‖:=by
 let v:Fish τ:=fun j=> if 0 ≤ X i j then 1 else -1; have hv:‖v‖ ≤ 1:=(pi_norm_le_iff_of_nonneg zero_le_one).mpr fun i=>by unfold v; split <;> simp
 have he:paintO X v i=∑ j,|X i j|:=Finset.sum_congr rfl fun j _ => by
    change X i j * v j= |X i j|; unfold v; split
    next hh=>rw [abs_of_nonneg hh,mul_one]
    next h=> simp only [mul_neg,mul_one,abs_of_neg (not_le.mp h)] -- indentation
 rw [←he]; exact (le_abs_self _).trans ((norm_le_pi_norm (paintO X v) i).trans (((paintO X).le_opNorm v).trans (mul_le_of_le_one_right (norm_nonneg _) hv)))
lemma notes_nn(X:Neige.Shelf τ):0 ≤ notesP X:=Finset.sum_nonneg fun i _=> Finset.sum_nonneg fun j _ => abs_nonneg _
lemma note_mul : notesP (X*Y)  ≤  notesP X * ‖paintO Y‖:=by
 unfold notesP; rw [Finset.sum_mul]; refine Finset.sum_le_sum fun i _=>?_ ; apply le_trans (Finset.sum_le_sum (fun j _ => show |∑ k,X i k * Y k j| ≤ _ from Finset.abs_sum_le_sum_abs ..)); simp_rw [Finset.sum_comm (s:=Finset.univ) (t:=Finset.univ) (f:=fun j k=>|X i k *Y k j|),abs_mul]
 rw [Finset.sum_mul]; exact Finset.sum_le_sum fun k _=> by rw [← Finset.mul_sum]; exact mul_le_mul_of_nonneg_left (row_S Y k) (abs_nonneg _)
lemma notes_add : notesP (X+Y) ≤ notesP X+notesP Y:=by unfold notesP; simp only [Matrix.add_apply, ← Finset.sum_add_distrib]; exact Finset.sum_le_sum fun i _=> Finset.sum_le_sum fun j _ => abs_add_le ..
lemma notes_swap(X:Neige.Shelf τ):notesP X.transpose=notesP X:= Finset.sum_comm
lemma note_prod : notesP (X*Y) ≤ ‖paintO X.transpose‖*notesP Y:=by rw [← notes_swap (X*Y),transpose_mul,mul_comm,← notes_swap Y]; apply note_mul
lemma fee_abs(X:Neige.Shelf τ):|X.trace| ≤ notesP X:=by apply le_trans (Finset.abs_sum_le_sum_abs ..); exact Finset.sum_le_sum (fun i _=> show |X i i| ≤ _ from Finset.single_le_sum (fun j _ => abs_nonneg (X i j)) (Finset.mem_univ _))
lemma pay_mul (h:notesP X ≤ C)(p: ‖paintO Y‖ ≤ A): notesP (X*Y) ≤ C*A:=note_mul.trans (mul_le_mul h p (norm_nonneg _) ((notes_nn X).trans h))
lemma buy_mul (h:‖paintO X.transpose‖ ≤ A)(p:notesP Y ≤ C):notesP (X*Y) ≤ A*C:=note_prod.trans (mul_le_mul h p (notes_nn Y) ((norm_nonneg _).trans h))
end matrix
section bill
variable {X Y: Fish ι→Neige.Shelf τ}{x:Fish ι}
private def unpaid: (Fish τ→L[ℝ] Fish τ)→L[ℝ] Neige.Shelf τ := LinearMap.toContinuousLinearMap {toFun:= fun M=> Matrix.of fun i j=> M (Pi.single j 1) i, map_add':=fun f g=> by ext; rfl, map_smul':=fun a f=>by ext; rfl}
private lemma rote(X:Neige.Shelf τ):unpaid (paintO X)=X:=by ext i j; change (X *ᵥ Pi.single j 1) i=X i j; rw [mulVec_single_one]; rfl
lemma steep (h:Protected n X x C):ContDiffAt ℝ n X x:=by
 let L: (Fish τ→L[ℝ] Fish τ)→L[ℝ] Neige.Shelf τ:= unpaid; let Φ:=fun y=>paintO (X y); have he:ContDiffAt ℝ n Φ x:=h.smooth; exact (L.contDiff.contDiffAt.comp (f:=Φ) x he).congr_of_eventuallyEq (Eventually.of_forall fun y=> (rote (X y)).symm)
abbrev pS (k:ℕ)(X:Fish ι→Neige.Shelf τ)(i:Fin k→ι)(x:Fish ι):=Uniform.entry X x i
lemma scaleS(h:Protected n X x C)(ht:i ≤ n)(v:Fin i→ι): ‖paintO (pS i X v x)‖ ≤ C:=by
 have hd:= Uniform.entry_bound (f:=fun y=>paintO (X y)) (p:=x) v
 refine le_trans ?_ (hd.trans (h.norm_le _ ht)); unfold Uniform.entry; change _ ≤ ‖iteratedFDeriv ℝ i (paintO ∘ X) _ _‖; erw [paintO.iteratedFDeriv_comp_left (steep h) (by exact_mod_cast ht)]; exact le_rfl
structure Jewel (X: Fish ι→Neige.Shelf τ)(x:Fish ι)(C Q:ℝ):Prop where
 upper:Protected 2 X x C
 turn:Protected 2 (fun i=> (X i).transpose) x C
 cents (i:ℕ):i<2→∀ j:Fin (i+1)→ι,notesP (pS (i+1) X j x) ≤ Q
lemma slipY (h:ContDiffAt ℝ n X x)(j:Fin n→ι): pS n (fun i=> (X i).transpose) j x=(pS n X j x).transpose:=by
 let L: Neige.Shelf τ→L[ℝ] Neige.Shelf τ:= LinearMap.toContinuousLinearMap { toFun := fun M=> M.transpose, map_add':=fun _ _=>rfl,map_smul':=fun _ _=>rfl}; change iteratedFDeriv ℝ _ (L ∘ X) _ _= _; erw [L.iteratedFDeriv_comp_left h le_rfl]; rfl
lemma Jewel.turnS(h:Jewel X x C Q)(v:Fin n→ι)(t:n≤2): ‖paintO (pS n X v x).transpose‖ ≤ C:=by
 rw [← slipY (steep (n:=n) (h.upper.order t))]; exact scaleS h.turn t v -- inference
lemma Jewel.rotate(h:Jewel X x C Q):Jewel (fun y=>(X y).transpose) x C Q:=by
 refine ⟨h.turn,h.upper,fun i hi j=>?_⟩; rw [slipY (steep (n:=i+1) (h.upper.order (by omega))), notes_swap]; exact h.cents _ hi j
lemma Jewel.merge(h:Jewel X x C Q)(p:Jewel Y x A V): Jewel (fun y=> X y+Y y) x (C+A) (Q+V):=by
 refine ⟨attach h.upper p.upper, attach h.turn p.turn,fun i hi j=>?_⟩
 let k:=i+1; have hk:k≤2:=by unfold k; omega
 rw [show pS (i+1) (fun y=> X y+Y y) j x=pS (i+1) X j x+pS (i+1) Y j x from ?_]; exact notes_add.trans (add_le_add (h.cents _ hi _) (p.cents _ hi _)); unfold pS Uniform.entry; erw [iteratedFDeriv_add_apply (steep (n:=k) (h.upper.order hk)) (steep (n:=k) (p.upper.order hk))]; rfl
end bill
end YM.CF.Souk
