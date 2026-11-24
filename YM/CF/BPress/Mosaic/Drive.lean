import YM.CF.BPress.Mosaic.Ownership
/-! histogram at block root. uses θ Finite I, power τ=4.G.Root.Geometry.K µ. -/
set_option autoImplicit false
set_option synthInstance.maxSize 20000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.BPress.Mosaic
open Function Finset NormedSpace MeasureTheory Filter Metric Lattice Wilson Branch LocalH Cube Lat SU Skye Port Locale Sugar Wealth Weave House Scree Precision Pressure Next.SectorChange RG Push.SectorMeasure Crew RG.PathData Grid Honey Recipe Peel
open scoped Topology BigOperators Classical YM.CF.BPress.Vesper Matrix Matrix.Norms.Frobenius InnerProductSpace
attribute [local instance] Gauge.frobInner
variable {N: Side}{B:BandWidth}{A: Bands (More N) B}
open Peel.Spine Ledger Push.AbsoluteSums
variable {R: Hangar (More N)} {H:Crew A}{I:Type}[Fintype I]
variable {C:ℝ} (r:ℕ)(p:I→Prop)(a:I→A.Hcols)(M:ℕ) (K:∀ i:A.Hcols,(univ.filter (fun j=>p j ∧ a j=i)).card ≤ M)
def d0(r C m:ℕ)(q:ℝ):= (estate r*C^3*m:ℕ) * (Real.exp (4*(estate r:ℕ))*q) -- tune coerc
include K
lemma histogram (h:0 ≤ C): Cash (fun i=> Peel.stem (own A R (a i)) r) (fun i=> if p i then C else 0) 4 (d0 r R.L.val M C):=by
 refine ⟨fun i=> by split; exact h; rfl,fun x=> ?_⟩; let V(v:A.Hcols):=univ.filter (fun j=>p j∧ a j=v); let F(u:BlockY A R):=(podium A R u).biUnion V; let P:=(hood x r).biUnion F; have h₁(i): (F i).card≤ R.L.val^3*M:= card_biUnion_le.trans ((sum_le_sum (fun j _=>K j)).trans_eq (by rw [sum_const,podium_cost,nsmul_eq_mul]; simp))
 have h₂:P.card≤ estate r*R.L.val^3*M:= by apply card_biUnion_le.trans; refine (sum_le_sum (fun i _=> h₁ i)).trans ?_; rw [sum_const,nsmul_eq_mul]; simpa [mul_assoc] using (Nat.mul_le_mul_right (R.L.val^3*M) (show (hood x r).card≤estate r from Locale.capacity ..)) -- tune
 let g:=Real.exp (4*(estate r: ℕ))*C; have hv:0≤g:=by unfold g; positivity
 let f:=fun x:I=> if p x then C else 0; let U:=fun i=>Peel.stem (own A R (a i)) r; let X(j:I):= Ledger.score U f 4 x j; have he(i:I): 0≤ X i:=by unfold X Ledger.score; split; apply mul_nonneg (Real.exp_pos _).le (ite_nonneg h le_rfl); rfl
 have hx(i:I)(k: X i≠0) : i∈P:=by
    unfold X Ledger.score at k; split at k; next v=>
       refine mem_biUnion.mpr ⟨own A R (a i), hood_flip (stem_bay _ _ v), mem_biUnion.mpr ⟨a i,mem_filter.mpr ⟨mem_univ _,rfl⟩, mem_filter.mpr ⟨mem_univ _,?_,rfl⟩⟩⟩; exact Classical.byContradiction (fun h=> k (by unfold f; simp [h]))
    next v=> contradiction
 have ht(i:I): X i≤g:=by
    unfold X Ledger.score; split
    next _=>
       unfold f; split; next v=> unfold g; gcongr; exact (card_le_card (stem_bay (own A R (a i)) r)).trans (Locale.capacity ..)
                                                                                                                  -- tune
       next _=> rw [mul_zero]; exact hv
    next _=> exact hv
 refine ⟨he,(hasSum_fintype _).summable,?_⟩; rw [tsum_fintype, ← sum_subset (Finset.subset_univ P)]; swap; · exact fun i _ t=> Classical.byContradiction fun v=> t (hx i v)
 refine (sum_le_sum (fun i _=>ht i)).trans ?_; rw [sum_const,nsmul_eq_mul]; exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr h₂) hv -- tune
lemma localSupply (v:0≤C)(u:I→ Visit A R H→ℂ)(g:∀ i,Measurable (u i))(h:∀ i x,‖u i x‖≤ if p i then C else 0)(t:∀ i,∀ (x y:Visit A R H),Along x.val y.val (Peel.stem (own A R (a i)) r)→u i x=u i y) : Lift (d0 r R.L.val M C) (fun x=>∑ i,u i x):=by
 let S:=fun i=>Peel.stem (own A R (a i)) r; refine (show Act0 S (fun i=>if p i then C else 0) _ u from ⟨fun i x y p=> t i x y (peeking _ _ _ p), histogram r p a M K v,h,fun i _=>tree_stem ..,g⟩).wallet -- tune
end YM.CF.BPress.Mosaic
