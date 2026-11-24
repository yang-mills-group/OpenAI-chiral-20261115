import YM.CF.BPress.Honey.Costs
/-! Jacobian etc scalar runtime meas accounting. -/
set_option autoImplicit false
set_option synthInstance.maxSize 20000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.BPress.Honey.Recipe
open Function Finset NormedSpace MeasureTheory Filter Metric Lattice Wilson Branch LocalH Cube Lat SU Skye Port Locale Sugar Wealth Weave House Scree Precision Pressure Next.SectorChange RG Push.SectorMeasure Crew RG.PathData
open scoped Topology BigOperators Classical YM.CF.BPress.Vesper Matrix Matrix.Norms.Frobenius InnerProductSpace
attribute [local instance] Gauge.frobInner
variable {N: Side}{B:BandWidth}{A: Bands (More N) B}
variable (H:Crew A){V:GramM N} (F:Recipe (A:=A) V) {ζ a k C' D τ:ℝ}
local notation "η"=> mState N A
lemma weight_m : Measurable (perturbY H):=by
 unfold perturbY perturb; apply ((canon (G:=group) A).continuous_of_finiteDimensional.measurable).comp; unfold softAl; let v(x:η):=chosen A H.κ H.y (H.skyio x); have hm:Measurable v:= askF _ fun i=> H.skyio_m (choose_meas ..)
 refine askM v hm (fun t u=> Wealth.low A t (soft A H.y (H.skyio u) H.T)) (fun t=>measurable_pi_lambda _ fun i=> ?_ ); unfold Wealth.low soft; split; exact measurable_const; exact H.T.logV_meas.comp (measurable_const.mul ((measurable_pi_apply i).comp H.skyio_m)) -- tune
lemma form_meas (i:Root (More N)): Measurable (form V.path F.M i ∘ perturbY H) :=by
 let C: Directions group (More N)→ₗ[ℝ] ink:= ⟨⟨_,shape_add F.M V.path F.work i⟩, shape_smul F.M V.path F.work i⟩ -- tune arguments
 exact C.continuous_of_finiteDimensional.measurable.comp (weight_m H)
variable {H F} (Q:Budgeting H F τ k D ζ a C')
namespace Budgeting
include Q
lemma main_meas(i: Root (More N)): Measurable fun (x:η)=> heavy V.path V.funds V.p V.beta F.M i (H.port x) := ((merit V.path V.funds V.p V.beta F.M F.work Q.chef Q.ageP i).1.meas.comp H.port_m)
lemma first_m (i:Root (More N)): Measurable fun x:η=> first V.path V.funds F.M V.beta H.y i (perturbY H x):= measurable_const.mul ((Continuous.measurable (by fun_prop : Continuous (fun x:ink=> inner ℝ (mA H.y • base V.path F.M i) x))).comp (form_meas H F i))
lemma wheat_m(i:Root (More N)): Measurable fun x:η=> tinW H F x i:=by
 unfold tinW; apply Measurable.ite (Crew.Sbudget (Set.to_countable {t|i∈Θ A F.M t}|>.measurableSet)) _ measurable_const; exact (Q.main_meas i).sub ((measurable_const.add (Q.first_m i)).add ((measurable_const.mul ((form_meas H F i).norm.pow_const 2)).div_const _)) -- tune
lemma grain_m(i:A.Hcols): Measurable fun x:η=> leftY H F x i:=by
 refine askM (fun i:η=>i.1.1) Sbudget (fun S x=> lTerm A H.J H.F H.y x.2.1.1 S i+ rTerm A H.F (fromSea H F) x.2.1.1 S i) (fun S=> ?_ ); let f:= fun x:η=> x.2.1.1; refine ((?_ : Measurable (fun p:Fills A=> lTerm _ _ _ _ p S i)).add (rT_meas A H.F (fromSea H F) S i)).comp (show Measurable f from (by unfold f; fun_prop)); exact l_seen A H.J H.F Q.jRoot S i H.y -- tune
lemma tail_m(i: Seal A.Hcols): Measurable fun x:η=>tailY H F x i:= (measurable_of_countable (tailJ A (H.P.heightClose H.y) F.l i)).comp Sbudget
lemma weak_m (i:Support (More N)): Measurable fun x:η=> weak H F x i:= (Q.world.unit i).meas.comp H.port_m
lemma cold_m (i:A.Hcols): Measurable fun x:η=> cold H F x i:=by
 unfold cold; apply Measurable.ite (Crew.Sbudget ((Set.to_countable {t:Seal A.Hcols|i∈t}).measurableSet)) ?_ measurable_const; apply Measurable.sub ?_ measurable_const; refine Measurable.add ?_ ((measurable_of_countable (burden A (H.P.heightClose H.y) F.l i)).comp Sbudget); refine askM (fun j:η=>j.1.1) Sbudget (fun S x=> Wealth.pays A F.M V.path V.funds V.p V.beta H.y S (perturbY H x) (H.port x) i) ?_; intro S; unfold Wealth.pays; exact Finset.measurable_fun_sum _ fun j _=>(measurable_const.add (Q.first_m j)).sub (Q.main_meas _)
lemma wageM : Measurable (Wage H F):= (Measurable.sub (((Finset.measurable_fun_sum _ (fun i _=>Q.cold_m i)).add (Finset.measurable_fun_sum _ fun i _=> Q.grain_m i)).add (Finset.measurable_fun_sum _ fun i _=>Q.tail_m i)) (Finset.measurable_fun_sum _ fun i _=>Q.wheat_m i)).sub (Finset.measurable_fun_sum _ fun i _=> Q.weak_m i)
lemma fair : Envelope fun x:H.castP=> Real.exp (Wage H F x.val):=by refine ⟨(Q.wageM.comp measurable_subtype_coe).exp, Real.exp (upperB H F ζ C' D), fun x=>?_⟩; rw [Real.norm_of_nonneg (Real.exp_pos _).le]; exact Real.exp_monotone (Q.pops x)
end Budgeting
end YM.CF.BPress.Honey.Recipe
