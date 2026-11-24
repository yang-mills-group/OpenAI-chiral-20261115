import YM.CF.Girt.Oar
set_option autoImplicit false
set_option quotPrecheck false
set_option synthInstance.maxSize 20000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000
noncomputable section
namespace YM.CF.Girt
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open Cube SU Fock Skye Scree Spire Dial Laic Pec Hest Hive
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
open Rush Tulip Vault Paige Drapes Peaks Brace Branch Lat Kennel CF.Jet Pressure
local notation "G₀"=> SU.group
open Scroll
variable {f n :Side}{CΛ δ v a P h d μ ε w e:ℝ}
open Work.F05
variable {B C L:Side}{j:ℕ}{ho:Odd L.val}{Y:Pricing j L ho (Thread j)}{P':Grasp Y B e}
-- envelope real, tag Borel, finite-dim BK ALL
lemma trust {X:Support (More n)}(U:Seat n)(F:InkD n)(p:BudgetPoint)(b:Finset (Dwell n)→ℝ)(V:Pane n)(H:Healthy p.threshold X V)
 (h:∀ z,Signs p U (fun x=>Pastry.crumb (F (increment V x)).val z) (b z)) : ‖F V‖ ≤∑ i,b i :=by
 refine (Pastry.lies le_rfl (F V)).trans ?_; unfold Pastry.tier; apply sum_le_sum; intro i _; have ht:= (h i).token 0 (by omega) 0 (fun u=>by exact u.elim0); simpa only [one_pow,one_mul,iteratedFDeriv_zero_apply,show increment V 0=V from by simp] using ht
lemma flow (p:BudgetPoint)(U:Hub n)(F:InkD n)(H:PressB p U F a v): RG.Envelope (numbE p.threshold U.val.2 F):=by
 obtain ⟨b,h,hf,w⟩:= H.worth
 refine ⟨H.measureV.indicator ping_o.measurableSet, ∑ i,b i,fun V=>?_⟩; by_cases z: pingS p.threshold U.val.2 V; · unfold numbE; rw [Set.indicator_of_mem (show V∈ _ from z)]; exact trust _ _ _ _ _ (ping_le z) (hf _ z)
 unfold numbE; rw [Set.indicator_of_notMem (show V∉ _ from z),norm_zero]; exact sum_nonneg fun i _=> h i
@[simp] lemma openG_zero (D:Support (More n))(p:BudgetPoint): openG p D 0=0:=by funext i; simp [openG]
lemma tokM (p:BudgetPoint)(U: Force n)(F:Copy n)(H: ForceB p U F a v): RG.Envelope (clamp p U F):=by
 classical
 obtain ⟨b,h,t,e⟩:= H.costP; have hx:MeasurableSet {x:Orbit n|boundF U p x.1} := measurable_fst ping_o.measurableSet
 refine ⟨Measurable.ite hx H.measureV measurable_const, ∑ i,b i,fun x=>?_⟩
 unfold clamp; split; next z=> refine (Pastry.lies le_rfl _).trans ?_; unfold Pastry.tier; refine sum_le_sum fun i _=>?_ ; have ht:= (t x z i).token 0 (by omega) 0 (fun j=>by exact j.elim0); simpa only [one_pow,one_mul,iteratedFDeriv_zero_apply,openG_zero, show increment x.1 0=x.1 from by simp] using ht
 rw [norm_zero]; exact sum_nonneg fun i _=>h i
section sn
variable {ι X Y Z:Type*}[MeasurableSpace ι][Norm X][MeasurableSpace X][MeasurableSpace Z][Norm Z][Norm Y][MeasurableSpace Y]
omit [Norm Z] in
lemma snap {F:ι→Y}{X:Z→ι}(h:RG.Envelope F)(p:Measurable X):RG.Envelope fun z=>F (X z):=by obtain ⟨b,u⟩:=h.cost; exact ⟨h.meas.comp p,b,fun x=>u (X x)⟩
lemma rite_c(x:X):RG.Envelope (fun _:ι=> x):=⟨measurable_const,_,fun _=> le_rfl⟩
end sn
section maps
variable {ι X Y Z:Type*}[MeasurableSpace ι][MeasurableSpace X][MeasurableSpace Y][MeasurableSpace Z][NormedAddCommGroup X][BorelSpace X][SecondCountableTopology X][ProperSpace X][NormedAddCommGroup Y][BorelSpace Y] [SecondCountableTopology Y] [NormedAddCommGroup Z][BorelSpace Z][SecondCountableTopology Z]
lemma pole_w(U:ι→X)(T:X→Y)(p:Continuous T)(h:RG.Envelope U): RG.Envelope fun i=>T (U i):=by
 obtain ⟨C,q⟩:= h.cost; obtain ⟨K,W⟩:= (isCompact_closedBall (0:X) C).bddAbove_image (p.norm.continuousOn); exact ⟨p.measurable.comp h.meas,K,fun x=> W ⟨_,mem_closedBall_zero_iff.mpr (q x),rfl⟩⟩
lemma kitE [ProperSpace Y](U:ι→X)(V:ι→Y)(T:X→Y→Z)(p:Continuous (uncurry T))(h:RG.Envelope U)(k:RG.Envelope V): RG.Envelope fun i=> T (U i) (V i):=by
 obtain ⟨C,w⟩:= h.cost; obtain ⟨D,W⟩:= k.cost; have ht:RG.Envelope fun i=>(U i,V i):=⟨h.meas.prodMk k.meas,C⊔D,fun x=>(le_of_eq (show ‖(U x,V x)‖=_ from Prod.norm_def _)).trans (max_le_max (w x) (W x))⟩; exact pole_w _ (uncurry T) p ht
end maps
lemma billE (R:GramM n)(H:Ward R): RG.Envelope R.board:=by
 classical
 have ht (F: RegBudget n)(p:∀ s:Hub n,∃ a v,PressB R.p s (F s) a v) : RG.Envelope fun x:Orbit n=> exponentL R.p F x.1:= by
    let L(s:Hub n):=numbE R.p.threshold s.val.2 (F s)
    exact snap (F:=exponentL R.p F) (Env.total (g:=L) _ (fun i=> by obtain ⟨a,v,t⟩:= p i; exact flow R.p i _ t)) measurable_fst
 let B:=R.K; let G:=R.F; let P:= R.p
 let J(s: Finset (Force n))(x:Orbit n):= ∏ i∈s,clamp P i (B i) x
 have hx(s):RG.Envelope (J s):=by
    induction s using Finset.induction_on with
    | empty=> simp only [J,prod_empty]; exact rite_c _
    | insert i s v ih=> obtain ⟨a,v',t⟩:= H.k i; rw [show J (insert i s)=(fun x=>clamp P i (B i) x*J s x) from funext fun x=>prod_insert v]; exact kitE _ _ (T:=(·*·)) (by fun_prop) (tokM R.p i _ t) ih -- order
 have hv:RG.Envelope (fueled P B):=by
    unfold fueled; apply Env.total; intro i; by_cases t:Set.PairwiseDisjoint (i:Set (Force n)) (fun x=> x.val.1.val.2)
    · rw [show (fun x:Orbit n=> if coverF P i x.1∧_ then J i x else 0) = Set.indicator {x:Orbit n| coverF P i x.1} (J i) from funext (fun x=> (by by_cases k:coverF P i x.1 <;> simp [k,t,Set.indicator]))]; obtain ⟨v,T⟩:= (hx i).cost; refine ⟨(hx i).meas.indicator (measurable_fst (show MeasurableSet {x|coverF P i x} by unfold coverF; simp_rw [eq_comm]; exact flags_measurable_eq ..)),max v 0,fun x=>?_⟩; by_cases k:coverF P i x.1; · rw [Set.indicator_of_mem (show x∈_ from k)]; exact (T _).trans (le_max_left ..)
      rw [Set.indicator_of_notMem (show x∉ _ from k),norm_zero]; exact le_max_right ..
    simp only [t,and_false,↓reduceIte]; exact rite_c _
 letI : NormedAlgebra ℚ (Scree.Cipher n):=NormedAlgebra.restrictScalars ℚ ℝ _
 have he:= pole_w _ exp (NormedSpace.exp_continuous (𝔸:=Scree.Cipher n)) (kitE _ _ (·+·) (by fun_prop) (ht G H.f) (ht _ H.g)) -- tune
 exact kitE _ _ (·*·) (by fun_prop) he hv
end YM.CF.Girt
