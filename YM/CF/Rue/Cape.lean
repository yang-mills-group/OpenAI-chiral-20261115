import YM.CF.Rue.Zag
set_option autoImplicit false
set_option quotPrecheck false
set_option synthInstance.maxSize 16000
noncomputable section
namespace YM.CF.Rue
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset Cube SU Fock Lat Spire Scroll MeasureTheory Mesa ProbabilityTheory Peaks Drapes Rush Precision Tree Push.SectorMeasure Next.SectorChange Tulip Jet Tap Laic Dial Paige Vault Pec Skye Pastry Cascade Scree
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open RG Pressure
attribute [local instance] opCStarAlgebra
open Hake Stilo Jet
variable {n : Type*} [LinearOrder n] [Fintype n]
variable {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E]{x:E}{K u: Raid n}{X X':E→↥(Dough n)}{k:ℕ}
open Planned.AtomRegular Forge AnalyticBridge.RelativeLogdet
variable [FiniteDimensional ℝ E]
section
lemma punch {U:ℕ→E→ℂ}{b c:ℕ→ℝ}(h:∀ᶠ i in 𝓝 x,∀ j,Allows k (U j) i (b j))(hp:Summable b)(q:Summable c)(v:∀ i,Pence k (U i) x (c i)):Pence k (fun i=>∑' j,U j i) x (∑' j,c j):=by
 let μ:= (Measure.count:Measure ℕ); obtain ⟨V,hV,g,t⟩:= _root_.mem_nhds_iff.mp h; have he:Integrable b μ:=integrable_count_iff.mpr hp.abs; have ht(i:E)(v:i∈V)(j:ℕ):Allows k (U j) i (b j):=hV v j
 have hy(y:E)(p:y∈V):Integrable (fun i=>U i y) μ:=integrable_count_iff.mpr (Summable.of_norm_bounded hp fun i=> by rw [norm_norm]; exact (ht y p i).value)
 have hm:= under (l:=g) (fun j y p=>(ht y p j).smooth) (fun y _=>StronglyMeasurable.of_discrete) he (fun j y p=>ht y p j);
 have hW: (fun i=>∫ j,U j i∂μ)=ᶠ[𝓝 x] fun i=>∑' j,U j i:=by filter_upwards [g.mem_nhds t] with i p; rw [integral_countable (hy i p)]; simp [μ]
 apply Pence.germ ?_ hW; refine ⟨hm.germ g t,?_⟩
 let R:=range (k+1); have hS (i:ℕ)(w:i∈ R):Integrable (fun j=>noble 1 i (U j) x) μ:=((hm.integrate t (Nat.le_of_lt_succ (mem_range.mp w))).norm).const_mul _
 have hh(i :ℕ)(v:i∈ R): noble 1 i (fun x=>∫ j,U j x∂μ) x≤ ∫ j, noble 1 i (U j) x∂μ:=by
    have hv:i≤k:= Nat.le_of_lt_succ (mem_range.mp v); unfold noble; rw [integral_const_mul, show (fun x=>∫ j,U j x∂μ)= Planned.AtomRegular.average μ U from rfl,(hm.less hv).differentiate g t]; exact mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) (by positivity)
 unfold potash; refine (sum_le_sum hh).trans ?_; have hx:Integrable c μ:=integrable_count_iff.mpr q.abs; rw [←integral_finsetSum _ hS]; exact (integral_mono (integrable_finsetSum _ hS) hx (fun i=>(v i).earned)).trans_eq (by rw [integral_countable hx]; simp [μ])
end
lemma blasts(h:Rigid X k x u):∃ v:Raid n,0≤v∧∀ᶠ y in 𝓝 x,Rigid X k y v:=by
 let f(i:Finset n):=SongF (fun x=> (X x).val) i; let K(i:Finset n):= u i+1
 have hp(i:Finset n): ContinuousAt (potash 1 k (f i)) x := by
    have he(j:ℕ)(v:j∈range (k+1)):ContinuousAt (noble 1 j (f i)) x:= continuousAt_const.mul (((h.haveP i).smooth.continuousAt_iteratedFDeriv (by exact_mod_cast (Nat.le_of_lt_succ (mem_range.mp v)))).norm)
    suffices l:∀ S⊆range (k+1),ContinuousAt (fun x=>∑ j∈ S,noble 1 j (f i) x) x from l _ (Subset.refl _)
    intro S p; induction S using Finset.induction_on with
    | empty=> simp only [sum_empty]; exact continuousAt_const
    | insert a S k ih=> simp_rw [sum_insert k]; exact (he a (p (mem_insert_self ..))).add (ih ((subset_insert ..).trans p))
 have hk(i):∀ᶠ y in 𝓝 x,Pence k (f i) y (K i):= by
    filter_upwards [(hp i).eventually (gt_mem_nhds ((h.haveP i).earned.trans_lt (lt_add_one ..))), (h.haveP i).smooth.eventually (by simp)] with i t v; exact ⟨v,t.le⟩
 exact ⟨K,fun i=> (hk i).self_of_nhds.nonneg,(eventually_all.mpr hk).mono fun y h=> ⟨Eventually.of_forall (fun x=> (fineShape _).allP),h⟩⟩
set_option maxHeartbeats 200000 in
lemma punt(Km:ℕ)(h: Rigid X k x u):Rigid (fun x=> ∑' j,beat (j+Km) (X x)) k x (saber u Km):=by
 refine ⟨Eventually.of_forall (fun x=>(fineShape _).allP),fun i=>?_⟩
 let F:Dough n →ₗ[ℝ] ℂ:={toFun := fun x=> Pastry.crumb x.val i,
                             map_add' := fun _ _=> rfl,
                             map_smul' := fun _ _=> rfl}
 let L:= F.toContinuousLinearMap; let Y(j x):= L (beat (j+Km) (X x)); obtain ⟨B,p,g⟩:= blasts h; have hb:= (summable_nat_add_iff Km).mpr (bait_s p); have hv:= (summable_nat_add_iff Km).mpr (bait_s h.p)
 have hz(x):Summable (fun j=>beat (j+Km) (X x)):= (summable_nat_add_iff Km (f:=fun i=> beat i (X x))).mpr (NormedSpace.expSeries_summable' (𝕂:=ℝ) (X x))
 let W(j:ℕ):=bait (j+Km) u i; let D(j:ℕ):= (k.factorial:ℝ)*bait (j+Km) B i
 have hV:∀ᶠ y in 𝓝 x,∀ j,Allows k (Y j) y (D j):=by
    filter_upwards [g] with y v j
    exact ((rung _ _ (j+Km) v).haveP i).pay
 have he1:Pence k (fun x=> ∑' j,Y j x) x (∑' j,W j):=punch hV ((Pi.summable.mp hb i).mul_left _) (Pi.summable.mp hv i) fun j=>(rung _ _ (j+Km) h).haveP i
 have he2(x:E): (∑' j,Y j x) = L (∑' j,beat (j+Km) (X x)):= (L.hasSum (hz x).hasSum).tsum_eq
 have hr: saber u Km i=∑' j,W j:=tsum_apply hv; rw [hr]; exact he1.germ (Eventually.of_forall he2)
lemma wagon(h: Rigid X k x u):Rigid (fun x=> exp (X x)) k x (saber u 0):=by
 convert! punt 0 h using 2; rw [exp_eq_tsum ℝ]; rfl
lemma wiser(h:Rigid X k x u):Rigid (fun x=> exp (X x)-1) k x (saber u 1):=by
 have ht(x): exp (X x)-1=∑' i, beat (i+1) (X x):=by rw [exp_eq_tsum ℝ]; change (∑' i,beat i (X x))-1=_; rw [← (Summable.sum_add_tsum_nat_add 1 (f:=fun i=>beat i (X x)) (NormedSpace.expSeries_summable' (𝕂:=ℝ) _))]; simp [beat]
 simp_rw [ht]; exact punt 1 h
lemma waxen(h:Rigid X k x u):Rigid (fun x=> exp (X x)-1-X x) k x (saber u 2):=by
 have ht(x): exp (X x)-1-X x=∑' i, beat (i+2) (X x):=by rw [exp_eq_tsum ℝ]; change (∑' i,beat i (X x))-1-X x=_; rw [← (Summable.sum_add_tsum_nat_add 2 (f:=fun i=>beat i (X x)) (NormedSpace.expSeries_summable' (𝕂:=ℝ) _))]; simp [beat,sum_range_succ]; abel
 simp_rw [ht]; exact punt 2 h
end YM.CF.Rue
