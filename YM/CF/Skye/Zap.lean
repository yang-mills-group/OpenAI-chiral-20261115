import YM.CF.Skye.Man
set_option autoImplicit false
noncomputable section
namespace YM.CF.Skye
open Function Filter Metric Lattice Wilson Laurent Finset Cube SU Fock Lat Spire Scroll MeasureTheory Mesa ProbabilityTheory
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker
variable {n:Side}{u d:ℝ}
-- per gauge vertex tags (potential applications extra marks for charges)
instance (n :Side): MeasurableSpace (Sweep n) := ⊤
instance (n:Side): MeasurableSingletonClass (Sweep n):=⟨fun _=>trivial⟩ -- tune
abbrev Bone(n:Side):= ℝ × Sweep n × E
abbrev Ids(n:Side):= Seat n→Bone n
def paperMeas(T:Type*) [Fintype T][MeasurableSpace T] : Measure T:= ((Fintype.card T:ℝ≥0∞)⁻¹) • ∑ i:T, Measure.dirac i
instance {T:Type*}[Fintype T][MeasurableSpace T][Nonempty T][MeasurableSingletonClass T]: IsProbabilityMeasure (paperMeas T):= ⟨by
 rw [paperMeas,Measure.smul_apply, Measure.finset_sum_apply]
 simp [ENNReal.inv_mul_cancel] -- tune
 ⟩
def pale :Measure ℝ:=volume.restrict (Set.Icc 0 1)
instance : IsProbabilityMeasure pale := ⟨by simp [pale]⟩
instance : NullSingletonClass pale := by unfold pale; infer_instance
def parcel(n:Side):Measure (Bone n):= pale.prod ((paperMeas _).prod group.probHaar)
instance(n:Side): IsProbabilityMeasure (parcel n):=by unfold parcel; infer_instance
def depot(n:Side):Measure (Ids n):= Measure.pi fun _=>parcel n
instance(n:Side): IsProbabilityMeasure (depot n):= by unfold depot; infer_instance
lemma twirl (b:Bool): MeasurePreserving (polarT b) group.probHaar group.probHaar:=by
 let f:=polarT b; have ht:Measurable f:=(rev_C b).measurable
 let μ:= group.probHaar.map f
 haveI:IsProbabilityMeasure μ:= ⟨by unfold μ; rw [Measure.map_apply ht MeasurableSet.univ]; simp⟩ -- tune
 haveI: Measure.IsMulLeftInvariant μ:=isMulLeftInvariant_map f.toMonoidHom.toMulHom ht f.surjective
 have hs: μ=group.probHaar:= calc
    _= _ :=Measure.haarMeasure_unique μ group.allElements
    _= _ :=by rw [show (group.allElements:Set E)= Set.univ from rfl,measure_univ,one_smul]; rfl
 exact ⟨ht,hs⟩
lemma specU {T:Type*}[Fintype T][MeasurableSpace T][MeasurableSingletonClass T](f:T≃T): MeasurePreserving f (paperMeas T) (paperMeas T):=by
 classical
 have ht:= measurable_of_countable (α:=T) (β:=T) f
 refine ⟨ht,Measure.ext fun s hs=>?_⟩; rw [Measure.map_apply ht hs]; simp only [paperMeas,Measure.smul_apply,Measure.finset_sum_apply, Measure.dirac_apply]; apply congrArg (fun x:ℝ≥0∞=> (Fintype.card T:ℝ≥0∞)⁻¹ • x); conv_rhs=> rw [← Equiv.sum_comp f]; 
 apply sum_congr rfl; intro i _; by_cases h:f i∈ s <;> simp [Set.indicator,h] -- tune
-- tag action
abbrev man(s: Sweep n)(x:Bone n): Bone n:= (x.1,s⁻¹*x.2.1,polarT s.charge x.2.2)
def bun(s: Sweep n)(τ:Ids n): Ids n:=fun i=> man s (τ (boxA s i))
def threadG (g:Seat n→E)(τ:Ids n): Ids n:=fun i=> ((τ i).1,(τ i).2.1,(τ i).2.2*(g i)⁻¹)
lemma tuft (s: Sweep n):MeasurePreserving (bun s) (depot n) (depot n):=by
 have he :MeasurePreserving (fun τ:Ids n=>fun i=> τ (boxA s i)) (depot n) (depot n):=by
    have ht:= measurePreserving_piCongrLeft (fun _:Seat n=> parcel n) (boxA s).symm; convert ht using 1 <;> first | rfl | skip; funext x j; simp [MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft_apply]
 have h:MeasurePreserving (man s) (parcel n) (parcel n):= (MeasurePreserving.id _).prod ((specU (Equiv.mulLeft s⁻¹)).prod (twirl s.charge))
 exact (measurePreserving_pi (fun _:Seat n=>parcel n) (fun _=> parcel n) (f:=fun _=>man s) (fun _=>h)).comp he
lemma threads (g: Seat n→E): MeasurePreserving (threadG g) (depot n) (depot n):= measurePreserving_pi (fun _=>parcel n) (fun _=>parcel n) (f:=fun (i:Seat n) (x:Bone n)=> (x.1,x.2.1, x.2.2*(g i)⁻¹)) (fun i=> (MeasurePreserving.id _).prod ((MeasurePreserving.id _).prod (measurePreserving_mul_right _ _))) -- tune ν
lemma pairsT(a b:Seat n)(v:a≠b):MeasurePreserving (fun τ:Ids n=>((τ a).1,(τ b).1)) (depot n) (pale.prod pale):=by
 let f(i:Seat n)(τ:Ids n):=(τ i).1
 have ht:iIndepFun f (depot n):=iIndepFun_pi (fun i=> (show AEMeasurable (Prod.fst: Bone n→ℝ) (parcel n) from measurable_fst.aemeasurable))
 have hp(i:Seat n):MeasurePreserving (f i) (depot n) pale:=measurePreserving_fst.comp (μc:=pale) (measurePreserving_eval _ i) -- tune
 refine ⟨(hp a).measurable.prodMk (hp b).measurable,?_⟩; calc
   _ = ((depot n).map (f a)).prod ((depot n).map (f b)):=IndepFun.map_prod_eq_prod_map_map (hp a).measurable.aemeasurable (hp b).measurable.aemeasurable (ht.indepFun v)
   _ = _:= by rw [(hp a).map_eq,(hp b).map_eq]
-- no ties a.e. without constraining budgets
lemma sepT : ∀ᵐ x:Ids n ∂depot n, Injective (fun i=> (x i).1):=by
 have h(a b:Seat n): ∀ᵐ x:Ids n ∂depot n,a≠b→(x a).1 ≠ (x b).1:=by
    by_cases v:a=b; exact Eventually.of_forall fun x z=> by contradiction
    suffices ∀ᵐ x:Ids n ∂depot n,(x a).1 ≠ (x b).1 from this.mono fun x p _=>p
    let P:=fun x:Ids n=> ((x a).1,(x b).1); let S:= {x:ℝ×ℝ| x.2=x.1}
    have he:MeasurableSet S:= (isClosed_eq continuous_snd continuous_fst).measurableSet
    rw [ae_iff]; rw [show {x:Ids n|¬ (x a).1 ≠ (x b).1} = P ⁻¹' S from ?_,(pairsT _ _ v).measure_preimage he.nullMeasurableSet,Measure.prod_apply he]; swap; · ext x; simp [S,P,eq_comm]
    simp only [show ∀ i:ℝ, (Prod.mk i) ⁻¹' S={i} from fun _=>rfl, measure_singleton, lintegral_zero]
 have p:= ae_all_iff.mpr fun a=>ae_all_iff.mpr (h a)
 exact p.mono fun x e i j=>not_imp_comm.mp (e i j) ∘ not_not_intro -- tune
lemma threads_T (g: Seat n→E)(τ:Ids n): threadG g⁻¹ (threadG g τ)=τ:=by funext i; simp [threadG]
lemma tuftT(s:Sweep n)(x:Ids n):bun s⁻¹ (bun s x)=x:=by
 funext i; simp only [bun, man,sitU,Equiv.apply_symm_apply,mul_inv_cancel,inv_inv,←mul_assoc,polar_t,one_mul]; change ((x i).1,(x i).2.1,polarT (s.charge.xor s.charge) (x i).2.2)=_; rw [Bool.xor_self]; rfl
end YM.CF.Skye
