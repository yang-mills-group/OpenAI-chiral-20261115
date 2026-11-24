import YM.CF.Rue.Salt
import YM.CF.Rue.River
set_option autoImplicit false
set_option quotPrecheck false
set_option synthInstance.maxSize 16000
noncomputable section
namespace YM.CF.Rue
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset Cube SU Fock Lat Spire Scroll MeasureTheory Mesa ProbabilityTheory Peaks Drapes Rush Precision Tree Push.SectorMeasure Next.SectorChange Tulip Jet Tap Laic Dial Paige Vault Pec Skye Pastry Cascade Scree
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open RG Pressure
attribute [local instance] opCStarAlgebra
variable {G:Gauge}{n:Side}{t:ℝ}
open Jet
-- strictly viable world. health rough support & holds through when visible. saturate via countable extension
abbrev Gates (W:Set (Config G n))(X:Support n)(U:Config G n):Prop:= ∃ V∈W, Agrees X U V
private def leaf(X:Support n)(U V:Config G n): Config G n:=fun i=> if i.1∈X ∧ i.1+step i.2∈ X then U i else V i -- ends only More
variable {W:Set (Config G n)} {X:Support n} {U:Config G n}
private lemma leaf_s (U V:Config G n)(X:Support n):Agrees X U (leaf X U V):=fun e p t=>(if_pos ⟨p,t⟩).symm
private lemma leaf_c(X:Support n):Continuous (uncurry (leaf (G:=G) X)):=by
 apply continuous_pi; intro j; unfold uncurry leaf; split <;> fun_prop
private lemma leaf_t(X:Support n)(p:IsOpen W)(U:Config G n): Gates W X U ↔ ∃ i:ℕ,leaf X U (TopologicalSpace.denseSeq (Config G n) i)∈ W:=by
 let f:=TopologicalSpace.denseSeq (Config G n); constructor
 · intro ⟨v,h,a⟩; have hu:Continuous (leaf X U):= (leaf_c X).comp (f:=fun z:Config G n=> (U,z)) (by fun_prop)
   let Y:=leaf X U ⁻¹' W; have hv:v∈ Y:=by rw [Set.mem_preimage,show leaf X U v=v from funext fun i=> by unfold leaf; split; rename_i p; exact a i p.1 p.2; rfl]; exact h
   obtain ⟨i,g⟩:= (TopologicalSpace.denseRange_denseSeq _).exists_mem_open (p.preimage hu) (show Y.Nonempty from ⟨_,hv⟩); exact ⟨_,g⟩ -- tune
 intro ⟨i,g⟩; exact ⟨_,g, leaf_s _ _ _⟩
lemma year_s(X:Support n)(p:IsOpen W):IsOpen {U|Gates W X U}:=by
 simp_rw [leaf_t X p,Set.setOf_exists]; apply isOpen_iUnion; intro i; apply p.preimage; exact (leaf_c X).comp (continuous_id.prodMk (continuous_const (y:=_)))
lemma pillar(X:Support n)(p:IsOpen W): ∃ f: Config G n→ Config G n, Measurable f ∧ ∀ U,Agrees X U (f U) ∧ (Gates W X U → f U∈ W):=by
 let ρ:= TopologicalSpace.denseSeq (Config G n); let L(U:Config G n)(i:ℕ):Prop:= Gates W X U→ leaf X U (ρ i)∈ W
 have he(U):∃ i,L U i:=by by_cases g:Gates W X U; · obtain ⟨i,t⟩:= (leaf_t X p U).mp g; exact ⟨i,fun _=> t⟩
                          exact ⟨0,fun h=> (g h).elim⟩ -- indentation
 have hv(i): MeasurableSet {x| L x i}:=by unfold L; simp_rw [imp_iff_not_or,Set.setOf_or]; exact MeasurableSet.union (year_s X p).measurableSet.compl (((leaf_c X).comp (f:=fun u=>(u,ρ i)) (by fun_prop)).measurable p.measurableSet)
 exact ⟨fun i=>leaf X i (ρ (Nat.find (he i))), (leaf_c X).measurable.comp (f:=fun x=> (x,ρ (Nat.find (he x)))) (measurable_id.prodMk ((measurable_from_top).comp (measurable_find he hv))), fun i=>⟨leaf_s _ _ _,Nat.find_spec (he i)⟩⟩
-- build reps by borrowing saturated witnesses; LOCAL on ALL gauges, unchanged on open grants domain
variable {A F:Type}[MeasurableSpace A][MeasurableSpace F][Zero F]
lemma via_g (f:A→ Config G n→F)(X:Support n)(p:IsOpen W)(h:∀ a,∀ U∈ W,∀ V∈ W,Agrees X U V→f a U=f a V)(hv:Measurable (fun i: A× W=> f i.1 i.2)):
 ∃ g:A→ Config G n→ F, Measurable (uncurry g) ∧ (∀ a,Set.EqOn (f a) (g a) W)∧ (∀ a,LocalOn X (g a))∧∀ U,¬ Gates W X U→∀ a,g a U=0:=by
 obtain ⟨T,hT,μ⟩:= pillar X p; let g(a)(i:Config G n):= if Gates W X i then f a (T i) else 0; refine ⟨g, ?_,fun a i u=>?_ ,fun a U V t=>?_ ,fun i v _=> if_neg v⟩
 · let Y:Set (A × Config G n):={u|Gates W X u.2}; apply measurable_of_restrict_of_restrict_compl (s:=Y) (measurable_snd (year_s X p).measurableSet) -- tune name
   · let L' (i:Y):W:= ⟨_, (μ i.val.2).2 i.property⟩; let L(i:Y):= (i.val.1,L' i); have hp:Measurable L:= (measurable_fst.comp measurable_subtype_coe).prodMk ((hT.comp (measurable_snd.comp measurable_subtype_coe)).subtype_mk); exact (congrArg _ (show Y.restrict (uncurry g)= (fun i:A× W=> f i.1 i.2)∘ L from funext fun i=>if_pos i.property)).mpr (hv.comp hp)
   rw [show Yᶜ.restrict (uncurry g)= fun _=>0 from funext fun i=> if_neg i.property]; exact measurable_const
 · have hu:Gates W X i:= ⟨_,u,fun _ _ _=>rfl⟩; exact (h _ _ u _ ((μ i).2 hu) (μ i).1).trans (if_pos hu).symm
 have ht: Gates W X U↔Gates W X V:=⟨fun ⟨y,w,p⟩=>⟨y,w,fun e k l=>(t e k l).symm.trans (p e k l)⟩,fun ⟨y,w,p⟩=>⟨y,w,fun e k l=>(t e k l).trans (p e k l)⟩⟩; by_cases k:Gates W X U; swap; · exact (if_neg k).trans (if_neg (mt ht.mpr k)).symm
 unfold g; rw [if_pos k,if_pos (ht.mp k)]; exact h _ _ ((μ U).2 k) _ ((μ V).2 (ht.mp k)) fun i u p=> ((μ U).1 i u p).symm.trans ((t _ u p).trans ((μ V).1 i u p))
def litres(t:ℝ)(X D:Support (More n)):Set (Pane n):={U|pingS t (X\D) U∧ D ⊆ RG.flags t U}
lemma open_l(t:ℝ)(X D:Support (More n)):IsOpen (litres t X D):=by
 refine IsOpen.inter ping_o ?_; change IsOpen {U:Pane n| D⊆ RG.flags t U}; rw [show {U:Pane n|D⊆ RG.flags t U} = ⋂ i:↥D, {U| i.val∈ RG.flags t U} from ?_]; exact isOpen_iInter_of_finite (fun i=> RG.flags_open ..)
 ext U; simp [Finset.subset_iff]
end YM.CF.Rue
