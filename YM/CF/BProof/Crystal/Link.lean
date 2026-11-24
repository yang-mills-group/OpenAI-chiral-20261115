import YM.CF.BProof.Crystal.Roots
/-! B-PfC with the finite (not uniformly bounded) labels used at FiniteGaugeData-pivot, and its
point-wise/local extension API. No analyticity of *activities* in angular variables.
Sup bound uses second of two parameters for log branch. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Crystal
open Function Filter Fock Finset NormedSpace Garden Align Wick Double Pastry Sprinkle Lattice Tenant Palot Gas Branch RG Push.AbsoluteSums
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator Classical
attribute [local instance] opCStarAlgebra
variable {V I: Type}[DecidableEq V][Fintype V][Fintype I][LinearOrder I]{P:Dew V I}
lemma Roots.novel {f: Finset V→ℂ}(g:∀ S: Finset V,S.Nonempty→ f S=0){N:Side}(X:V→ Y N)(i:Y N): Roots.cents X f i=0:=by
 have h(j:Y N):bankB X f j=0:=by rw [bank_p,sum_eq_zero]; intro k hk; exact g k (slate_s hk).1
 unfold Roots.cents jingle; refine Eq.trans (tsum_congr (g:=fun _=>0) ?_) tsum_zero; intro z; split; unfold guava; rw [prod_eq_zero (mem_univ (none:SongQ _)) (h (z.2 none)), smul_zero]; rfl
namespace Civic
variable {N:Side}
structure Able (p:Civic N P)(a C:ℝ)(H α W:ℝ)(f:I→I→Support N→ℝ)(w:V→ℝ):Prop where
 h:0 < α
 positive :0<C
 mild:Roots.mild α C
 BrightT:Bright p f a H
 blur:α≤a/2
 taxes : Moment.Toll (fun i=>(p.zone i).val) (costW P w H) α W
 shape(x:V): w x≠0→ Grove (terr N) (p.zone x).val
 slope(v:V):0≤ w v
 spill:puffPrice (a/2)*W≤C
structure Known (F:I→I→Support N→ℂ)(A: V→ ℂ)(f:I→I→Support N→ℝ)(w:V→ℝ):Prop where
 ct(i j:I) (S:Support N)(h:i<j): ‖F i j S‖≤f i j S
 atV(i): ‖A i‖≤w i
variable (p:Civic N P)
def logF(F:I→I→Support N→ℂ)(A:V→ℂ): Y N→ℂ:=Roots.cents p.border (P.quartet A F)
def logP(f:I→I→Support N→ℝ)(w:V→ℝ): Y N→ℝ:= Roots.price p.border (expense w f)
namespace Able
variable {p} {a C H α W:ℝ}{f:I→I→Support N→ℝ}{w:V→ℝ}{F:I→I→Support N→ℂ}{A:V→ℂ}(m:Able p a C H α W f w)
include m
lemma escape: Moment.Toll (stern ∘ p.border) (expense w f) α C:= ((manyD m.BrightT m.slope W (budget_nonneg (m.taxes.pays 0)) m.taxes m.blur m.h)).weaken _ _ le_rfl m.spill -- tune
lemma prices : Moment.Toll stern (p.logP f w) (α/4) (4*C):=Roots.tariff m.h m.positive m.escape (trackSkin m.BrightT m.shape) m.mild
theorem logG(S:Y N)(h:p.logP f w S ≠0): Grove (terr N) S.val:=Roots.connect m.h m.positive m.escape (trackSkin m.BrightT m.shape) m.mild _ h
variable (h: Known F A f w)
include h
lemma bills(S:Y N): ‖p.logF F A S‖≤p.logP f w S:= Roots.charge m.h m.positive m.escape (trackSkin m.BrightT m.shape) m.mild (truthAlpha m.BrightT m.slope h.atV h.ct) S
theorem pfC (D:Op I)(x:Dᵀ= -D)(g:∀ i j,i<j→ D i j=∑ k:Support N,F i j k): (∑ i:Finset V, P.silica A D i)= Complex.exp (∑ i:Y N,p.logF F A i):=(P.sip D A F g x).trans (Roots.chit m.h m.positive m.escape (trackSkin m.BrightT m.shape) m.mild (truthAlpha m.BrightT m.slope h.atV h.ct) (p.gather _ (zCode m.BrightT h.ct)))
end Able
-- support comparison at point arguments
lemma contact (F F':I→I→Support N→ℂ)(A A':V→ℂ)(S:Support N)(i:Deco P N)(h:(p.border i).val ⊆S)(f:∀ T:Support N,T⊆S→∀ i j:I,i<j→ F i j T=F' i j T)(g:∀ i,(p.zone i).val ⊆S→ A i=A' i): P.litmus A F i=P.litmus A' F' i:=by
 unfold Dew.litmus Dew.flareC; rw [g _ ((show (p.zone i.1).val ⊆ (p.border i).val from subset_union_left).trans h)]; congr 1; apply prod_congr rfl; intro j _; cases e:i.2 j with
 | none=> rfl
 | some k=>
    unfold Dew.charge; rw [Option.elim_some,Option.elim_some]; split; rename_i v; · apply f _ _ _ _ v; intro t ht; apply h; exact mem_union_right _ (mem_biUnion.mpr ⟨j,mem_univ _,e.symm ▸ ht⟩)
    rfl
lemma gaugeRead(F F':I→I→Support N→ℂ)(A A':V→ℂ)(S:Y N)(f:∀ T:Support N,T⊆S.val→∀ i j:I,i<j→ F i j T=F' i j T)(g:∀ i,(p.zone i).val ⊆S.val→ A i=A' i): p.logF F A S=p.logF F' A' S:=by
 apply Roots.outflow; intro Z v; unfold Dew.quartet Dew.quint; split; congr 1; exact prod_congr rfl (fun i t=> p.contact F F' A A' _ i (v i t) f g); rfl -- tune
lemma origin(F:I→I→Support N→ℂ)(S:Y N): p.logF F 0 S=0:=by
 apply Roots.novel; intro i t; obtain ⟨j,u⟩:=t; unfold Dew.quartet Dew.quint; split; rw [prod_eq_zero (show j∈i from u) ?_,zero_mul]; unfold Dew.litmus; simp; rfl -- tune
variable{D:Type*}(F:D→I→I→Support N→ℂ)(A:D→V→ℂ)
lemma measurable [MeasurableSpace D](f:∀ i j T,i<j→ Measurable (fun x=> F x i j T))(g:∀ i, Measurable (fun x=> A x i))(S:Y N):Measurable (fun x=> p.logF (F x) (A x) S):=by
 apply Roots.meas; intro i; unfold Dew.quartet Dew.quint; split; swap; · exact measurable_const
 have he(i j:I)(T:Support N): Measurable (fun x:D=> if i<j then F x i j T else 0):=by split; exact f _ _ _ ‹_›; exact measurable_const
 have hv(i:I)(t:Prism I N): Measurable (fun x:D=>Dew.charge (F x) i t):=by cases t; exact measurable_const; exact he ..
 unfold Dew.litmus Dew.flareC; fun_prop
lemma continuity {a C H α W:ℝ}{f':I→I→Support N→ℝ}{w:V→ℝ}(m:Able p a C H α W f' w)[TopologicalSpace D](b:∀ i,Known (F i) (A i) f' w) (f:∀ i j T,i<j→ Continuous (fun x=> F x i j T))(g:∀ i, Continuous (fun x=> A x i))(S:Y N):Continuous (fun x=> p.logF (F x) (A x) S):=by
 apply Roots.continuity m.h m.positive m.escape (trackSkin m.BrightT m.shape) m.mild (fun x=>P.quartet (A x) (F x)) (fun x=>truthAlpha m.BrightT m.slope (b x).atV (b x).ct); intro i; unfold Dew.quartet Dew.quint; split; swap; · exact continuous_const
 have he(i j:I)(T:Support N): Continuous (fun x:D=> if i<j then F x i j T else 0):=by split; exact f _ _ _ ‹_›; exact continuous_const
 have hv(i:I)(t:Prism I N): Continuous (fun x:D=>Dew.charge (F x) i t):=by cases t; exact continuous_const; exact he ..
 unfold Dew.litmus Dew.flareC; fun_prop
end Civic
end YM.CF.BProof.Crystal
