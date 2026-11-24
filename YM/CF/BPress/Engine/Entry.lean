import YM.CF.BPress.Engine.Basis
/-! meas from readers & continuous regular clock path. Doesn't assume indicator masks have any continuity -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.BPress.Engine
open Function Filter NormedSpace MeasureTheory Finset Lattice Branch Ledger Push.AbsoluteSums Palmer Fock Pastry Pine Pine.EdgeD Pf Vesper Spin Spin.Pledge Spin.Stride Currency Spin.Cellar Spin.Cellar.Pass Spin.Basement Pine.Story
open Spark Cube Lat SU Spin.Paint Skye Girt Scree Tulip Tenant Pf.RealBook RG Chalk Lily DoughBag Shot Till Store
open scoped Topology Matrix Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators InnerProductSpace Classical YM.CF.BPress.Vesper
attribute [local instance] opCStarAlgebra
variable {N:Side}{D:Type}{P:Form N D} [TopologicalSpace D] {A:Actor N D}{W:Pledge}{F:GramM N}{μ h ε r g q:ℝ}{U:Till P F}
namespace Shot
variable {X:Type}[MeasurableSpace X]
structure Given(Z:X→Shot N):Prop where
 field : Measurable fun i=>(Z i).field
 f:∀ i:Force N,Measurable fun j=>(Z j).f i
 j:∀ i:Site N, Measurable fun j=>(Z j).j i
 inserts:∀ i: Site N, MeasurableSet {j| i∈(Z j).inserts}
 stamp : Measurable fun i=>(Z i).stampX
lemma Given.clear {Z:X→Pane N}(h:Measurable Z): Given (clearF ∘ Z):=by
 refine ⟨h.prodMk measurable_const,fun i=>measurable_const, fun i=>measurable_const,fun i=>?_,measurable_const⟩; simp [clearF]
end Shot
namespace Store
variable (G:Store P A W F h ε r g q μ U)
lemma crumb_c (X:Finset (Dwell N)): Continuous fun x:Cipher N=> crumb x.val X:= ((continuous_id (X:=FC (Dwell N))).matrix_elem X (∅:Finset (Dwell N))).comp continuous_subtype_val
variable {X:Type}
section measured
variable [MeasurableSpace D] [OpensMeasurableSpace D][MeasurableSpace X]{α:X→ℂ}{u:X→ D}{T:X→Shot N} (qα:Measurable α)(qX:Measurable u)(t:Shot.Given T)(v:Measurable A.KG)
private lemma core_meas (V:X→ℂ)(p:Measurable V)(q:X→Cipher N)(r:Measurable q)(z:Finset (Dwell N)): Measurable fun i=>crumb (weft (V i) (q i)).val z:=by simp_rw [weft_u, crumb_scale]; exact p.mul ((crumb_c z).measurable.comp r)
private lemma meas_pair {I:Type}[Fintype I][DecidableEq I][Nonempty I] (g: Op I→ Op I→ℂ)(v:Continuous (Function.uncurry g))(q r:X→ Op I)(u:Measurable q)(f:Measurable r): Measurable fun i=> g (q i) (r i) := v.measurable.comp (u.prodMk f)
private lemma quote_here (q r:X→ Op SU.Slot)(i:WantJ N)(b:Bool)(u:Measurable q)(f:Measurable r): Measurable (fun y=>Lily.quote i.1 (q y) (r y) b i.2.val) :=by
  apply meas_pair (I:= SU.Slot) (fun x y=> Lily.quote i.1 x y b i.2.val) (Lily.quote_cont i.1 b i.2.val) _ _ u f
include G t qα qX v -- qX used only opt
lemma all_fires(i:Heat N): Measurable fun a=> U.fires A (u a) (T a) (α a) i:=by
 rcases i with (i|(i|i))
 · let f(x): Op SU.Slot:= A.KG (u x) (node i.1); let z(x): Op SU.Slot:= (T x).stampX (node i.1); let qr(b:Bool)(x:X):= Lily.quote i.1 (f x) (z x) b i.2.val; have hh:Measurable f:=(measurable_pi_apply (node i.1)).comp (v.comp qX); have hp:Measurable z:=(measurable_pi_apply (node i.1)).comp t.stamp; have ht(b:Bool):Measurable (qr b):=  quote_here f z i b hh hp
   change Measurable (fun a=> (T a).j i.1 * qr (selectP i.1 (T a).inserts) a); apply (t.j i.1).mul; convert! Measurable.ite (t.inserts i.1) (ht true) (ht false) using 1; ext1 i'; by_cases h:i.1 ∈ (T i').inserts <;> simp [selectP,h]; infer_instance
 · change Measurable (fun x=> regVal F (T x).field.1 (α x) i); unfold regVal; simp_rw [pickStone_val]; exact core_meas α qα _ ((G.rit.r i.1).comp t.field.fst) i.2.val
 change Measurable (fun x=> fuelVal F (T x).field (T x).f i); exact core_meas _ (t.f _) _ ((G.ent.r i.1).comp t.field) i.2.val
lemma gas_f (p:Support (More N)): Measurable fun x=> U.logGas A (u x) (T x) (α x) p:=by
 refine (report_meas (Ω:=X) (Saga P F.p.B) (U.e ∘ u) (fun i=>U.fires A (u i) (T i) (α i)) ?_ ?_ p).add ?_; · exact (continuous_pi (fun i=>(G.pfo.help i).connected)).measurable.comp qX
 · apply measurable_pi_lambda; exact G.all_fires qα qX t v
 unfold Estimate Ledger.lump; apply Measurable.tsum; intro i; split; exact core_meas α qα _ ((G.rit.r i).comp t.field.fst) ∅; exact measurable_const
omit t
lemma pure_f {Y:X→Pane N}(c: Measurable Y)(p:Support (More N)):Measurable fun x=> RegGas U A (α x) (u x) (Y x) p:= G.gas_f qα qX (Shot.Given.clear c) v p -- omit T design
end measured
section continuity
variable [TopologicalSpace X] -- real alpha
variable (T: Shot N)(u : D) {F':X→ℂ}
lemma ember(i:Heat N)(v:Continuous F'): Continuous fun x=> U.fires A u T (F' x) i:=by
 rcases i with (i|(i|i)); exact continuous_const; simp_rw [fires,issue_spin, termsO, Sum.elim_inr,Sum.elim_inl,regVal,pickStone_val]; exact (crumb_c _).comp (weft_κ (I:=Dwell N)|>.comp (v.prodMk continuous_const)); exact continuous_const -- tune
include G
lemma νcont (v:Continuous F')(e:∀ i,‖F' i‖≤1)(h:T.inBudget g)(s:Support (More N)): Continuous fun x=> U.logGas A u T (F' x) s:=by
 have ht:=G.Tclock.upl; refine Continuous.add ?_ ?_
 · apply report_c (Saga P F.p.B) U.γ (Memo U (g:=g)) (FoldUnit _) ?_ (G.ZScore.chill (ht.cap.trans (min_le_left ..))) ht.buys (σ:=W.rate/2) (root_earn ht.h _) ht.awake ht.u.le le_rfl (ht.cap.trans (min_le_right ..)) (fun i=>by simpa only [_root_.norm_zero] using (G.empty_stamp i)) (fun _=>U.e u) _ continuous_const (continuous_pi fun i=> ember _ _ _ v); · exact fun i x=>(G.pfo.help i).bounded u
   · exact fun i x=> U.Fires A W u T (F' x) (e x) G h i
   rw [add_halves]; exact G.pfo.weight
 unfold Estimate Ledger.lump; simp_rw [tsum_fintype]; apply continuous_finsetSum; intro i _; split; exact (crumb_c _).comp (weft_κ (I:=Dwell N)|>.comp (v.prodMk continuous_const)); exact continuous_const
end continuity
end Store
end YM.CF.BPress.Engine
