import YM.CF.Siete.Plane
set_option autoImplicit false
noncomputable section
namespace YM.CF.Siete
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG PhysicalNext.JointLoad Heir Next.Foundations AnalyticBridge.SectorAffine AnalyticBridge.SectorAffine.Offset Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Jet Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Classical Matrix.Norms.Frobenius
variable {G:Gauge}{c f:Side}{P:Teller G}{S: StepData c f}{F: Forest S.ratio}{A:Stores S}{x d:ℝ}{X:Support f}{T:Tube G S}{Y:Support c}{I:Type}[Fintype I][DecidableEq I]{n:ℕ}
variable (T) (M:Museum F x A X Y I)(β:ℝ)(k:S.Choices)(q:Chi)(d:ℝ)(l:ℕ)(B:Config G f)(Z:LogArray G (Active A x F)) (g:Site c→ G.El)
variable {a s C J w Q:ℝ}
def Count(G:Gauge)(x:ℝ):Prop:=1≤x∧∀ i:G.Color,‖i‖ ≤ x*‖i.ofLp‖
lemma count (G: Gauge):∃ C:ℝ,Count G C:=by obtain ⟨N,h,H⟩:= Lift.sense G; exact ⟨max 1 N,le_max_left ..,fun i=>(H _).trans (mul_le_mul_of_nonneg_right (le_max_right ..) (norm_nonneg _))⟩ -- tune namespace
lemma atomsG(o:Site c)(r:ℕ)(p:RG.BudgetPoint)(h:p.threshold=temp x)(hg:∀ i:I,separation o (incF M i) ≤ r)(V: Config G c) (hr:Ready T x)(hp:1000 ≤ radiusB x)(u:Allows n (traceU T M β k q d l B Z ∘ Vmove x V) 0 C)(hm:Count G J): Guide _ (p.dirBound o) 0 (atoms T M β k q d l B Z g ∘ increment V) n (J*(C*((1+((r+(l+50)*radiusB x):ℕ):ℝ)^(p.power*n)))):=by
 let K:= M.extra g 1; let R:= traceU T M β k q d l B Z ∘ increment V; obtain ⟨e,t⟩:=usher T M β k q d l B Z o r p h hg V hr hp u
 have ht(w:Prices G I):‖K w‖ ≤ J* ‖w‖:=by
    refine (M.extra_size g 1 zero_le_one w).trans ((one_mul _).le.trans ?_); have hx:0≤J:= zero_le_one.trans hm.1; apply (pi_norm_le_iff_of_nonneg (show 0 ≤ J*‖w‖ by positivity)).mpr; intro i; exact (hm.2 _).trans (mul_le_mul_of_nonneg_left ((pi_norm_le_iff_of_nonneg (norm_nonneg w)).mpr (fun j=> norm_le_pi_norm w (i,j))) hx)
 change Guide _ _ _ (K ∘ R) _ _; refine ⟨K.contDiff.contDiffAt.comp 0 e,fun i v f g=>?_⟩; rw [K.iteratedFDeriv_comp_left (f:=R) e (Nat.cast_le.mpr v)]; exact (ht _).trans (mul_le_mul_of_nonneg_left (t _ v f g) (zero_le_one.trans hm.1))
-- canon museums & rituals orientation
abbrev PlaceZ (F:Forest S.ratio)(X:Support f)(A:Stores S)(x:ℝ):= {i: Active A x F//i.val.val.1∈inspected X∧ i.val.val.1+step i.val.val.2 ∈ inspected X}
def museZ (X:Support f)(Y:Support c)(F: Forest S.ratio)(A:Stores S)(x:ℝ)(p:Disjoint A.place Y)(h:∀ p:Site f,p∈inspected X→halo (Heir.reach x+4) {S.ratio.parent p} ⊆ Y): Museum F x A X Y (PlaceZ F X A x):={
 seat:={toFun:=Subtype.val, inj':=Subtype.val_injective}
 away:=p
 asks:=h
 covers:=fun i l u=>⟨⟨i,l,u⟩,rfl⟩
 stores:=fun i=>h _ i.property.1 }
lemma cappoint (K:BudgetPoint)(p:Site f)(hB:K.B≤2*radiusB x)(hp:p∈ X)(hs:Heir.Short S K X)(h₁:Disjoint A.place Y)(h₂:∀ p:Site f,p∈inspected X→halo (Heir.reach x+4) {S.ratio.parent p} ⊆ Y):∀ i,_root_.YM.Lattice.separation (S.ratio.parent p) (incF (museZ X Y F A x h₁ h₂) i) ≤ 7*(1+radiusB x):=by
 intro i; rw [separation_comm]; exact (short_patch hs hB hp i.property.1).trans (by omega)
lemma trust (K:BudgetPoint)(p:Site f)(hB:K.B≤2*radiusB x)(hp:p∈ X)(hs:Heir.Short S K X)(f': BudgetPoint)(h:f'.threshold=temp x)(hv:∀ i:I,separation (S.ratio.parent p) (incF M i) ≤ 7*(1+radiusB x))(V: Config G c) (hr:Ready T x)(hk:1000 ≤ radiusB x)(u:Allows n (traceU T M β k q d l B Z ∘ Vmove x V) 0 C)(hm:Count G J) : Guide _ (f'.dirBound (S.ratio.parent p)) 0 (atoms T M β k q d l B Z g ∘ increment V) n (J*(C*((1+((7*(1+radiusB x)+(l+50)*radiusB x):ℕ):ℝ)^(f'.power*n)))):=atomsG _ _ _ _ _ _ _ _ _ g _ _ _ h hv V hr hk u hm
end YM.CF.Siete
