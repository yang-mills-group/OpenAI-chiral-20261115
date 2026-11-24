import YM.CF.Siete.Home
set_option autoImplicit false
set_option maxHeartbeats 500000
noncomputable section
namespace YM.CF.Siete
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG PhysicalNext.JointLoad Heir Next.Foundations AnalyticBridge.SectorAffine AnalyticBridge.SectorAffine.Offset Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Skye Scree Cube Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Classical Matrix.Norms.Frobenius
variable {n j l:ℕ}{K M' H C Q b v a ε r u R x t:ℝ}{c f:Side}{L:Side}{S:StepData (More c) (More f)}{F:Forest S.ratio}{A:Stores S}{P B:BudgetPoint}{X X':Support (More f)}{Y:Support (More c)}{I:Type}[Fintype I][DecidableEq I]
local notation "G"=>SU.group
structure Dawn(P B:BudgetPoint)(o:Seat f)(X:Support (More f))(Y:Support (More c))(V:Pane c)(U:Pane c→Pane f)(n l:ℕ)(T:Tube G S)(L:Side)(M A C:ℝ):Prop where
 hi:Healthy (B.threshold/4) X (U V)
 lo:Major P B V o (S.ratio.parent o) X U n (fleece n l X B M A)
 pre:Short S B X → Glow P B T C n X Y o V U L
lemma gate_mono(G₀:Gauge)(L:Side) {u v:ℝ}(hu:0<u)(h:u ≤ v)(p:j ≤ n): gateX G₀ L l n x u ≤ gateX G₀ L l j x v:=by
 have ht :0<feeI x l j:=by unfold feeI; positivity
 have hv:0 ≤ v:=hu.le.trans h; have he:= Scales.pos G₀ L x; unfold gateX; gcongr; unfold feeI; exact pow_le_pow_right₀ (le_add_of_nonneg_right (Nat.cast_nonneg _)) p
lemma lights (K:Teller G)(n s:ℕ)(p:2 ≤ n)(hs:2 ≤ s)(η J:ℝ)(h:0<η)(hJ:0 ≤ J) : ∃ C a C':ℝ,1 ≤ C∧1 ≤ a∧1 ≤ C'∧∀ P:Patch, P.Branches K.bind G → licensed η J P.L →∀ W: Push.Uniform.Before G K.top.width K.top.paths K.j K.bind (n+1+1),∀ q:Chi,∀ R:ℝ,0 < R → ∀ l:ℕ,l ≤ 18 → ∃ t:ℝ,0<t∧∀ᶠ x in atTop,∀ B Y:BudgetPoint,Find B Y n s x P.L→ 0 < gateX G P.L l (s*n+s*n) x t ∧∀ {c f:Side}(S:StepData (More c) (More f))(F:Forest S.ratio)(T:Tube G S)(V: Pane c)(k:S.Choices)(A:Stores S)(X:Support (More f))(U:Support (More c))(o:Seat f),Cert P K S T x→ Seam T η J → A.flags=flags (temp x) V →sizedP G P K S T F → o∈X → Healthy B.threshold U V →∀ (I:Type)[Fintype I][DecidableEq I](M:Museum F x A X U I), ∀ (β:ℝ), y G P.L x/2 ≤ β →∀ N:Pane f,∀ Z: LogArray G (Active A x F),(∀ i∈coZ M,‖Z i‖ ≤ gateX G P.L l (s*n+s*n) x t) → Dawn B Y o X U V (recent T β k q (R*fiery G x P.L) l N Z) n l T P.L C a C':=by
 obtain ⟨C,a,hC,hA,H⟩:=file K n s p hs; obtain ⟨M,hM,hM'⟩:=cloud K n s p hs η J h hJ
 refine ⟨C,a,M,hC,hA,hM,fun P ht hP W q R v l hl=>?_⟩
 obtain ⟨t,hz,Y'⟩:=hM' P ht hP W q R v l hl; obtain ⟨ε,hε,h'⟩:= H P ht W q R v l hl
 let t':=min t ε; have ht':0<t':=lt_min hz hε
 refine ⟨t',ht',?_⟩; filter_upwards [Y',h'] with x y' h' B Y u
 have hy:=Scales.pos G P.L x
 refine ⟨by unfold gateX feeI; positivity,fun {c f} S F T V k A X U o hx hv hf he ho hb I _ _ Z β hβ N Z' he'=>?_⟩
 have HH (X':Support (More f))(o':Seat f)(p:o'∈ X')(h:X'⊆X)(u':Short S Y X') : Glow B Y T M n X' U o' V (recent T β k q (R*fiery G x P.L) l N Z') P.L:=(y' B Y u).2 S F T V k A X' U o' hx hv hf he p u' hb _ (fringe Z h) (cappoint Y o' u.hU p u' (fringe Z h).away (fringe Z h).asks) β hβ N Z' (fun i p=>(he' i (fry Z h p)).trans (gate_mono _ _ ht' (min_le_left ..) (Nat.le_add_right ..)))
 refine ⟨?_,(h' B Y u).2 S F T V k A X U o hx hf he ho hb _ Z β hβ N Z' (fun i p=>(he' i p).trans (gate_mono _ _ ht' (min_le_right ..) le_rfl)),HH X o ho (Finset.Subset.refl _)⟩
 exact Finset.disjoint_left.mpr fun {i} p=> Finset.disjoint_left.mp (HH {i} i (mem_singleton_self _) (singleton_subset_iff.mpr p) (short_s S i)).hi (mem_singleton_self _)
-- principal large ANY local coefficient at literal. pre L constant.
lemma launchS (n:ℕ):∃ K:ℝ, 1 ≤ K∧∀ {c f:Side}(V: Pane c)(U:Pane c→Pane f)(B P:BudgetPoint)(X:Support (More f))(o:Seat f)(o':Seat c)(C:ℝ),1 ≤ C → Major P B V o o' X U n C → n=P.order→n≤ B.order→∀ (u:ℝ) (F:Pane f→ℂ),LocalOn X F →Signs B o (F ∘ increment (U V)) u → Signs P o' (F ∘ U ∘ increment V) (K*C^n*u):=by
 obtain ⟨K,h,H⟩:=factorial n; refine ⟨K,h,@fun c f V U B P X o o' C hC hx ht he u F hF hg=>?_⟩
 obtain ⟨Z,hZ,r,a,ha⟩:=hx.expZ; have hu:= hg.grade
 have heq : (F∘ U ∘ increment V)=ᶠ[𝓝 (0:tangD c)] (F∘ increment (U V)) ∘ Z:= a.mono fun w p=> show (F∘ U ∘ increment V) w=((F∘ increment (U V)) ∘ Z) w from hF _ _ p
 let f':=F ∘ increment (U V); have hv :ContDiffAt ℝ (n:ℕ∞ω) f' (Z 0):= by rw [r]; exact hg.paid.of_le (Nat.cast_le.mpr he)
 refine ⟨by positivity,by rw [←ht]; exact (hv.comp _ hZ).congr_of_eventuallyEq heq,fun j hj v hy=>?_⟩
 rw [(heq.iteratedFDeriv ℝ j).eq_of_nhds]; have hh:j ≤ n:=hj.trans_eq ht.symm
 refine (advances n f' Z 0 (h:=fun x=> Sized C x B o) hv hZ (fun i p v w=>show _≤C^n*u from ?_) (P.dirBound o') (fun i _ b => ha i b) j hh v hy).trans ?_
 · rw [r]; apply (seals hg _ (fun _=>C) (p.trans he) w).trans; simp only [prod_const,card_univ,Fintype.card_fin]; gcongr
 rw [mul_assoc K]; exact mul_le_mul_of_nonneg_right (H j hh) (by positivity)
end YM.CF.Siete
