import GaugeFieldConstruction.AllWorldRP
/-! slot linear: contaminants already allowed on domain. CLM on a single slot with arbitrary sides; vector-valued from kernel continuity. -/
set_option autoImplicit false
set_option maxHeartbeats 350000
noncomputable section
namespace YM.NSF.Boundary
open YM.Boundary Function Mink Set Filter MeasureTheory Analysis Distribution LD Bid Work.C22 Work.C23 Work.C24 OS Small Complex Metric Poincare
open scoped BigOperators Topology ContDiff InnerProductSpace NNReal
variable {n m:ℕ}{G:Gauge}{L:Register G}{S T:Table L}{C:LRoom T timeAxis}
variable {B:Small S C}{p q:ℝ≥0}{F:Waves S}{K:Spins S}{W:Surface S}{J:StarOp S}{D:∀ i,Blanket i}{R:S.Rotation}{s:S.RealSpin}
namespace Fields
-- vector arbitrary single slot as CLM.
variable (M:Fields S)(x:S.Union)(a b:Sentence S)
def pageRP (a:Sentence S): Module.End ℂ M.domain:= (a.map M.edits).prod
@[simp] lemma pageZeroRP: pageRP M []=1:=by simp [pageRP]
lemma pageMoreRP (l:Letter S): pageRP M (l::a)=M.edits l*(pageRP M a):=by simp [pageRP]
lemma fromPageRP:M.evaluates (a++b)=M.pageRP a (M.evaluates b):=by
 induction a with
 | nil=> simp
 | cons l t ih=> rw [List.cons_append,evaluates,ih,M.pageMoreRP]; rfl
def singlePageRP : Test4→ₗ[ℂ] M.H:= M.domain.subtype.comp ((M.pageRP a).comp ((M.field x).flip (M.evaluates b)))
lemma unitPageRP (z: Test4): singlePageRP M x a b z=M.vector (a++((x,z)::b)):=by unfold vector; rw[M.fromPageRP]; rfl
variable (Q:M.realizes W)(h:M.sharpPair J)
include Q h
lemma kernel_pageRP(f g:Test4): inner ℂ (singlePageRP M x a b f) (singlePageRP M x a b g)= W.expect (Sentence.rev J b ++ ((J x, Probe.bar f) :: (Sentence.rev J a ++ a) ++ ((x,g)::b))) :=by
 rw [unitPageRP,unitPageRP,M.general _ Q _ h]; simp [Sentence.rev,Surface.kernel,Letter.op]
lemma flowingPageRP:Continuous (singlePageRP M x a b):=by
 let r:=Sentence.rev J b; let t:=Sentence.rev J a++a; let v(p:Test4 × Test4):Fin (r.length+((t.length+(b.length+1))+1))→ Letter S:= Fin.append r.get (Fin.cons (J x, Probe.bar p.1) (Fin.append t.get (Fin.cons (x,p.2) b.get)))
 let A:=singlePageRP M x a b; let X(p:Test4× Test4):=inner ℂ (A p.1) (A p.2)
 have hu(p:Test4×Test4): X p= W.expect (List.ofFn (v p)):=by
    rw [show X p= _ from M.kernel_pageRP x a b Q h ..]; simp only [v, List.ofFn_fin_append,List.ofFn_cons,List.ofFn_get]; rfl
 have hp : Continuous X :=by
    rw [show X= _ from funext hu]; apply Work.C29.continuousExpect W v (Prod.fst ∘ v (0,0))
    · intro p i; refine Fin.addCases (fun j=>?_) (fun j=>?_) i
      · simp [v]
      refine Fin.cases ?_ ?_ j
      · simp [v]
      intro i; refine Fin.addCases (fun k=>?_) (fun k=>?_) i
      · simp[v]
      induction k using Fin.cases <;> simp[v]
    intro i; refine Fin.addCases ?_ ?_ i
    · intro j; simpa [v] using (continuous_const (X:=Test4×Test4) (y:=(r.get j).2))
    intro j; refine Fin.cases ?_ ?_ j
    · simpa [v,Function.comp_def] using (Probe.bar (V:=E4)).continuous.comp (continuous_fst (Y:=Test4))
    intro i; refine Fin.addCases (fun k=>?_) (fun k=>?_) i
    · simpa [v] using (continuous_const (X:=Test4×Test4) (y:=(t.get k).2))
    induction k using Fin.cases with
    | zero=> simpa [v] using (continuous_snd (X:=Test4) (Y:=Test4))
    | succ k=> simpa [v] using (continuous_const (X:=Test4×Test4) (y:=(b.get k).2))
 apply continuous_iff_continuousAt.2; intro f; apply OS.ketC -- tune
 · exact (hp.comp (continuous_id.prodMk continuous_id)).continuousAt
 exact (hp.comp (continuous_const.prodMk continuous_id)).continuousAt
def singleLocalRP : Test4→L[ℂ] M.H := ⟨singlePageRP M x a b,M.flowingPageRP x a b Q h⟩
lemma singleQuoteRP (f:Test4): singleLocalRP M x a b Q h f= M.vector (a++((x,f)::b)):=unitPageRP ..
#print axioms singleQuoteRP
end Fields
end YM.NSF.Boundary
end
