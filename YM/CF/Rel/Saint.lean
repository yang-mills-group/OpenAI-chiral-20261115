import YM.CF.Rel.Stack
set_option autoImplicit false
noncomputable section
namespace YM.CF.Rel
open Function Filter Metric Lattice Wilson Laurent Precision Tree Finset Exterior Extra Bloch MeasureTheory NormedSpace Nacre Braid Font
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius InnerProductSpace
variable{G:Gauge}{n:Side}{m l r:ℕ}{A C σ:ℝ}
open Stationary Push.Loops
def silica (s:SpotG G m):Delph G m:= (ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin m) ℂ).compContinuousLinearMap fun i=> tapG G (s i)
lemma ston(s:SpotG G m): ‖silica s‖ ≤ 1:=ContinuousMultilinearMap.opNorm_le_bound zero_le_one (fun i=>by
 rw [one_mul]; change ‖∏ j,tapG G (s j) (i j)‖≤ _; rw [norm_prod]; refine prod_le_prod (fun _ _=> norm_nonneg _) fun j _=>?_ ; rw [finW,Complex.norm_real]; exact PiLp.norm_apply_le ..)
lemma diskG(p:CurRun (m+1))(d:DialT n m)(j:Fin (m+1)): diskP 0 d p j=(fillSpot d j,p j):=by induction j using Fin.cases<;> simp [diskP,fillSpot]
lemma scribe(s:SpotG G (m+1))(p:CurRun (m+1))(u:InputZ G n)(d:DialT n m): silica s (fun j=>sumH G u (diskP 0 d p j))= oct p u s d 0:=by unfold oct; simp_rw [add_zero, diskG]; rfl
-- measure integrate ∑ Fin indices
lemma oct_u (s:SpotG G (m+1))(p:CurRun (m+1))(u:InputZ G n)(d:DialT n m): vat (diskP 0 d p) (rope (silica s)) u=∫ g,oct p (atU G g u) s d 0 ∂G.probHaar:=by
 simp_rw [vat,rope_u,sumH_p,scribe]
lemma oct_v (s:SpotG G (m+1))(p:CurRun (m+1))(u:InputZ G n)(d:DialT n m): Integrable (fun g:G.El=>oct p (atU G g u) s d 0) G.probHaar:=by
 simp_rw [←scribe, ←sumH_p]; exact ((silica s).contDiff (n:=ω)|>.continuous.comp (continuous_pi fun i=> ad_j _)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
def saltP (f:Salt n G)(x:InputZ G n):ℂ:=∫ g,f (atU G g x) ∂G.probHaar
def serene(f:Salt n G):Prop:=∀ x:InputZ G n,Integrable (fun g=>f (atU G g x)) G.probHaar
variable {f t:Salt n G}
lemma serene.sub(p:serene f)(h:serene t):serene (f-t):=fun i=> (p i).sub (h i)
lemma serene.add(p:serene f)(h:serene t):serene (f+t):=fun i=> (p i).add (h i)
lemma serene.mul(q:ℂ)(p:serene f):serene (q • f):=fun i=>(p i).smul q
lemma serene.shift(k x:Site n)(p:serene f):serene (courseC k x f):=fun i=> (p (te i x)).const_mul _
lemma serene.total {ι:Type}(p:Finset ι){f:ι→ Salt n G}(h:∀ i∈p,serene (f i)):serene (∑ i∈p,f i):=by intro i; simp_rw [Finset.sum_apply]; exact integrable_finsetSum p (fun i hi=> h i hi _)
lemma saltP_mul(q:ℂ)(f:Salt n G):saltP (q • f)=q • saltP f:=by funext x; unfold saltP; simp only [Pi.smul_apply, smul_eq_mul,integral_const_mul]
lemma saltP_sub(p:serene f)(h:serene t):saltP (f-t)=saltP f-saltP t:=by funext x; exact integral_sub (p x) (h x)
lemma saltP_sum {ι:Type}(p:Finset ι)(f:ι→ Salt n G)(h:∀ i∈p,serene (f i)): saltP (∑ i∈p,f i)=∑ i∈p,saltP (f i):=by
 ext1 x; unfold saltP; simp_rw [Finset.sum_apply]; exact integral_finsetSum p fun i hi=> h i hi x
lemma salt_shift (k x:Site n)(f:Salt n G):saltP (courseC k x f)=courseC k x (saltP f):=by ext1 i; unfold saltP courseC; rw [integral_const_mul]; rfl
lemma sailC(W:KitM G n (m+1))(k:Site n)(h:∀ i,Trade (W i)):
 let P:=∑ i:Disk n (m+1),courseC k (-(i 0).1) (vat i (W i)); saltP P=P:=by
 intro P; let f(i:Disk n (m+1)):=courseC k (-(i 0).1) (vat i (W i)); have hh(x:InputZ G n)(g:G.El):P (atU G g x)=P x:= by
    unfold P; simp_rw [Finset.sum_apply]; refine sum_congr rfl fun i _=> ?_; unfold courseC vat; change _* W i (fun j=> sumH G (atU G g (te x _)) (i j))=_; simp_rw [←sumH_p]; rw [show W i _= W i _ from h i (fun j=> sumH G (te x (-(i 0).1)) (i j)) g]
 ext1 x; simp [saltP,hh]
-- null credit functions unintegrated. prune sums by hh. payer arity.
end YM.CF.Rel
