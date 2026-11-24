import YM.CF.Rel.Coef
set_option autoImplicit false
noncomputable section
namespace YM.CF.Rel
open Function Filter Metric Lattice Wilson Laurent Precision Tree Finset Exterior Extra Bloch MeasureTheory NormedSpace Nacre Braid Font
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius InnerProductSpace
variable{G:Gauge}{n:Side}{m l r:ℕ}{A C σ:ℝ}
open Stationary
variable {α:Type}{k:ℕ}
def diskP (x:Site n)(z:DialT n m)(j:CurRun (m+1)):Disk n (m+1):= Fin.cons (x,j 0) (fun a=> (x+z a,j a.succ))
private def modelD: (Site n× DialT n m × CurRun (m+1)) ≃ Disk n (m+1) where
 toFun x:=diskP x.1 x.2.1 x.2.2
 invFun q:= ((q 0).1,(fun i=> (q i.succ).1-(q 0).1),fun i=>(q i).2)
 left_inv x:=by
    rcases x with ⟨a,x,y⟩; dsimp only [diskP]; simp only [Fin.cons_zero,Fin.cons_succ,add_sub_cancel_left]; congr 2; funext i; induction i using Fin.cases <;> simp
 right_inv x:=by ext1 i; induction i using Fin.cases <;> simp [diskP]
lemma d_sum {D:Type}[AddCommMonoid D](F:Disk n (m+1)→ D): ∑ i,F i=∑ i:Site n,∑ v:DialT n m, ∑ j:CurRun (m+1), F (diskP i v j):=by rw [←modelD.sum_comp,Fintype.sum_prod_type]; simp_rw [Fintype.sum_prod_type]; rfl
abbrev SpotG(G:Gauge)(m:ℕ):= Fin m→ G.ColorIndex
def spanW(x:DialT n m): stencil m:= fun i=> Lattice.lift (x i.1) i.2
lemma coil_W(x:DialT n m):coil n (spanW x)=x:= funext fun _=> wrap_lift _
abbrev jewelG (G:Gauge)(i:G.ColorIndex):= EuclideanSpace.basisFun G.ColorIndex ℝ i
def grabG (W:KitM G n (m+1))(k:Site n)(s:SpotG G (m+1))(d:DialT n m)(a:CurRun (m+1)):ℂ:= ∑ x,cell k x* W (diskP x d a) (fun i=>jewelG G (s i))
def breathL(W:KitM G n (m+1))(k:Site n)(s:SpotG G (m+1))(a:CurRun (m+1)) (p:Space m):ℂ:= ∑ d, mode p (spanW d)*grabG W k s d a
lemma coins_r (W:KitM G n (m+1)) (k:Site n) (s:SpotG G (m+1))(a:CurRun (m+1))(x:DialT n m): breathL W k s a (tollX x)= ∑ d:DialT n m,cMul x d*grabG W k s d a:=by unfold breathL; simp_rw [cord,coil_W]
lemma grab_paid (W:KitM G n (m+1)) (k:Site n)(s:SpotG G (m+1))(a:CurRun (m+1))(h:∑ i,‖W i‖≤ A): ∑ d:DialT n m,‖grabG W k s d a‖ ≤ A:=by
 unfold grabG; apply (sum_le_sum (fun i _=>norm_sum_le ..)).trans; rw [sum_comm]; refine le_trans ?_ h; rw [d_sum]
 refine sum_le_sum fun i _=> sum_le_sum fun j _=>?_ ; rw [norm_mul,legX,one_mul]; apply ((W _).le_opNorm _).trans; simp [jewelG]; exact single_le_sum (f:=fun p=>‖W (diskP i j p)‖) (fun i _ => norm_nonneg _) (mem_univ a)
lemma markV(x: Site n): size (Lattice.lift x)≤4* separation 0 x:=by
 unfold Laurent.size; rw [separation_comm,separation,sub_zero]; exact (sum_le_sum (g:=fun _=>pdist x) fun i _=>component_le x i).trans_eq (by simp)
def nerve(o:Site n)(r:ℕ)(W:KitM G n m):= ∀ i : Disk n m,i∉Pots o r m→ W i=0
lemma skip_h {o:Site n}{W:KitM G n (m+1)}(k:Site n)(s:SpotG G (m+1))(a:CurRun (m+1))(d:DialT n m)(h:nerve o r W)(he:d∉ketch (2*r) n m) : grabG W k s d a=0:=by -- o undecl
 apply sum_eq_zero; intro i _; rw [h (diskP i d a) _,_root_.zero_apply,mul_zero]; intro hi; apply he; apply (ketch_p ..).mpr; rw [shade_p] at hi; intro j
 have h₁ : separation o i ≤ r:= hi 0; have hi':= hi j.succ; simp only [diskP, Fin.cons_succ] at hi'; have hp:separation 0 (d j)=separation i (i+d j):=by rw [← separation_translate 0 (d j) i,zero_add,add_comm i];
 rw [hp]; exact (separation_triangle i o (i+d j)).trans (by rw [separation_comm i o]; omega)
lemma forda (W:KitM G n (m+1))(p:nerve 0 r W)(k:Site n)(s:SpotG G (m+1))(a:CurRun (m+1))(h:∑ i,‖W i‖≤ A):Braid.Pond (m*(4*(2*r))) A (breathL W k s a):=by
 let I:= ketch (2*r) n m; let F(d:DialT n m):= grabG W k s d a; have he: breathL W k s a=(fun p=>∑ i∈I, mode p (spanW i)*F i):=by
    funext y; unfold breathL; symm; exact sum_subset (subset_univ _) (fun i _ hi=>by unfold F; rw [skip_h k s a i p hi,mul_zero])
 rw [he]; apply (fundsF I _ (fun i=> ‖F i‖) ?_).mono _ le_rfl
 swap; · exact (sum_le_sum_of_subset_of_nonneg (subset_univ I) (fun _ _ _=>norm_nonneg _)).trans (grab_paid W k s a h)
 intro i hi; apply (Braid.Pond.modes _ _).mono le_rfl; unfold Laurent.size; rw [Fintype.sum_prod_type]; apply (sum_le_sum (g:=fun _ :Fin m=>4*(2*r)) fun j _=> (markV (i j)).trans (Nat.mul_le_mul_left _ ((ketch_p (r:=2*r) i).mp hi j))).trans_eq (by simp)
end YM.CF.Rel
