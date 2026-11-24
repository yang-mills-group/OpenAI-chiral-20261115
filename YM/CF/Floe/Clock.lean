import YM.CF.Floe.Shy
set_option autoImplicit false
noncomputable section
namespace YM.CF.Floe
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Topology Kronecker
open Filter NormedSpace Function Lattice Lat SU Fock Phase Cube Tenant Branch Drapes Metric Finset
attribute [local instance] opCStarAlgebra
variable {N:Side}{a b c d r e:ℝ}
namespace LedgerP
variable{F:pMat}{u:Bool}
lemma scaledT (h:certS F u u a b c)(x:ℝ): certS (fun i z=>x • F i z) u u a b (‖x‖*c):=by
 intro i; have he:=(h i).scale (x:ℂ); rw [Complex.norm_real] at he; convert he using 1; funext z; exact (RCLike.real_smul_eq_coe_smul ..) -- tune
lemma seriesC (h:LedgerP F u u)(t:∀ (i: IndexK)(x:Own i.1), ‖F i (skin x.val)‖≤ c)(hc:0 ≤ c)(e:c<1)(d:ℕ→ℝ)(p:∀ i, ‖d i‖ ≤1)(k:ℕ) : LedgerP (fun i z=>∑' j:ℕ,d j • F i z^(j+k)) u u:=by
 obtain ⟨a,b,D,g,l,s,v,h,p',J⟩:=powS _ h e hc t; let A(j):= D*g^(j+k); have he:Summable A:= ((summable_nat_add_iff k).mpr (summable_geometric_of_lt_one h.le p')).mul_left _
 refine keeps (a:=a) (b:=b) (c:=∑' j,A j) (fun i=>Crown.tsK A ?_ l.le he) l s; intro j; exact ((scaledT (J (j+k)) (d j) i).books (mul_le_of_le_one_left (by positivity) (p j)))
lemma geom (h:LedgerP F u u) (t:∀ (i:IndexK)(x:Own i.1), ‖F i (skin x.val)‖ ≤ c)(hc:0≤c)(e:c<1): LedgerP (fun i x=> (1-F i x)⁻¹) u u:=by
 obtain ⟨z,hz,v⟩:= exists_between e; obtain ⟨a,k,g⟩:= warm h hz t
 have hx:=seriesC h t hc e (fun _=> 1) (fun _=>by simp) 0; obtain ⟨u,b,r,t,p,w,Q⟩:=hx; refine keeps (a:=u) (c:=r) (b:=min b a) (fun i=>?_) t (lt_min p k); have he:= slim_e Q (min_le_left b a) i; convert he using 1; funext x; exact Eq.symm (by simp only [add_zero,one_smul]; exact route_inv ((g _ _ (cut_j x.property (min_le_right ..))).trans_lt v))
lemma logF(h:LedgerP F u u) (t:∀ (i:IndexK)(x:Own i.1), ‖F i (skin x.val)‖ ≤ c)(hc:0≤c)(e:c<1): LedgerP (fun i x=> pencil (F i x)) u u:= seriesC h t hc e bcoef bc_norm 1
lemma focal (h:LedgerP F u u)(t:∀ (i:IndexK)(x:Own i.1), Safe (F i (skin x.val))):LedgerP (fun i x=> projector (F i x)) u u:=by
 let U(i:IndexK)(x):= slack (F i x); have ht : LedgerP U u u:=by unfold U slack; simp_rw [sq]; exact (LedgerP.sub (identL _) (scale_t (times h h) _))
 have he:= seriesC ht (c:=rho) (fun i x=>(t i x).good) rho_pos.le rho_lt SignScalar.c SignScalar.c_norm 0
 have hp: LedgerP (fun i x=> rsEval (F i x)) u u:=by unfold rsEval rsTerm; simpa only [add_zero] using he
 exact scale_t (plus (identL _) (times (scale_t h _) hp)) _
end LedgerP
end YM.CF.Floe
