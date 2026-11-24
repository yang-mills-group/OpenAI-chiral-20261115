import YM.CF.Levier.Vase
set_option maxHeartbeats 350000
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 20000
set_option linter.unusedVariables false
noncomputable section
namespace YM.CF.Levier
open Function Filter Metric NormedSpace Finset Fock Lattice Wilson Laurent Lat Rush SU Drapes Fir Peaks Dial Paige Brace Vault Tulip Tenant Phase Broc Matrix Scroll Thera Branch Laic Cube
open scoped Matrix.Norms.L2Operator Matrix Topology ContDiff MatrixOrder BigOperators InnerProductSpace Kronecker
attribute [local instance] opCStarAlgebra
open Spire Nacre
-- analytic profiles under affine pullback incl sail seams
variable {N:Side}(b:Bool)(a:Shape)
open Urn
variable {P:Side}(G:Ratio N P)(e:ℝ)
lemma cloud_p (S:Seal (Site (More P))): roarD N a (cloudG G S)=cloudG G (roarD P (a.broad G) S):=by
 ext i; obtain ⟨i,rfl⟩:= a.anon_b.2 i; simp only [roarD,mem_image,a.anon_b.1.eq_iff,exists_eq_right,cloudG,mem_filter,mem_univ,true_and,a.foldsT, (Shape.broad G a).anon_b.1.eq_iff] -- tune
lemma clan_b(p c:Shape):Shape.broad G (joinX p c) = joinX (Shape.broad G p) (Shape.broad G c):=by unfold Shape.broad joinX; congr 1; rw [smul_add, show p.s.act (G.count.val • c.t) = G.count.val • p.s.act c.t from map_nsmul (p.s.actEquiv (R:=ℤ)) .. ]
local notation "β"=>Shape.broad G a
def quay (x:Coil N P):Coil N P:= (gateC b β x.1,gateC b a x.2)
def wish(x:cro G e): ↑(cro G e):=⟨(quay b a G x.val.1,gateC b β x.val.2),by
 obtain ⟨U,h,v⟩:= x.property.1; obtain ⟨V,g,w⟩:=x.property.2
 refine ⟨⟨stanza G a (xtra b) U, alongS _ _ _ _ _ h,?_⟩, _,keepC (xtra b) β V _ g,?_⟩
 · have he: unionP (stanza G a (xtra b) U) = quay b a G (unionP U):= Prod.ext (veil_p ..) (veil_p ..); rw [he,Prod.norm_def]; dsimp only [quay, Prod.fst_sub,Prod.snd_sub]; rw [gate_n,gate_n]; exact v
 rw [veil_p,gate_n]; exact w⟩ -- tune
lemma wish_seq(t:Bool)(c:Shape)(x:cro G e): wish t c G e (wish b a G e x)=wish (b.xor t) (joinX a c) G e x:=by
 apply Subtype.ext; refine Prod.ext (Prod.ext ?_ (stanceB ..)) ?_
 all_goals change gateC t (Shape.broad G c) (gateC b (Shape.broad G a) _) =gateC (b.xor t) (Shape.broad G (joinX a c)) _; rw [stanceB,clan_b]
lemma wish_i(x:cro G e):wish false (incX 1) G e x=x:=by 
 have ht(v:Chin P): gateC false (Shape.broad G (incX 1)) v=v:=by rw [show Shape.broad G (incX 1) = incX 1 by simp [Shape.broad,incX],wone]
 exact Subtype.ext (Prod.ext (Prod.ext (ht _) (wone _)) (ht _))
lemma wish_cov(h:Site (More P)→ E)(x:cro G e): wish b a G e ((hall G e).drive h x)=(hall G e).drive (starG b β h) (wish b a G e x):=by
 have ht:scaleG G (starG b β h)=starG b a (scaleG G h):=by ext1 i; simp only [scaleG,starG,Function.comp_apply,Shape.foldsT]
 apply Subtype.ext; refine Prod.ext (Prod.ext (covB ..) ?_) (covB ..); change gateC b a (relayg (scaleG G h) _) =relayg (scaleG G (starG b β h)) _; rw [covB,ht]; rfl
lemma wish_e(S:Seal (Site (More P)))(x y:cro G e): (hall G e).eval S (wish b a G e x) (wish b a G e y)=(hall G e).eval (roarD P β S) x y:=by unfold hall deal wish quay; dsimp only; rw [roseC,roseC,roseC, cloud_p]
lemma gate_c :Continuous (gateC (N:=N) b a):=by
 apply continuous_pi; intro i; apply continuous_pi; intro v
 let f(x:Chin N):=x (elf a i) (v.xor (a.s.flip i.2)); have he:Continuous f:=by unfold f; fun_prop
 exact ((typ_l b).comp (continuous_fst.comp he)).prodMk ((typ_l b).comp (continuous_snd.comp he)) -- tune
lemma cans : Continuous (wish b a G e):=by
 apply Continuous.subtype_mk; exact (((gate_c b _).comp (continuous_fst.comp (continuous_fst.comp continuous_subtype_val))).prodMk ((gate_c b _).comp (continuous_snd.comp (continuous_fst.comp continuous_subtype_val)))).prodMk ((gate_c b _).comp (continuous_snd.comp continuous_subtype_val))
end YM.CF.Levier
