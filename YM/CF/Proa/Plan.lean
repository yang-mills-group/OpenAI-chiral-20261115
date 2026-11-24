import YM.CF.Proa.Lily
set_option autoImplicit false
noncomputable section
namespace YM.CF.Proa
open Function Filter Metric NormedSpace Finset Fock Lattice Wilson Laurent Lat Rush SU Drapes Fir Peaks Dial Paige Brace Vault Tulip Tenant Phase Broc Matrix Scroll Thera Branch Laic Cube
open scoped Matrix.Norms.L2Operator Matrix Topology ContDiff MatrixOrder BigOperators InnerProductSpace Kronecker
attribute [local instance] opCStarAlgebra
variable {ι:Type*}{u v:Bool}{L:Side}{F:WG ι}
variable (L) (ho: Odd L.val)(j:ℕ) (hj:Even j)(hu:1≤j) (K:WG ι)(H:Lively K)(p:∀ i n,K i n 1=0)(S:ι→Male)(v:Bool)
def Spree(C U: Script ι): Script ι:=fun i _ _ G x=> star (C i G (icec x))*U i G x
lemma SpreeV (C U:Script ι)(h:Save L false true @C)(v:Save L false true @U): Save L true true (Spree @C @U):= (h.withOpp ..).mul v
abbrev liftD(D:List Axis): Script ι:=fun i _ _ G x=> grapple D (S i) G x * treeF L ho j K S v (grass j S v) i G x
-- powerful budget magnitude pre-L
omit L ho hu K H S p
include hj
set_option linter.unusedSectionVars false in
lemma tremendous(v:Bool)(D:List Axis)(k:D.length+2≤j)(m:ℕ):∃ C:ℝ,0<C∧∀ (L:Side)(t:Odd L.val){I:Type*} (K:WG I),Lively K→(∀ i n,K i n 1=0)→∀ S:I→Male,∃ a e: ℝ,0<a∧0<e∧∃ k:ℕ, Score L (liftD L t j K S v D) true false a (C*followV D L) m k e:=by
 have hu:1≤j:=by omega
 obtain ⟨c,h,X⟩:= Scale j v D k m hj; refine ⟨c+1,by linarith,fun L t I K H p S=>?_⟩
 let T:=Thread j; let V:= canUse j L t
 obtain ⟨d,a,u,l,w,Z⟩:=X L t (@T) V
 let F:=treeF L t j K S v (grass j S v); have hF:= vitalC L t j hj hu K H p S v (grass j S v) (grass_S L t j hj hu S v)
 let G':=transportS (grapple_f j L t hj hu _ V D) S
 let B:=liftD L t j K S v D; let W:= optical j v D L t T
 have hp:= transportS (pine_funds j L t hj hu _ V v) S
 have ht:= G'.mul (hp.mul (hood_tag (ι:=I) _ t)); -- check Script defeq
 let R:Script I:=fun i _ _ G x=> B i G x-W (S i) G x; have hR:Save L true false @R:= (G'.mul hF).sub ht
 obtain ⟨z,y,b,q,g,hy,n,R'⟩:=hR; obtain ⟨c',p',N,C'⟩:= joined j L t hj hu _ V
 let e:=min b d; have he:0<e:=lt_min hy u; let n':=n+N+w
 have hh:Tax L @R true false z y n' e:=fun i _ _ G hl hv=> (decayV R' he (min_le_left ..) i G hl ((show n≤n' by unfold n'; omega).trans hv))
 have hz (i) {N₀ Q:Side}(G:Ratio N₀ Q)(hc:G.count=L)(x:n'≤N₀.val): R i G 1=0:=by
   have hp:unionP (1:Nom N₀ Q)=1:=by simp [unionP,profile_trivial]
   have hj':JointB G 1 c':=by
      let T:= (1:Nom N₀ Q); refine ⟨guard0 p'.le, guard0 p'.le,fun i=>?_⟩; have he(x:Site (More Q))(d:Walk): travel T.1 x d=1:=by induction d generalizing x with| nil=>rfl|cons a d ih=>rw [travel,ih]; simp [T,Step.read]; -- tune
      change ‖brand 1-brand (travel T.1 _ _)‖≤_; rw [he,sub_self,norm_zero]; exact p'.le
   have hv:=C' G hc ((show N≤ n' by unfold n'; omega).trans x) (S i) _ hj'; rw [hp] at hv; unfold R B W liftD optical; rw [mab _ _ _ hj hu _ p _ v G i hv]; exact sub_self _
 obtain ⟨a',l',f,j',r,v',E⟩:=weighted hh q g he _ (Vpos D L) @hz m
 refine ⟨min a' a,l',lt_min f l,j',w+v',fun i c f G h p=>?_⟩
 have hx:= (E i G h ((show v'≤ w+v' by omega).trans p)).desc (min_le_left a' a) (by positivity)
 have hv:= ((Scroll (A:=@W) Z j' (r.trans (min_le_right ..))) (S i) G h ((show w≤ w+v' by omega).trans p)).desc (min_le_right a' a) (by positivity)
 have hu:=hx.plus hv; -- XXX
 have he:(fun x: legal G l'=>R i G x.val+ W (S i) G x.val)=(fun x:legal G l'=> B i G x.val):=funext fun x=>by unfold R; rw [sub_add_cancel]
 rw [he] at hu; refine hu.prime ?_; intro i; simp [add_mul,add_comm]
end YM.CF.Proa
