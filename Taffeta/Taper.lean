import Weft.Fiber
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Mew
open Set Filter Metric MeasureTheory Function Finset
open scoped Classical
variable {I E:Type*}[Fintype I][LinearOrder I][NormedAddCommGroup E][NormedSpace ℂ E][CompleteSpace E]
-- sparsity of all list tips. if two functions agree on Keys supported within list and hill guaranteed equality
abbrev sparse (l:Finset I)(z:Key I):Prop:=∀ i,i∉ l→z i=0
lemma lance_sparse (l:List I)(f g:Key I→E)(D:Finset I)(u:l.toFinset⊆D)(t:∀ z,sparse D z→z∈hill I→f z=g z):∀ z,sparse D z→ z∈hill I→ lance f l z=lance g l z:=by
 induction l generalizing f g with
 | nil=>exact fun z v w=>t z v w
 | cons i l ih=>
    have e:i∈D:=u (by simp)
    exact ih (cutI _ _) (cutI _ _) (fun j p=>u (by rw [List.toFinset_cons]; exact mem_insert_of_mem p)) (fun z p v=> integral_congr_ae (ae_of_all _ fun θ=> congrArg ((homeB θ)⁻¹ • ·) (t _ (fun j h=>by rw [Function.update_of_ne (fun p:j=i=>h (p ▸ e))]; exact p j h) (fill_I v _ (homeC _)))))
lemma tip_sparse (l:List I)(f g:Key I→E)(t:∀ z,sparse l.toFinset z→z∈hill I→f z=g z):tipI f l=tipI g l:=lance_sparse l _ _ _ (Finset.Subset.refl _) t _ (fun i h=>rfl) roots
/- rename coordinates in a contour tip. Missing labels set to zero, always use distinct destinations. -/
variable {J:Type*}[Fintype J][LinearOrder J](σ:I→Option J)(D:J→I)(pD:∀ a b,σ a=some b→D b=a)
def channel(z:Key J): Key I:=fun i=> Option.elim (σ i) 0 z
#check Option.elim
lemma relay (z:Key J)(i:I){j:J}(p:σ i=some j):channel σ z i=z j:=by unfold channel; rw [p]; rfl
lemma voidMl (z:Key J)(i:I)(p:σ i=none):channel σ z i=0:=by unfold channel; rw [p]; rfl
lemma endpoints : ∀ z:Key J,z∈hill J→ channel σ z∈hill I:=by
 intro z p; apply hill_i.mpr; intro i; cases h:σ i; · rw [voidMl _ _ _ h]; simp
 rename_i j; rw [relay _ _ _ h]; exact hill_i.mp p j
lemma runway: Continuous (channel σ):=by
 apply continuous_pi; intro i; cases h:σ i; · simp_rw [voidMl σ _ _ h]; exact continuous_const
 rename_i j; simp_rw [relay σ _ i h]; exact continuous_apply _
include pD
lemma arrival (z:Key J)(j:J)(i:I)(p:σ i=some j)(x:ℂ): channel σ (update z j x)= update (channel σ z) i x:=by
 funext a; by_cases h:a=i; · subst a; rw [relay _ _ _ p,update_self,update_self]
 rw [update_of_ne h]; cases t:σ a; rw [voidMl _ _ _ t,voidMl _ _ _ t]; rename_i b; rw [relay _ _ _ t,relay _ _ _ t,update_of_ne (fun u:b=j=> h ((pD a b t).symm.trans ((congrArg D u).trans (pD i j p))))]
lemma river_relay (f:Key I→E)(p:River f):River (fun z=>f (channel σ z)):=by
 refine ⟨p.shore.comp (runway _).continuousOn (endpoints _),fun z t j x h=>?_⟩
 cases Classical.em (∃ i:I,σ i=some j)
 case inl g=> obtain ⟨i,g⟩:=g; simp_rw [arrival σ D pD z j i g]; exact p.slope _ (endpoints σ _ t) _ _ h
 case inr g=>
    have he(v:ℂ): channel σ (update z j v)=channel σ z:=by
      funext i; cases w:σ i; rw [voidMl _ _ _ w,voidMl _ _ _ w]; rename_i k
      rw [relay _ _ _ w,relay _ _ _ w,update_of_ne (fun k:k=j=> g ⟨i,w.trans (congrArg _ k)⟩)]
    simp only [he]; exact differentiableAt_const _
lemma lance_relay (l:List J)(f:Key I→E)(ψ:∀ i∈l,σ (D i)=some i):∀ z:Key J,lance (fun z=>f (channel σ z)) l z=lance f (l.map D) (channel σ z):=by
 induction l generalizing f with
 | nil=> exact fun _=>rfl
 | cons i l ih=>
    have h:cutI (fun z=>f (channel σ z)) i=(fun z:Key J=> cutI f (D i) (channel σ z)):=by
        funext z; unfold cutI; simp_rw [arrival σ D pD z i _ (ψ i (List.mem_cons_self))]
    intro z; change lance _ l _=_; rw [h,ih _ (fun i p=>ψ i (List.mem_cons_of_mem _ p))]; rfl
lemma tip_relay (l:List J)(f:Key I→E)(ψ:∀ i∈l,σ (D i)=some i):tipI (fun z=>f (channel σ z)) l=tipI f (l.map D):=by
 change lance ..=_; rw [lance_relay σ D pD l f ψ]
 suffices g:channel σ 0=0 by rw [g]
 funext i; cases h:σ i; rw [voidMl _ _ _ h]; rfl; exact relay _ _ _ h
#print axioms tip_sparse
#print axioms tip_relay
#print axioms river_relay
end YM.CF.Mew
end
