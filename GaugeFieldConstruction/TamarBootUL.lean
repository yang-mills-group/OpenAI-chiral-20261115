import GaugeFieldConstruction.TraceBootUL
set_option autoImplicit false
noncomputable section
namespace YM.GaugeFieldConstruction.Fathom
open Function Filter Analysis Points Set MeasureTheory Complex
open scoped Topology BigOperators ContDiff Classical
variable {n:ℕ}(a:Axis)(p:Points n)(B:Fin n→Bulb)
-- all steps mandatory of same F
abbrev RockUL (n:ℕ):= Fin n × Axis
variable (F:Points n→ℂ)(G: RockUL n → Axis → Points (n+1)→ℂ)
noncomputable def CξUL (i:RockUL n): Points n →L[ℝ] ℝ:={ toFun:=fun x=> x i.1 i.2, map_add':=by simp, map_smul':=by simp, cont:= (show Continuous (fun (x:E4)=> x i.2) by fun_prop).comp (show Continuous fun (x:Points n)=> x i.1 by fun_prop)} -- syntax && simp
noncomputable def ZipUL (i:RockUL n):Points n:=mirDirYL i.1 i.2
variable (h: ∀ k, BreatherMars (B k) k p)
variable (w:∀ i:RockUL n,∀ x r, calmYL i.1 i.2 r x (B i.1)→ F (ledgeYL i.1 i.2 r x 1)= F x+r • ∑ j:Axis,ScrollOpYL i.2 x (B i.1) j i.1 r (G i j))
variable (e:∀ i j, ContinuousOn (G i j) (conf (n+1)))
variable (s:Finset (RockUL n))
noncomputable def silkUL (B:Fin n→Bulb)(G:RockUL n → Axis → Points (n+1)→ℂ)(i:RockUL n)(x:Points n):ℂ:=∑ j:Axis,raysCostYL (B i.1) j (G i j) x
noncomputable abbrev HopUL(p:Points n)(s:Finset (RockUL n))(x:Points n):= p + ∑ i∈s,CξUL i (x-p) • ZipUL i
noncomputable abbrev SoUL (z:RockUL n → ℂ)(s:Finset (RockUL n)): Points n →L[ℝ] ℂ:=∑ i∈s, ContinuousLinearMap.toSpanSingleton ℝ (z i) ∘L CξUL i
lemma ZipSprUL (x:Points n): (∑ i:RockUL n,CξUL i x • ZipUL i) = x:=by
 rw [Fintype.sum_prod_type]; ext j a
 simp [CξUL,ZipUL,mirDirYL, NSF.Points.direction] 
 rw [Finset.sum_eq_single j]
 · simp
 · intro i _ z; have hp : j ≠ i:=Ne.symm z; simp [hp]
 intro v; exact (v (Finset.mem_univ _)).elim
lemma HopProfUL (i j:RockUL n): CξUL i (ZipUL j) = if i=j then 1 else 0:=by
 rcases i with ⟨i,a⟩; rcases j with ⟨j,b⟩; by_cases s:i=j; · subst j; simp [CξUL,ZipUL,mirDirYL, NSF.Points.direction]
 simp [CξUL,ZipUL,mirDirYL, NSF.Points.direction,s]
lemma ZipProcUL (z:RockUL n → ℂ) (i:RockUL n): SoUL z Finset.univ (ZipUL i)=z i:=by simp [SoUL,HopProfUL] -- needs
include h w e
lemma HopPrUL : HasFDerivAt (F ∘ HopUL p s) (SoUL (fun i=>silkUL B G i p) s) p:=by
 induction s using Finset.induction_on with
 | empty => rw [show F ∘ HopUL p ∅=(fun _:Points n=>F p) from funext fun x=>by simp [HopUL]]; simpa only [SoUL,Finset.sum_empty] using hasFDerivAt_const (𝕜:=ℝ) (F p) p
 | @insert i s ho hi =>
   let T:= HopUL p s; let L:= CξUL i; let S:= L ∘ (fun x=>x-p)
   let X:=fun x:Points n=>(T x,S x); let M:=i.2; let j:=i.1
   have hu:T p=p:=by simp [T,HopUL]
   have hv:S p=0:=by simp [S]
   have hx:ContinuousAt X p:= (((continuous_const.add (continuous_finsetSum _ (fun i _=>(Continuous.smul ((CξUL i).continuous.comp (continuous_id.sub continuous_const)) continuous_const)))) : Continuous T).prodMk (L.continuous.comp (continuous_id.sub continuous_const))).continuousAt -- tune
   let Y:Set (Points n × ℝ):={x| calmYL j M x.2 x.1 (B j)}
   have q:Y∈𝓝 (X p):= (ArchUL M (B j) j).mem_nhds (show calmYL _ _ (S p) (T p) _ from by rw [hv,hu]; exact calmUL _ _ _ _ (h j))
   let A(x:Points n):= ∑ t:Axis,ScrollOpYL M (T x) (B j) t j (S x) (G i t)
   have hp:ContinuousAt A p:= by
     have hr(t:Axis): ContinuousAt (fun x:Points n=>ScrollOpYL M (T x) (B j) t j (S x) (G i t)) p:= ((RouteUL M (B j) j t (G i t) (e i t)).continuousAt q).comp hx
     change ContinuousAt (fun x=>∑ t:Axis,ScrollOpYL M (T x) (B j) t j (S x) (G i t)) p
     exact (tendsto_finsetSum Finset.univ (fun i _=> (hr i).tendsto))
   have hb:A p=silkUL B G i p:=by simp only [A,hv,hu,silkUL]; exact Finset.sum_congr rfl fun t _=>ChargeUL M p (B j) j t (h j) _ (e i t)
   rw[SoUL,Finset.sum_insert ho,←hb, add_comm]
   refine (hi.add (TrackUL p L A hp)).congr_of_eventuallyEq ?_
   filter_upwards [hx.tendsto q] with x hy
   change F (HopUL p (insert i s) x)= F (T x)+ S x • A x
   rw[show HopUL p (insert i s) x=ledgeYL j M (S x) (T x) 1 from ?_]; exact w i _ _ hy
   simp [j,M,L,S,T,ledgeYL,ZipUL,HopUL,ho]
   abel -- simp add sm risky
lemma UrnUL : HasFDerivAt F (SoUL (fun i=>silkUL B G i p) Finset.univ) p:=by
 have he:= HopPrUL p B F G h w e Finset.univ
 apply he.congr_of_eventuallyEq
 apply Eventually.of_forall; intro x; simp only [HopUL,Function.comp_apply,ZipSprUL,add_sub_cancel]
#print axioms UrnUL
end YM.GaugeFieldConstruction.Fathom
end
