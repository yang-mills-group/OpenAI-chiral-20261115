import GaugeFieldConstruction.VenusΛL
/-!
 # Inert projections. Unit lifting to operators.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 15000
set_option maxHeartbeats 300000
noncomputable section
namespace YM.NSF.Boundary
open YM.Boundary Mink Function Set Filter MeasureTheory Complex Finset
open scoped Topology BigOperators ContDiff InnerProductSpace
open NSF.Work.C20
variable {n:ℕ}(k:Fin (n+1))
def cutPithΛL (k:Fin (n+1)): WithLp 2 (E4 × Points n) ≃ₗᵢ[ℝ] Points (n+1) where
 toFun u:= points (k.insertNth (α:=fun _=>E4) u.fst u.snd.ofLp)
 invFun u:= WithLp.toLp 2 (u k,pithΛL k u)
 left_inv u:=by
    apply WithLp.ofLp_injective 2; apply Prod.ext
    · simp
    apply PiLp.ext; intro i; simp [pithΛL,remΛ]
 right_inv u:=by
    apply PiLp.ext; intro i; change k.insertNth (α:=fun _=>E4) (u k) (k.removeNth u.ofLp) i=u i; rw[Fin.insertNth_self_removeNth]
 map_add' a b:=by ext1 i; cases i using Fin.succAboveCases k <;> simp
 map_smul' a b:=by ext1 i; cases i using Fin.succAboveCases k <;> simp
 norm_map' a:=by
    rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), PiLp.norm_sq_eq_of_L2, WithLp.prod_norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2 _ a.snd,Fin.sum_univ_succAbove _ k]; simp
abbrev TulipΛL (k:Fin (n+1)): (E4 × Points n)≃L[ℝ] Points (n+1):= (WithLp.prodContinuousLinearEquiv 2 ℝ _ _).symm.trans (cutPithΛL k).toContinuousLinearEquiv
lemma measureΛL : MeasurePreserving (TulipΛL k):= (cutPithΛL k).measurePreserving.comp (WithLp.volume_preserving_toLp _ _)
lemma pithCutΛL (x:E4× Points n):pithΛL k (TulipΛL k x)=x.2:= (congrArg (WithLp.snd) ((cutPithΛL k).symm_apply_apply (WithLp.toLp 2 x)))
lemma pithCoinΛL (u:Points (n+1))(y:Heights (n+1)): waneΛL k (glow u (dawn y))= glow (pithΛL k u) (dawn (remΛ k y)):=rfl
lemma dimeΞΛL (v: Fin (n+1) →Test4)(x:E4× Points n): Joint.materialize (n+1) v (TulipΛL k x)= v k x.1 * Joint.materialize n (remΛ k v) x.2:=by
 rw [Joint.material_at,Joint.material_at, Fin.prod_univ_succAbove _ k]; change v k (k.insertNth (α:=fun _=>E4) _ _ k) * (∏ i:Fin n,v (k.succAbove i) (k.insertNth (α:=fun _=>E4) _ _ _))=_; simp[remΛ]
lemma seekCoinΛL : Tendsto (fun x:Heights (n+1)=> remΛ k x) (𝓝[east (n+1)] 0) (𝓝[east n] 0) := by
 refine tendsto_nhdsWithin_iff.2 ⟨?_,?_⟩
 · apply tendsto_pi_nhds.mpr; intro i; exact ((continuous_apply (k.succAbove i):Continuous fun x:Heights (n+1)=> x _).tendsto (0: Heights (n+1))).mono_left nhdsWithin_le_nhds
 filter_upwards [self_mem_nhdsWithin] with y hy; change StrictMono (remΛ k y); exact (show StrictMono _ from hy).comp k.strictMono_succAbove
variable {G:Gauge}{L:Register G}{S:Table L}{Y:Surface S}{F:Waves S}{D:∀ i, Blanket i}{N:Y.Aurora D}(p:F.NonTangentialFree Y)(r:N.FullBody F)
variable (A: S.Union)
abbrev TreeΛL (A:S.Union):Prop:=∀ (n:ℕ)(k:Fin (n+1))(V:Fin (n+1)→S.Union),V k=A →∀ x∈tube (n+1), N.emit V x=N.emit (remΛ k V) (waneΛL k x)
variable (u:TreeΛL (N:=N) A)
include u p r
lemma ΓCheapΛL (a:Heights (n+1))(e:a∈east (n+1))(v:Fin (n+1)→Test4)(T:Fin (n+1)→S.Union)(h:T k=A): (∫ x:Points (n+1), F.restricted T a x* Joint.materialize _ v x)= (∫ x:E4, v k x)*(∫ y:Points n, F.restricted (remΛ k T) (remΛ k a) y* Joint.materialize _ (remΛ k v) y) :=by
 let Q:= fun x:Points (n+1)=> F.restricted T a x*Joint.materialize _ v x; change (∫ x,Q x)=_
 have hc:Integrable Q:=p.int _ _ _ e _
 have hy:remΛ k a∈east n:= (show StrictMono a from e).comp k.strictMono_succAbove
 rw [← (measureΛL k).integral_comp (TulipΛL k).toHomeomorph.measurableEmbedding Q]; let R:= fun y:Points n=>F.restricted (remΛ k T) (remΛ k a) y* Joint.materialize _ (remΛ k v) y
 have H(z:E4×Points n):Q (TulipΛL k z)=v k z.1 * R z.2:=by
    unfold Q R; rw [dimeΞΛL,← r.pure _ _ _ _ e, u _ k T h _ (roseΛ (etched e) _),pithCoinΛL,pithCutΛL,r.pure _ _ _ _ hy]; ring
 simp_rw [H]; exact integral_prod_mul _ _
lemma ΓCheapWΛL (v:Fin (n+1)→Test4)(T:Fin (n+1)→S.Union)(h:T k=A): Y.W (n+1) T (Joint.materialize _ v)= (∫ x:E4, v k x)*Y.W n (remΛ k T) (Joint.materialize _ (remΛ k v)):=by
 have z:= p.corner (n+1) T (Joint.materialize _ v)
 haveI:= awaits (light (n+1)); apply tendsto_nhds_unique z
 refine (((p.corner n (remΛ k T) (Joint.materialize _ (remΛ k v))).comp (seekCoinΛL k)).const_mul (∫ x:E4,v k x)).congr' ?_; filter_upwards [self_mem_nhdsWithin] with y hy; exact (ΓCheapΛL k p r A u y hy v T h).symm
lemma ΓCheapEΛL (q: Letter S) (v: Fin n → Letter S)(h:q.1=A): Y.expect (List.ofFn (k.insertNth q v : Fin (n+1)→Letter S))= (∫ x:E4,q.2 x)*Y.expect (List.ofFn v):=by
 simp only [Work.C29.expectOfFn]
 rw [ΓCheapWΛL k p r A u]; swap; · simp [h]
 simp [remΛ,Function.comp_assoc]
omit u p r
-- insert with Any list by rec p into address v.
lemma versionInsertΛL {A :Type*}(j i:List A)(x:A): ∃ (n:ℕ)(k:Fin (n+1))(V: Fin n→A), j++i=List.ofFn V ∧ j++(x::i)=List.ofFn (k.insertNth x V : Fin (n+1)→A):=by
 induction j with
 | nil=>refine ⟨i.length,0,i.get,?_⟩; simp [Fin.insertNth_zero']
 | cons z j ih=> obtain ⟨n,k,V,h,g⟩:=ih; refine ⟨n+1,k.succ,Fin.cons z V,?_⟩; simp only[List.cons_append,Fin.insertNth_succ_cons,List.ofFn_cons,h,g,and_self]
variable (b:Test4)
include p r u
lemma ΓAtΛL (j i: Sentence S): Y.expect (j ++ ((A,b)::i))= (∫ x:E4,b x)* Y.expect (j++i):=by
 obtain ⟨n,k,V,h,z⟩:= versionInsertΛL j i (A,b); rw [h,z]; exact ΓCheapEΛL k p r A u _ _ rfl
variable (R:Fields S)(e:R.Total)
local notation "XΩ"=> R.domain
include e
lemma TrueCoinΛL (J:StarOp S)(s:R.sharpPair J)(m:R.realizes Y): R.field A b=(∫ x:E4,b x) • (1:Module.End ℂ XΩ):=by
 apply DrivesΛL R e; intro i; apply ΓEyesΛL R e; intro j
 rw [LinearMap.smul_apply,inner_smul_right]; change inner ℂ (R.vector j) (R.vector ((A,b)::i))=_ * inner ℂ (R.vector j) (R.vector i); rw [R.general Y m J s,R.general Y m J s,Surface.kernel,Surface.kernel,ΓAtΛL p r A u] -- tune.
#print axioms TrueCoinΛL
end YM.NSF.Boundary
end
