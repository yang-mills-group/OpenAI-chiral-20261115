import YM.SU5.FiniteGaugeData.Hills.Mass
/-! # An iterative synchronized joint closure in the actual phase spaces (abstract here). Work SOT. Then proof of two-group and extension. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy.Hills
open Function Filter NormedSpace Finset Topology
open scoped Topology BigOperators InnerProductSpace ComplexOrder
variable {H F Y: Hilbert}
inductive Sync (p:H.Op→ F.Op→ Prop) : H.Op→ F.Op → Prop
 | joint {x y} : p x y→ Sync p x y
 | van : Sync p 0 0
 | plus {x y v w} : Sync p x y→ Sync p v w→Sync p (x+v) (y+w)
 | scales {x y} (z:ℂ): Sync p x y→ Sync p (z • x) (z • y)
 | horizon {T:ℕ→ H.Op}{S:ℕ→ F.Op}{t:H.Op}{s:F.Op}: (∀ i,Sync p (T i) (S i))→ strong T t → strong S s → Sync p t s
namespace Sync
variable {p:H.Op→F.Op→Prop}
lemma total {I:Type*}(S:Finset I)(x:I→ H.Op)(y:I→ F.Op)(w:∀ i∈S, Sync p (x i) (y i)): Sync p (∑ i∈ S,x i) (∑ i∈S,y i):=by
 classical
 induction S using Finset.induction_on with
 | empty=> rw [sum_empty,sum_empty]; exact van
 | @insert i S v ih=> rw [sum_insert v,sum_insert v]; exact plus (w _ (mem_insert_self _ _)) (ih fun j u=> w j (mem_insert_of_mem u))
-- motif.Corr.Post-compose ordinary CLM.Olympic。Need both smooth Op function preserves SOT. For common sizes.M.
lemma billCL (g:H.Op→ₗ[ℂ] H.Op)(f:F.Op→ₗ[ℂ] F.Op)(V:∀ {x:ℕ→H.Op} {a:H.Op},strong x a → strong (fun i=>g (x i)) (g a))(P:∀{x:ℕ→ F.Op}{a:F.Op},strong x a → strong (fun i=> f (x i)) (f a))
    (h:∀{x y},p x y→ Sync p (g x) (f y)){x:H.Op}{y:F.Op}(c:Sync p x y) : Sync p (g x) (f y):=by
 induction c with
 | joint z=> exact h z -- use h z
 | van=> rw [map_zero,map_zero]; exact van
 | plus _ _ a b=> rw [map_add,map_add]; exact a.plus b
 | scales _ _ ih=> rw [map_smul,map_smul]; exact ih.scales _
 | horizon _ b t ih=> exact horizon ih (V b) (P t)
-- preservation of ordinary component. separately cont.
variable {x y:H.Op}{v w:F.Op}
lemma common (c:∀ a b u v,p a b→ p u v → Sync p (a*u) (b*v))(u:Sync p x v)(t:Sync p y w):Sync p (x*y) (v*w):=
 let s (a b)(h:p a b):= billCL (LinearMap.mulLeft ℂ a) (LinearMap.mulLeft ℂ b) (fun h=>strong.follows h a) (fun h=>strong.follows h b) (fun hw=>c a b _ _ h hw) t
 billCL (LinearMap.mulRight ℂ y) (LinearMap.mulRight ℂ w) (fun h=>h.leads y) (fun h=> h.leads w) (fun p=> s _ _ p) u
lemma rare (c:∀ a b u v,p a b→ p u v → Sync p (a*u) (v*b))(u:Sync p x v)(t:Sync p y w):Sync p (x*y) (w*v):=
 let s (a b)(h:p a b):= billCL (LinearMap.mulLeft ℂ a) (LinearMap.mulRight ℂ b) (fun h=>strong.follows h a) (fun h=>strong.leads h b) (fun hw=>c a b _ _ h hw) t
 billCL (LinearMap.mulRight ℂ y) (LinearMap.mulLeft ℂ w) (fun h=>strong.leads h y) (fun h=> strong.follows h w) (fun p=> s _ _ p) u
lemma goldene (Ω:H)(ψ:F)(c:∀ x y,p x y→inner ℂ Ω (x Ω)=inner ℂ ψ (y ψ))(g:Sync p x v): inner ℂ Ω (x Ω)=inner ℂ ψ (v ψ):=by
 induction g with
 | joint g=> exact c _ _ g
 | van=> simp
 | plus _ _ u v=> simp [inner_add_right,u,v]
 | scales c _ ih=>simp [inner_smul_right,ih]
 | horizon _ H f ih=> exact tendsto_nhds_unique_of_eventuallyEq ((continuous_const.inner (𝕜:=ℂ) continuous_id).continuousAt.tendsto.comp (H Ω)) ((continuous_const.inner (𝕜:=ℂ) continuous_id).continuousAt.tendsto.comp (f ψ)) (Eventually.of_forall ih)

-- transfer projection mean. mean Linear SOT. at every finite mean.Nat re-index.
variable {V U:Hilbert}{X:ClosedSubmodule ℂ V} {Z:ClosedSubmodule ℂ U} {p: (CoreH X).Op→ (CoreH Z).Op→ Prop}
-- frame price long
lemma frame_sumL (I:V.Op)(c:ClosedSubmodule ℂ V)(R:V.Op)(A:ℕ→ V.Op)(i:ℕ):
 social c (I * meanL A i * R)= meanL (fun i=>social c (I*A i*R)) i:= by
 unfold meanL; rw [Algebra.mul_smul_comm,Algebra.smul_mul_assoc,social_fee]; apply congrArg; change broadcast c _=∑ j∈ range i, broadcast c _; rw [Finset.mul_sum,Finset.sum_mul,map_sum]
lemma extract {A:ℕ→ V.Op}{B:ℕ→ U.Op}{X':V.Op}{Z':U.Op}(f g:V.Op)(h t:U.Op)
 (P:∀ i, Sync p (social X (f*A i*g)) (social Z (h* B i*t)))(e:strong (meanL A) X')(u:strong (meanL B) Z'): Sync p (social X (f*X'*g)) (social Z (h*Z'*t)):= by
 have he(i:ℕ): Sync p (social X (f*meanL A i*g)) (social Z (h* meanL B i*t)):=by rw [frame_sumL,frame_sumL]; exact scales ((i:ℂ)⁻¹) (total _ _ _ fun j _=> P j)
 exact horizon he (((e.follows f).leads g).socializes) (((u.follows h).leads t).socializes)
-- many means sequentially. requires Sync for all choices of tapes (indices available unconditionally in size n). price order.Geom.Initial.R adjust.
variable {A:Type*} (F:A→ ℕ→V.Op)(G:A→ℕ→ U.Op)(H':A→ V.Op)(Y:A→ U.Op)
lemma group (w:List A)(x y:V.Op)(z d:U.Op)(P₁:∀i,strong (meanL (F i)) (H' i))(Q₁:∀i,strong (meanL (G i)) (Y i))(g:∀ l:List (A × ℕ), l.map Prod.fst=w→ Sync p (social X (x * (l.map (uncurry F)).prod*y)) (social Z (z * (l.map (uncurry G)).prod*d))): Sync p (social X (x * (w.map H').prod*y)) (social Z (z*(w.map Y).prod*d)):=by
 induction w generalizing x z with
 | nil=> exact g [] rfl
 | cons a c ih=>
    let R' := (c.map H').prod * y; let Q' := (c.map Y).prod * d
    change Sync p (social X (x * (H' a * (c.map H').prod)* y)) (social Z (z * (Y a * (c.map Y).prod)* d))
    suffices e:Sync p (social X (x* H' a * R')) (social Z (z* Y a * Q')) by unfold R' Q' at e; simpa only [mul_assoc] using e
    apply extract x R' z Q' _ (P₁ a) (Q₁ a)
    intro i; have he:= ih (x* F a i) (z* G a i) (fun l p=>?_)
    · unfold R' Q'; simpa only [mul_assoc] using he
    have ht:= g ((a,i)::l) (by simp [p]); simpa only [List.map_cons,List.prod_cons,Function.uncurry_apply_pair,mul_assoc] using ht
#print axioms group
end Sync
end YM.CF.Buffered.Afterglow.Hierarchy.Hills
