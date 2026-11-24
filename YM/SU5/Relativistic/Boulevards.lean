import YM.Hilbert.Kolmogorov
import YM.SU5.FiniteGaugeData.Tower.Reflect
/-! # General structure for movement on directed linear pouch. Sym and contractions. -/
set_option autoImplicit false
set_option synthInstance.maxSize 18000
set_option maxHeartbeats 300000
noncomputable section
namespace YM.HostLegal
open Function Filter Topology Analysis Set
open scoped Topology MatrixOrder InnerProductSpace ComplexOrder
variable {X:Type} [AddCommGroup X][Module ℂ X]
structure Tier (X :Type)[AddCommGroup X][Module ℂ X] where
 F (s:ℕ): X→ₗ⋆[ℂ] X→ₗ[ℂ] ℂ
 cl (s m:ℕ): X →ₗ[ℂ] X
 fares(s:ℕ): ∀ i:X, 0 ≤ F s i i
 up(s m:ℕ) (v:s≤ m) (x y): F m (cl s m x) (cl s m y)= F s x y
 same(s:ℕ)(x): cl s s x=x
 further(s m k:ℕ)(h:s≤ m)(p:m≤k)(x) : cl m k (cl s m x)= cl s k x

variable (T:Tier X)
def Tier.Post(a b:ℕ× X):ℂ:=let t:= max a.1 b.1; T.F t (T.cl a.1 t a.2) (T.cl b.1 t b.2)
namespace Tier
variable (s n:ℕ)
lemma site_at (x y:ℕ× X)(h:x.1 ≤ s)(p:y.1≤ s):T.Post x y=T.F s (T.cl x.1 s x.2) (T.cl y.1 s y.2):=by
 unfold Post; simp only; rw [← T.up _ _ (show max x.1 y.1 ≤ s from max_le h p),T.further x.1 _ _ (le_max_left ..), T.further y.1 _ _ (le_max_right ..)] <;> exact max_le h p
lemma blessed:Nonempty (Kernel.Gram T.Post):=by
 apply Kernel.host; intro I p; let k:=Finset.univ.sup (fun i=> (p i).1)
 have h(i:Fin I): (p i).1≤ k:= Finset.le_sup (f:=fun i=> (p i).1) (Finset.mem_univ _)
 simp_rw [show ∀ i j,T.Post (p i) (p j)= T.F k (T.cl (p i).1 k (p i).2) (T.cl (p j).1 k (p j).2) from fun i j=> site_at T k _ _ (h i) (h j)]
 exact CF.Buffered.Afterglow.Tower.halfSpaceKernel (T.F k) (T.fares k) _
noncomputable def cabin:Kernel.Gram T.Post:= T.blessed.some
noncomputable abbrev booth := T.cabin.H

def entry(s:ℕ):X →ₗ[ℂ] T.cabin.H where
 toFun x:= T.cabin.plant (s,x)
 map_add' x y:=by
    apply T.cabin.whole.eq_of_inner_right ℂ
    intro h; induction h using Finsupp.induction_linear with
    | zero=> simp
    | add f g p t=> rw [map_add,inner_add_left,p,t,←inner_add_left] -- tune
    | single a r => simp only [_root_.YM.Kernel.Gram.stems,Finsupp.linearCombination_single]; rw [inner_smul_left,inner_smul_left,inner_add_right,T.cabin.measure,T.cabin.measure,T.cabin.measure]; simp [Post]
 map_smul' r x:=by
    apply T.cabin.whole.eq_of_inner_right ℂ
    intro h; induction h using Finsupp.induction_linear with
    | zero=> simp
    | add f g p t=> rw [map_add,inner_add_left,p,t,←inner_add_left]
    | single a r' => simp only [_root_.YM.Kernel.Gram.stems,Finsupp.linearCombination_single]; rw [inner_smul_left,inner_smul_left,inner_smul_right,T.cabin.measure,T.cabin.measure]; simp [Post] -- tune
lemma arrived (x y:X): inner ℂ (T.entry s x) (T.entry s y)=T.F s x y:=by change inner ℂ (T.cabin.plant _) (T.cabin.plant _)=_; rw [T.cabin.measure,T.site_at s _ _ (le_refl _) (le_refl _)]; simp only [T.same]
lemma increase {s n:ℕ}(h:s≤ n)(x:X): T.entry n (T.cl s n x)=T.entry s x:=by
 apply T.cabin.whole.eq_of_inner_right ℂ; intro f; induction f using Finsupp.induction_linear with
 | zero=>simp
 | add _ _ p q=>rw [map_add,inner_add_left,p,q,inner_add_left]
 | single a r=>
    let k:=max n a.1; have hn:n≤k:=le_max_left ..; have hz:a.1≤ k:=le_max_right ..
    simp only [Kernel.Gram.stems,Finsupp.linearCombination_single]; rw [inner_smul_left,inner_smul_left]; apply congrArg (fun z:ℂ=>(starRingEnd ℂ) r*z)
    change inner ℂ (T.cabin.plant a) (T.cabin.plant (n,T.cl s n x))=inner ℂ (T.cabin.plant a) (T.cabin.plant (s,x)); rw [T.cabin.measure,T.cabin.measure, site_at T k _ _ hz hn, site_at T k _ _ hz (h.trans hn)]; simp only [T.further _ _ _ h hn]
lemma ascend : Monotone (fun i=> LinearMap.range (T.entry i)):=fun i j p x ⟨u,t⟩=> ⟨T.cl i j u,(T.increase p u).trans t⟩
lemma front : Dense (⋃ i:ℕ, Set.range (T.entry i)):= by
 let M(i):= LinearMap.range (T.entry i); rw [show (⋃ i:ℕ, Set.range (T.entry i))= ↑(⨆ i,M i) from Eq.symm (Submodule.coe_iSup_of_directed M T.ascend.directed_le)]
 exact T.cabin.dense.mono (fun i h=> (Submodule.span_le.mpr (by rintro r ⟨⟨s,x⟩,rfl⟩; exact (le_iSup M s) ⟨x,rfl⟩) : Submodule.span ℂ (Set.range T.cabin.plant) ≤ ⨆ i,M i) h)
lemma see_late {f g:T.booth}(h:∀ k:ℕ,s≤k → ∀ z:X,inner ℂ (T.entry k z) f = inner ℂ (T.entry k z) g):f=g:=by
 apply T.front.denseRange_val.eq_of_inner_right ℂ; intro i; obtain ⟨a,w⟩:= mem_iUnion.mp i.property; obtain ⟨z,t⟩:=w; change inner ℂ i.val _=_; rw [← t]; exact (T.increase (show a≤ max a s from le_max_left ..) z) ▸ h _ (le_max_right ..) (T.cl a (max a s) z)

lemma by_front {D:Hilbert}{U V:T.booth→L[ℂ] D} (h:∀k:ℕ,s≤k → ∀ z:X,U (T.entry k z)=V (T.entry k z)):U=V:=by
 apply Kernel.Gram.by_bud; intro i; rcases i with ⟨a,b⟩; change U (T.entry a b)=V (T.entry a b); rw [← T.increase (show a≤ max s a from le_max_right ..), h _ (le_max_left ..)]

structure Lamination where
 mover(k:ℕ): X→ₗ[ℂ] X
 weak (k:ℕ)(p:s≤k) (x:X):‖T.entry k (mover k x)‖≤‖T.entry k x‖
 roll (k t:ℕ)(p:s≤k)(v:k≤ t)(x:X): T.cl k t (mover k x)=mover t (T.cl k t x)

lemma choose_ext (s:ℕ)(F:Lamination T s):∃ O:T.cabin.H.Op, ‖O‖ ≤ 1 ∧ ∀ n:ℕ,s≤n→∀ x:X,O (T.entry n x)= T.entry n (F.mover n x):=by
 let z(i:ℕ×X):T.booth:= let k:=max s i.1; T.entry k (F.mover k (T.cl i.1 k i.2))
 have hp(i:ℕ× X)(n:ℕ)(h:s≤n)(e:i.1≤ n): z i = T.entry n (F.mover n (T.cl i.1 n i.2)):= by
    unfold z; simp only; have ht:max s i.1≤ n:=max_le h e; rw [←increase T ht, F.roll _ _ (le_max_left ..) ht,T.further _ _ _ (le_max_right ..) ht]
 have hx:∀ f:(ℕ×X) →₀ ℂ, ‖Finsupp.linearCombination ℂ z f‖≤ 1*‖T.cabin.stems f‖:=by
    intro f; let u:=max s (f.support.sup (fun i=>i.1)); let x:=f.sum fun i v=> v • T.cl i.1 u i.2
    have hs:s≤u:=le_max_left ..; have he(i:ℕ×X)(p:i∈ f.support): i.1 ≤ u := (Finset.le_sup (f:=fun i=>i.1) p).trans (le_max_right ..)
    have h:T.cabin.stems f=T.entry u x:=by unfold x; simp only [map_finsuppSum,map_smul,Kernel.Gram.stems,Finsupp.linearCombination_apply]; unfold Finsupp.sum; refine Finset.sum_congr rfl fun i p=>?_ ; dsimp only; rw [T.increase (he i p)]; rfl -- tune
    have t:Finsupp.linearCombination ℂ z f=T.entry u (F.mover u x):=by unfold x; simp only [map_finsuppSum,map_smul,Finsupp.linearCombination_apply]; unfold Finsupp.sum; refine Finset.sum_congr rfl fun i p=>?_ ; dsimp only; rw [hp i u hs (he i p)]
    rw [h,t,one_mul]; exact F.weak u hs _
 obtain ⟨O,t,e⟩:= T.cabin.by_bound z 1 zero_le_one hx; refine ⟨O,t,fun n h x=>?_⟩; change O (T.cabin.plant (n,x))=_; simpa only [T.same] using ((e (n,x)).trans (hp _ n h le_rfl))

end Tier
end YM.HostLegal
