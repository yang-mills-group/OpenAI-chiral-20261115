import YM.CF.Roots.Mara
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Roots
open Function Set Metric Mew MeasureTheory Filter Finset
open scoped Topology ContDiff BigOperators Matrix Classical
variable {I E F X N :Type*}[Fintype I][LinearOrder I][NormedAddCommGroup E][NormedSpace ℂ E][CompleteSpace E][NormedAddCommGroup F][NormedSpace ℂ F][CompleteSpace F][NormedAddCommGroup X][NormedSpace ℂ X][CompleteSpace X]
variable [NormedCommRing N][NormedAlgebra ℂ N][CompleteSpace N]
variable {f g:Key I→E}{u v:Key I→F}{a b a' b': Key I→N}{s t r:List I}
namespace GJ
abbrev SameS (s:List I)(f g: Key I→ E):Prop:=∀t:List I,t.Sublist s→tipI f t=tipI g t
lemma SameS.trim(p:SameS s f g)(q:t.Sublist s): SameS t f g:=fun l h=> p l (h.trans q)
variable (B:E→L[ℂ] F→L[ℂ] X)
def pulseV (f:Key I→ E)(u:Key I→F) :Key I→X:=fun z=> B (f z) (u z)
local notation "pζ"=> pulseV B
lemma prodR(p:River f)(q:River u):River (pζ f u):=⟨(B.continuous.comp_continuousOn p.shore).clm_apply q.shore,fun i v j x g=> ((B.differentiableAt.comp _ (p.slope i v j x g)).clm_apply (q.slope i v j x g))⟩
lemma prodTip(p:River f)(q:River u)(i:I)(l:List I):tipI (pζ f u) (i::l)= tipI (pζ (cutI f i) (u∘ dune i)) l+tipI (pζ (f∘ dune i) (cutI u i)) l:=by
 let P:= pζ (cutI f i) (u∘dune i); let V:= pζ (f∘dune i) (cutI u i)
 have hz:Set.EqOn (cutI (pζ f u) i) (fun z=> P z+V z) (hill I):=by
    intro t ht; have hx:= ((B.hasFDerivAt.comp_hasDerivAt _ (mitt p ht i)).clm_apply (mitt q ht i)).deriv; exact (mitt (prodR B p q) ht i).deriv.symm.trans hx -- tune
 exact (lace_C l hz roots).trans (tip_A (prodR B (p.flow i) (q.stay i)) (prodR B (p.stay i) (q.flow i)) _)
lemma prodTilt(i:I)(p:SameS (i::s) f g): SameS s (cutI f i) (cutI g i):= fun j h=> p _ (List.cons_sublist_cons.mpr h)
lemma uponS (i:I)(p:i∉s)(q:SameS s f g):SameS s (f∘dune i) (g∘dune i):= fun j h=> by rw [tip_V _ _ (fun v=>p (h.subset v)),tip_V _ _ (fun v=>p (h.subset v)),q _ h]
lemma prodS(p:River f)(q:River u)(t:River g)(w:River v)(r:SameS s f g)(k:SameS s u v)(τ:s.Nodup): SameS s (pζ f u) (pζ g v):=by
 induction s generalizing f u g v with
 | nil=> intro j h; rw [List.sublist_nil.mp h]; exact congrArg₂ (fun x y=> B x y) (show f 0=g 0 from r [] (List.Sublist.refl [])) (show u 0=v 0 from k [] (List.Sublist.refl []))
 | cons i l ih=>
    obtain ⟨a,b⟩:=List.nodup_cons.mp τ; let h:=List.sublist_cons_of_sublist i (List.Sublist.refl l); let V:= r.trim h; let W:=k.trim h
    intro j u'; cases u' with
    | cons _ e=>exact ih p q t w V W b j e
    | cons_cons _ e=>rw [prodTip B p q,prodTip B t w,ih (p.flow i) (q.stay i) (t.flow i) (w.stay i) (prodTilt _ r) (uponS _ a W) b _ e,ih (p.stay i) (q.flow i) (t.stay i) (w.flow i) (uponS _ a V) (prodTilt _ k) b _ e]
structure May (f g:Key I→E):Prop where
 Ra:River f
 Rb:River g

variable {J:Type*}(σ:I→J)
structure Kin (σ:I→J)(f g:Key I→E) : Prop where
 leftC: River f
 rightC: River g
 queen:∀s:List I,ψS σ s→tipI f s=tipI g s
lemma Kin.refl(p:River f):Kin σ f f:=⟨p,p,fun _ _=>rfl⟩
omit σ
variable {σ:I→J}
lemma Kin.symm(p:Kin σ f g):Kin σ g f:=⟨p.2,p.1,fun s h=>(p.3 s h).symm⟩
lemma Kin.trans{v:Key I→E}(p:Kin σ f g)(t:Kin σ g v):Kin σ f v:= ⟨p.1,t.2,fun s h=>(p.3 s h).trans (t.3 s h)⟩
lemma Kin.map(p:Kin σ f g)(V:E →L[ℂ] F):Kin σ (V∘f) (V∘g):=⟨sc_V p.1 V,sc_V p.2 V,fun s h=> (sim_H p.1 V s roots).trans ((congrArg _ (p.3 s h)).trans (sim_H p.2 V s roots).symm)⟩
lemma Kin.prod(b:Kin σ f g)(p:Kin σ u v): Kin σ (pζ f u) (pζ g v):=⟨prodR B b.1 p.1,prodR B b.2 p.2,fun s t=>prodS B b.1 p.1 b.2 p.2 (fun i h=> b.3 i ((h.map σ).nodup t)) (fun i h=>p.3 i ((h.map σ).nodup t)) (List.Nodup.of_map σ t) s (List.Sublist.refl _)⟩
lemma Kin.mulT(x:Kin σ a b)(y:Kin σ a' b'):Kin σ (a*a') (b*b'):= x.prod (ContinuousLinearMap.mul ℂ N) y
lemma Kin.expT(x:Kin σ a b): Kin σ (NormedSpace.exp ∘ a) (NormedSpace.exp ∘ b):=by
 refine ⟨x.1.exp_V,x.2.exp_V,fun s h=>?_⟩; let P(i:I):=(1:ℂ); have ph:South P s b a:= fun j t=>by rw [x.3 j ((t.map σ).nodup h)]; simp only [P,kR,one_smul]
 simpa only [P,kR,one_smul] using south_e x.2 x.1 P (List.Nodup.of_map σ h) ph s (List.Sublist.refl _)
-- every ∆ with a factor z_i in values only
variable (σ:I→J)
open NormedSpace
lemma sprigE (i:I)(p:River a)(h:∀ x:Key I,x i=0 → a x=0): Kin σ (exp ∘ a) (fun z=> 1+a z):=by
 have he: River fun z=> 1+a z:= dub_V (zeroR 1) p
 refine ⟨p.exp_V,he,?_⟩
 intro s v; have hy(d:Key I): a (dune i d)=0:=h _ (update_self ..)
 by_cases ht:i∈ s
 · obtain ⟨l,q,hx⟩:= List.append_of_mem ht; -- inspect
   let D:=l++q; have hf:s.Perm (i::D):=hx ▸ List.perm_middle -- tune
   have hu:i∉ D:= (List.nodup_cons.mp ((hf.nodup_iff.mp (List.Nodup.of_map σ v)))).1
   have hs:SameS D (cutI a i) (cutI a i):= fun j _=>rfl
   have hξ:(exp∘a)∘dune i=fun _=>1:=funext (fun z=>by change exp (a _)=_; rw [hy z,exp_zero])
   calc
    _ = tipI (exp∘ a) (i::D):=move_ζ hf p.exp_V roots
    _ = tipI (cutI a i*((exp∘a)∘dune i)) D:=sailE p i D
    _ = tipI a (i::D):=by rw [hξ,show cutI a i*(fun _=>1)=cutI a i from mul_one _]; rfl
    _ = tipI (fun z=>1+a z) (i::D):=by rw [tip_A (zeroR _) p,proper,zero_add]
    _ = _:=move_ζ hf.symm he roots
 rw [←tip_V i s ht,←tip_V (f:=fun z=> 1+a z) i s ht] -- ambiguous
 congr 1; funext j; change exp (a _)=1+a _; rw [hy,exp_zero,add_zero]

-- formal UNIQUE via ζexp and exp inverse [at truncated sublists].
lemma expResonF [DecidableEq J](p:River a)(q:River b)(x:a 0= b 0)(t:SameS s (exp∘a) (exp∘b))(h:ψS σ s):SameS s a b:=by
 let P:=ContinuousLinearMap.mul ℂ N; let inv:Key I→N:=fun z=>exp (- (a z)); have hi: River inv:=by
    have u:River fun z=> -a z:= by simpa using p.scale (-1:ℂ)
    exact u.exp_V
 intro k hp; cases k with
 | nil=>exact x
 | cons i k=>
    have ht:(i::k).Nodup:= hp.nodup (List.Nodup.of_map σ h); have hE: SameS k (exp∘a) (exp∘ b):= t.trim ((List.sublist_cons_of_sublist i (List.Sublist.refl k)).trans hp)
    have hw:SameS k (cutI a i*(exp∘a)) (cutI b i*(exp∘b)):=fun j u=> by
       have hw:(i::j).Sublist s:= ((List.cons_sublist_cons.mpr u).trans hp); have hk:ψS σ (i::j):=(hw.map σ).nodup h; rw [←ζexp _ p i hk,←ζexp _ q i hk,t _ hw]
    have hh:k.Nodup:=(List.nodup_cons.mp ht).2
    let A:=cutI a i* (exp∘a); let B0:= cutI b i*(exp∘a)
    have hu:SameS k B0 (cutI b i*(exp∘b)):=prodS P (q.flow i) p.exp_V (q.flow i) q.exp_V (fun _ _=>rfl) hE hh
    have hy:tipI (A*inv) k=tipI (B0*inv) k:=prodS P ((p.flow i).mul_T p.exp_V) hi ((q.flow _).mul_T p.exp_V) hi (fun s w=>(hw s w).trans (hu s w).symm) (fun _ _=>rfl) hh k (List.Sublist.refl _)
    suffices hI:(exp ∘ a)*inv=1 by unfold A B0 at hy; rw [mul_assoc, mul_assoc,hI,mul_one,mul_one] at hy; exact hy
    funext x; change exp (a x)*exp (-(a x))= (1:N); letI: NormedAlgebra ℚ N:= NormedAlgebra.restrictScalars ℚ ℂ _; rw [←exp_add,add_neg_cancel,exp_zero]

#print axioms Kin.prod
#print axioms sprigE
#print axioms expResonF
end GJ
end YM.CF.Roots
end
