import YM.CF.BProof.Tetrad.Shuffle
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Regard
open Function Finset Equiv
open scoped BigOperators Classical
variable {I A B U V W E T:Type*}{f:A→I→U}{A₁ A₂:Finset I}{g:A→T→V}
lemma pen_walk (p:Pen A₁ A₂ f)(S T': Finset T)(h:∀ x y:A,Matches A₁ (f x) (f y)→ Matches S (g x) (g y))(u:∀ x y:A,Matches A₂ (f x) (f y)→ Matches T' (g x) (g y)): Pen S T' g:=by
 obtain ⟨E,p⟩:= p; refine ⟨E,penMake g S T' E fun x=>?_⟩; obtain ⟨a,b,c,d⟩:= fromPen p x; exact ⟨h _ _ a,h _ _ b,u _ _ c,u _ _ d⟩
def piece(K:Type*){w:K→Type*}(E:∀ k:K,Perm (w k× w k)): Perm ((∀ i,w i)×(∀ i,w i)) where
 toFun x:=(fun i=>(E i (x.1 i,x.2 i)).1, fun i=>(E i (x.1 i,x.2 i)).2)
 invFun x:=(fun i=>((E i).symm (x.1 i,x.2 i)).1,fun i=>((E i).symm (x.1 i,x.2 i)).2)
 left_inv x:=by simp
 right_inv x:=by simp
lemma pen_array(K:Type*){w h:K→Type*}(F:∀ i:K,w i→I→h i)(p:∀ i,Pen A₁ A₂ (F i)): Pen A₁ A₂ (fun p:(∀ k,w k) => fun i:I => fun k=>F k (p k) i) :=by
 choose X H using p; let g:=piece K X; refine ⟨g, penMake _ _ _ _ fun z=>?_⟩; have h(i):=fromPen (H i) (z.1 i, z.2 i) -- remove t
 exact ⟨fun _ ht=> funext (fun k=>(h k).1 ht),fun _ ht=>funext (fun k=>(h k).2.1 ht),fun _ ht=>funext (fun k=>(h k).2.2.1 ht),fun _ ht=>funext (fun k=>(h k).2.2.2 ht)⟩
lemma pen_prod {g:B→ I→V}(p:Pen A₁ A₂ f)(u:Pen A₁ A₂ g): Pen A₁ A₂ (fun w:A×B=>fun i=> (f w.1 i,g w.2 i)):=by
 obtain ⟨X,h⟩:=p; obtain ⟨Y,w⟩:=u; let e:(A× B)×(A×B)≃ (A×A)×(B×B):= Equiv.prodProdProdComm ..; refine ⟨e.trans ((Equiv.prodCongr X Y).trans e.symm),penMake _ _ _ _ fun i=>?_⟩
 let x:= fromPen h (e i).1; let y:=fromPen w (e i).2
 exact ⟨fun _ h=>congrArg₂ _ (x.1 h) (y.1 h),fun _ h=>congrArg₂ _ (x.2.1 h) (y.2.1 h),fun _ h=>congrArg₂ _ (x.2.2.1 h) (y.2.2.1 h),fun _ h=>congrArg₂ _ (x.2.2.2 h) (y.2.2.2 h)⟩
lemma pen_seed (p:Disjoint A₁ A₂) : Pen A₁ A₂ (fun f:I→U=>f):=by
 let z(i:I) := if i∈A₂ then Equiv.prodComm U U else Equiv.refl _; refine ⟨piece (w:=fun _=>U) I z,penMake _ _ _ _ fun u=>?_⟩
 have ha(i)(x:i∈A₁):z i=Equiv.refl _:= if_neg (fun v=>Finset.disjoint_left.mp p x v); have hb(i:I)(x:i∈A₂):z i= prodComm _ _:=if_pos x
 have hz(i:I):(((piece (w:=fun _=>U) I z u).1 i),((piece (w:=fun _=>U) I z u).2 i))= z i (u.1 i, u.2 i):=rfl
 let t(i)(x:i∈A₁):= (hz i).trans (by rw [ha _ x]); let w(i)(x:i∈A₂):= (hz i).trans (by rw [hb _ x]); exact ⟨fun i v=> congrArg Prod.fst (t i v), fun i v=>congrArg Prod.snd (t i v),fun i v=>congrArg Prod.fst (w i v),fun i v=>congrArg Prod.snd (w i v)⟩ -- tune
end YM.CF.BProof.Regard
