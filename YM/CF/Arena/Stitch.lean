import YM.CF.Arena.Watt
set_option autoImplicit false
set_option maxHeartbeats 700000
noncomputable section
namespace YM.CF.Arena
open Function Filter Metric Lattice Wilson Laurent Precision Tree Finset Exterior Extra Bloch MeasureTheory NormedSpace Nacre Braid Font
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius InnerProductSpace Matrix Kronecker
open Jet Rel Stationary Push.Loops
variable{G:Gauge}{n:Side}{m l r:ℕ}{A C σ:ℝ}
open RG
section
variable{c f:Side}{S: StepData c f}
abbrev Tab(S:StepData c f):= Forest S.ratio × S.Choices
def token(A:Finset (Site c))(X Y:Forest S.ratio):Forest S.ratio where
 up i:=if S.ratio.parent i∈A then X.up i else Y.up i
 height i:=if S.ratio.parent i∈A then X.height i else Y.height i
 bound i:=by split; apply X.bound; apply Y.bound
 rise i h:=by
    by_cases p:S.ratio.parent i∈A
    · simp only [if_pos p,X.stays i h]; exact X.rise _ h
    simp only [if_neg p,Y.stays i h]; exact Y.rise _ h
 stays i h:=by split; exact X.stays i h; exact Y.stays i h
def unite(S:StepData c f)(A:Finset (Site c))(X Y:Tab S):Tab S:=⟨token (S:=S) A X.1 Y.1,(fun i=> if i∈A then X.2.1 i else Y.2.1 i),(fun i=>if i.1 ∈ A then X.2.2 i else Y.2.2 i)⟩
lemma eq_t(X Y:Tab S)(h:X.1.up=Y.1.up)(p:X.1.height=Y.1.height)(q:X.2=Y.2):X=Y:=by rcases X with ⟨⟨a,b,h',p',q'⟩,x⟩; rcases Y with ⟨⟨c,d,h'',p'',q''⟩,y⟩; dsimp only at *; subst c d y; rfl
lemma empty_U(U V:Tab S):unite S ∅ U V=V:= eq_t _ _ (funext fun i=>by simp [unite,token]) (funext fun i=>by simp [unite,token]) (Prod.ext (funext fun i=>by simp [unite]) (funext fun i=>by simp [unite]))
lemma all_U (U V: Tab S): unite S univ U V=U:=eq_t _ _ (funext fun i=>by simp [unite,token]) (funext fun i=>by simp [unite,token]) (Prod.ext (funext fun i=>by simp [unite]) (funext fun i=>by simp [unite]))
structure Kind(S:StepData c f)(A B:Tab S)(X:Support c):Prop where
 up i : S.ratio.parent i∈X→ A.1.up i=B.1.up i
 ht i : S.ratio.parent i∈X → A.1.height i=B.1.height i
 site i:i∈X→A.2.1 i=B.2.1 i
 edge (i:Edge (Site c)): i.1∈X→A.2.2 i=B.2.2 i
lemma KinT{A B:Tab S}{X:Support c}(h:Kind S A B X)(i:Edge (Site f))(p:S.ratio.parent i.1∈X):i∈ A.1.trunks ↔ i∈ B.1.trunks:=by
 have hh{A B:Tab S}(t: Kind S A B X)(v:i∈ A.1.trunks):i∈ B.1.trunks:=by
    obtain ⟨j,h,v⟩:=(A.1.trunk_mem_iff _).mp v
    have hz : S.ratio.parent i.1= S.ratio.parent j:=by
       rw [←v]; let e:= A.1.up j; have hx:= A.1.stays j h; unfold Step.used; split
       next p=> 
          have he : (j - Lattice.step (A.1.up j).dir)= j+(A.1.up j).vec:=by simp [Step.vec,p,sub_eq_add_neg]
          rw [he]; exact hx -- tune
       rfl
    exact (B.1.trunk_mem_iff _).mpr ⟨j,h,(t.up j (hz ▸ p)) ▸ v⟩
 exact ⟨hh h,hh ⟨fun i p=>(h.up i p).symm,fun i p=>(h.ht i p).symm,fun i p=>(h.site i p).symm,fun i p=>(h.edge i p).symm⟩⟩
lemma sprayT{A B:Tab S}{X Y Z:Support c}(h:∀ i∈X,(i∈Y↔ i∈Z)): Kind S (unite S Y A B) (unite S Z A B) X:= by
 refine ⟨fun i p=>?_ ,fun i p=>?_,fun i p=>?_,fun i p=>?_⟩ <;> simp only [unite,token,h _ p]
lemma differT {A B:Tab S}{X Y:Support c} (h:Kind S A B X) (Z: Tab S): Kind S (unite S Y A Z) (unite S Y B Z) X:=by refine ⟨fun i p=>?_ ,fun i p=>?_,fun i p=>?_,fun i p=>?_⟩; exact congrArg (fun t=> if S.ratio.parent _∈Y then t else Z.1.up i) (h.up _ p); exact congrArg (fun t=> if S.ratio.parent _∈Y then t else Z.1.height i) (h.ht _ p); exact congrArg (fun t=> if i∈Y then t else Z.2.1 i) (h.site _ p); exact congrArg (fun t=> if i.1∈Y then t else Z.2.2 i) (h.edge _ p)
end
end YM.CF.Arena
