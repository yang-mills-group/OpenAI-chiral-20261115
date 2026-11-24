import YM.CF.BProof.Nerve.Pocket
/-! Use weighted Voronoi gaps instead of Delaunay lemma. This surrogate has
 dimension-4 *abstract simplices of barycentric weights*, used only in making
 the Basic maps. No eta' for other distances needed: can use any MinAbs tie lift beyond.
-/
set_option autoImplicit false
set_option linter.unusedVariables false
set_option synthInstance.maxSize 4096
set_option maxRecDepth 4800
set_option maxHeartbeats 780000
noncomputable section
namespace YM.CF.BProof.Mesh.Nerve
open Lattice Function Finset Equiv Regard Rows Sleet
open scoped BigOperators Classical
variable {n:Side}{C A:Type*}{s z l k R d:ℕ}
namespace Guard
variable (U : Field n A Prop) (g:Field n A (Fin z))
variable (s:ℕ)(u:ℕ)(F:Field n A ℝ)
open Policy
local notation "Hν"=> (King*s)
lemma lineL(a b:Support n)(x:Site n)(t:∀ i,separation x i ≤ Hν→ (i∈a↔ i∈b)) : Lines a s x=Lines b s x:=by
 ext y; rw [enters,enters]; apply and_congr_left; intro h; constructor; rintro ⟨g,p,q⟩; exact ⟨g, fun i=> (t _ (h ▸ (cost0 (s:=s) (Test.mk g p q) _ i))).1 (p i),q⟩; rintro ⟨g,p,q⟩; exact ⟨g, fun i=> (t _ (h ▸ (cost0 (s:=s) (Test.mk g p q) _ i))).2 (p i),q⟩
lemma jut_uses : Uses (Joint (Joint U g) F) (jut U g s u F) (King*s):=by
 intro x a b h; let X:=Joint (Joint U g) F; have ht(i)(p:separation x i≤Hν):X a i=X b i:= h (reg_in ..|>.2 p); have he{i}(p:separation x i≤ Hν):F a i=F b i:=congrArg Prod.snd (ht i p); unfold jut; rw [show g a x= _ from (show _=g b x from congrArg (Prod.snd ∘Prod.fst) (ht x (by simp))),he (by simp)]; suffices t: bump (z:=z) U s F a x u = bump U s F b x u by rw [t]
 unfold bump; congr 2; ext k; rw [lineL s (crowd U a) (crowd U b) x (fun i p=>by simp only [Sleet.crowd_in]; exact iff_of_eq (congrArg (Prod.fst ∘Prod.fst) (ht i p)))]; apply forall_congr'; intro i; refine imp_congr_right fun w=>?_ ; unfold due; obtain ⟨t,g⟩:=enters ..|>.1 w; rw [drift (i:=x) _ _ t g.symm]; intro y p; by_cases hg:y=x; rw [hg,Function.update_self,Function.update_self]; rw [update_of_ne hg,update_of_ne hg,he ((reg_in ..).1 p)] -- tune
lemma Test.travelU {a b:Support n}(r:Perm (Site n))(h:∀ i j,separation (r i) (r j)=separation i j)(g:∀ i,i∈ a↔ r i∈b) {X:Quint n}:Test a s X↔Test b s (r ∘ X):=by
 constructor
 · intro p; exact ⟨r.injective.comp p.spread,fun i=>(g ..).1 (p.crew i),fun i j=> (h ..).trans_le (p.cost ..)⟩
 intro p; exact ⟨fun i j h=> p.spread (congrArg r h), fun i=> (g ..).2 (p.crew i), fun i j=> (h ..).symm.trans_le (p.cost i j)⟩
lemma jut_l(t:SmallN s n) : Loyal (Joint (Joint U g) F) (jut U g s u F):=by
 intro r x E p w v; let e:=facet r x; have he(j):g (E w) j=g w (e j):=congrArg (Prod.snd∘Prod.fst) (p w j); have hv(j):F (E w) j=F w (e j):=congrArg Prod.snd (p w j); have h(j): U (E w) j=U w (e j):=congrArg (Prod.fst∘Prod.fst) (p w j)
 unfold jut; suffices py: bump (z:=z) U s F (E w) v u=bump U s F w (e v) u by rw [he,hv,py]
 unfold bump; congr 2; ext k; let A:=crowd U (E w); let B:=crowd U w; let Y(V:Quint n) := due z s u V (F w) (e v) k; let Z(V:Quint n):= due z s u V (F (E w)) v k
 have hm(V):Test A s V↔ Test B s (e∘V):=Test.travelU s e (facet_keeps r x) (fun i=>by simp [A,B,h]); have hg(V:Quint n)(p:Test A s V): Z V↔ Y (e ∘ V):=by
    unfold Y Z due; rw [equate t r x p]; suffices h:update (F w) (e v) (jot z u k) ∘ (e:Site n→Site n)= update (F (E w)) v (jot z u k) by rw [h] 
    ext j; by_cases g:j=v <;> simp [hv,g]
 have hh(V): V∈ Lines A s v↔(e ∘ V)∈ Lines B s (e v):=by
    rw [enters,enters]; constructor
    · rintro ⟨p,h⟩; exact ⟨(hm _).1 p,(twist t r x p).trans (congrArg e h)⟩
    rintro ⟨p,h⟩; let hl:= (hm V).2 p; exact ⟨hl,e.injective ((twist t r x hl).symm.trans h)⟩
 constructor
 · intro f V w; let P:=e.symm ∘ V; have he:e∘P=V:=funext fun i=>e.apply_symm_apply _; have hw:= (hh P).2 (he.symm ▸ w); exact he ▸ (hg P ((enters ..).1 hw).1).1 (f P hw)
 intro f V w; exact (hg V ((enters ..).1 w).1).2 (f (e ∘ V) ((hh V).1 w))
lemma wage_eq : Uses (Joint U g) (stageD U g s z) (z*(King*s)):=stage_uses _ _ _ _ (jut_uses U g s) z
lemma noble(t:SmallN s n) : Loyal (Joint U g) (stageD U g s z):=stageL _ _ _ (fun i y=> jut_l U g s i y t) z -- supply
end Guard
end YM.CF.BProof.Mesh.Nerve
