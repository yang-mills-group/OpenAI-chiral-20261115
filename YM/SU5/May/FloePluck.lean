import YM.CF.Emu.Fez
set_option autoImplicit false
set_option maxHeartbeats 450000
set_option synthInstance.maxSize 30000
set_option maxRecDepth 3000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.May.Arctic
open Function Filter Finset Fock Emu
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators ComplexOrder InnerProductSpace
attribute [local instance] opCStarAlgebra
variable {α n:Type*} [LinearOrder n][Fintype n]
-- PRESERVE ordered Wick words, no requirement cash on arrangements asked outside the panel order
private lemma picked_out (l:List α)(k:Bout α)(g:k∈picks l): (∀ i∈ k.back, i∈l) ∧ k.front∈l:=by
 induction l generalizing k with
 | nil=> simp [picks] at g
 | cons i l ih=>
   rw [picks,List.mem_cons] at g; rcases g with rfl|g
   · exact ⟨fun i v=> by simp [show i∈l from v],by simp⟩ -- front simp
   obtain ⟨z,u,rfl⟩:=List.mem_map.mp g; obtain ⟨v,w⟩:=ih z u; refine ⟨fun k g=> ?_,List.mem_cons_of_mem i w⟩
   exact List.mem_cons.mpr ((List.mem_cons.mp g).imp_right (v _))
private lemma kept(s:List α)(d:α→α→Prop)(u:s.Pairwise d) (x:Cl α)(p:x∈claps s): (∀ i∈x.term,i∈s) ∧ ∀ a∈x.up,d a.1 a.2 := by
 induction s generalizing x with
 | nil=> simp [claps] at p; subst x; simp
 | cons i l ih=>
    obtain ⟨c,h,h'⟩:=List.mem_flatMap.mp p; obtain ⟨e,f⟩:=ih ((List.pairwise_cons.mp u).2) c h; rw [besideX,List.mem_cons] at h'; rcases h' with rfl|h'
    · exact ⟨fun z p=>List.mem_cons.mpr ((List.mem_cons.mp p).imp_right (e _)), f⟩
    obtain ⟨k,w,rfl⟩:=List.mem_map.mp h'; obtain ⟨g,G⟩:=picked_out _ _ w; refine ⟨fun v h=>List.mem_cons_of_mem i (e _ (g _ h)),fun a w=>?_ ⟩
    rcases List.mem_cons.mp w with e'|e'; rw [e']; exact (List.pairwise_cons.mp u).1 _ (e _ G); exact f a e'
lemma runners (s:List α)(c d:α→α→ℂ)(p:s.Pairwise fun i j=> c i j=d i j): runes c s=runes d s:=by
 unfold runes; have hu(x:Cl α)(p':x∈claps s): spinC c x=spinC d x:=by
    unfold spinC; split; swap; exact rfl
    unfold offer; let F (y: α × α):=c y.1 y.2; let G (y:α × α):=d y.1 y.2; exact congrArg (fun y:List ℂ=>cval x.cpos*y.prod) (List.map_congr_left (f:=F) (g:=G) fun i h=>(kept s _ p x p').2 i h)
 exact congrArg List.sum (List.map_congr_left hu)
-- normalized cash: fake CARs enforce ordering on s for now no orientation reference
lemma java (c:α→α→ℂ)(S A B:α→FC n)(f:∀ i,S i=B i+A i)(p:∀ i, acts (A i) (vacuum n)=0)(h:∀ i,acts (star (B i)) (vacuum n)=0)(g:∀ i j,antiB (A i) (B j)=c i j•1) (l:List α) : inner ℂ (vacuum n) (acts (rollC S l) (vacuum n))=runes c l:=by
 let x:=vacuum n; have hw(i:Cl α): inner ℂ x (Fock.invest B x c i)=spinC c i:= by unfold invest spinC; cases k:i.term with|nil=> rw [emptyChime,inner_smul_right]; simp [x,vacuum]|cons y z=> rw [charm,inner_smul_right,←act_inner, h]; simp
 change inner ℂ x (chime S x l)=_; rw [shadeW S B A x c p g f]; unfold runes; generalize claps l=M; induction M with| nil=> simp|cons i w ih=> simp only [List.map_cons,List.sum_cons,inner_add_right, hw]; rw [ih]
private abbrev _no_use : (Unit→Prop):= fun _=>True
end YM.CF.May.Arctic
#print axioms YM.CF.May.Arctic.java
#print axioms YM.CF.May.Arctic.runners
