import YM.CF.Emu.Bolt
set_option autoImplicit false
noncomputable section
namespace YM.CF.Emu
open YM.CF.Onyx
open Function Filter Metric Fir Lattice Laurent Next.Free Bloch Finset Lat Ember Jill Kea Flare Rush Tulip Cube Fock SU Dial Thera
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix Matrix.Norms.L2Operator Kronecker
attribute [local instance] opCStarAlgebra
open YM.Stationary (Gaia)
section wick
variable {n α:Type*}[LinearOrder n][Fintype n]
def spinC(G:α→α→ℂ)(W:Cl α):ℂ:= if W.term.isEmpty then offer G W else 0
def runes(G:α→α→ℂ)(L:List α):ℂ:= ((claps L).map (spinC G)).sum
def eyeC(L:Op n)(i:Reader0 n):FC n:= creed i.1 ((acts (if i.1 then star L else -L)) i.2)
def rankG(L:Op n)(j k: Reader0 n):ℂ:= if j.1=k.1 then 0 else if j.1 then -(inner ℂ j.2 (acts L k.2)) else inner ℂ k.2 (acts L j.2)
lemma wing_h(L:Op n)(i:Reader0 n):iceT L i=eyeC L i+ton i:=by unfold iceT eyeC ton; split_ifs with h; rw [act_add,act_one,creed_a,add_comm]; rw [act_sub,act_neg, act_one,sub_eq_add_neg,creed_a,add_comm]
lemma hall(L:Op n)(i j:Reader0 n): antiB (ton i) (eyeC L j)=rankG L i j • 1:=by
 obtain ⟨i,v⟩:=i; obtain ⟨j,w⟩:=j; unfold ton eyeC rankG; cases i<;> cases j
 · change antiB (create v) (create _)=(0:ℂ) • _; rw [antiB,car_create,zero_smul]
 · change antiB (create v) (remove _)=(inner ℂ w _) • _; rw [antiB_comm]; unfold antiB; rw [car]; congr 1; exact act_inner L w v
 · change antiB (remove v) (create ((acts (-L)) w))=(-inner ℂ v (acts L w)) • _; rw [antiB, car,act_neg,inner_neg_right]
 change antiB (remove v) (remove _)=(0:ℂ) • _; rw [car_rem,zero_smul]
variable {Q P T V K:Op n}(g:Clad P Q T V K){p q:Wave n}
def KeyT(i:Reader0 n)(Q:Op n):Prop:= acts Q i.2= if i.1 then 0 else i.2
include g in
lemma vase (h:Sea Q q)(Z:α→ Reader0 n)(w:∀ i,KeyT (Z i) Q)(L:List α): inner ℂ q (chime (iceT (laneP Q T K) ∘ Z) q L)=runes (fun i j=>rankG (laneP Q T K) (Z i) (Z j)) L:=by
 let F:=laneP Q T K; let A:=eyeC F ∘ Z
 let B:=ton ∘ Z; let d(i j:α):=rankG F (Z i) (Z j)
 have ht(i):acts (B i) q=0:=by
    have ht:= w i; generalize hy:Z i=x; change acts (ton (Z i)) _=_; rw [hy]; rw [hy] at ht; rcases x with ⟨f,u⟩; cases f; exact tarp g.helm h.1 ht; exact tars g.helm h.1 ht
 have hv(i):acts (star (A i)) q=0:=by
    have ht:=w i; generalize hx: Z i=y; change acts (star (eyeC F (Z i))) q=_; rw [hx]; rcases y with ⟨f,u⟩; cases f
    · change acts (remove (acts (-F) u)) q=_; exact tars g.helm h.1 (by rw [←act_mul,mul_neg,g.bare,neg_zero,act_zero])
    change acts (star (remove (acts (star F) u))) q=0; rw [show star (remove (acts (star F) u))=create (acts (star F) u) from star_star _]; refine tarp g.helm h.1 ?_; rw [←act_mul,show Q*star F=star F from ?_]; nth_rw 1 [←g.helm.isSelfAdjoint]; rw [←star_mul,g.chest]
 have hj(x:Cl α): inner ℂ q (invest A q d x)=spinC d x:=by
    unfold invest spinC; cases hm:x.term
    · rw [emptyChime,inner_smul_right,inner_self_eq_norm_sq_to_K, h.2]; simp
    rw [charm,inner_smul_right,←act_inner, hv,inner_zero_left]; simp
 rw [shadeW (iceT _ ∘ Z) A B q d ht (fun i j=> hall ..) (fun i=> wing_h F (Z i))]; unfold runes; change inner ℂ q (((claps L).map _).sum)= ((claps L).map (spinC d)).sum; generalize claps L=W; induction W with| nil=> simp| cons a b ih=> simp only [List.map_cons,List.sum_cons,inner_add_right,hj]; rw [ih]
def pRead (p q:Wave n)(Z:α→Reader0 n)(X:FC n)(L:List α):ℂ:= inner ℂ q (acts (rollC (ton∘Z) L*X) p)
include g in
lemma frown(h:Sea Q q)(l:Sea P p)(Z:α→ Reader0 n)(w:∀ i,KeyT (Z i) Q)(L:List α):pRead p q Z (quant T) L= skyGlow q T p * runes (fun i j=> rankG (laneP Q T K) (Z i) (Z j)) L:=by
 unfold pRead; rw [show rollC (ton∘Z) L=rollC ton (L.map Z) from (by simp [rollC]), read0 g p q l h]; congr 1; rw [show rollC _ (List.map Z L)=_ from (show rollC (iceT _) (L.map Z)=rollC (iceT (laneP Q T K) ∘ Z) L from (by simp [rollC]))]; exact vase g h Z w L -- tune
lemma offer_v(G:α→α→ℂ)(F:ℕ→α→α→ℂ)(h:∀ i j,Tendsto (fun m=>F m i j) atTop (𝓝 (G i j)))(L: List α): Tendsto (fun m=>runes (F m) L) atTop (𝓝 (runes G L)):=by
 have he(W: List (α × α)):Tendsto (fun i=> (W.map fun v=> F i v.1 v.2).prod) atTop (𝓝 ((W.map fun v=> G v.1 v.2).prod)):=by
   induction W with| nil=> exact tendsto_const_nhds| cons i t ih=> exact (h i.1 i.2).mul ih
 have hp(W:Cl α) : Tendsto (fun i=>spinC (F i) W) atTop (𝓝 (spinC G W)):=by
   unfold spinC; split_ifs; exact (he _).const_mul _; exact tendsto_const_nhds -- tune
 unfold runes; generalize claps L=W; induction W with| nil=>exact tendsto_const_nhds| cons a l ih=> exact (hp a).add ih
end wick
end YM.CF.Emu
