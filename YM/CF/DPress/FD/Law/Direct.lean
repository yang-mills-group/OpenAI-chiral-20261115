import YM.CF.DPress.FD.Law.Vision
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.DPress.FD
open Function Filter Lattice Finset Cash
open scoped Topology BigOperators ENNReal NNReal Classical
namespace Cycle
variable {n:Side}{r:ℕ}(S W:Equiv.Perm (Site n))(h:∀ i,S i≠i)(u:∀ i,separation i (S i)≤r)
abbrev screen(U:Support n):Setoid (Skin (Site n)) := ruleFx (fun x:Skin (Site n)=>fun i:↥U=> x i.val)
lemma look (S:Support n) (x y:Skin (Site n)): (screen S).r x y↔∀ i∈ S,x i=y i:=by change (fun i:↥S=> x i.val)=(fun i:↥S=> y i.val) ↔ _; exact ⟨fun p i h=>congrFun p ⟨i,h⟩,fun p=>funext fun i=>p i.val i.property⟩
abbrev wealth(h:∀ i,S i≠i): Cash (Skin (Site n)):=⟨Cycle.mass S,fun i=> Cycle.positive S,Cycle.unit S h⟩
include u h
local notation "cube"=> Site n
abbrev capP(U:Support n)(x:Skin (Site n))(i:Site n):= if i∈U then ({x i}:Finset C) else univ
private lemma mapLife (U V : Support n) (f:DPress.FD.Far r U V):Pair (wealth S h) (screen U) (screen V):=by
 intro x y; let P:=capP U x; let Q:=capP V y; let T:= wealth S h
 have he (i:cube)(U:Support n)(x:Skin cube)(b:C)(g:i∉U): capP U x i=univ:=by unfold capP; rw [if_neg g]
 have hv: ∀ i,EmptyP P i ∨EmptyP Q i:= fun i=> by by_cases g:i∈U; swap; exact Or.inl (he i U x 0 g); exact Or.inr (he i V y 0 (fun p=>by have he:= f i g i p; rw [separation_self] at he; omega))
 have hg(i:cube):(EmptyP P i ∨ EmptyP Q (S i))∧(EmptyP Q i∨ EmptyP P (S i)):=by
    constructor; · by_cases p:i∈U; swap; exact Or.inl (he i U x 0 p); exact Or.inr (he _ V y 0 fun q=> (not_lt_of_ge (u i)) (f i p (S i) q))
    by_cases p:i∈V; swap; exact Or.inl (he i V y 0 p); exact Or.inr (he _ U x 0 fun q=> not_lt_of_ge ((separation_comm ..).trans_le (u i)) (f _ q i p))
 have hy:= merit_F S h P Q hv hg
 have hk (U:Support n)(x z:Skin cube) : (screen U).r z x↔ ∀ i,z i∈ capP U x i:=by
    simp only [look,capP]; constructor; · intro h i; split; exact mem_singleton.mpr (h i (by assumption)); exact mem_univ _
    intro h i t; have hi:=h i; rw [if_pos t] at hi; exact mem_singleton.mp hi
 rw [tape (wealth S h) (P:=fun z=>(screen U).r z x∧(screen V).r z y) (Q:=fun z=>∀ i,z i∈ joint P Q i) (fun z=> by rw [hk U x,hk V y]; simp only [joint,mem_inter,forall_and,P,Q]), tape (wealth S h) (P:=fun z=>(screen U).r z x) (hk U x),tape (wealth S h) (P:=fun z=>(screen V).r z y) (hk V y)]; -- bridge DecidablePred
 convert hy using 2
 · ext; simp only [mem_filter,mem_univ,true_and]
 all_goals (apply sum_congr ?_ (fun i _=>rfl); ext; simp [P,Q])
-- cost API
abbrev Lens: Vision n r (Skin (Site n)):=⟨wealth S h,screen,mapLife S h u,fun V U p x y g=>(look V x y).2 fun i t=> (look U x y).1 g i (p t)⟩
end Cycle
end YM.CF.DPress.FD
