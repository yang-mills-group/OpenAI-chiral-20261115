import Compass.Sloop
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Compass
open Function Spire Scroll Pec
abbrev side01:=Equiv.swap (0:Axis) 1
abbrev side23:=Equiv.swap (2:Axis) 3
abbrev facing:Equiv.Perm Axis:=Equiv.swap 0 2 * Equiv.swap 1 3
lemma facing_anchor : Anchored (X facing):=by decide
lemma quad_anchor : Anchored (X side01):=by decide
lemma deep_anchor : Anchored (X side23):=by decide
lemma facing_det : detX (X facing)=false:=by rw [show X facing=X (Equiv.swap 0 2)* X (Equiv.swap 1 3) from rfl, det_p,detSwap _ _ (by decide),detSwap _ _ (by decide)]; rfl
-- perm classification by Anchor. $H=kernel(cost chambers)
def ticket (f:Bool)(g:Equiv.Perm Axis):Equiv.Perm Axis:=if f then g else 1
lemma lists (s:Signed)(h:Anchored s) : ∃ a b c:Bool,s.perm=ticket c facing * ticket a side01 * ticket b side23:=by
 let u:= s.perm 0; let v:=s.perm 1; let w:=s.perm 2; let x:=s.perm 3
 -- helper when h.1. enumerate images via 4 for last. injective.
 have t(i:Axis): i=0∨i=1∨i=2∨i=3:=by fin_cases i<;>decide
 have e:=h.duet
 -- reconstruct directly f arg solve via generated code. choose conjug by facing if swaps. $ classify permutations stabilizing 0 pair
 suffices helper : ∀ p:Equiv.Perm Axis,p 0=0→p 1=1→p=1∨p=side23 by
    have he (p:Equiv.Perm Axis)(t:(p 0=0∧p 1=1)∨(p 0=1∧p 1=0)):∃ a b:Bool, p=ticket a side01*ticket b side23:=by
      rcases t with ⟨i,j⟩|⟨i,j⟩
      · rcases helper p i j with g|g <;> subst p; exact ⟨false,false,(one_mul _).symm⟩; exact ⟨false,true,(one_mul _).symm⟩
      let q:= side01*p; have hx:q 0=0:= congrArg side01 i |>.trans (Equiv.swap_apply_right ..); have hv:q 1=1:=congrArg side01 j|>.trans (Equiv.swap_apply_left ..)
      refine helper q hx hv|>.elim (fun l=>⟨true,false,?_⟩) (fun l=>⟨true,true,?_⟩)
      all_goals change p= side01*_; rw [←show side01*q=p from (show side01*(side01*p)=p from ?_ ),l] <;> first|rfl|rw [←mul_assoc,show side01*side01=(1:Equiv.Perm Axis) by ext1 t; exact Equiv.swap_apply_self ..,one_mul]
    rcases e with l|l|l
    · obtain ⟨a,b,p⟩:=he _ (Or.inl l); exact ⟨a,b,false,p.trans (by rw [show ticket false facing=1 from rfl,one_mul])⟩
    · obtain ⟨a,b,p⟩:=he _ (Or.inr l); exact ⟨a,b,false,p.trans (by rw [show ticket false facing=1 from rfl,one_mul])⟩
    let q:= facing*s.perm; have hz:(q 0=0∧q 1=1)∨(q 0=1∧q 1=0):=by
      have hF:facing 2=0 ∧ facing 3=1:=by decide
      rcases l with ⟨p,r⟩|⟨p,r⟩; exact Or.inl ⟨(congrArg facing p).trans hF.1,(congrArg facing r).trans hF.2⟩; exact Or.inr ⟨(congrArg facing p).trans hF.2,(congrArg facing r).trans hF.1⟩
    obtain ⟨a,b,u⟩:=he q hz; refine ⟨a,b,true,?_⟩
    have ht:facing*q=s.perm:=by unfold q; rw [←mul_assoc,show facing*facing=(1:Equiv.Perm Axis) from by ext1 i; exact (show facing (facing i)=i from (((by decide) : ∀ i,facing (facing i)=i) i)),one_mul]
    exact ht.symm.trans ((congrArg (facing *·) u).trans (mul_assoc ..).symm)
 intro p a b
 have hi{i j:Axis}(u:i=2∨i=3)(v:j=0∨j=1):p i≠ j:=by
    have he:p j=j:=by rcases v with l|l <;>subst j; exact a; exact b
    rw [←he]; exact p.injective.ne (by rcases u with l|l <;> rcases v with h|h <;>rw [l,h] <;> decide)
 have hx(i:Axis)(h:i=2∨i=3): p i=2∨p i=3:=by rcases t (p i) with l|l|l|l; exfalso; exact hi h (Or.inl rfl) l; exfalso; exact hi h (Or.inr rfl) l; exact Or.inl l; exact Or.inr l
 have f:p 2≠p 3:=p.injective.ne (by decide)
 rcases hx 2 (Or.inl rfl) with v|v <;> rcases hx 3 (Or.inr rfl) with d|d
 all_goals first| (exfalso; exact f (v.trans d.symm))|skip
 · left; ext1 i; calc
                   p i = i := by rcases t i with l|l|l|l <;> subst i <;> assumption
                   _ = _ := rfl
 right; ext1 i; rcases t i with l|l|l|l <;> subst i <;> first|exact a|exact b|exact v|exact d
end YM.CF.Compass
