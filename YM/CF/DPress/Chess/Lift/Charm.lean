import YM.CF.DPress.Chess.Lift.Tone
set_option autoImplicit false
set_option linter.unusedVariables false
noncomputable section
namespace YM.CF.DPress.Chess.Lift
open Function Filter Finset Lattice Rush Scroll Tulip Lat Peaks Cube Dial SU Branch Wilson Fock Fixed NormedSpace Spire Scree Skye Tap Reed Print
open scoped Topology BigOperators NNReal ENNReal Kronecker Classical Matrix.Norms.L2Operator InnerProductSpace
attribute [local instance] opCStarAlgebra
variable {n m L:Side}(G:Ratio n m)(M: Male)(j:ℕ){o: Odd L.val}(Q:Op Slot)
variable (w:Shape)(x:UNI SpinIdx)(p:JetS w.s false true x)
local notation "W"=>ψθ w x n
include p
lemma dawnH {X:Ket (Single n)}(v: Upper (tickA n) X):Lower (tickA n) (acts (ψθ w x n).val X):=by
 let T:=ψθ w x n; let i:= cutM (upperIndices n); have h : acts i X=X:= (by unfold i; rw [←Fixed.tickA_upper]; exact v); have ht:= act_cost T _ _ (Print.τ_p (n:=n) w x p) X; unfold Lower; rw [Fixed.tickA_upper]; change acts i _=_; change _=_ at ht; rw [show acts (cutM _) _=X from h,act_sub,act_one] at ht; exact (sub_eq_self.mp ht.symm) -- name
lemma duskH {X:Ket (Single n)}(v: Lower (tickA n) X):Upper (tickA n) (acts (ψθ w x n).val X):=by
 let T:=ψθ w x n; let i:= cutM (upperIndices n); have h : acts i X=0:= (by unfold i; rw [←Fixed.tickA_upper]; exact v); have ht:= act_cost T _ _ (Print.τ_p (n:=n) w x p) X; unfold Upper; rw [Fixed.tickA_upper]; change acts i _=_; rw [show acts (cutM _) _=0 from h,act_sub,act_one,map_zero] at ht; exact Eq.symm (sub_eq_zero.mp ht.symm)
omit p
lemma hostP {S:CoverS n}{X:Ket (Single n)}(p:Upper (tickA n) X)(t:nodeS S X): RefineE S true (create X):=by
 rw [create_def]; apply Fine.sumF; intro i h; by_cases e:X.ofLp i=0; rw [e,zero_smul]; apply Fine.empty
 have hg:i∈Fixed.matterRegion n S:=by by_contra z; apply e; rw [←t,cut_apply,if_neg z]
 rw [Fixed.tickA_upper] at p; refine (Print.put_p hg ?_).scale _; by_contra z; apply e; rw [←p,cut_apply,if_neg z]
lemma hostT {S:CoverS n}{X:Ket (Single n)}(p:Lower (tickA n) X)(t:nodeS S X):RefineE S true (remove X):=by
 rw [remove_def]; apply Fine.sumF; intro i h; by_cases e:X.ofLp i=0; rw [e,star_zero,zero_smul]; exact Fine.empty _
 have hg:i∈Fixed.matterRegion n S:=by by_contra z; apply e; rw [←t,cut_apply,if_neg z]
 rw [Fixed.tickA_upper] at p; refine Fine.scale (Print.take_p hg ?_) _; intro z; apply e; rw [←show (acts (cutM _) X).ofLp i=X.ofLp i from (cut_apply ..).trans (if_pos z),p]; rfl
variable {r:ℕ}{S:CoverS n}{b:Bool}(v:Odd G.count.val)(pT:∀ i:Male,Symbol.Stroke G (pulse G j i) r)(q:star Q= Q)
include v pT q
local notation "η'"=> spreadB G S r
lemma rise_P (i:Ket (Single n))(e:nodeS S i)(t:Upper (tickA n) i): PrintU G M j Q (spreadB G S r) true (create i) (fun X=>create (byrise G j M X Q i)) :=⟨create_cont.comp (shineC G (show Continuous _ from (pT M).ω) _),fun x y p=> congrArg create (pay_x G pT (crestQ Q e|>.1) p),fun x=>hostP (rise_g G v j M x Q t) (phr G pT (crestQ Q e|>.1)), fun x L o t' u=>bring_up G v j M x Q t' i t u, fun X v' Z h L o t' =>by rw [theta_upV,theta_upV,flyH G v]; exact rise.color _ (fun x=> bring_down G v j M (stanza G v' inert X) Q q _ (dawnH v' Z h t) x); exact h ⟩ -- tune `let` parse
lemma fall_P (i:Ket (Single n))(e:nodeS S i)(t:Lower (tickA n) i): PrintU G M j Q (spreadB G S r) true (remove i) (fun X=>remove (bydrop G j M X Q i)):=by
 have hh{I: Type}[LinearOrder I][Fintype I]:Continuous (@remove I _ _) := continuous_star.comp create_cont; refine ⟨hh.comp (shineC G (pT M).ω _),fun x y p=> congrArg _ (pay_x G pT (crestQ Q e|>.2) p),fun x=>hostT (drop_g G v j M x Q t) (phr G pT (crestQ Q e|>.2)), fun x L o t' u=>bring_down G v j M x Q q i t u, fun X v' Z w L o h => ?_⟩
 rw [theta_downV,theta_downV,flyB G v]; exact rise.color _ (fun l=>bring_up G v j M _ Q h _ (duskH v' Z w t) l); exact w
lemma shipB (A:ReOp n)(p:RefineE S b A) :∃ X,PrintU G M j Q (spreadB G S r) b A X:=by
 unfold RefineE at p; induction p with
 | empty=> exact ⟨_,PrintU.zero⟩
 | one=> exact ⟨_,PrintU.one⟩
 | add _ _ a b=> obtain ⟨y,k⟩:=a; obtain ⟨z,l⟩:=b; exact ⟨_,k.add l⟩
 | scale _ c a=> obtain ⟨y,k⟩:=a; exact ⟨_,k.color c⟩
 | grow _ _ a b=> obtain ⟨y,k⟩:=a; obtain ⟨z,l⟩:=b; exact ⟨_,k.mul l⟩
 | seed i y=>
    have hp : nodeS S (basisKet i):=(cut_basis ..).trans (if_pos y); by_cases h:i∈ Fixed.upperIndices n; swap
    · rw [show (think _).term i=(-1:ℂ) • remove (basisKet i) from ?_]; refine ⟨_,(fall_P G M j Q v pT q (basisKet i) hp ?_).color (-1)⟩; unfold Lower; rw [Fixed.tickA_upper,cut_basis,if_neg h]
      rw [show (think (upperIndices n)).term i= -takeF i from if_neg h, remove,create_put]; simp [takeF]
    rw [show (think _).term i=create (basisKet i) from ((show (think _).term i=put i from if_pos h).trans (create_put _).symm)]; refine ⟨_,rise_P G M j Q v pT q (basisKet i) hp ?_⟩; unfold Upper; rw [Fixed.tickA_upper,cut_basis,if_pos h]
end YM.CF.DPress.Chess.Lift
