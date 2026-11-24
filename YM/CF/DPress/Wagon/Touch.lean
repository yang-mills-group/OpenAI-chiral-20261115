import YM.CF.DPress.Wagon.Steam
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
namespace YM.CF.DPress.Wagon
open Function Filter Lattice RG Wilson MeasureTheory Skye Rush Spire Scree Tulip
open Fock Finset Scroll SU Lat Cube Phase Branch BPress Chess
open scoped Topology BigOperators Pointwise Classical ENNReal NNReal ComplexOrder Matrix.Norms.L2Operator Kronecker YM.CF.BPress
attribute [local instance] opCStarAlgebra
variable {n L:Side}
namespace Race
structure Bound (T:Race n L)(F:Fixed.Test n→ ℝ):Prop where
 light (x):0 ≤ F x
 cap(c:ℝ):∃ v:ℝ,∀ U:Fixed.Test n,(∀ i,‖U i‖ ≤ c)→Measurable U→ F U≤ v
 cross(w:ℤ) (U V:Fixed.Test n): let Z:=T.wall w; let S:= Z.crop _ T.grip; Boss n S U→Boss n S V→ F (peer Z U * V)^2 ≤ F (peer Z U*U)* F (peer Z V*V)
variable {T:Race n L}(A:Style T){a:ℤ}
open Credit
-- recall `s` lies immediately to negative half and `t` in positive. choose seam W. moves full output. apply at shifted seam any.
lemma duplicate {ℒ:Fixed.Test n→ℝ} (p:Bound T ℒ) {X:Fixed.Test n}(c:Bool){s t:List Bool}(u:Credit A a c (s++t) X)(v:s.length=t.length)(q:s.length*A.w+t.length*A.w=T.η):∃ P Q, Credit A a c (s++s.reverse) P ∧ Credit A a c (t.reverse++t) Q ∧ (ℒ X)^2≤ ℒ P*ℒ Q:=by
 obtain ⟨Y,Z,h,k,rfl⟩:= splitC u; let L':= s.length*A.w; let m:= blockP A a s; let i:=turned s.length c; let V:=T.wall m; have hz:T.η=L'+L':=by rw [← v] at q; exact q.symm
 have ht:m=a+(L':ℤ):=rfl; have hp:blockP A (blockP A a s) t=m+ (L':ℤ):=by unfold blockP; rw [←v]
 let P:=peer V Y; let Q:=peer V Z; have he:Credit A m i s.reverse P:= (Eq.mp (congrArg (fun i':ℤ=> Credit A i' i s.reverse P) (show retro m m=m from (by unfold retro; omega))) (reverse_P m h (by rw [hz]; change m ≤ _; omega))); have hg:Credit A a c t.reverse Q:=by
    have hv:= reverse_P m k (by rw [hp,hz]; change _ ≤ m+_; omega); rw [hp,show retro m (m+L')=a from (by unfold retro; omega),←v,turn₂] at hv; exact hv
 have hh:a+(T.η:ℤ)≥ m+L':=by rw [hz]; omega
 have f:blockP A m s.reverse=m+(L':ℤ):=by unfold blockP; rw [List.length_reverse]
 have g:blockP A a t.reverse=m:=by unfold blockP; rw [List.length_reverse,←v]
 have uP:= T.crop_t (i:=L') hz.symm m; refine ⟨_,_,h.companion he,hg.companion ((by rw [g, List.length_reverse, ←v]; exact k)),?_⟩
 let F:=ℒ; have e':peer V P=Y:= truly_ V h.tag; have w:=p.cross m P Z (by rw [uP]; exact ⟨_,f ▸ he.tag⟩) (by rw [uP]; exact ⟨_,hp ▸ k.tag⟩); change (F (peer V P*Z))^2 ≤ F (peer V P*P)* F (Q*Z) at w; rw [e'] at w; exact w -- tune implicit glue.CS order witness
end Race
end YM.CF.DPress.Wagon
