import YM.CF.Urn.Smelt
set_option autoImplicit false
set_option synthInstance.maxSize 20000
set_option linter.unusedVariables false
noncomputable section
namespace YM.CF.Urn
open Function Filter Metric NormedSpace Finset Fock Lattice Wilson Laurent Lat Rush SU Drapes Fir Peaks Dial Paige Brace Vault Tulip Tenant Phase Broc Matrix Scroll Thera Branch Laic Cube
open scoped Matrix.Norms.L2Operator Matrix Topology ContDiff MatrixOrder BigOperators InnerProductSpace Kronecker
attribute [local instance] opCStarAlgebra
open Proa
variable {P N L:Side}(G:Ratio N P)(h:Odd L.val)(j:ℕ){α:Type*}(K:WG α)(S:α→Male)(k:α)
abbrev vane (u b:Bool)(x:Coil N P × Chin P):= foot G (cope j u b (S k) P x.2)
abbrev smoke (u b:Bool)(x:Coil N P× Chin P):=foot G (icyS j u b S k P x.2)
def Ash (z b:Bool)(x:Coil N P×Chin P): Op (Iota G):= smoke G j S k z b x* Sky L h j K S z k G x.1
def ember (u v b t w z:Bool)(x:Coil N P× Chin P): Op (Iota G):= smoke G j S k u b x * meet j K S h u v w z k G x.1 * vane G j S k v t x
lemma smoke_r (u b:Bool)(y:Bkg (More P))(x: Coil N P): smoke G j S k u b (x,profile y)=star (vane G j S k u b (x,profile y)):= by unfold smoke vane icyS pale; dsimp only; rw [ice_pr,foot_s]
variable {P':Op (Iota G)}(x:Nom N P)(y:Bkg (More P))
abbrev sprigZ:=stick (foot G (funde j (S k) P (profile y)))
lemma mathS (i:Twig (Iota G)):let d:=sprigZ G j S k y; d.matrix i=vane G j S k (d.seek i) (tallC i) (unionP x,profile y):=by
 intro d; change (if tallC i then _ else _)= _; unfold vane; unfold cope; split
 · change Proa.sprig (d.seek i) (foot G _) = _; cases u:d.seek i; · change 1-foot G _=foot G (1-_); rw [foot_sub,foot_one]
   rfl
 · rw [foot_one]
lemma steam (i:Twig (Iota G))(J:Bool): let d:=sprigZ G j S k y; let M:=S k; let B:=wh j L h true M G (unionP x); let E:=prism L h j K S k G (unionP x); let W:=ticketT (Thread j) true M G (unionP x); let V:=ticketT (Thread j) false M G (unionP x)
 Proa.sprig J B * Proa.aqua d E W V i=startZ j K S h (d.seek i) J k G (unionP x)*vane G j S k (d.seek i) (tallC i) (unionP x,profile y):=by
 intro d M B E W V; rw [startZ, saved_P]; simp only [mul_one]; rw [mul_assoc]; unfold Proa.aqua; rw [show d.matrix i=_ from mathS G j S k x y i]
lemma soot (i:Twig (Iota G))(l :Single N):let d:=sprigZ G j S k y; let u:=d.seek i; let z:=(twigS i).2; let M:= S k; let H:=prism L h j K S k G (unionP x); let V:=ticketT (Thread j) true M G (unionP x); let W:=ticketT (Thread j) false M G (unionP x); let B:=wh j L h true M G (unionP x); let F:= Ash G h j K S k u (tallC i) (unionP x,profile y)
 enC d B H V W i (patchQ G l)=(if u then F z (patchQ G l) else star (F z (patchQ G l))):=by
 intro d u z M H V W B F; unfold enC Proa.main; rw [steam G h j K S k x y i u]
 have hh(j): treeF L h ‹ℕ› K S u (fun _ _ _ _ _=>1) k G (unionP x) j (patchQ G l) = (star (startZ _ K S h u u k G (unionP x))) j (patchQ G l):= tree_F .. -- tune shadow
 let X:=startZ j K S h u u k G (unionP x); let Y:=vane G j S k u (tallC i) (unionP x,profile y); have hp(z): F z (patchQ G l)= (star (X*Y)) z (patchQ G l):=by
    unfold F Ash; rw [smoke_r,star_mul,Matrix.mul_apply,Matrix.mul_apply]; exact sum_congr rfl fun t _=> congrArg _ (hh t)
 change (if u then star (X*Y) z _ else (X*Y) _ z)=_
 rw [hp]; split; rfl; exact (star_star _).symm
lemma fireT (i l:Twig (Iota G)):let d:=sprigZ G j S k y; let u:=d.seek i; let v:=d.seek l; let M:= S k; let H:=prism L h j K S k G (unionP x); let V:=ticketT (Thread j) true M G (unionP x); let W:=ticketT (Thread j) false M G (unionP x); let B:=wh j L h true M G (unionP x); let X:=(unionP x,profile y); let A:=ember G h j K S k u v (tallC i) (tallC l) (!u) v X;
 fuelC d B H V W i l= if u=v then 0 else if u then A (twigS i).2 (twigS l).2 else star (A (twigS i).2 (twigS l).2):=by
 intro d u v M H V W B X A; unfold fuelC; change (if u=v then 0 else if u then _ else _)=_
 let P:=Proa.dust d B H V W i; let Q:=Proa.main d B H V W l; have hp: star P*Q=A:=by unfold P Q A X ember Proa.dust Proa.main meet Spree; rw [steam G h j K S k x y i (!u),steam G h j K S k x y l v,smoke_r]; dsimp only; rw [revI]; unfold u v d; rw [star_mul]; simp only [mul_assoc]
 split; rfl; split; exact congrArg (fun A:Op (Iota G)=> A (d.sites i) (d.sites l)) hp
 rw [←hp]; change (star Q*P) (d.sites l) (d.sites i)= (star (star P* Q)) (d.sites l) (d.sites i); rw [star_mul,star_star]
end YM.CF.Urn
