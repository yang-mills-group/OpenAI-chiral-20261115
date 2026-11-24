import YM.CF.Levier.Crete
set_option maxHeartbeats 350000
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 20000
set_option linter.unusedVariables false
noncomputable section
namespace YM.CF.Levier
open Function Filter Metric NormedSpace Finset Fock Lattice Wilson Laurent Lat Rush SU Drapes Fir Peaks Dial Paige Brace Vault Tulip Tenant Phase Broc Matrix Scroll Thera Branch Laic Cube
open scoped Matrix.Norms.L2Operator Matrix Topology ContDiff MatrixOrder BigOperators InnerProductSpace Kronecker
attribute [local instance] opCStarAlgebra
open Spire Nacre
-- analytic profiles under affine pullback incl sail seams
variable {N:Side}(b:Bool)(a:Shape)
open Urn
variable {P: Side}(G:Ratio N P)(h: Odd G.count.val)(e:ℝ)(k:Sweep N)(q:Shape)
local notation "κ"=> (Iota G)
-- dual locally evaluate on conjugated ambient
variable {C:Seal (Site (More P))→Toll (Iota G)}{d p r:ℝ}{v t:Bool}
open Proa Hake Pastry
abbrev TailB:= Bool×Bool
abbrev liftA(i:TailB)(p:Bool):TailB:=(i.1,i.2.xor p)
variable {α:Type*}{j:ℕ}(S:α→Male)(K:WG α)(c:α)
-- tag true formal; charge second
abbrev mineB (i:TailB): Raw (cro G e) (Iota G):=fun x=> Ash G h j K S c (!i.2) i.1 x.val
abbrev mineC(i:Grave): Raw (cro G e) (Iota G):=fun x=> ember G h j K S c (!(carL i)) (!(beltG i)) i.1 i.2.1 (carL i) (!(beltG i)) x.val
abbrev Radix(K:TailB → Op (Iota G)):Ax (Iota G) (Single N):=fun u r=> marge G (K (u,r))
variable (U:Nom N P)(X: Bkg (More P))(x:cro G e)(yn:x.val=(unionP U,profile X))
include yn
lemma prime_A (i:Urn.Twig (Iota G))(z:LeanV (Single N)): let W:=sprigZ G j S c X; let A:=prism G.count h j K S c G (unionP U); let V:=wh j G.count h true (S c) G (unionP U); let B:= ticketT (Thread j) true (S c) G (unionP U); let P:= ticketT (Thread j) false (S c) G (unionP U); mount (Radix G fun i=> mineB G h e (j:=j) S K c i x) i z=if z.1=(twigS i).1 then enC W V A B P i (patchQ G z.2) else 0:=by
 intro W A V B P; unfold mount; dsimp only; split; swap; rfl
 rw [show enC _ _ _ _ _ _ _= _ from soot G h j K S c U X i z.2]; unfold mineB; rw [yn]; -- tune
 generalize ht:tallC i=g; generalize hz:twigS i=x'; rcases x' with ⟨p,y⟩; change cSignX p _= _; have hu: W.seek i= !p:=by unfold W sprigZ; change (!(twigS i).1)= !p; rw [hz]
 rw [hu]; cases p<;>rfl
lemma prime_F : let W:=sprigZ G j S c X; let A:=prism G.count h j K S c G (unionP U); let V:=wh j G.count h true (S c) G (unionP U); let B:=ticketT (Thread j) true (S c) G (unionP U); let P:= ticketT (Thread j) false (S c) G (unionP U); Urn.soar (oakN G fun i=>mineC G h e (j:=j) S K c i x) = fuelC W V A B P:=by
 intro W A V B T; funext i v; rw [show fuelC _ _ _ _ _ _ _= _ from fireT G h j K S c U X i v]; unfold Urn.soar oakN mineC; rw [yn]; let I:= twigS i; let J:= twigS v; let a:=I.1; let b:=J.1; change (if a=b then _ else cSignX a _)=(if (!a)=(!b) then _ else if (!a) then _ else _); -- dependent tune
 cases p:a <;>cases q:b <;> simp only [cSignX,Bool.not_true,Bool.not_false,Bool.false_eq_true,ite_true,ite_false,carL,beltG,Bool.true_eq_false, Bool.not_not]; -- rewrite lemmas
lemma enKind (J:IsStarProjection (foot G (funde j (S c) P (profile X))))(A:Along j G.count h (Thread j) true (S c) G (unionP U))(f:IsUnit (1+nuke G.count h j K S c G (unionP U))) : KindX (Urn.soar (oakN G fun i=> mineC G h e (j:=j) S K c i x)):=by
 let W:=sprigZ G j S c X; let V:=prism G.count h j K S c G (unionP U)
 have ht:=court _ _ _ _ _ true _ A; have he: V*V=0:=(thrust_tag ht (tag_g (foot G _) A.lead) f).nil; rw [prime_F G h e S K c U X x yn]; constructor <;> intro i j' <;> apply melody W _ _ _ _ ht.helm he ht.rain -- tune
 · unfold W sprigZ; rw [stickUp,stickUp,rind _ J,zero_smul]
 unfold W sprigZ; rw [stickLo,stickLo,orchestra]; split_ifs<;>simp
end YM.CF.Levier
