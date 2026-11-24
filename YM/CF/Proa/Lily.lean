import YM.CF.Proa.Pylon
set_option autoImplicit false
noncomputable section
namespace YM.CF.Proa
open Function Filter Metric NormedSpace Finset Fock Lattice Wilson Laurent Lat Rush SU Drapes Fir Peaks Dial Paige Brace Vault Tulip Tenant Phase Broc Matrix Scroll Thera Branch Laic
open scoped Matrix.Norms.L2Operator Matrix Topology ContDiff MatrixOrder BigOperators InnerProductSpace Kronecker
attribute [local instance] opCStarAlgebra
variable {ι:Type*}{u v:Bool}{L:Side}{F:WG ι}
variable (L) (ho: Odd L.val)(j:ℕ) (hj:Even j)(hu:1≤j) (K:WG ι)(H:Lively K)(p:∀ i n,K i n 1=0)(S:ι→Male)(v:Bool)
-- φ matrices read jointly
abbrev coldY : Script ι:= fun i _ _ G x=> ticketT (Thread j) v (S i) G x
abbrev sees : Script ι:= fun i _ _ G x=>if v then star (1+prism L ho j K S i G (icec x)) * coldY j S false i G x else (1-prism L ho j K S i G x)*coldY j S true i G x
abbrev Fresco(w:Bool)(A:Script ι) : Script ι:= fun i _ _ G x=> sprig w (wh j L ho true (S i) G x) *(sees L ho j K S v i G x * A i G x)
abbrev treeF (A: Script ι): Script ι:=fun i _ _ G x=> star (Fresco L ho j K S v v @A i G (icec x)) * hood G
abbrev grass(v:Bool): Script ι:= fun i _ _ G x=> sprig v (foal j true (S i) G x)
include hj hu H p
lemma claim : Save L false true (sees L ho j K S v):=by
 let X:= transportS (cup j L ho hj hu (canUse j L ho) v).1 S
 let P:=prism L ho j K S; have hp:Save L false false @P:=(prism_s L ho j hj hu K H p S).2.2 -- tune
 cases v
 · exact ((Save.one ι).sub hp).mul (transportS (cup j L ho hj hu (canUse j L ho) true).1 S)
 exact (((Save.one _).plus hp).withOpp ..).mul (transportS (cup j L ho hj hu (canUse j L ho) false).1 S)
lemma valley(w:Bool)(A:Script ι)(k: Save L true true @A): Save L false true (Fresco L ho j K S v w @A):=by
 let P:= transportS (cup j L ho hj hu (canUse j L ho) true).2.2 S
 apply Save.mul _ ((claim L ho j hj hu K H p S v).mul k) -- tune
 cases w
 · exact (Save.one _).sub P
 exact P
lemma vitalC(A:Script ι)(k:Save L true true @A): Save L true false (treeF L ho j K S v @A):=((valley L ho j hj hu K H p S v v @A k).withOpp ..).mul (hood_tag L ho)
omit hj hu H p
variable {N Q:Side}(G:Ratio N Q)(X:Nom N Q)(k:ι)
lemma saved_P(w:Bool)(A:Script ι): Fresco L ho j K S v w @A k G (unionP X)=sprig w (wh j L ho true (S k) G (unionP X))* (liftJet v (prism L ho j K S k G (unionP X)) (coldY j S true k G (unionP X)) (coldY j S false k G (unionP X))* A k G (unionP X)):=by unfold Fresco sees; rw [revI]; cases v<;>rfl
lemma tree_F(A: Script ι)(i:Iota G)(l:Single N): treeF L ho j K S v @A k G (unionP X) i (patchQ G l) = (star (Fresco L ho j K S v v @A k G (unionP X))) i (patchQ G l) :=by rw [treeF,revI,lighthouse,cutM, mul_diagonal]; simp only [if_pos (coil_hit ..),mul_one]
include ho hj hu
lemma grass_S: Save L true true (grass j S v):=by
 let P:=transportS (cup j L ho hj hu (canUse j L ho) true).2.1 S; cases v; exact (Save.one _).sub P; exact P -- hj hu include
include p
lemma mab (T:∀ u,Along j L ho (Thread j) u (S k) G 1) : treeF L ho j K S v (grass j S v) k G 1=pine j L ho (Thread j) v (S k) G 1 * hood G:=by
 have hp:unionP (1:Nom N Q)=1:=by simp [unionP,profile_trivial]
 have he:icec (1:Coil N Q)=1:=by rw [←hp, revI]
 rw [treeF,he]; congr 1; unfold Fresco sees; rw [he,pris_z L ho j K p]
 let P:= foal j true (S k) G 1; let B:=wh j L ho true (S k) G 1; let W:=coldY j S true k G 1; let V:=coldY j S false k G 1; let U:=pine j L ho (Thread j) true (S k) G 1; let Y:=pine j L ho (Thread j) false (S k) G 1; let F:=laneP B W U
 have h:Clad P B W V U:= court G j L ho (Thread j) true (S k) (T _); have hu:= court G j L ho (Thread j) (!true) (S k) (T (!true)); rw [foil_neg,wh_neg,Bool.not_not] at hu
 cases v
 · change star ((1-B)* (((1-F)*W)*(1-P)))=Y; rw [←mul_assoc (1-B),←mul_assoc (1-B), h.sprint hu,star_star]; rfl
 change star (B * ((star (1+F)*V)*P))= U; rw [star_add,star_one, ←mul_assoc B, ←mul_assoc B, h.cave,star_star]
end YM.CF.Proa
