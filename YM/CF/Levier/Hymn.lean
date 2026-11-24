import YM.CF.Levier.Soup
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
variable {α:Type*}{j:ℕ}(S:α→Male)(K:WG α)(c:α)
def aura(x:Meter TailB G e):Prop:=∀ i k A u,toSpin G k (x i A u)= x (liftA i (accent k)) (toRoar G k⁻¹ A) (toWish G e k u)
variable (X:Meter TailB G e)(Z:Meter Grave G e)(x:cro G e)(V:Finset (Seal (Site (More P))))
abbrev LenT: Ax (Iota G) (Single N):= Radix G fun i=>∑ s∈V,X i s x
include h
lemma su_p (p:aura G e X): tendA k.charge (accent k) (pflux (castX k) G (spinU k.charge k.s) (xtra k.charge)) (siteU (castX k) k.charge (spinU k.charge k.s) N) (LenT G e X x V) (LenT G e X (toWish G e k x) (V.image (toRoar G k⁻¹))):=by
 intro u t; let i:TailB:=(u,t); unfold LenT Radix; dsimp only; rw [sum_image]; swap; · exact fun a _ b _ p=> (weaveS G k⁻¹).injective p
 simp_rw [show ∀ A: Seal (Site (More P)),_ = toSpin G k (X i A x) from fun A=> (show toSpin G k (X _ _ _)=X (u,t.xor _) _ _ from p i k A x).symm] -- tune
 rw [←toSpin_sum _ h]; exact marchT .. -- tune
omit h
variable (U:Nom N P)(u:Bkg (More P)) {m:ℝ}(w:x.val=(unionP U,profile u))
include w
local notation "P₀"=> pflux (castX k) G (spinU k.charge k.s) (xtra k.charge)
lemma wish_g: (toWish G e k x).val=(unionP (stanza G (castX k) (xtra k.charge) U), profile (stir (xtra k.charge) (Shape.broad G (castX k)) u)):=by
 unfold toWish wish; dsimp only; -- tune
 rw [w]; exact Prod.ext (Prod.ext (veil_p ..).symm (veil_p ..).symm) (veil_p ..).symm
variable (he:∀ y:Bkg (More N),Guard y m→PaidG j m y)(g:∀ y:Bkg (More P), Guard y m→PaidG j m y)(y:Guard u m)(f: JointB G U m)(o:1≤j)
local notation "F₁"=>xtra k.charge
local notation "s₀"=> castX k
local notation "U₀"=>spinU k.charge k.s
variable (H:∀ b (v:Nom N P),v=U ∨ v=stanza G (castX k) (xtra k.charge) U → Along j G.count h (Thread j) b (S c) G (unionP v))(J:IsUnit (Peaks.cloth j (S c) G (unionP U)))(v':K c P (profile (stir (xtra k.charge) (Shape.broad G (castX k)) U.1))=Thera.jazz (accent k) (sings k.charge (siteU (Shape.broad G (castX k)) k.charge (spinU k.charge k.s) P) (K c P (profile U.1)))) (l:IsUnit (1+nuke G.count h j K S c G (unionP U)))(hp:IsUnit (1+nukeR j K S h c G (unionP U)))
include h he g y f o H J v' l hp
lemma Vow (i:TailB)(t:Grave): toSpin G k (mineB G h e (j:=j) S K c i x)= mineB G h e (j:=j) S K c (liftA i (accent k)) (toWish G e k x) ∧ toSpin G k (mineC G h e (j:=j) S K c t x)=mineC G h e (j:=j) S K c (flingX t (accent k)) (toWish G e k x):=by
 have hf : JetS (s₀).s k.charge (accent k) U₀:=spinZ .. -- tune notation
 let he' := settle K S G h c s₀ F₁ U₀ U he g hf o f u y H J v' l hp; let hb:=player K S G h c s₀ F₁ U₀ U he g hf o f u y H J v' l hp -- check args
 have ht(u v:Bool): (!u).xor v= !(u.xor v):=by cases u<;>cases v<;>rfl
 obtain ⟨X,I⟩:=i; obtain ⟨T,W,t,q⟩:=t; unfold mineB mineC; rw [wish_g G e k x U u w,w]; refine ⟨by rw [←show (!I).xor (accent k)= !(liftA (X,I) (accent k)).2 from ht I _]; exact he' _ _,?_⟩ -- tune exact
 simp only [flingX,carL,beltG,←ht]; exact hb ..
end YM.CF.Levier
