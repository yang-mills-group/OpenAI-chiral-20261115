import YM.CF.Hive.Lino
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 20000
set_option linter.unusedVariables false
noncomputable section
namespace YM.CF.Hive
open Function Filter Metric NormedSpace Finset Fock Lattice Wilson Laurent Lat Rush SU Drapes Fir Peaks Dial Paige Brace Vault Tulip Tenant Phase Broc Matrix Scroll Thera Branch Laic Cube
open scoped Matrix.Norms.L2Operator Matrix Topology ContDiff MatrixOrder BigOperators InnerProductSpace Kronecker
attribute [local instance] opCStarAlgebra
open Urn Hake Levier Spire Scree Stilo
attribute [local instance] opCStarAlgebra
open Acorn Nacre Skye
variable {N B m L:Side}{k j:ℕ}{a b d c e p H:ℝ}{o:Odd L.val}{Y:Pricing j L o (Thread j)}{P:Grasp Y B e}{I:Aim (CSide m B)}{M:Male}{S:Seal (Skye.Seat (CSide m B))}
local notation "N₀"=> CSide m B
abbrev Stent (N:Side):= Finset (Seal (Skye.Seat N))
variable (V:∀ S:Seal (Skye.Seat (CSide m B)),Lend m B e S)
def cozen (Z:Seal (Skye.Seat N₀))(X: Stent N₀)(y:Castle m B e Z): FC (Single N₀):=∑ i:(V Z).slots, if ((V Z).crew i).1 ∈ X then vowC ((V Z).crew i) y else 0
abbrev turnZ(s:Sweep N)(X:Stent N): Stent N:= X.image (actS s)
lemma actG_in(s:Sweep N):Injective (actS s):= Function.LeftInverse.injective (actG_l s)
lemma turnU(s t:Sweep N)(X:Stent N):turnZ t (turnZ s X)=turnZ (s*t) X:=by rw [turnZ,turnZ,turnZ, Finset.image_image]; congr 1; funext; rw [actG_s]; rfl
lemma cozy {Z:Seal (Skye.Seat N₀)}(X: Stent N₀)(y:Castle m B e Z)(h:Vista P M I V k H b c a)(hx:Grove (terr _) Z): Keys (cozen V Z X y):=by
 classical
 refine Keys.all_s (ι:=(V Z).slots) univ _ fun i _=> ?_ ; split; exact Keys.col _ (Keys.roll _ ((h.carry _ hx).1 i).2.2.1); exact Keys.null
lemma viewX(S:Seal (Skye.Seat N₀))(x:Castle m B e S)(A:Ids N₀)(X: Stent N₀):hula V S x A X=mallC S A (cozen V _ (turnZ (chip S A) X) (strideH S A x)):=by
 unfold cozen hula; dsimp only; apply congrArg (mallC S A)
 refine sum_congr rfl fun i _=> ?_ ; let k:=chip S A
 have hp(y:Seal (Skye.Seat N₀)):actS k⁻¹ y∈ X ↔ y∈turnZ k X:=by
    constructor; intro p; have ht:actS k (actS k⁻¹ y)=y:=by simpa only [inv_inv] using actG_l k⁻¹ y
    exact mem_image.mpr ⟨_,p,ht⟩; intro h; obtain ⟨t,p,rfl⟩:=mem_image.mp h; rwa [actG_l]
 let y:=((V (strideG S A)).crew i).1; change (if _ then _ else _)=(if _ then _ else _); by_cases h:actS (chip S A)⁻¹ y ∈ X; rw [if_pos h, if_pos ((hp _).mp h)]; rw [if_neg h,if_neg (mt (hp _).mpr h)]
lemma shrew(X: Stent N₀)(g:Grove (terr _) S)(s:Sweep N₀)(x:Castle m B e S)(A:Ids N₀)(h:Injective (priorP A))(hv:Vista P M I V k H b c a) :
 hula V (actS s S) (pullT s x) (bun s A) (turnZ s X)=teen s (hula V S x A X):=by
 let S':=actS s S; let a':=chip S A; let c':=chip S' (bun s A); let U:= hula V S x A X; have he:=chore V hv g x A X
 have hp: S.Nonempty:=by cases g <;> simp
 have hh:s*c'= a':=by unfold c'; rw [chipA S hp _ h,mul_inv_cancel_left]
 let t:= strideH S A x; let t':= strideH S' (bun s A) (pullT s x); let Q:=strideG S A; let R:=strideG S' (bun s A)
 have hx:R=Q:= by change actS c' (actS s S)= _; rw [←actG_s,hh]
 have hz: t.val=t'.val:=by funext i; change flashA a' (Lattice.gauge (frameP A) _) = flashA c' (Lattice.gauge (frameP _) (flashA s _)); rw [boong,lights,hh]
 have hr{Q R: Seal (Skye.Seat N₀)}(x:Castle m B e Q)(y:Castle m B e R)(i:Stent N₀)(p:Q=R)(l:x.val=y.val): cozen V Q i x= cozen V R i y:=by subst R; rw [Subtype.ext l]
 have hk:= cozy V (turnZ a' X) t hv (grove_t S a' g)
 rw [viewX]; change mallC S' (bun s A) (cozen V R (turnZ c' (turnZ s X)) t')=teen s U; rw [turnU,hh, hr t' t (turnZ a' X) hx hz.symm]; nth_rw 1 [←morn S A _ hk]; rw [show mallC S A (cozen V Q (turnZ a' X) t)= U from ?_] -- direction
 rw [← wore s A S hp h U he, mare S' (bun s A) _ (Keys.tour_b _ _ _ U he)]
 exact (viewX V S x A X).symm -- tune
lemma hub_u(X:Stent N₀)(g:Grove (terr _) S)(h: Vista P M I V k H b c a)(x:Castle m B e S)(U: Ids N₀)(z:Skye.Seat N₀→ E): hula V S (pullF S z x) (threadG z U) X=Gaze z (hula V S x U X):=by
 let A:= threadG z U; let v:=chip S A; let W:=turnZ v X; let B:=strideH S U x; rw [viewX]; change mallC _ A (cozen V _ W _)= _
 rw [show strideH S A (pullF S z x)= B from ?_]; swap
 · apply Subtype.ext; funext i; change flashA v (Lattice.gauge _ (Lattice.gauge z _))= _; rw [Skye.gauge_sq,show frameP A*z= _ from ?_]; rfl; change frameP A*z=frameP U; funext i; simp [A,frameP,threadG]
 let P:=cozen V _ W B; have hv:= cozy V W B h (grove_t _ _ g); have hp:Keys (hula V S x U X):=chore V h g x U X
 change mallC S A P=_; nth_rw 1 [← morn S U P hv]; rw [show mallC S U P=_ from (viewX V S x U X).symm,←worthZ U S _ hp z]; exact mare _ _ _ (Keys.tour_b _ _ _ _ hp)
end YM.CF.Hive
