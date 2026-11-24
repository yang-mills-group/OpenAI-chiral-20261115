import YM.CF.Cour.Culm
import YM.CF.Scree.Locus
set_option autoImplicit false
set_option maxHeartbeats 450000
noncomputable section
namespace YM.CF.Gingham.Ruff
open Function NormedSpace Finset Fock Scree Pastry
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
open Lattice Wilson Laurent Cube SU Lat Spire Scroll Peaks Drapes Rush Precision Tulip Jet
    Tap Laic Dial Paige Vault Pec Skye
open Nacre Levier Cour Broc Kennel Branch Thera
variable {N:Side}

/-- Both S and T with Crown, on a common P.d qualification. Full-profile
    projections and movement also paid on these qualifications. -/
structure Plumes (S T: Chin N → Op (Single N))(a c e:ℝ):Prop where
 lead : Solo a c S e
 silk : Solo a c T e
 pure : ∀ p:Pane N, Guard p e → IsStarProjection (S (profile p))
 step : ∀ (a:Shape)(b:Bool)(U:UNI SpinIdx), JetS a.s b (detX a.s) U →
   ∀ p:Pane N, Guard p e →
   sings b (prepU a U (xtra b) N) (S (profile p)) =
    swapX (detX a.s) (S (profile (stir (xtra b) a p))) ∧
   T (profile (stir (xtra b) a p))= yank b a U (T (profile p))

abbrev prince (j:ℕ) (R:GramM N) := funde j R.J.M N
abbrev princeps (R:GramM N) := Moire.bloom R.J.P

abbrev Diadem (R:GramM N) (j:ℕ)(a c e:ℝ):= Plumes (prince j R) (princeps R) a c e

lemma plume_den (R:GramM N) (j:ℕ)(p:Pane N):
    prince j R (profile p)=spar j R.J.M p ∧
    princeps R (profile p)=R.J.P.den p :=
 ⟨rfl,Moire.bloom_P _ _⟩


namespace Plumes
variable {S T: Chin N → Op (Single N)}{a c e:ℝ}
def finery (s:Cover) (p:Pane N):= stir inert (lagX s) p
abbrev fineryS(s:Cover)(N:Side):=prepU (lagX s) 1 inert N

lemma parade (h:Plumes S T a c e) (s:Cover) (p:Pane N)(g:Guard p e):
 let i:= fineryS s N
 S (profile (finery s p))=twist i (S (profile p)) ∧
 T (profile (finery s p))=twist i (T (profile p)) :=by
 let i:= lagX s
 have y:detX i.s=false:=det_i
 obtain ⟨t,b⟩:= h.step i false 1 (y.symm ▸ calmSX) p g
 rw [y] at t
 unfold yank at b; rw [y] at b
 exact ⟨t.symm,b⟩


abbrev glass (k:Axis)(s:Cover) (p:Pane N):= stir inert ⟨Signed.mirror k,s⟩ p
abbrev glassS(k:Axis)(s:Cover)(N:Side):=
 prepU ⟨Signed.mirror k,s⟩ (⟨Mir.pin k,Mir.pin_U k⟩) inert N

lemma windowpane (h:Plumes S T a c e) (k:Axis)(s:Cover) (p:Pane N)(g:Guard p e):
 let i:= glassS k s N
 S (profile (glass k s p))=twist i (1-S (profile p)) ∧
 T (profile (glass k s p))= -twist i (star (T (profile p))) :=by
 let i:=Scroll.Shape.mk (Signed.mirror k) s
 have y:detX i.s=true:=det_t k
 obtain ⟨t,b⟩:= h.step i false _ (y.symm ▸ mirrorX k) p g
 rw [y] at t
 unfold yank at b; rw [y] at b
 change twist (glassS k s N) (S (profile p))=1-S (profile (glass k s p)) at t
 change T (profile (glass k s p))= -star (twist (glassS k s N) (T (profile p))) at b
 constructor
 · rw [map_sub,map_one,t]; abel
 rw [b,map_star]
