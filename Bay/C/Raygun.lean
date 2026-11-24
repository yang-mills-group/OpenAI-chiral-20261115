import Bay.C.Blade
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 800000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Bay.C
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open Skye Scree Cadre Palot
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open Cube Lat Tulip Fock Rush Scroll Paige Vault Phase Acorn Spire
open Pastry Vow Rue
attribute [local instance] opCStarAlgebra
open Hake Jet Sault Stax Sour
attribute [local instance] Sour.loreM Sour.loreN
open Rill Branch Tenant Drapes Leaf



open Levier Urn Ione
open Peaks

set_option maxRecDepth 3500
set_option synthInstance.maxHeartbeats 160000
open Py Py.Rate Thera Dial Nacre Laic
open LocalLimit Preparation

open Salt SU Swell QuadClock Mew Vow.TreasuryFog BProof.Bide
open scoped YM.CF.Mew

variable {I J:Type}[Fintype I][LinearOrder I][Fintype J][LinearOrder J]


variable {n:Side}
structure Tip (n:Side) where
 e:RegBudget n
 k:ForceBudget n
abbrev twinB {n:Side}{I:Type}[LinearOrder I][Fintype I]
 (U:Key I→RegBudget n)
 (V:Key I→ForceBudget n)
 (i:I) :Tip n:=⟨νTip U i, emberTip V i⟩

abbrev Slide (s:Sweep n)(V W:Tip n):Prop:=passingR n s V.e W.e ∧ passingF n s V.k W.k

variable (s t:Sweep n)
lemma twiceH (j:Scree.Hub n):
 moveHub t (moveHub s j)=moveHub (s*t) j:=Subtype.ext (Prod.ext (by
   change (boxA _).symm ((boxA _).symm _) = (boxA (s*t)).symm _
   apply (boxA (s*t)).injective; rw[step_V];simp) (tape_B ..))
lemma twiceF(j:Force n):moveForce t (moveForce s j)=moveForce (s*t) j:=
  Subtype.ext (Prod.ext (twiceH ..) (tape_B ..))

variable {s t}{X Y Z:Tip n}
lemma Slide.between (u:Slide s X Y)(v:Slide (s*t) X Z):Slide t Y Z:=by
 constructor
 · intro i x
   obtain ⟨i,rfl⟩:=Finite.surjective_of_injective (hub_inj s) i
   obtain ⟨x,rfl⟩:(∃ z,flashA s z=x):=⟨flashA s⁻¹ x,by simpa using revB s⁻¹ x⟩
   rw [twiceH,Spire.lights,v.1,u.1,moon_Y]
 intro i x p
 obtain ⟨i,rfl⟩:=Finite.surjective_of_injective (force_inj s) i
 obtain ⟨x,rfl⟩:=surRaise s x
 have e:Pine x:=unyell s x ▸ treeV s⁻¹ p
 rw [twiceF,yell_t,v.2 i x e,u.2 i x e,moon_Y]

open Push.Uniform
variable (w:Berth)
abbrev soloI:= Fin 1
abbrev soloS (a:SealV w.side) :Fin 1→SealV w.side:=fun _=>a
lemma minio (S:SealV w.side)(M:ℕ)(p:1≤M): w.GaugeBill M (gr (soloS w S)):=by
 constructor
 · intro x
   refine le_trans ?_ p
   exact (card_le_univ ..).trans_eq (by simp)
 intro i j q; exact False.elim (q rfl)

def Native (w: Berth)(T:SealV w.side)(L s:ℕ)
 (p:Tip w.side) : Prop:=
 ∀ (I:Type)[Fintype I][LinearOrder I]
  (S:I→SealV w.side)
  (b:ℝ)
  (E:Key I→RegBudget w.side)(V:Key I→ForceBudget w.side),
   Dons w S L s b E V→
    ∀ i:I,∀θ:Sweep w.side,S i = watch θ T →Slide θ p (twinB E V i)

-- therefore also slides of arbitrary paired poses
variable {w}{M m L s:ℕ}{a c:ℝ}{F C D:ℝ→ℝ}{r:blazeK w.side}
lemma nativeRoot (g:w.Thermal M L F C D r)(h:w.Rig a c m)(k:w.Tall)(p:1 ≤ M)
 {S:SealV w.side}(d:Grant w C D S)(x:w.lampCap ≤ s):
 ∃U V, Dons w (soloS w S) L s (icedCost w.P M L F D w.x) U V ∧
 Native w S L s (twinB U V 0):=by
  obtain ⟨U,V,q⟩:= licensing g h k (minio w S M p) (fun _=>d) x
  refine ⟨_,_,q,?_⟩
  intro I f e A b P W l i θ t
  refine pin_V h.high.le q l θ 0 i ?_ ?_
  · rw [t]; exact salute θ S.ink
  rw [t];rfl
