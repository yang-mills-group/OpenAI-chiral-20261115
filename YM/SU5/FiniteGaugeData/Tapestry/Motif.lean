import YM.SU5.FiniteGaugeData.Tapestry.Fountain
import YM.SU5.FiniteGaugeData.Tapestry.Raffia
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 460000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tapestry
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder ENNReal Classical
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent Next.Free Bloch Drapes Spire Lifted Skye Sound Precision Tree Push.SectorMeasure Next.SectorChange Common Fock
open Satin
attribute [local instance] opCStarAlgebra
open Py Py.Rate LocalLimit Preparation Journey Vale FullBill
open Nacre Mir Phase RP
open Altitude Heat Pastry
open PiTensorProduct (tprod)

/-!
# Common-priced motifs: mixed finite products

We can pay receipt on all their coefficients, on the stated supports & heights.
Cast all members to their native partners in a finite Dressing. Use Swatches
(hence all f) whose view in Family has the support qualification on ALL levels
of this cost. Support-growth in advancement does not change throughout cutoffs;
it is a function only of the outer stencil sequence supplied.
-/
set_option quotPrecheck false

abbrev BillOfWork := ℕ → Finset Cover
abbrev Employee (S:BillOfWork) := ∀ i:ℕ,Swatch (S i)
variable (K:Calibration) (S:BillOfWork) (x y: Employee S)
def employ (K:Calibration)(S:BillOfWork)(x: Employee S): sequenceOf K := fun i=> badge K (S i) (x i)
def motif : Cloud (Dome K):= pureShot K (employ K S x)
variable {K}
def Clocked (n:ℕ)(x:Employee S): Prop:= Altitude.Enough n (employ K S x)
variable (K) (n:ℕ)
lemma motif_paid (p:Clocked (K:=K) S n x): motif K S x∈boardedDB K n:= board (P:={f| Altitude.Enough n f}) p
lemma badges_location (f:sequenceOf K) : ∃ (S:BillOfWork)(x:Employee S), f=employ K S x:=by
 let S(i:ℕ):= precinct K (f i); exact ⟨S,(fun i=>trophy K (f i) (precinct_spec K (f i))),funext fun i=> (trophy_at K (f i) (precinct_spec ..)).symm⟩
lemma motif_represents (f:sequenceOf K)(p:∀ i,f i∈bay K (S i) true): ∃ x:Employee S, employ K S x=f:=
 ⟨(fun i=> trophy K (f i) (p i)),funext (fun i=>trophy_at K (f i) (p i))⟩
lemma certify {f:Cloud (Dome K)}(p:f∈shorter (Dome K) n) : f∈ Submodule.span ℂ {v : Cloud (Dome K)| ∃ (S:BillOfWork) (x:Employee S), Clocked (K:=K) S n x ∧ motif K S x=v}:=by
 let P:= {f: ℕ→Dome K|Altitude.Enough n f}; let h:=Submodule.span ℂ {v : Cloud (Dome K)| ∃ (S:BillOfWork) (x:Employee S), Clocked (K:=K) S n x ∧ motif K S x=v}
 refine Submodule.span_le (R:=ℂ) (s:=PiTensorProduct.tprod ℂ '' P)|>.mpr ?_ p -- binder s?
 rintro _ ⟨f,v,rfl⟩; obtain ⟨S,x,rfl⟩:= badges_location K f; exact Submodule.subset_span (s:={v : Cloud (Dome K)| ∃ (S:BillOfWork) (x:Employee S), Clocked (K:=K) S n x ∧ motif K S x=v}) ⟨S,x,v,rfl⟩
lemma promptNectar (C: ℕ→ℝ) (q:∀ i,i≤n→∃ m:Side,Hosp (S i) (K.c m) ∧ ∀ z,‖(employ K S x i).val m z‖ ≤ C i) :
 nectar n x ≤ ∏ i∈ Finset.Iic n,C i:= by
 apply nectarBelow; intro i h; obtain ⟨m,u,z⟩:= q i h; exact sampling (S i) K m u _ z -- maybe timeout

variable (Λ:Preparation)(l:ℕ)
-- support providing rolled-forward warm/sharp price, step-independent of volume
local notation "Up" S:max=> followBox (Λ:=Λ) (l:=l) S
def frameBudget : ℕ→ Finset Cover
 | 0=> S 0
 | i+1=> followBox (Λ:=Λ) (l:=l) (frameBudget i) ∪ S (i+1)
local notation "Δ"=> frameBudget S Λ l
lemma frame_open : S n⊆ frameBudget S Λ l n := by cases n with| zero=>exact le_refl _|succ n=> exact subset_union_right
lemma frame_lines {V:Set RSpace}(q:∀ i,i ≤ n→ printedHere Λ l i (S i) V): printedHere Λ l n (frameBudget S Λ l n) V:=by
 induction n with
 | zero=> exact q 0 le_rfl
 | succ n ih=> exact unionPrinted Λ l _ _ _ V (shielding Λ l n V (frameBudget S Λ l n) (ih fun i v=> q i (by omega))) (q (n+1) le_rfl)

-- Line computes α0, then l₁ maps on fixed Swatch, μ output Swatch; links & lifts use ultimate observation price. Define fillers wrappers.
local notation "U" i:max=> Swatch (Δ i)
local notation "V" i:max=> Swatch (S i)
abbrev QuiltLinks := ∀ i:ℕ,Swatch (frameBudget S Λ l i)→L[ℂ]Swatch (frameBudget S Λ l (i+1))
def extendLeft : Swatch (followBox (Λ:=Λ) (l:=l) (frameBudget S Λ l n)) →L[ℂ] Swatch (frameBudget S Λ l (n+1)) := Tapestry.broad K _ _ subset_union_left
def extendRight : Swatch (S n) →L[ℂ] Swatch (frameBudget S Λ l n) := Tapestry.broad K _ _ (frame_open S n Λ l)
def buildStart : Swatch (S 0) →L[ℂ] Swatch (frameBudget S Λ l 0) := ContinuousLinearMap.id ℂ _ -- choose not extendRight
lemma began (x:Employee S): badge K (frameBudget S Λ l 0) (buildStart S Λ l (x 0)) = employ K S x 0 :=rfl

instance (priority := high)(S T: Finset Cover): Module ℂ (Swatch S →L[ℂ] Swatch T):=inferInstance
instance (priority := high)(S T: Finset Cover): NormedSpace ℂ (Swatch S →L[ℂ] Swatch T):=inferInstance

def material : Swatch (frameBudget S Λ l (n+1))→L[ℂ] (Swatch (S (n+1)) →L[ℂ] Swatch (frameBudget S Λ l (n+1))) :=
 ((brocadeL K (frameBudget S Λ l (n+1))).flip.comp (extendRight K S (n+1) Λ l)).flip
lemma material_eq (u : Swatch (frameBudget S Λ l (n+1)))(v: Swatch (S (n+1))) :
 material K S n Λ l u v = brocade K (frameBudget S Λ l (n+1)) u (extendRight K S (n+1) Λ l v):=rfl
-- one price recursion and actual tests
def powers (θs: QuiltLinks S Λ l)(n:ℕ): Employee S → Swatch (frameBudget S Λ l n):=
 herring (X:=fun i=> V i) (Y:=fun i=>U i) (buildStart S Λ l) (fun i=>material K S i Λ l) θs n
lemma powers_zero (θs): powers K S Λ l θs 0 x=buildStart S Λ l (x 0):=rfl
lemma powers_succ (θs: QuiltLinks S Λ l): powers K S Λ l θs (n+1) x = material K S n Λ l (θs n (powers K S Λ l θs n x)) (x (n+1)):=rfl

end YM.CF.Buffered.Afterglow.Tapestry
#print axioms YM.CF.Buffered.Afterglow.Tapestry.certify
#print axioms YM.CF.Buffered.Afterglow.Tapestry.frame_lines
#print axioms YM.CF.Buffered.Afterglow.Tapestry.promptNectar
#print axioms YM.CF.Buffered.Afterglow.Tapestry.began
