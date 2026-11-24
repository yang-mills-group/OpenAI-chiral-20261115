import YM.SU5.Relativistic.Backing

/-!
# Basis prescription for the exterior test system

A homogeneous multi-mesh measurement, finitely many ordered inputs (at equal height
first form their product as one InTest mark). Contact multiplication of such measurements
must respect this convention—not freely multiply as evaluated on highest resolution.
Need a Koszul sign on merging; use braided syntax separately.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 25000
set_option maxHeartbeats 400000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.Reconstruction
namespace FermionSlab
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Fock
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder NNReal ENNReal Classical InnerProductSpace
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat PhaseChoice SlabMark Vacancy Tapestry Tapestry.Altitude Tapestry.Exhibition Tower.Selected
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(H:Real.exp 1≤Λ.x)
local notation "K"=>tent Y H
variable {a b:ℕ→ℕ}{I:ℕ→Family (tent Y H)→ℕ→ℂ}{E:ℕ→Family (tent Y H)→ℂ}(V:Universal Y H a b I E)
variable {D:ℕ→Family (tent Y H)→Family (tent Y H)}{i k:ℕ→ℕ}(Q:Coherent Y H (i:=a) (k:=b) (E:=E) D i k)
variable (u:ℕ→ℕ)(T:ℕ→ Bool→Family (tent Y H)→Family (tent Y H))(t:GradesAll (i:=a) (a:=i) (k:=b) (b:=k) Y H u T)
local notation "W"=> wingspan Λ l

structure Ink (J:Calibration) where
 mark : Family J
 kind : Bool
 S : Finset Cover
 bill : InTest J true S kind mark
-- test prescriptions indexed by s (starting observing level) and n LEVELS after that one
inductive Lariat (J:Calibration): ℕ→Type where
 | start: Ink J → Lariat J 0
 | stretch {n:ℕ}: Lariat J n→ Ink J → Lariat J (n+1)
variable (s:ℕ)
namespace Lariat
section neutral
variable {K':Calibration}
def hue : {n:ℕ}→ Lariat K' n → Bool
 | _,start f=> f.kind
 | _,stretch f g=> (hue f).xor g.kind
def evens : {n:ℕ}→ Lariat K' n→ Prop
 | _,start f=> f.kind=false
 | _,stretch f g=> evens f ∧ g.kind=false
def neutral : {n:ℕ}→ Lariat K' n→ Prop
 | _,start f=> CovCover K' f.mark
 | _,stretch f g=> neutral f ∧ CovCover K' g.mark
-- hermetic permits (all factors budgeted inside this physical region at this origin height)
variable {n:ℕ}
def box (Λ:Preparation)(l:ℕ) {n:ℕ} : Lariat K' n→ Finset Cover
 | start f=> f.S
 | @stretch _ n f g=> wingspan Λ l (box Λ l f) ∪ g.S -- syntax check

def priced (C:ℕ→ℝ) : {n:ℕ}→ Lariat K' n→ Prop
 | 0,start f=> pay f.mark (C 0)
 | n+1,stretch f g=> priced C f ∧ pay g.mark (C (n+1))

def ordains {Λ:Preparation}(l:ℕ)(s:ℕ)(j:Axis)(z:ℤ) : {n:ℕ}→ Lariat K' n→ Prop
 | 0,start f=> Tower.region j z K'.ℓ f.S
 | n+1,stretch f g=> ordains (Λ:=Λ) l s j z f ∧ Tower.region j (planeAt z Λ.R.L (n+1)) K'.ℓ g.S

def stamps {Λ:Preparation}(l:ℕ)(s:ℕ)(U:Set RSpace) : {n:ℕ}→ Lariat K' n→ Prop
 | 0,start f=> SupportedPhysically Λ l s f.S U
 | n+1,stretch f g=> stamps (Λ:=Λ) l s U f ∧ SupportedPhysically Λ l (s+(n+1)) g.S U
end neutral
variable {n:ℕ}
-- at every price: cinema chooses (ascender scaled Y H i k), no replacement of cutoff.
def rideL (T:ℕ→Bool→Family (tent Y H)→Family (tent Y H))(s:ℕ) : {n:ℕ}→ Lariat (tent Y H) n→ Family (tent Y H)
 | _, start f=> f.mark
 | n+1,stretch f g=> (T (s+n) (hue f) (rideL T s f))*g.mark -- parameters order implicit (inside recursion omit)

def priceAt (s:ℕ) (i k:ℕ): {n:ℕ}→ Lariat (tent Y H) n→ Family (tent Y H)
 | _, start f=> f.mark
 | n+1,stretch f g=> moveUp Y H (s+n) i k (box Λ l f) (hue f) (priceAt s i k f)*g.mark -- recurse syntax
local notation "ε" f:max=> rideL Y H T s f
local notation "Π₀" i:max k:max f:max=> priceAt Y H s i k f
variable (f:Lariat (tent Y H) n)
lemma sizes : ∃ n:ℕ, priced (fun _=> (n:ℝ)) f:= by
 induction f with
 | start f=> obtain ⟨r,h⟩:= Journey.valuation Y H f.bill; obtain ⟨n,u⟩:= exists_nat_gt r; exact ⟨n,fun i x=> (h ..).trans u.le⟩
 | stretch f g ih=> obtain ⟨n,h⟩:=ih; obtain ⟨r,t⟩:= Journey.valuation Y H g.bill; obtain ⟨m,u⟩:= exists_nat_gt r; refine ⟨max n m,paidScale f h (by exact_mod_cast le_max_left n m),fun i x=> ((t ..).trans u.le).trans (show (m:ℝ)≤(max n m:ℕ) from by exact_mod_cast le_max_right n m)⟩ -- `fun` maybe t expand
where
 paidScale {i:ℕ}(f:Lariat K i) {c y:ℝ}(p:priced (fun _=> c) f)(u:c ≤ y): priced (fun _=>y) f:= by induction f with| start f=>exact fun i x=> (p i x).trans u| stretch f g ih=> exact ⟨ih p.1,fun i x=> (p.2 i x).trans u⟩
lemma groundPrice(i k:ℕ): InTest K true (box Λ l f) (hue f) (Π₀ i k f):=by induction f with| start f=>exact f.bill| @stretch n f g ih=> exact ((stay Y H (s+n) i k (box Λ l f) _ (hue f)).mono subset_union_left).mul (g.bill.mono subset_union_right)
include t
lemma aboard : InTest K true (box Λ l f) (hue f) (ε f):=by induction f with| start f=>exact f.bill| @stretch n f g ih=> exact ((t.pays Y H u (s+n) ih).mono subset_union_left).mul (g.bill.mono subset_union_right)
-- `priceAt` support uses declared support box even within Seq. Keep exact Y probability, at highest marks true compatibility.
include V Q t
lemma singlet (p:f.neutral): CovCover K (ε f):=by induction f with| start f=> exact p| @stretch n f g ih=> exact (covariant_parts K (t.bless Y H V Q u (s+n) (aboard Y H u T t s f) (ih p.1)) p.2).2
-- order Q explicit verify
end Lariat
end FermionSlab
end YM.CF.Buffered.Afterglow.Tower.Reconstruction
