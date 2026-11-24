import SatinPP.Tuxedo
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 3000
set_option maxHeartbeats 320000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance Lamour.Bridge.Celeste Designs Twah Prototype
open Lamour.Bridge.Celeste.Morn
namespace Spine
open Aria Casting Six OS.Semigroup OS.Semigroup.Balloon
open MacroGrid SatinNucleus SatinJets DoseTravel Set
variable (P:Spine)(x:P.Spectrum0 3)

local notation "ξ"=>P.advocate 3 x 3
local notation "H"=>P.ColorHil 3 ξ
local notation "S"=>P.physicalEnergy 3 ξ
local notation "ω"=>P.colorZero 3 ξ
local notation "E"=>(S).E
local notation "Υ"=> P.shifts 3
variable (n:ℕ)
local notation "ϐ"=>bell (timeMesh P.par) n

section

local notation "β"=>P.birthF 3 n
local notation "ρ"=>P.viewF 3 ξ n
variable {P x n}
lemma stock_here {w:ℕ}{z:P.Test}{B:(P.ColorHil 3 (P.advocate 3 x 3)).Op}
    (h:P.Stock 3 ξ n w z B): P.Acts 3 ξ n w z B:=by
 have v:=h n le_rfl
 rw [Nat.sub_self,pow_zero,one_mul] at v; exact v

variable {l d:ℕ}{f g:P.Test}
variable {X Y:(P.ColorHil 3 (P.advocate 3 x 3)).Op}
lemma from_stock (r:P.Stock 3 ξ n l f X):
 ∃ q:β f,ρ q=X (ω):=by
 obtain ⟨a,H₁⟩:=stock_here r 1 (P.faceUnit 3 n)
 exact P.issue_eq 3 ξ (by rw [map_one,mul_one]) a ((H₁).trans (congrArg X (P.view_one ..)))

lemma stock_mean (r:P.Stock 3 ξ n l f X):
 inner ℂ (ω) (X (ω))=P.singleState 3 n x f:=by
  obtain ⟨a,b⟩:=from_stock r
  rw [←b,P.view_scalar,P.single_agrees]
lemma stock_val (r:P.Stock 3 ξ n l f X)
 (s:P.Stock 3 ξ n d g Y)(m:ℕ):
 inner ℂ (ω) (X (E ((ϐ m).toNNReal) (Y (ω))))=
   P.singleState 3 n x (f * Υ ((l:ℤ)+m) g):=by
  obtain ⟨a,b⟩:=from_stock s
  have v:=P.releasedLater 3 ξ n m a

  have v':(ϐ m).toNNReal=whenly (timeMesh P.par) n m:=
    (congrArg _ (natural_time ..)).trans Real.toNNReal_coe
  rw [←b,v',←v]
  obtain ⟨c,p⟩:=stock_here r _ (P.passesLater 3 n m a)
  rw [←p,P.view_scalar,P.single_agrees,P.shifts_sum]


end
-- jacket prices
/-- Literal purchase on panel [a,b]. `Z` at absolute placements; relative to mesh left
wall L implemented by translation -L, stored (all finer releases).
Limits u−l real widths; both mesh walls must fit,
remaining slack filled with heat. -/
def Stocked (a b:ℝ)(z:P.Test)(A:(P.ColorHil 3 (P.advocate 3 x 3)).Op):Prop:=
   ∃ (L U:ℤ)(B:(H).Op), a ≤ ϐ L ∧ ϐ U ≤ b ∧ L ≤ U ∧
         P.Stock 3 ξ n (U-L).toNat (Υ (-L) z) B ∧
         A=jacket (S) (ϐ L-a) (b-ϐ U) B

variable {P x n}
variable {l u a b:ℝ}{f g:P.Test}{A B:(P.ColorHil 3 (P.advocate 3 x 3)).Op}

lemma jacket_ω (X:(P.ColorHil 3 ξ).Op)(a b:ℝ):jacket (S) a b X (ω)= E a.toNNReal (X (ω)):=by
    change E _ (X (E _ (ω)))=_; rw [P.sector_hot]
lemma heat_ket (t:ℝ≥0)(X:H):inner ℂ (ω) (E t X)=inner ℂ (ω) X:= by
 rw [←ContinuousLinearMap.adjoint_inner_left,(S).sym,P.sector_hot]

lemma Stocked.meanP (p:P.Stocked x n l u f A):
   inner ℂ (ω) (A (ω))=P.singleState 3 n x f:=by
 obtain ⟨L,U,X,_,_,_,q,rfl⟩:=p
 rw [jacket_ω,heat_ket,stock_mean q,P.slide_single]
#check sector_hot


lemma Stocked.pairP (p:P.Stocked x n l u f A)(q:P.Stocked x n a b g B)(h:u ≤ a):
   inner ℂ (ω) (A (E (a-u).toNNReal (B (ω))))=P.singleState 3 n x (f*g):=by
 obtain ⟨L,U,X,e,i,K,r,rfl⟩:=p
 obtain ⟨M,N,Y,z,y,I,s,rfl⟩:=q
 let t:=u-ϐ U; let v:=ϐ M-a; let m:ℕ:=(M-U).toNat
 have UM:U ≤ M:=(bell_le _ _ _ _).mp (i.trans (h.trans z)) -- orientation
 have T: t.toNNReal+((a-u).toNNReal+v.toNNReal)=(ϐ m).toNNReal:=by
   unfold t v
   rw [← Real.toNNReal_add (sub_nonneg.mpr h) (sub_nonneg.mpr z),
       ←Real.toNNReal_add (sub_nonneg.mpr i) (add_nonneg (sub_nonneg.mpr h) (sub_nonneg.mpr z))]
   apply congrArg
   unfold m
   rw [Int.toNat_of_nonneg (sub_nonneg.mpr UM)]
   simp [bell,_root_.sub_mul]
 rw [jacket_ω]
 change inner ℂ (ω) (E _ (X (E t.toNNReal (E (a-u).toNNReal (E v.toNNReal (Y (ω)))))))=_
 rw [heat_ket,←ContinuousLinearMap.comp_apply (E (a-u).toNNReal),
     ←ContinuousLinearMap.comp_apply (E t.toNNReal),← (S).time,←(S).time,T,
     stock_val r s]
 have j: ((U-L).toNat:ℤ)+m+ -M = -L:=by unfold m; omega
 rw [P.shifts_sum,j,← map_mul,P.slide_single]

#print axioms Stocked.pairP

end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
