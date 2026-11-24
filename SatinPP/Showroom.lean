import SatinPP.Cards
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

local notation "τ"=>P.meshPose n 
local notation "Vv"=>P.vtile n
variable (A:P.Apron)(F:SampleDose)
local notation "w"=> A.realWidth P 3
local notation "G'"=>P.usedGrid n F
local notation "α"=>P.activation n F

/-- Panel cleared if *all* mesh insertions fit. -/
def SetPanel (l u:ℝ):Prop:=∀ p∈tsupport F.val,
    w ≤ p (3:Axis)-l ∧ w ≤ u-p 3
def Occupies (L U:ℤ):Prop:=∀ k∈G',
    w ≤ τ k 3-ϐ L ∧ w ≤ ϐ U-τ k 3
def panelOne (l u:ℝ)(k:Cover): (H).Op:=
  P.charter 3 ξ (Vv k) (P.locket 3 ξ A (τ k 3-l) (u-τ k 3))
/-- Real walls. Needs clearing, otherwise just syntax (prices only intrinsic widths). -/
def gridRun (l u:ℝ): (H).Op:= ∑ k∈G', α k • P.panelOne x n A l u k


variable {P x F n A}
lemma run_gap {L U:ℤ}{l u:ℝ}(h:P.Occupies n A F L U)
  (a:l ≤ ϐ L)(b:ϐ U ≤ u) :
 P.gridRun x n A F l u=jacket (S) (ϐ L-l) (u-ϐ U) (P.gridRun x n A F (ϐ L) (ϐ U)):=by
 unfold gridRun; rw [map_sum]
 refine Finset.sum_congr rfl fun k c=>?_
 obtain ⟨e,i⟩:=h k c
 rw [map_smul,panelOne,P.widen_locket 3 ξ A e i
       (sub_le_sub_left a _) (sub_le_sub_right b _),
       charter_inside,sub_sub_sub_cancel_left,sub_sub_sub_cancel_right]
 rfl

lemma install_piece  {L U:ℤ}(dn:A.s ≤ n)(k:Cover)
    (h:w ≤ τ k 3-ϐ L ∧ w ≤ ϐ U-τ k 3):
 P.Stock 3 ξ n (U-L).toNat (Υ (-L) (P.issuing n A k))
       (P.panelOne x n A (ϐ L) (ϐ U) k):=by
 have e:τ k 3=ϐ (k 3):=rfl
 rw [e,← A.zoom_bell P 3 n dn] at h
 let z:=A.zoom P n 3
 have sub(b a:ℤ):ϐ (b-a)=ϐ b-ϐ a:=by simp [bell,_root_.sub_mul]
 have l:(z:ℤ)≤k 3-L:=(bell_le _ _ _ _).mp ((sub ..).symm ▸ h.1) -- check
 have u:(z:ℤ)≤U-k 3:=(bell_le _ _ _ _).mp ((sub ..).symm ▸ h.2)
 let v:= (k 3-L).toNat; let r:= (U-k 3).toNat
 have i:z ≤ v:=by unfold v; omega
 have j:z ≤ r:=by unfold r; omega
 have t:=P.transport_stock 3 ξ A n k dn i j
 have a:(v:ℤ)=k 3-L:=by unfold v; omega
 have b:(r:ℤ)=U-k 3:=by unfold r; omega
 rw [show v+r=(U-L).toNat by omega, a, b,sub,sub,show k 3-L-k 3= -L by omega] at t
 exact t


lemma install_all {L U:ℤ}(h:P.Occupies n A F L U)
    (dn:A.s ≤ n):
 P.Stock 3 ξ n (U-L).toNat (Υ (-L) (P.prepared n A F))
       (P.gridRun x n A F (ϐ L) (ϐ U)):=by
 unfold prepared gridRun
 rw [map_sum]; simp_rw [map_smul]
 refine stock_sum _ fun k hk=> (install_piece dn k (h k hk)).smul _
#check macroStep_pos
#check Apron.zoomP
#check Apron.real_width_pos

variable {l u:ℝ}
def SetReady (P:Spine)(A:P.Apron)(F:SampleDose)(l u:ℝ):Prop:=
   l+2*A.realWidth P 3≤u ∧ P.SetPanel A F (l+A.realWidth P 3) (u-A.realWidth P 3)
lemma SetPanel.ofReady (h:P.SetReady A F l u):P.SetPanel A F l u:=fun p i=>by
 have ⟨j,b⟩:=h.2 p i
 constructor <;> linarith only [j,b,A.real_width_pos P 3]
local notation "D"=>P.macroStep n
lemma upper_wall (dn:A.s≤n)(r:ℝ):∃ j:ℤ, r ≤ ϐ j ∧ ϐ j≤ r + w:=by
 have v: (D) ≤ w:=
    calc
     D = ϐ 1 :=by simp [bell,macroStep]
     _ ≤ ϐ (A.zoom P n 3):=(bell_le _ _ _ _).mpr
         ((Nat.one_le_iff_ne_zero.mpr (A.zoomP P 3 n).ne')|>Int.ofNat_le.mpr)
     _ = _:=A.zoom_bell P 3 n dn
 refine ⟨⌈r/(D)⌉, (div_le_iff₀ (P.macroStep_pos n)).mp (Int.le_ceil _),?_⟩
 have g:=mul_le_mul_of_nonneg_right (Int.ceil_lt_add_one (r/(D))).le (P.macroStep_pos n).le
 rw [_root_.add_mul, one_mul,div_mul_cancel₀ _ (P.macroStep_pos n).ne'] at g
 exact g.trans (by linarith)
#check upper_wall


lemma install (h:P.SetReady A F l u)(dn:A.s≤n):
 P.Stocked x n l u (P.prepared n A F) (P.gridRun x n A F l u):=by
 obtain ⟨L,a,b⟩:=upper_wall dn l
 obtain ⟨U,e,i⟩:=upper_wall dn (u-w)
 have r:P.Occupies n A F L U:= fun k c=>by
   obtain ⟨y,v⟩:=h.2 _ ((P.usedPose n F k).mp c)
   exact ⟨y.trans (sub_le_sub_left b _), v.trans (sub_le_sub_right e _)⟩
 have j:ϐ U ≤ u:=by linarith
 exact ⟨L,U,_,a,j,(bell_le _ _ _ _).mp (by linarith only [e,h.1,b]),install_all r dn,run_gap r a j⟩
#print axioms install
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
