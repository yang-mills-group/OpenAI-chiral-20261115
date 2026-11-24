import GaugeFieldConstruction.«PlatoΘ3»
import GaugeFieldConstruction.Sommar
set_option autoImplicit false
set_option quotPrecheck false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 60000
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Scree.Ing
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree
open Skye Scree Vow Hake Jet Fock
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open Cube Lat Tulip Peaks
attribute [local instance] opCStarAlgebra
open Rush Scroll Paige Vault Phase Acorn Spire
open scoped YM.CF.Mew
open BasisI Roots GJ Mew Lattice.Corona.Hive
open Py.Rate.Pitching.Focus.CoeffArc
open Pastry Grotto
namespace Ivey
open Sault Leaf Sour
open Ladder3 Drapes Tenant Palot Rue Iona
attribute [local instance] loreM loreN
variable {n: Side}{I α β γ G:Type}[LinearOrder I][Fintype I][Fintype α][Fintype β][Fintype γ]
-- old bank
namespace ShoreQ
open Tuner
variable (P:BudgetPoint)
namespace Argos
variable (Q:LeaseQ γ n)(C:Factor3 n)(F:RegLime I α n)(V:Mica I β n)(k:I)
section
variable (G W:Orbit n)
local notation "SC"=> Support (More n)
local notation "𝕏"=> FC (Dwell n)
local notation "Dk"=> Cipher n
variable (H:Hub n)(p d:ℕ)(L:Fin p→γ)(r:Fin d→α)
abbrev RangeG := (p+d ≤ fadeN C)
variable (z:Key I)
-- Raw models all over F♭. For K, Pack.FL.X.J root.
variable (S X D:Support (More n))(U:Support (More n) → FC (Dwell n))(R:Support (More n) → α→Cipher n)
-- model.C.S.PI.
def CGrant (Z:Support (More n)→ FC (Dwell n))(Y:Support (More n))(D:Support (More n))(A:Cipher n): FC (Dwell n):=
 rind (Z D*A.val)-(if Disjoint Y D then Sault.rind (Z ∅)*A.val else 0)
section geom
variable {n:Side}
open Sault
lemma grant_Ax {α:Type}(i:Finset α)(f:α→ Cipher n)(Z:Support (More n) → FC (Dwell n))(Y D:Support (More n)) : CGrant Z Y D (∑ j∈i,f j)=∑ j∈i,CGrant Z Y D (f j):=by
 let V':= (Dough (Dwell n)).val; unfold CGrant; rw [Finset.sum_sub_distrib]; change Sault.rind (_*V' _) - _= _; rw [map_sum,mul_sum,Sault.rind,map_sum]; congr 1; split; · change _* (V' _)=_; rw[map_sum,mul_sum]; rfl
 exact (Finset.sum_const_zero).symm
lemma grant_AX {γ:Type}(i:Finset γ)(f:γ→Support (More n) → FC (Dwell n))(Y D:Support (More n))(w:Cipher n): CGrant (fun S=>∑ j∈i,f j S) Y D w=∑ j∈i,CGrant (f j) Y D w:=by
 unfold CGrant; rw [Finset.sum_sub_distrib,sum_mul,Sault.rind,map_sum]; congr 1; split; · simp only [sum_mul,map_sum] -- tune ite simp
 exact (Finset.sum_const_zero).symm
lemma grant_Aτ (V:Support (More n)→FC (Dwell n))(Y D:Support (More n))(A:Cipher n)(r c:ℂ):CGrant (r • V) Y D (c • A)= (r*c) • CGrant V Y D A:=by
 unfold CGrant; change Sault.rind (_* (c • A.val))-(if Disjoint Y D then Sault.rind (r • _) * (c • A.val) else 0)=_; unfold Sault.rind
 simp_rw [Pi.smul_apply,smul_sub,Algebra.smul_mul_assoc r,Algebra.mul_smul_comm c,map_smul]; split_ifs <;> simp [smul_smul,mul_comm r c]
end geom
section
variable (A:Heart C.H Q.H p)(u:Heart H F.S d)
local notation "Zp"=>Legist H F.S d u
local notation "SΛ"=>(Legist H F.S d u).val.2
local notation "Body_" D:max=>BodyX Q p d A.val u.val D W (C.issue D W)
variable (hp:p+d≤fadeN C)(s:∀ D:Support (More n), Fock.Sector univ false (C.issue D W))
local notation "Φ"=> peatE F C Q k p d hp A H
local notation "rσ" j:max=> carR z (F.V j)
def wax_κ (F:RegLime I α n)(x:Key I)(W:Orbit n) :=fun (D:Support (More n))(i:α)=> carR x (F.V i) • F.K i D W
include s
lemma νpure (g:Ids n)(e:∀ j,C.issue ∅ (W.1,j)=C.issue ∅ W)(e':∀ i j,Q.issue i ∅ (W.1,j)=Q.issue i ∅ W)(h:∀ i j,F.K i ∅ (W.1,j)=F.K i ∅ W): (carR z (tags F d H u)) • (((pureT V Φ g).termR u W.1).val)= Sault.rind (BodyX Q p d A.val u.val ∅ W (C.issue ∅ W) (wax_κ F z W ∅)):=by -- pureT V Φ args verify
 let Rwα:= fun D=> BodyX Q p d A.val u.val D W (C.issue D W) (fun j=>F.K j D W)
 let b:= (W.1,g)
 have hm: filmic F C Q p d A H u ∅ b= Rwα ∅:=by
    rw [ScaEq]; unfold Rwα BodyX; unfold b; simp_rw[e',h,e]
 change _ • (fair (filmic F C Q p d A H u ∅ (W.1,g))).val= _; rw[show filmic F C Q p d A H u ∅ (W.1,g)= _ from hm, show (fair _).val= _ from ScaLight Q C p d _ _ _ W _ (s ∅)] -- tune
 unfold tags wax_κ; rw [roster_N, body_rate Q p d A.val u.val ∅ W (C.issue ∅ W) (fun i=> F.K i ∅ W) (fun i=> rσ i)]; unfold Sault.rind BodyX; simp only [map_smul]
lemma νboat (M: Finset β): let P:=Legist H F.S d u; let L:= fun D=> BodyX Q p d A.val u.val D W (C.issue D W) (wax_κ F z W D); carR z ((tags F d H u) ++ V.legend M) • (((busyT V Φ).termB u M W).val)= CGrant L P.val.2 (til V.z M) (∏ i∈M,Mu_z V z i W):=by
 intro P' L
 let E:=V.legend M; let Z:= tags F d H u; let G:=∏ i∈M, V.K i W; let D:= til V.z M; let Y:= fun D=> BodyX Q p d A.val u.val D W (C.issue D W) (fun j=>F.K j D W)
 let r:= carR z Z; let e:= carR z E
 have hL: L=r • Y:=by
    funext i; unfold L wax_κ; change _= r • (Y i); rw[show r= _ from roster_N (univ:Finset (Fin d)) (fun i=> F.V (u.val i)) z]; exact body_rate Q p d _ _ _ _ _ _ (fun i=> rσ i) -- tune notation invalid syntax r
 have he: e • G=∏ i∈M,Mu_z V z i W:= roster_M M V.V (fun i=> V.K i W) z
 have hz: filmic F C Q p d A H u D W=Y D:=ScaEq .. -- tune
 have h0: filmic F C Q p d A H u ∅ W=Y ∅:=ScaEq ..
 have hu: ((busyT V Φ).termB u M W).val=CGrant Y SΛ D G:=by
    change (fair (filmic F C Q p d A H u D W * ((∏ i∈ M,V.K i) W).val)).val - (((if Disjoint SΛ D then _*_ else 0):Copy n) W).val= _
    rw [Finset.prod_apply, hz]; have hG : Sector univ false (Y D):= (ψScar C D W (s D) _).scale _; -- how put syntax
    have hp: (fair (Y D*G.val)).val=Sault.rind (Y D*G.val):=by unfold fair; rw [dif_pos (light_e (hG.mul (life (fineShape G))))]
    rw [show ((∏ i∈M, V.K i W):Cipher n)=G from rfl,hp]; unfold CGrant; split_ifs
    · change _ - (fair (filmic F C Q p d A H u ∅ W)).val* ((∏ i∈M,V.K i) W).val= _
      rw [Finset.prod_apply,h0, show (fair _).val=_ from ScaLight Q C p d A.val u.val ∅ W (fun j=>F.K j ∅ W) (s ∅)] -- tune args
    rfl
 rw [hu,hL,←he,grant_Aτ,show carR z (tags F d H u ++ V.legend M)=r*e from (by unfold carR; rw[List.map_append,List.prod_append])] -- car not defeq
#print axioms νboat
end
end
end Argos
end ShoreQ
end Ivey
end YM.CF.Scree.Ing
end
