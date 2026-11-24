import GaugeFieldConstruction.Whirls
import GaugeFieldConstruction.Synod
import YM.UVNext.PRICED_KERNELS.Basin
import YM.CF.Yaw.Viv
import GaugeFieldConstruction.Plaid
import GaugeFieldConstruction.Corbie
/- Gauge average phase extensions. -/
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 320000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.XGarden
open Function Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG WilsonStartup Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Matrix.Norms.L2Operator Classical
open Buffered Buffered.Region FlightFlux Fluxim Work Tensor
open Fock Tulip Lat Spire Phase Cube Scroll Paige Vault Phase Spire Branch
open Push.SectorMeasure
attribute [local instance] opCStarAlgebra
variable {n:Side}
namespace MastTin
open Shield Echo Ledger Jet Salt Pastry Hake Urn Levier Hive Nacre Rush Peaks
local notation "GS"=>SU.group
open Next.SectorChange.Motion Ione
open TableF.Lenten TableF.Lenten.Housing TableF.Lenten.Layout
open Haro
open scoped YM.CF.Mew
-- nongauge Hot support label
open Roots GJ Mew Wosk
open Tenant Push.AbsoluteSums Trees
open Sour Sour.SliceRoof
variable (I:Type)[LinearOrder I][Fintype I]
variable {e a d b c f l:ℝ}(F:Elm n Unit e a c)(R:Loom n)(k u:ℝ)(p:BudgetPoint)(m:ℕ)(b0:ℝ)(T:Ids n)
local notation "Y"=> Single n
local notation "eV"=>eBook I F R u m b0 T
local notation "Kern"=> street I F R u m b0 T
variable (v: Roof n u k m R)(h:k<e)(hp:0<e)(v0:0≤b0)(tK:coinH f b0)(z:hud_T 7 f)(t:1 ≤f)(w:p.threshold≤u)(s:p.order≤6)
variable (Z:Finset (Seat n))(A: Pane n)(L:Tulip.Male)(r:ℕ)(uF: NearL F (fun _=>hemi_L n r L))(g:groupShape F)(pw:pure_Rim F)
namespace SeasonH
open Thera
-- e labels pack with clipped half symbol.H_Z not true projector, inverse by formal family proof at this radius
def Lar_M (X:Hubber n): Op Y:=Matrix.of fun i j=> kiosk X m u R T (fun A=> releaseQ F X A i j) A
lemma lar_C (X:Hubber n): Lar_M F R u m T A X=if flag_H X m u A then releaseQ F X (R (A,T)) else 0:=by split<;>next h=> ext; simp only [Lar_M,kiosk,h,↓reduceIte, Matrix.of_apply ] <;> first|rfl|done -- no goal after tactic
abbrev costχ(X:Hubber n):Prop:= Sect X m⊆Z
def Moon_M : Op Y:= ∑ i:Hubber n, if Sect i m⊆Z then Lar_M F R u m T A i else 0
attribute [local simp] Matrix.of_apply
include h v hp t v0 tK
private lemma Lem_Burn(i j:Y)(x:Hubber n)(q:F.W x i j=0):Lar_M F R u m T A x i j=0:=by
 let G:= (LArmor0 Unit F R k u m b0 T v h hp v0 tK i j x).1; exact congrFun (houseZ v h T t x _ G (by unfold LemKer; rw [q,mul_zero])) A
lemma budgetL (x:Key I)(i j:Y): Lee (eV i j) (fun t=>egest t Z x A)= Moon_M F R u m T Z A i j:=by
 unfold eBook; rw [mapA,Lee,leafage,Moon_M]; simp_rw [Matrix.sum_apply]; let g(S):=egest (LemKer I F R u m b0 T i j S) Z x A
 have h0(X:Hubber n): (if Sect X m⊆ Z then Lar_M F R u m T A X else 0) i j=g X:=by
    unfold g egest LemKer GJ.stalk; split; next he => simp only [he,↓reduceIte,List.map_nil,List.prod_nil,one_smul]; rfl
    rfl
 simp_rw [h0]; change ∑ S∈ _,g S= _; apply Finset.sum_subset (s₁:={i₀ | F.W i₀ i j ≠ 0}) (subset_univ _); intro i0 y H; rw [←h0]; split; exact Lem_Burn F R k u m b0 T v h hp v0 tK t _ i j i0 (by simpa using H); rfl
omit h v hp v0 tK t
abbrev halfP(X:Hubber n): Op Y:= Matrix.diagonal (fun i=> if Ekm n (true,i) ∈ X then (1:ℂ)/2 else 0)
def alter_M (B C:Op Y):FinV n→ FinV n→ℂ
| (true,i),(false,j)=> B j i
| (false,i),(true,j)=> C i j
| _,_=>0
abbrev rayP (P:Op Y):= alter_M P (1-P)
abbrev blade0 : Op Y:= halfP Z+ Moon_M F R u m T Z A
abbrev blade1 : Op Y:= halfP Z- Moon_M F R u m T Z A
abbrev frame0 := alter_M (blade0 F R u m T Z A) (blade1 F R u m T Z A)
private lemma halfL(x:Key I)(i j:Y): Lee (unitK I i j) (fun t=>egest t Z x A)=halfP Z i j:=by
 unfold unitK halfP; split
 next w=> subst j; simp [baseK,egest,GJ.stalk,Lee,Matrix.diagonal_apply]
 next w=> simp [egest,GJ.stalk,Lee,w,Matrix.diagonal_apply]
include h v hp v0 tK t
lemma dimL (x:Key I):cryH Kern Z x A=frame0 F R u m T Z A:=by
 funext i j; rcases i with ⟨i,V⟩; rcases j with ⟨j,S⟩; cases i<;> cases j; · rfl
 · unfold cryH; simp only [street,appA,mapA,e_mer, halfL]; rw [show Lee (eV V S) (fun t=> -egest t Z x A)= - Lee (eV V S) (fun t=>egest t Z x A) from sealA _ _ (-AddMonoidHom.id ℂ)|>.symm, budgetL I F R k u m b0 T v h hp v0 tK t Z A]; change _=halfP Z V S-Moon_M F R u m T Z A V S; abel
 · unfold cryH; simp only [street,appA, halfL]; rw [budgetL I F R k u m b0 T v h hp v0 tK t Z A]; change _=halfP Z S V+ _; unfold halfP; rw [Matrix.diagonal_apply, Matrix.diagonal_apply]; by_cases g:V=S <;> simp [g,Ne.symm] -- tune
 rfl
include w uF
omit v0 tK t
lemma Moon_true (q: flags p.threshold A=∅): Moon_M F R u m T Finset.univ A= Dial.spar r L A-halfBand n:=by
 unfold Moon_M; simp_rw [if_pos (subset_univ _),lar_C F R u m T A,if_pos (flag_off m u _ _ q w),roof_elem v T A q w]; have he:A∈ Clode n e:=Ledger.top_strict v h q w
 have hb: Guard A e:= interior_subset (s:={x:Pane n|Guard x e}) he; simp_rw [re_L F _ _ hb hp]; exact (uF () (light e A hp hb) A hb rfl).symm
end SeasonH
end MastTin
end YM.CF.XGarden
end
