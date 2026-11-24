import GaugeFieldConstruction.Hussy
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
local notation "Y"=>Single n
open SeasonH Thera
variable (p r:Bool)(U:UNI (Single n))(B C X Z:Op (Single n))(a:Altaz U p r B C X Z)
-- startup primitive structures $$
lemma formula_r (p:Bool)(B C:Op Y)(Q:if p then star B=B else True)(i j:Y): alter_M B C (p,i) (!p,j)=cSignX p ((if p then B else C) i j):=by
 cases p; rfl
 change B j i=star _; simp only [↓reduceIte] at *; exact (Matrix.ext_iff.mpr Q j i).symm
#print link_l
abbrev ox (x:Bool) := if x then B else C
include a
private lemma peak_Mov (i:Bool): twist U (windX p (ox B C i))=ox X Z (i.xor r):=by
 cases i; change twist _ (windX _ (if false then B else C))=_; rw [if_neg Bool.false_ne_true,a.endo]; cases r<;>rfl
 rw [ox,if_pos rfl,a.auth]; cases r<;> rfl
private lemma Herm_M (i:Bool):star (ox X Z (i.xor r))=ox X Z (i.xor r):=by
 rw [←peak_Mov p r U B C X Z a,← map_star,← win_s]; have hx:star (ox B C i)=ox B C i:=by cases i; exact a.shine1; exact a.shine0
 rw [hx]
lemma duet (b:Bool)(i j:Y): let G:=moko U r b; let Q:=alter_M B C; let Q':=alter_M X Z; let x:=b.xor r;
    ∑ k,G k i* Q' (x,k) (!x,j)=∑ k, cSignX (p.xor r) (Q (b,i) (!b,k)) *star (moko U r (!b) j k):=by
 intro V F F' x
 have he:ox X Z x=suburban p U U (ox B C b):=(peak_Mov p r U _ _ _ _ a _).symm.trans (by rw [twist_formula,suburban,wun])
 have hx:= link_l p r b U U (ox B C b) (ox X Z x) he i j
 change ∑ k,V k i* cSignX x (ox X Z x k j)= _ at hx
 have hp(k:Y): cSignX x (ox X Z x k j)= F' (x,k) (!x,j):= (formula_r x _ _ (by
    by_cases p0:x; · rw [if_pos p0]; have hm:=Herm_M p r U B C X Z a b; change star (ox X Z x)=ox X Z x at hm; rw [p0] at hm; exact hm
    rw [if_neg p0]; trivial) _ _).symm
 have hu(k:Y):cSignX b (ox B C b i k)= F (b,i) (!b,k):= (formula_r b _ _ (by
    by_cases p:b
    · rw [if_pos p]; exact a.shine0
    rw [if_neg p]; trivial) _ _).symm
 have hG: crib U r b=ccU (crib U r (!b)):=link_b (!b) b p r (by simp) U
 simp_rw [hp,hu,hG] at hx; exact hx -- V folded
omit a
-- Figment exterior representation.
variable {J:Type}[LinearOrder J][Fintype J]
def iceK (H:J→J→ℂ) (i:J): FC J:= ∑ j:J,H i j • takeF j
def Icycle (H:J→J→ℂ): J→FC J:=fun i=> put i+iceK H i
lemma heroK(H:J→J→ℂ):Flesh (Icycle H) put (iceK H) H (vacuum J):=by
 refine ⟨put_put,fun i j=>?_,fun i=>?_,fun _=>rfl⟩
 · rw [iceK,antiB_sum]; simp_rw [antiB_smul, show ∀ i j:J,antiB (takeF i) (put j)= if i=j then 1 else 0 from fun i j=>mixed i j]; rw [sum_eq_single j]; simp; intro i _ h; simp [h]; simp
 rw [iceK,act_sum]; exact sum_eq_zero fun j _=> Sault.rock ..
include a
local notation "Q"=> alter_M B C
local notation "H'"=>alter_M X Z
local notation "L"=> lotY p r U
omit a
private lemma trans_L (v:FC (FinV n)):L (star v)=star (L v):=by change sings (p.xor r) _ _= star (sings (p.xor r) _ _); simp only [singT,win_s,map_star]
private lemma leg_downL (x:Bool)(i:Y): L (takeF (n:=FinV n) (x,i))=∑ h:Y,star (moko U r x h i) • takeF (n:=FinV n) (x.xor r,h):=by
    let z:= (x,i)
    rw [show takeF _= star (put (n:=FinV n) (x,i)) from rfl,trans_L, L_mile p r U]
    change star (∑ j:Y,moko U r x j i • put (n:=FinV n) (x.xor r,j))= _; rw [star_sum]
    refine sum_congr rfl fun j _=> ?_; rw [star_smul]
include a
lemma ΗLeg (u:Bool)(i:Y): L (iceK Q (u,i))=∑ j:Y,moko U r u j i • iceK H' (u.xor r,j):=by
 let t:=u.xor r; let P:=moko U r u; let F:=moko U r (!u); let s:=p.xor r; let g(x):= cSignX s x
 have ht(j:Y): L (takeF (n:=FinV n) (!u,j))=∑ h:Y,star (F h j) • takeF (n:=FinV n) (!t,h):=by
    rw [leg_downL p r U (!u) j]
    have hp : (!u).xor r= !t:=by cases u<;>cases r<;>rfl
    rw [hp]
 have hp(P T:Op Y)(u:Bool)(i:Y):iceK (alter_M P T) (u,i)=∑ j:Y,alter_M P T (u,i) (!u,j) • takeF (n:=FinV n) (!u,j):=by
    unfold iceK; rw [Fintype.sum_prod_type, sum_eq_single (!u)]; intro b _ p; apply sum_eq_zero; intro j _; cases u <;>cases b<;>first| contradiction| exact zero_smul ..
    simp
 rw [hp,map_sum]; simp_rw [Ione.G_lot,ht,hp, Finset.smul_sum,smul_smul]; rw [sum_comm]; apply Eq.trans _ ((sum_comm).symm); refine sum_congr rfl fun j _=>?_; rw [←sum_smul,←sum_smul]; apply congrArg (· • takeF (n:=FinV n) (!t,j)); exact (duet p r U B C X Z a u i j).symm
lemma archive_Z (i:Y)(b:Bool): L (Icycle Q (b,i))= ∑ j:Y,moko U r b j i • Icycle H' (b.xor r,j):=by unfold Icycle; simp_rw [smul_add,sum_add_distrib]; rw [map_add,ΗLeg p r U B C X Z a]; exact congrArg (· + _) (L_mile ..)
#print axioms archive_Z
end MastTin
end YM.CF.XGarden
end
