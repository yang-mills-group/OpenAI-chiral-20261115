import YM.CF.Vp929.Canon.Plum
import YM.CF.Moto.Thistle
import YM.CF.Iva.Cart
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option linter.flexible false
noncomputable section
namespace YM.CF.Py.Rate
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open AnalyticBridge.Annulus1AD Ac Esti
open Atala Forge Cloak Rill Hive Fock Stilo Palot Scion
open Cube Lat Tenant Tulip
open Pastry Hake Levier Urn Peaks Fock Laic Branch Drapes
attribute [local instance] opCStarAlgebra
open Rush Scroll Paige Vault Phase Acorn Spire
attribute [local instance] opCStarAlgebra
open Tarn Cay Slate Esti Cour Hest Arena Reine Kennel Facet Broc Pec Push.SectorMeasure.Oriented
open Hom Vale Vale.Grace Next.Free Thera Nacre Dial Fock
open Tye Lich Stake Pail Pail.Dew
open Ione Beau Haro Cascade Fief
open scoped Mew

open Taxi RG.PathData Next.Scheduling UVNext.PricedKernels Work.F03 WilsonStartup
open Jet Yaw Nor Prism Font Push.AbsoluteSums Wray
open Next.Foundations Push.Local AnalyticBridge.VerifiedReset Vow Rue
namespace Test
namespace Plum
section core
variable {I:Type}[LinearOrder I][Fintype I]
local notation "τ"=> Wave I
local notation "Br"=> ribbon I
variable {P:Op I}{X:ribbon I}{p: Wave I} (u:IsStarProjection P)(s:Sea P p)
include u s
lemma stampK (h:acts (tank P X) p=0): (1-P)*orbitPH X* P=0:=by
 obtain ⟨U,L,rfl⟩:= spot_projection P u; let V:= quantU U; let C:=Fock.cutM L; let A:= twist U C; let Z:=star U; let F:= paintR false false Z X; let W:=Fock.wedge U.val L; let c:= inner ℂ W p
 have hp:p=c • W:=s.1.symm.trans (act_twistLine ..); have hB:c≠0:=by intro e; have hb:= s.2; rw [hp,e,zero_smul,norm_zero] at hb; linarith
 have he:acts (tank A X) (acts V.val (basisKet L))=0:=by
    rw [hp,map_smul] at h; have hx:= (smul_eq_zero.mp h).resolve_left hB; exact (show W=acts V.val (basisKet L) from (quant_column ..).symm) ▸ hx
 have hg: twist Z A=C:=twist_inv ..; have hV:twist (star V) (tank A X)=tank C F:=by
    rw [←quantU_star]; exact appleT u (cutM_idp L) false false (star U) hg X
 have hW: acts (tank C F) (basisKet L)=0:=by
    have ht:= congrArg (acts (star V.val)) he; rw [map_zero] at ht; change acts (star V:UNI (Finset I)).val _=0 at ht; rw [Fock.swivel,hV] at ht; exact (show acts (star V:UNI (Finset I)).val (acts V.val (basisKet L))=basisKet L from act_unit ..) ▸ ht
 have Hz:orbitPH F=twist Z (orbitPH X):=Haro.paral X false false Z
 apply (twist Z).injective; simp only [map_mul,map_zero,map_sub,map_one]; change (1-twist Z A)* _* twist Z A=_; rw [hg]; change (1-C)* (twist Z (orbitPH X))*C =_; rw [←Hz]; exact projected0 F hW
omit u s
lemma sinkH (A:ℂ)(h:IsStarProjection P): tank P (Pastry.hollow A)= A • (1: FC I):=by
 change (nursery P h).eval (A • (1:FC (LeanV I)))=_; rw [map_smul,(nursery P h).eval_one]
end core
section bound
variable {m:Side}
local notation "Ω"=> Single m
variable {P:Op (Single m)}{X Y:Cipher m}{p:Wave (Single m)} {a b:ℂ}
local notation "Pλ"=> Pastry.pane
local notation "TE"=> tank P
variable (u:IsStarProjection P)(v:Sea P p)
include u v
lemma rootExp (H:Complex.exp a • acts (TE (exp X)) p= Complex.exp b • acts (TE (exp Y)) p): (1-P)*orbitPH X*P=(1-P)*orbitPH Y*P:=by
 let W:= cloudless (X-Y); let T:= (nursery P u).cook
 have ht:Pλ W=0:= cloudless_two _
 let z:= hollow (n:=LeanV Ω) (Pλ (X-Y)); have hw: X=W+Y+z:=by unfold W cloudless z; abel

 letI : NormedAlgebra ℚ (Cipher m):= NormedAlgebra.restrictScalars ℚ ℝ (Cipher m)
 let U:= acts (T (exp (-(Y+z))))
 have hv:U (acts (T (exp X)) p)=acts (TE (exp W)) p:=by unfold U; rw [←act_mul,←map_mul,←exp_add,show (-(Y+z))+X=W by unfold z W cloudless; abel]; rfl
 have hz:U (acts (T (exp Y)) p)=Complex.exp (-(Pλ (X-Y))) • p:=by
    unfold U; rw [←act_mul,←map_mul,←exp_add,show -(Y+z)+Y= - z by abel]; change acts (TE _) p= _; rw [show -z=hollow (-Pλ (X-Y)) from ?_,← Iva.yeaH,sinkH _ u,act_smul,act_one]; exact Subtype.ext (Eq.symm (neg_smul (Pλ (X-Y)) (1:FC (LeanV Ω))))
 let β:= Complex.exp b * Complex.exp (-(Pλ (X-Y))); let Xp:= exp W; let a:=Complex.exp a;
 have hP:a • acts (TE Xp) p=β • p:=by rw [←hv,← map_smul]; change U (_ • acts (TE _) p)=_; rw [H]; rw [map_smul]; change Complex.exp b • U (acts (T (exp Y)) p)=_; rw [hz,smul_smul]
 have he:a=β:=by
    have hx:=congrArg (inner ℂ p) hP
    rw [inner_smul_right,inner_smul_right,testTank u v,paneExp,ht,Complex.exp_zero,mul_one,inner_self_eq_norm_sq_to_K] at hx; simpa only [v.2,one_pow,RCLike.ofReal_one,mul_one] using hx
 have hY:=smul_right_injective (M:=Wave (Single m)) (R:=ℂ) (show a ≠ 0 from Complex.exp_ne_zero _); rw [←he] at hP; have hx:acts (TE (exp W-1)) p=0:=by change acts (T _) p=_; rw [map_sub,map_one,act_sub,act_one]; exact sub_eq_zero.mpr (hY hP)
 have h:= stampK u v hx; rw [Moto.peak_l W ht] at h; unfold W cloudless at h; simp_rw [Moto.tail_K,Moto.hol_l,sub_zero,mul_sub,sub_mul] at h; simp only [sub_mul]; exact sub_eq_zero.mp h
end bound
end Plum
end Test
end YM.CF.Py.Rate
