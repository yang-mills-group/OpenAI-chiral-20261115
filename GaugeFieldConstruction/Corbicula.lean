import GaugeFieldConstruction.Pilote
import YM.CF.Urn.Ione
import YM.CF.Ione.Rake
import YM.CF.Urn.Role
/- Symmetry on tensors. Use moves Lie with charge bits for phase-axis consent. -/
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 140000
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
open Shield Echo Ledger Jet Salt Pastry Hake Urn Levier Hive
local notation "GS"=>SU.group
abbrev ChartP(n:Side):= Wa n→ℂ
variable (U V: UNI (Single n)) (p t:Bool)
-- order out left/right. xp flips with xor.
local notation "c∗"=>cSignX
abbrev sealC (K:ChartP n)(x:Bool): Op (Single n) := Matrix.of fun i j=> K (some (x,i,j))
abbrev moko (i:Bool):Op (Single n):= (crib U t i).val
-- col(moved) bottom old.
def steerZ (A:ChartP n) : ChartP n
 | none => cSignX (p.xor t) (A none)
 | some (x,j,k) => let i:= x.xor t; (moko U t i * windX (p.xor t) (sealC A i)* (moko U t (!i))ᵀ) j k
private lemma rider_v{m:Type*}[LinearOrder m][Fintype m](F:Op m)(x:Bool)(i j:m): (windX x F) i j=cSignX x (F i j):=by cases x <;>rfl
lemma seal_D(A:ChartP n)(i:Bool): sealC (steerZ U p t A) (i.xor t)=moko U t i*windX (p.xor t) (sealC A i)*(moko U t (!i))ᵀ:=by
 ext x y; unfold sealC steerZ; simp [xor_assoc] -- Tune Bool
-- compositional seed. Proof implements copied seat.
private lemma fee_comp (b r c:Bool): moko V b (c.xor t) * windX (r.xor b) (moko U t c)= feeJ t (b.xor r) • moko (V*whiten r U) (t.xor b) c:=by
 cases t <;>cases c <;>cases b <;>cases r <;> simp [moko,crib,Pastry.thread,whiten,windX,ccU,feeJ,filmG, Matrix.smul_mul,Matrix.mul_smul,smul_smul,cc_mul,cc_smul]
private lemma wind_x (A:Op (Single n))(B:Bool) :windX B Aᵀ=(windX B A)ᵀ:=by cases B <;> rfl
lemma convoyZ (A:ChartP n)(b c:Bool): steerZ V b c (steerZ U p t A)= steerZ (V*whiten b U) (p.xor b) (t.xor c) A:=by
 let W:= V*whiten b U; let Y:=steerZ U p t A; let h:=feeJ t (c.xor b); let s:=t.xor c
 have he: h*h=1:=by unfold h feeJ; split_ifs <;> ring
 let d:= (p.xor b).xor s; let X0:=steerZ V b c Y; let X':=steerZ W (p.xor b) (t.xor c) A
 have hp(i:Bool): sealC X0 (i.xor s) = sealC X' (i.xor s):=by
    rw [show sealC X' (i.xor s) = _ from seal_D W (p.xor b) s A i]
    have ht: (i.xor t).xor c=i.xor s:=by unfold s; rw [Bool.xor_assoc]
    have hv: sealC X0 (i.xor s)=moko V c (i.xor t)*windX (b.xor c) (sealC Y (i.xor t))*(moko V c ((!i).xor t))ᵀ:=by rw [←ht]; convert seal_D V b c Y (i.xor t) using 1 <;> cases i <;> cases t <;> simp
    rw [hv, show sealC Y (i.xor t)=_ from seal_D U p t A i]; let Z(Q:Op (Single n)):=windX (b.xor c) Q; rw [win_m,win_m]
    let T:= sealC A i; let Q:=moko V c (i.xor t); let R:=moko V c ((!i).xor t); let e':= moko U t i; let e:=moko U t (!i); let A0:=windX (p.xor t) T
    change Q*(Z (e') * Z A0* Z eᵀ)*Rᵀ=_
    rw [show Z (eᵀ)=(Z e)ᵀ from wind_x e _,show Q*_ *Rᵀ= (Q*Z e') * Z A0 * (R*Z e)ᵀ from (by rw [Matrix.transpose_mul]; simp only [mul_assoc]), show Q*Z e'= h • moko W s i from fee_comp U V t c b i, show R*Z e=h • moko W s (!i) from fee_comp U V t c b _, show Z A0=windX d T from ?_,Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul, smul_smul,he,one_smul]
    unfold Z A0 d s; cases b <;>cases c<;> cases p<;>cases t<;> simp [windX,cc_cc]
 funext i
 cases i with
 | none=> cases p <;>cases b <;> cases c<;> cases t<;> simp [steerZ,cSignX]
 | some i=> obtain ⟨x,y,v⟩:=i; have he:= Matrix.ext_iff.mpr (hp (x.xor s)) y v; rw [show ((x.xor s).xor s)=x from (by rw [Bool.xor_assoc]; simp)] at he; exact he
lemma rayZ{z:ℂ}(g:U.val=z • V.val)(k:z^2=1)(h:star z=z)(A:ChartP n): steerZ U p t A=steerZ V p t A:=by
 have hx(i):moko U t i=z • moko V t i:=by cases i <;> cases t <;> simp only [moko,Urn.crib,Pastry.thread] <;> simp [filmG,ccU,g,cc_smul,h,smul_comm z]
 funext i; cases i with
 | none=> rfl
 | some i=> rcases i with ⟨i,j,k'⟩; simp only [steerZ]; rw [hx,hx,Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul,smul_smul, ←sq,k,one_smul]
lemma one_S (A:ChartP n):steerZ 1 false false A=A:=by funext i; cases i with| none=>rfl| some i=>rcases i with ⟨i,j,k⟩; unfold steerZ; cases i <;> simp [moko,sealC,windX,crib,thread,ccU] -- tune name
-- physics payment
abbrev αLines(A:Paper n)(v:Pane n) : ChartP n:=fun i=> A i v
lemma swipe_u (x:Bool)(i j:Single n)(A: ChartP n) :steerZ U p t A (some (x.xor t,i,j))= ∑ q:Single n,∑ k:Single n,cSignX (p.xor t) (A (some (x,q,k))) * (moko U t x i q * moko U t (!x) j k):=by
 change sealC (steerZ U p t A) _ _ _=_; rw [seal_D]; simp_rw [Matrix.mul_apply,sum_mul]; rw [sum_comm]; apply sum_congr rfl; intro q _; apply sum_congr rfl; intro k _; rw [rider_v]; rw [Matrix.transpose_apply]; unfold sealC; simp only [Matrix.of_apply]; ring
private lemma swapRx {I D:Type}[Fintype I][AddCommMonoid D](f:I→I→I→I→D): (∑ i:I,∑ j:I,∑ k:I,∑ l:I,f i j k l)=∑ k:I,∑ l:I,∑ i:I,∑ j:I,f i j k l:=by
 conv_lhs => arg 2; intro i; rw [sum_comm (f:=fun j k:I=>∑ l:I,f i j k l)]; arg 2; intro k; rw [sum_comm (f:=fun j l:I=> f i j k l)]
 rw [sum_comm]; apply sum_congr rfl; intro i _; rw [sum_comm (f:=fun j k:I=>∑ l:I,f j l i k)]
lemma migrate {E:Type}[NormedRing E][NormedAlgebra ℂ E](F:E→+*E) (b:Bool→ Single n→E)(h:∀ x i, F (b x i)= ∑ j:Single n,moko U t x j i • b (x.xor t) j)(w:∀ v:ℂ,∀ y:E,F (v • y)=cSignX (p.xor t) v • F y)(D:Wa n→E)(d:D none=1)(e:∀ (x:Bool)(i j: Single n),D (some (x,i,j))=b x i * b (!x) j) (A:ChartP n):
 F (∑ j:Wa n,A j • D j)=∑ j:Wa n, steerZ U p t A j • D j:=by
 let V:=steerZ U p t A
 let s (x:Bool):= x.xor t;
 have hh(x): F (∑ i:Single n,∑ j:Single n,A (some (x,i,j)) • D (some (x,i,j)))=∑ i:Single n,∑ j:Single n,V (some (x.xor t,i,j)) • D (some (x.xor t,i,j)):=by
    unfold V; rw [map_sum F]; simp_rw [map_sum F]; simp_rw [e,w,map_mul F,h,sum_mul,mul_sum, swipe_u, Finset.smul_sum, Finset.sum_smul, Algebra.smul_mul_assoc,Algebra.mul_smul_comm,smul_smul]; -- maybe sum_mul loops?
    let he: (!x).xor t = !(x.xor t):=by cases x <;> cases t<;> rfl
    simp_rw [he]; exact swapRx _
 rw [Fintype.sum_option,Fintype.sum_option]; simp_rw [Fintype.sum_prod_type (α₁:=Bool) (α₂:=Single n × Single n), Fintype.sum_prod_type (α₁:=Single n) (α₂:=Single n)]; rw [map_add]; -- tune eta
 apply congrArg₂ (· + ·)
 · rw [d,w,map_one]; rfl
 rw [map_sum]; -- Goal bool; get p explicit. 
 change (∑ x:Bool,F (∑ i:Single n,∑ j:Single n,A (some (x,i,j)) • D (some (x,i,j)))) = ∑ x:Bool,∑ i:Single n,∑ j:Single n,V (some (x,i,j)) • D (some (x,i,j))
 simp_rw [hh]; let L(x:Bool):=∑ i:Single n,∑ j:Single n,V (some (x,i,j)) • D (some (x,i,j))
 let E: Bool ≃ Bool:=⟨s,s,fun i=>by simp [s,Bool.xor_assoc],fun i=>by simp [s,Bool.xor_assoc]⟩; exact Equiv.sum_comp E L

def tokenZ (x:Wa n) : FC (LeanV (Single n)) := match x with
 | none=>1
 | some (b,i,j)=> put (b,i)*put (!b,j)
lemma exportD (x:ChartP n): let W:=fun A:ChartP n=> ∑ i:Wa n,A i • dot_Q i; lotB p t U (W x)= W (steerZ U p t x):=by
 intro W; apply migrate U p t (lotB p t U) (fun x i=> bell (x,i)) (fun x i=>?_ ) (fun v y=> Urn.visage ..) (fun i:Wa n=> dot_Q i) rfl (fun x i j=> by cases x <;> rfl)
 rw [Urn.mole]; unfold roseB; rw [Fintype.sum_prod_type,sum_eq_single (x.xor t)];
 · apply sum_congr rfl; intro j _; unfold sewV; rw [Urn.cream, if_pos rfl]
 · intro a _ w; apply sum_eq_zero; intro i _; unfold sewV; rw [Urn.cream,if_neg w,zero_smul]
 simp
lemma exportV (X:ChartP n) : let Y:=fun A:ChartP n=>∑ i:Wa n,A i • tokenZ i; lotY p t U (Y X)= Y (steerZ U p t X):=by
 intro Y; exact migrate U p t (lotY p t U) (fun x i=> put (x,i)) (fun x i=> Ione.L_mile ..) (fun v y=> Ione.G_lot ..) tokenZ rfl (fun x i j=> rfl) X
end MastTin
end YM.CF.XGarden
end
