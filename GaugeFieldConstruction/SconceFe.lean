import GaugeFieldConstruction.CodaFe
import YM.CF.Pyx.Like
set_option autoImplicit false
set_option maxHeartbeats 35000
set_option quotPrecheck false
set_option synthInstance.maxSize 22000
noncomputable section
namespace YM.CF.BrentFe
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory Precision Tree Push.SectorMeasure
open Cube SU Fock Skye Scree Spire Dial Laic Pec Hest Hive
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
open Rush Tulip Vault Paige Drapes Peaks Brace Branch Lat Kennel CF.Jet Pressure

open YM.GaugeFieldConstruction (Flavor)
open YM.GaugeFieldConstruction.Flavor

def player (f:Bool→ Op CrewFe):Op Slot:= YM.GaugeFieldConstruction.Matter.coeffs (fun i=> f i.1 i.2.1 i.2.2)
lemma player_v (f:Bool→Op CrewFe)(x y:Slot): player f x y=if x.2=y.2 then f (tagged x.2) x.1 y.1 else 0:=wear ..
lemma player_u : player 1=1:=by ext ⟨x,a⟩ ⟨y,b⟩; by_cases e:a=b <;> by_cases p:x=y <;> simp [player_v,Matrix.one_apply,e,p]
lemma player_m (f g:Bool→Op CrewFe): player (f*g)=player f*player g:=by
 apply Matrix.ext; intro ⟨x,a⟩ ⟨y,b⟩; rw[player_v, Matrix.mul_apply, Fintype.sum_prod_type]; by_cases p:a=b
 · subst b; simp only [player_v, ite_true, Pi.mul_apply,Matrix.mul_apply]; refine sum_congr rfl fun i h=>?_ ; rw [sum_eq_single a]; simp
   · intro _ _ hm; simp [hm]; -- tune
   simp
 rw [if_neg p]; simp_rw[player_v]; symm; apply sum_eq_zero; intro i h; apply sum_eq_zero; intro j q
 change (if a=j then _ else _) * (if j=b then _ else _)=0; split_ifs <;> (first|expose_names; grind|simp)
lemma player_s (f:Bool→Op CrewFe): player (star f)=star (player f):=by
 ext i j; by_cases p:i.2=j.2
 · simp [player_v,p]
 simp [player_v,p,Ne.symm p]
abbrev ΨsFe (x: BigFe): Bool→ Op CrewFe:= fun i=> (x i).val
lemma play_h (x:BigFe): player (ΨsFe x) ∈ unitary _:=by
 let y:=ΨsFe x; have h:star y * y=1:=funext fun i=> (x i).property.1; have p:star (player y)*player y=1:=by rw [←player_s,←player_m,h,player_u]; -- avoid orbit
 exact ⟨p,mul_eq_one_comm.mp p⟩
def Ferr : BigFe→* UNI Slot where
 toFun i:=⟨_,play_h i⟩
 map_mul' x y:= Subtype.ext (player_m (ΨsFe x) (ΨsFe y))
 map_one':= Subtype.ext player_u

abbrev TkFe(I:Type*)[Fintype I][DecidableEq I] (v:Op Slot):Op (I×Slot):=(1:Op I)⊗ₖv
def RiseFe(I:Type*)[Fintype I][DecidableEq I] : BigFe→* UNI (I×Slot) where
 toFun i:= ⟨TkFe I (Ferr i).val,by
    let M:= (Ferr i).val
    have ht:star ((1:Op I)⊗ₖ M)* ((1:Op I)⊗ₖ M)= (1:Op (I×Slot)):=by rw[op_star_kron]; change (star (1:Op I)⊗ₖ star M)*((1:Op I)⊗ₖM)=1; rw [op_kron_mul,mul_one,(Ferr i).property.1,star_one,Matrix.one_kronecker_one] -- implicit ?_
    exact ⟨ht,mul_eq_one_comm.mp ht⟩⟩
 map_mul' x y:= Subtype.ext (by
    rw [map_mul]; change TkFe I ((Ferr x).val*(Ferr y).val)=TkFe I (Ferr x).val*TkFe I (Ferr y).val; exact (by unfold TkFe; rw [op_kron_mul]; simp)) -- tune
 map_one' := Subtype.ext (by rw[map_one]; exact Matrix.one_kronecker_one)
abbrev FieldFe(N:Side) : BigFe→* UNI (Single N):= RiseFe _
lemma projectXP {I:Type*}[Fintype I][DecidableEq I](U:UNI I)(P:Op I)(h:twist U P=P): twist U (projector P)=projector P:=by
 have hx(i:ℕ): twist U (rsTerm P i)=rsTerm P i:=by simp only [rsTerm,slack,sq,map_smul,map_pow,map_sub,map_one,map_mul,h]
 have he:twist U (rsEval P)= rsEval P:=by
    have ht(V:UNI I):Continuous (twist V):=by change Continuous (fun P=>V.val*P*star V.val); fun_prop
    unfold rsEval; change (twist U).toRingEquiv.toAddMonoidHom _=_; rw [Function.LeftInverse.map_tsum (g:=(twist U).toRingEquiv.toAddMonoidHom) (g':=twist (star U)) (rsTerm P) (ht U) (ht _) (fun v=>twist_inv U v)]
    exact tsum_congr hx

 simp only [projector,polarity,map_smul,map_add,map_mul,map_one,h,he]

lemma twistFE {I:Type*}[Fintype I][DecidableEq I](U:UNI I)(P:Op I)(h:U.val*P=P*U.val): twist U P=P:=by rw [twist_formula,h,mul_assoc,U.property.2,mul_one]
variable {n:Side}
abbrev coΛ(N:Side)(x:BigFe):UNI (Model N):= Lat.conjG Ferr (fun _=>x)
lemma FieldPay (x:BigFe): (FieldFe n x).val=love n (coΛ n x).val:=by
 let M:=(Ferr x).val; ext ⟨⟨p,b⟩,j⟩ ⟨⟨q,c⟩,k⟩; change TkFe _ M _ _= jump (Equiv.refl (Site n)) (fun _=>(1:Op SpinIdx) ⊗ₖ M) (p,b,j) (q,c,k); by_cases h:p=q <;> by_cases v:b=c <;> simp [TkFe,h,v,jump_apply]
lemma twistField(x:BigFe)(A: Op (Model n)) : love n (twist (coΛ n x) A)=twist (FieldFe n x) (love n A):=by rw [twist_formula,twist_formula,map_mul,map_mul,map_star,FieldPay]
variable (x: BigFe)(U:Bkg (More n))
lemma χ_shift (i:Axis) : twist (coΛ n x) (Lat.shift matter (links U) (anticut n) i)= Lat.shift matter (links U) (anticut n) i:=by
 apply twistFE; simp only [coΛ, conjG, Lat.shift, jump_mul,Equiv.refl_apply, Equiv.refl_trans,Equiv.trans_refl]; congr 1; ext1 j
 unfold Lat.hop; rw [Algebra.mul_smul_comm, Algebra.smul_mul_assoc]; simp only [Lat.color,op_kron_mul, mul_one]; congr 2; exact (YM.GaugeFieldConstruction.Matter.coeff_ok _ _).symm
lemma dome_Fe : twist (FieldFe n x) (dome n (profile U))= dome n (profile U):=by
 let F:=frame matter (links U) (anticut n); let G:= twist (coΛ n x)
 have ht(i:Axis): G (F.T i)=F.T i:=χ_shift x U i
 have hi(i:Axis): G (F.inc i)= F.inc i:=by
    have hb:G (F.gamma i)= F.gamma i:= twist_spin Ferr (fun _:Site n=>x) _
    simp only [WilsonFrame.inc,WilsonFrame.lap,WilsonFrame.diff,map_smul,map_sub,map_add,map_mul,map_star,map_one,ht,hb]
 have he:G F.H0= F.H0:=by simp only [WilsonFrame.H0,map_add,map_neg,map_one,map_sum,hi]
 rw [dome_kernel,←twistField]; apply congrArg (love _); change G F.H=_; rw [WilsonFrame.H,map_mul,he]; exact congrArg (· * _) (show G F.chir=F.chir from twist_spin Ferr (fun _:Site n=>x) grading)
lemma fundFe (j:ℕ)(M:Male)(h:M.val=1): twist (FieldFe n x) (spar j M U)=spar j M U:=by unfold spar funde; rw [if_pos h]; exact projectXP _ _ (dome_Fe ..)
lemma flatFe (j:ℕ)(M:Male)(k:1≤j):twist (FieldFe n x) (spar j M 1)= spar j M 1:=by
 unfold spar; rw [profile_trivial, funde_flat _ k]; apply twistFE; change ((1:Op _)⊗ₖ _)*_=(cart n (Fir.tub (Fir.bar j M.val))⊗ₖ (1:Op Slot)) *((1:Op _)⊗ₖ (Ferr x).val); rw [op_kron_mul, op_kron_mul]; simp -- tune
lemma tickFe(N:Side): twist (FieldFe N x) (tickA N)=tickA N:=by change twist _ (love N (cutM _))= love N (cutM (upperP N)); rw [←twistField, plane_diag]; rw [show twist (coΛ N x) (Lat.spin _ _ (cutM plusHalf))= _ from twist_spin Ferr (fun _:Site N=>x) (cutM plusHalf)]; try rfl
abbrev TVfe (N:Side)(x:Flavor):UNI (Single N):= FieldFe N (chipUFe x)
lemma tick_Fix (N:Side)(x:Flavor): acts (quant (TVfe N x).val) (mateK N)= mateK N:=coastOne _ (carts_p _ (cutM_idp _)) _ (tickB N) (FieldFe N) (fun i=>tickFe i N) x
#print axioms fundFe
#print axioms tick_Fix
#print axioms flatFe
end YM.CF.BrentFe
