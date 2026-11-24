import YM.SU5.SatinWard.Resolution.Laplaya
import ForceSatin.Horizon
import YM.SU5.SatinWard.Resolution.Bokeh
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxHeartbeats 350000
noncomputable section
namespace YM.CF.LitCurrent
open Function Filter Topology NormedSpace Lattice Wilson Fock Pastry Scree Sault Sour
open Stax Skye Jet Scroll Finset Palot Cadre Vow RG Rive Nor Hake MeasureTheory
open Metric Drapes Tulip Lat Branch Cube Tenant
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Classical Kronecker
attribute [local instance] opCStarAlgebra
open Rush SU Prism Nacre Laic Tap Levier Thera Moto Oath Font Haro Spire Dial Rill
open Kennel Swell StressExchange
variable {N:Side}{X Y:SOp N}{o:Seat N}{a b c d v:ℝ}{r:ℕ}
local notation "Γ" => Single N
open Buffered _root_.Zephyr.Chern
open IndexMag Chamber Surplus
namespace AuroraX
local notation "I"=> _root_.Zephyr.Chern.IS
open Laurent
open Ember Hove Lifted
variable (D:Division) {P T:SOp N} (E:Pattern P T r d a v)
variable (q:BudgetPoint)(t:Scree.Loom N){k m:ℕ}{g:ℝ} (C:Checked q t g d a k m)(H:4*q.B<N.val)
local notation "Φ"=> saleLoc (B:=q.B) N
local notation "Σ"=>shoreEntry q.B
variable (x:Cover)
open Papyrus.Franc.SatinForce Papyrus.Franc.Loaves
-- CAN derivative vectors.Just coefficients no blocks outside. Sum enumer.Order.Linear.
local notation "Ζ" i:max=> flag N i
noncomputable def feePoint {B:ℕ}(x:Cover)(i:shoreEntry B):ℂ:= flag N (x+i.1.val)
local notation "Tx" z:max=> feePoint (N:=N) x z
abbrev glassPair(B:ℕ):= shoreEntry B× shoreEntry B
abbrev curUnit {B:ℕ}(x:Cover)(A:Op (Single N))(i:glassPair B):ℂ:= (Complex.I)* (shore N (x+i.1.1.val) (x+i.2.1.val) (enamel A)) i.1.2 i.2.2
local notation "V"=>glassPair q.B
lemma realFlag (x:Cover): star (flag N x)=flag N x:= fee_real _
abbrev crestB{B:ℕ}(x:Cover)(i:shoreEntry B)(b:Bool):Bite:=⟨x+i.1.val,i.2.1,i.2.2,b⟩
abbrev readB{B:ℕ}(x:Cover)(i:glassPair B): List Bite:= [crestB x i.1 false, crestB x i.2 true]
lemma crestRead (i:glassPair q.B): chartP N (readB x i)= ((Tx i.1) • put (Φ x i.1))* ((Tx i.2) • takeF (Φ x i.2)):=by
 let F(b:Bool)(i:shoreEntry q.B):= vix N (crestB x i b); have he:F false i.1=(Tx i.1) • put (Φ x i.1):=by change create ((Tx i.1) • (basisKet (Φ x i.1)))=_; rw [map_smul,create_put]
 have hu:F true i.2=(Tx i.2) • takeF (Φ x i.2):=by change star (create ((Tx i.2) • basisKet _))=_; rw [map_smul,create_put,star_smul,show star (Tx i.2)=_ from realFlag ..]; rfl
 unfold chartP readB; simp only [List.map_cons,List.prod_cons,List.map_nil,List.prod_nil,mul_one]; rw [←he,←hu]
variable (A:Op (Single N)) (w:cutM (modesIn N (offsetMask q.B (wrap N x))) * A * cutM (modesIn N (offsetMask q.B (wrap N x)))=A)
lemma shineZero (i:V): curUnit x A i • chartP N (readB x i)= Complex.I • ((enamel A) (Φ x i.1) (Φ x i.2) • (put (Φ x i.1)*takeF (Φ x i.2))):=by
 rw [crestRead, Algebra.smul_mul_assoc, Algebra.mul_smul_comm]; change (Complex.I*((Tx i.1)*(Tx i.2)*_)) • _=_; rw [smul_smul,smul_smul,smul_smul]; congr 1
 let a:=Tx i.1; let b:=Tx i.2; have hp: a*a=1:=flag_sq ..; have hb:b*b=1:=flag_sq ..; let c:=enamel A (Φ x i.1) (Φ x i.2); change (Complex.I* (a*b*c)*a)*b= _; ring_nf at *; rw [hp,hb]; ring -- fix let C
include H w
lemma paintTrain : (∑ i:glassPair q.B, curUnit x A i • chartP N (readB x i))= Complex.I • dg (enamel A):=by
 rw [dg, dyad, standardLayout q H x A w (fun i j=>(enamel A) i j • (put i*takeF j)) (fun i j h=>by simp [enamelBill,h])]; simp_rw [smul_sum]; rw [Fintype.sum_prod_type]; exact sum_congr rfl fun i _=>sum_congr rfl fun j _=> shineZero q x A (i,j)
lemma paintPrice : (∑ i:glassPair q.B, ‖curUnit x A i‖) ≤ frameR A:=by apply le_trans _ (enamel_frames A); unfold frameR; rw [standardLayout q H x A w (fun i j=> ‖enamel A i j‖) (fun i j h=>by simp [enamelBill,h]),Fintype.sum_prod_type]; apply le_of_eq; refine sum_congr rfl (fun i _=>sum_congr rfl (fun j _=>?_)); unfold curUnit; change ‖Complex.I*(Ζ _ * Ζ _ * _)‖=_; rw [norm_mul,norm_mul,norm_mul, Complex.norm_I, flag_norm,flag_norm,one_mul,one_mul,one_mul]; rfl -- tune {Ζ _ reserved index}.
omit H w
open QuadClock.SignSlot
lemma heightℓ(Q:Op I)(u v:I): lacquer Q u v=if u.1∈plusHalf∧ v.1∉plusHalf then Q u v else 0:=by
 rw [lacquerPay,show bins SU.Slot= _ from (show bins SU.Slot=cutM (univ.filter (fun i':Kt=> i'.1∈plusHalf)) from tagFormula)]; rw [mul_sub,Matrix.sub_apply,Fock.cutM, Matrix.mul_diagonal, mul_one, Matrix.diagonal_mul]; by_cases hu:u.1∈plusHalf<;>by_cases hv:v.1∈plusHalf<;>simp [hu,hv] -- El.Ch
abbrev plusLayer{B:ℕ}(i:glassPair B):Prop:= i.1.2.1∈plusHalf∧ i.2.2.1∉plusHalf
lemma terrainB (i:glassPair q.B) : curUnit x A i= Complex.I * (lacquer ((shore N (x+i.1.1.val) (x+i.2.1.val)) A)) i.1.2 i.2.2:=by
 rw [heightℓ]; unfold curUnit; congr 1; change (Tx i.1)*(Tx i.2)*(enamel A (Φ x i.1) (Φ x i.2))= _; rw [enamelBill]; by_cases h:i.1.2.1∈plusHalf∧ i.2.2.1∉plusHalf <;> simp [saleLoc,h,_root_.Zephyr.Chern.tag,feePoint, lint]
lemma nonstd (i:glassPair q.B)(h:¬ plusLayer i) : curUnit x A i=0:=by rw [terrainB,heightℓ,if_neg h,mul_zero]
#print axioms terrainB
end AuroraX
end YM.CF.LitCurrent
