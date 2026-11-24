import YM.SU5.SatinWard.Resolution.RoxyL
import YM.CF.Tap.Pallet
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
variable {S:Type}{F: Ultrafilter S}{s:ℕ}(X': Cross s (F:Filter S)) {p:Stack}
local notation "X★"=> X'
local notation "Nβ"=> X'.N
local notation "Mβ"=> X'.M
open Ember Hove
variable (D:Division)
local notation "H"=> Coats I
local notation "X"=> bins SU.Slot
abbrev SectorLayer := Cover × Cover

-- Fubini on (fixed row 0, column y, center o) into cost `(o,y)`. Each connector root stencil t contributes. Cancel one of two orderings, $j$ fixed.
def summit (t:Cover) : SectorLayer≃SectorLayer where
 toFun z:=(t+z.1,z.2-(t+z.1))
 invFun z:=(z.1-t,z.2+z.1)
 left_inv z:=by cases z; simp
 right_inv z:=by cases z; simp
local notation "A" d:max k:max=> seam d k
local notation "ℐ"=> Complex.I
variable (h:Axis)(P W:H) (t:Cover)
def profileM(t:Cover)(h:Axis)(P: H):H:=(-Complex.I) • Δ h P- (t h:ℂ) • P
local notation "Φ"=> profileM t h
lemma moment_prec (z:Cover) : seam z (profileM t h P) = ((z-t) h:ℂ) • seam z P:=by rw [profileM,map_sub,map_smul,map_smul,seam_Δ, smul_smul, rune,←mul_assoc,neg_mul,Complex.I_mul_I,neg_neg,one_mul, Pi.sub_apply,Int.cast_sub,sub_smul]; -- nonsense
local notation "C"=> coinPal D
-- Op norm from finite dim CC. maybe Lean.. count.
def layer (D:Division)(P W:H)(h:Axis)(G z:Cover) (Ξ:SectorLayer):=let y:= G+Ξ.1; (Ξ.1 h:ℂ) • roomSand D (fun i j=> seam (j-i) P) (fun i j=>seam (j-i) W) z Ξ.2 y
lemma levyCost : let p(x:SectorLayer):= (seam x.1 (profileM t h P))*coinPal D*(seam x.2 W); layer D P W h t 0=p∘summit t:=by
 intro p; funext z; unfold layer roomSand; dsimp only; rw [sub_zero]; change _= seam (t+z.1) _*_ * _; rw [moment_prec, add_sub_cancel_left]
 simp only [Matrix.smul_mul]; rfl
local notation "ΦA" h:max t:max x:max => flash 0 (profileM t h x)
local notation "Ψ" x:max=> flash 0 x
lemma layerTrue : HasSum (layer D P W h t 0) ((flash 0 (profileM t h P))*coinPal D*(flash 0 W)):=by
 let f:=fun x=>seam x (profileM t h P)*coinPal D; let g:=fun x=>seam x W; let p(x:SectorLayer):= f x.1 * g x.2; rw [levyCost]; apply (Equiv.hasSum_iff (summit t)).2 -- binder implicit
 have h1: Summable f:= (riseSum (profileM t h P)).mul_right _; have h2:Summable g:=riseSum W; have hh: ∑' x:SectorLayer,p x=(flash 0 (profileM t h P))*coinPal D*(flash 0 W):=by rw [←tsum_mul_tsum_of_summable_norm h1.norm h2.norm,(riseSum (profileM t h P)).tsum_mul_right _]; unfold g; simp_rw [wave_floor] -- defs f' maybe needed
 rw [←hh]; exact (summable_mul_of_summable_norm h1.norm h2.norm).hasSum
 -- not imported Bokeh choose. need ∎ Culm.Or own.SP.
noncomputable def lacquer : Op I →L[ℂ] Op I:= let Lc:Op I→ₗ[ℂ]Op I:=
  { toFun V:=bins SU.Slot*V*(1-bins SU.Slot)
    map_add' V W:=by rw [mul_add,add_mul]
    map_smul' a b:=by rw [Matrix.mul_smul,Matrix.smul_mul]; rfl }
 Lc.toContinuousLinearMap
lemma lacquerPay(G:Op I): lacquer G=X*G*(1-X):=rfl
private lemma stockHat : X*X=X:=binsSq _
lemma dadoRight (a:Axis): (petal a⊗ₖ (commission D))*(1-X)=(petal a⊗ₖ commission D):=by
 rw [bins, show (1:Op I)=(1:Op SpinIdx)⊗ₖ (1:Op SU.Slot) from Matrix.one_kronecker_one.symm]
 have he: (1:Op SpinIdx)⊗ₖ(1:Op SU.Slot) - Fir.Aop ⊗ₖ 1=((1:Op SpinIdx)-Fir.Aop)⊗ₖ(1:Op SU.Slot):=by simp only [sub_eq_add_neg,Matrix.add_kronecker, op_kron_neg]
 have hv: Fir.Aop*gammaOp a=gammaOp a*(1-Fir.Aop):=by simp only [Fir.Adef,Matrix.mul_smul,Matrix.smul_mul,mul_sub, add_mul, mul_add,mul_one,one_mul, gradingSwap]; module
 rw [he,op_kron_mul,mul_one,petal,hv,Matrix.smul_mul,mul_assoc,show (1-Fir.Aop)*(1-Fir.Aop)=1-Fir.Aop from (by rw [sub_mul,one_mul,mul_sub,mul_one,Fir.AOne]; abel)]
lemma lampOut (a:Axis)(p:H)(F:flash 0 p=1-X)(q:flash 0 (Δ a p)=Tap.boom a) (t:Cover) (D:Division):
 (let K(x y:H):= lacquer (flash 0 (profileM t a x) * coinPal D * flash 0 y); K p (1-p)+K (1-p) p)=Complex.I • (petal a⊗ₖ commission D):=by
 let M:= (flash 0 (profileM t a p)); let C1:=coinPal D; let Y:=1-X; let Z:=Tap.boom a; let W':=flash 0 (profileM t a (1-p)); have hx:X*C1=C1*X:=by change bins SU.Slot* coinPal D=_; unfold C1 bins coinPal; rw [op_kron_mul,op_kron_mul,one_mul,mul_one,one_mul,mul_one] -- repetitions
 have hp:Y*Y=Y:=by unfold Y; rw [sub_mul,one_mul,mul_sub,mul_one,stockHat]; abel
 have ht:X*Y=0:=by unfold Y; rw [mul_sub,mul_one,stockHat,sub_self]
 have hf:(flash 0) (1-p)=X:=by rw [map_sub,map_one,F,sub_sub_cancel]
 have hW: W'=Complex.I • Z-(t a:ℂ) • X:=by unfold W' profileM; rw [map_sub,map_smul,map_smul,hf, map_sub,Δ_one,zero_sub,map_neg,q, neg_smul,smul_neg,neg_neg]
 let V:=petal a⊗ₖ commission D
 have hV: X*Z*C1=V:=by unfold Z; rw [Tap.boom_A,show C1=(1:Op SpinIdx)⊗ₖ commission D from rfl,op_kron_mul,mul_one,one_mul]
 dsimp only; rw [lacquerPay,lacquerPay,hf,F]; change X*(M*C1 * X)* Y+X*(W'*C1*Y)*Y=Complex.I • V
 rw [mul_assoc X (M*C1*X), mul_assoc (M*C1),ht,mul_zero,mul_zero,zero_add,mul_assoc X (W'*C1*Y),mul_assoc (W'*C1),hp, ←mul_assoc X,←mul_assoc X,hW,mul_sub (bins SU.Slot) (Complex.I • Z),sub_mul,Matrix.mul_smul,Matrix.mul_smul,stockHat,Matrix.smul_mul,Matrix.smul_mul,hV,sub_mul,Matrix.smul_mul,Matrix.smul_mul,show V*Y=V from dadoRight D a] -- V defeq?
 rw [hx,mul_assoc,ht,mul_zero,smul_zero,sub_zero]
#print axioms lampOut
end AuroraX
end YM.CF.LitCurrent
