import Bay.D.Myrtle
import YM.SU5.Regis.Curators
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 3000
set_option synthInstance.maxSize 24000
set_option quotPrecheck false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Bay
open Function Filter Topology NormedSpace Lattice Wilson Fock Pastry Scree Sault Sour Stax Skye Jet Scroll Finset Palot Cadre Vow
open RG MeasureTheory Rue
open Metric Drapes Tulip Lat Branch Cube Tenant
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Classical
attribute [local instance] opCStarAlgebra
open Rush SU Tap Levier Thera Oath Font Spire Dial Rill
open Kennel Swell

namespace D
open Exterior Precision Nacre
open scoped ContDiff
open Regis Regis.Head Etch Gleam Next.SectorChange Next.SectorChange.Gaussian
open Pressure Work.F03 ProbabilityTheory
local notation "T4"=>SU.group

structure Kite(n:Side) where
 turn:Signed
 gust:Site n
variable {n:Side}
namespace Kite
variable (g h j:Kite n)
abbrev rise:=affine g.turn g.gust
abbrev swirl:=@Lattice.pull (ZMod n.val) (T4).El _ _ _ g.turn g.gust
abbrev sail:=Head.bank (G:=T4) g.turn g.gust
instance : Mul (Kite n):= ⟨fun a b=>⟨a.turn*b.turn, a.rise b.gust⟩⟩
instance : One (Kite n):= ⟨⟨1,0⟩⟩
lemma r_one(x): (1:Kite n).rise x=x:= by change Signed.act 1 x+0=x; rw[Signed.act_one,add_zero]
lemma r_mul(x): (g*h).rise x=g.rise (h.rise x):=by
 change (g.turn*h.turn).act x+g.rise h.gust=_
 simp[rise,affine,Signed.act_mul,Signed.act_add,add_assoc]
lemma r_inj:Injective g.rise:=fun _ _ p=>g.turn.act_injective (add_right_cancel p)
instance:Monoid (Kite n) where
 mul_assoc g h j:=by
    change Kite.mk (_*_ * _) ((g*h).rise _) = Kite.mk (g.turn*(h.turn*j.turn)) (g.rise (h.rise j.gust))
    rw[r_mul,_root_.mul_assoc]
 mul_one g:=by
   change Kite.mk (_ * 1) (g.turn.act 0 +g.gust)=g
   rw[Signed.act_zero,zero_add,_root_.mul_one]
 one_mul g:=by
   change Kite.mk (1 * _) ((1:Kite n).rise _) =g
   rw[r_one, _root_.one_mul]

lemma union (x:Config T4 n): h.swirl (g.swirl x) = (g*h).swirl x:=pull_pull ..
end Kite

abbrev brief(F:PlaqAxes): RG.Slot:=⟨[],F⟩
variable (g h:Kite n)(i:Cella n)
lemma falls: slotFace (brief i.2.1) i.1 = tulipF i :=by
 unfold slotFace; rw [show (brief i.2.1).offset=0 from rfl,map_zero,zero_add]

variable {Y₁ Y₂:Head.Dir T4 n}
lemma brine_eq (e:∀t:ℝ,represent (t • Y₁) = represent (t • Y₂)):
 brine Y₁ i = brine Y₂ i:=by
   have h:=slot_deriv (brief i.2.1) i.1 Y₁
   simp_rw [e] at h
   have j:=h.unique (slot_deriv (brief i.2.1) i.1 Y₂)
   unfold brine; rw[←falls,j]
lemma brine_union(y:Head.Dir T4 n): brine (h.sail (g.sail y)) i=brine ((g*h).sail y) i:=by
 apply brine_eq; intro t
 unfold Kite.sail; rw [bank_at,bank_at,bank_at]
 exact g.union h _
lemma brine_one(y:Head.Dir T4 n): brine ((1:Kite n).sail y) i=brine y i:=by
 apply brine_eq; intro t;rw [Kite.sail,bank_at]; exact pull_id _

abbrev Dock n:=Altar T4 n
abbrev budD(F:PlaqAxes)(s:Signed):RG.Slot:=skewSlot T4 (brief F) s
abbrev leaf:= slotFace (budD i.2.1 g.turn) (g.rise i.1)
abbrev parity:=skewSig T4 (brief i.2.1) g.turn
lemma brine_sail(y:Head.Dir T4 n):
    brine (g.sail y) i=parity g i*faceCurl (leaf g i) y i.2.2:=by

 unfold brine;rw [←falls,Kite.sail, reflex];rfl

def sea (q:Clip) (g:Kite n)(x:Dock n)(i:Cella n):=
    parity g i * river q (leaf g i) x i.2.2

section Charts
variable {q:Clip}{Z:PathData T4}{H:Bed}{η C S:ℝ}(B:Z.Bounds q η C S)(P:Attached H Z)
lemma at_sea(y:Head.Dir T4 n) :
    sea q g (tiler B P y) i=brine (g.sail y) i:=by rw[sea,river_now q B P,brine_sail]

lemma sea_mul(y:Head.Dir T4 n):
 sea q h (tiler B P (g.sail y))= sea q (g*h) (tiler B P y):= funext fun j=>by
    rw [at_sea h j B P,at_sea (g*h) j B P,brine_union]
end Charts
lemma sea_smooth(q:Clip):ContDiff ℝ 1 (fun v: Dock n=>sea q g v i):=by
   let π:=PiLp.proj (𝕜:=ℝ) 2 (fun _:(T4).ColorIndex=>ℝ) i.2.2
   exact contDiff_const.mul (π.contDiff.comp ((river (G:=T4) q (leaf g i)).toContinuousLinearMap.contDiff))
lemma sea_minus(q:Clip)(x y:Dock n):sea q g x i-sea q g y i=sea q g (x-y) i:=by
 unfold sea
 rw[_root_.map_sub,←mul_sub]; rfl
lemma sea_le(q:Clip)(x:Dock n)(ρ:ℝ):
   |ρ*sea q g x i|≤ rays q ρ * ‖cup (leaf g i) x‖:=by
 rw [sea,abs_mul,abs_mul,parity,skewSq,one_mul]
 have he:=PiLp.norm_apply_le (river q (leaf g i) x) i.2.2
 rw [Real.norm_eq_abs] at he
 apply le_trans (mul_le_mul_of_nonneg_left he (abs_nonneg _))
 apply le_of_eq
 rw [river, LinearMap.smul_apply, norm_smul]

 rw [Real.norm_eq_abs, abs_of_nonneg (by positivity : 0≤(Real.sqrt q.direct)⁻¹)]
 exact (mul_assoc ..).symm

-- charge per-cell over copies with distinct image of anchor o
variable {I:Type*}[Fintype I]
lemma celia(o:Site n)(j:I→Kite n)(p:Injective (fun w=> (j w).rise o))
 (x:Dock n):∑ w:I, ‖cup (leaf (j w) i) x‖≤ 
    (Fintype.card Signed:ℝ)*Real.sqrt (Fintype.card I)*‖x‖:=by
 let z(s:Signed)(w:I):=(j w).rise o + s.act (i.1-o)
 let d(s:Signed)(w:I):= ‖cup (slotFace (budD i.2.1 s) (z s w)) x‖
 apply le_trans (b:=∑w:I,∑s,d s w)
 · refine sum_le_sum fun w _=>le_trans ?_ (single_le_sum (f:=fun s=>d s w) (fun _ _=>norm_nonneg _) (mem_univ (j w).turn))
   have e:(j w).rise i.1=z (j w).turn w:=by unfold z Kite.rise affine; rw[Signed.act_sub];abel
   unfold d leaf;rw [e]
 rw[sum_comm]
 refine (sum_le_sum (fun s _=>cup_sum (z s) (fun _ _ h=>p (add_right_cancel h)) (budD i.2.1 s) x)).trans_eq ?_
 rw[sum_const,nsmul_eq_mul,card_univ,mul_assoc]

end YM.CF.Bay.D
