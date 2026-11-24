import YM.SU5.FiniteGaugeData.Reliance.LiftG
/-! # Temperature charge. Convert absolute basis to `Gross` invoice.

 Keep β and common Ω in actual arrays and their comparison donor. All estimates on `Cashbox`
 election by the new stronger tariff. -/
set_option autoImplicit false
set_option maxHeartbeats 420000
set_option synthInstance.maxSize 24000
set_option quotPrecheck false
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

open Wray Oath Feu Feu.Corset Nor Yaw Pig Oise Jade Plume Push.AbsoluteSums
open Trees Lich.Muster Jet
set_option linter.flexible false
open Chaff Gloss Maize Tye RP RP.Str Oise
namespace LocalLimit

open FullBill Window Marks
open Pyx
open Girt

open Window Graph Period Jade.Earn Buffered.Reliance
namespace Preparation
local notation "q₀" => Chi.canonical
variable (P:Preparation)

namespace Universum
open YM.Next.Rank
local notation "V"=> P.V
local notation "s"=> P.h
-- level frame matching from paid Cashbox and history
variable (j:ℕ){m:Side}{l:ℕ}
local notation "p'"=> Vale.mesh m P.R.L j
local notation "Λ"=> P.Ctor m j
local notation "x₀"=> hat P.R.L P.x j
local notation "M"=> massMeter (P.Ctor m j)
local notation "kU"=> cashU P.W.C

def slope (P:Preparation)(j:ℕ):ℝ:= Buffered.Reliance.fare P.K.top.clip (2 * soaked (hat P.R.L P.x j))
lemma above_zone (p:Cashbox P) : BigHeart (hat P.R.L P.x j)∧ dleaf P.R.L (hat P.R.L P.x j) ≤1:= (p.choose_spec.2 _ (Vale.crown ..)).2
lemma slope_n (p:Cashbox P) :0< slope P j:= by
 have he:(2:ℝ) ≤ x₀:= ((above_zone P j p).1).live
 exact fare_n _ (mul_pos two_pos ((amplifier _ (zero_lt_two.trans_le he)).2.2.1))

local notation "P'"=> Carousel P.V 1 2 6 P.N0 P.J q₀ P.h P.R0 P.δ P.x m l
local notation "βL"=> 2*soaked (hat P.R.L P.x j)
variable (F:Carousel P.V 1 2 6 P.N0 P.J Chi.canonical P.h P.R0 P.δ P.x m l)(W:Cashbox P)(hi:j≤l)
local notation "gH" => soaked (F.E j).beta
local notation "fare'"=> fare (F.E j).funds gH
include W hi
private lemma lateβ : fare (F.E j).funds (soaked (F.E j).beta) ≥ slope P j :=by
 let X:= hat P.R.L P.x j; let b:=(F.E j).beta
 have he:b≥ X/2:= (F.sift j (hi.trans F.probed)).1; have hx:0<X:= zero_lt_two.trans_le (above_zone P j W).1.live
 have hb:0<b:= (half_pos hx).trans_le he
 have ht:Real.sqrt X/2≤Real.sqrt b:= by nlinarith only [he,Real.sq_sqrt hx.le,Real.sq_sqrt hb.le,Real.sqrt_pos.mpr hx,Real.sqrt_pos.mpr hb]
 have H:soaked b≤2*soaked X:= (inv_anti₀ (by positivity : 0<Real.sqrt X/2) ht).trans_eq (by unfold soaked; simp [div_eq_mul_inv])
 rw [slope, Buffered.Reliance.fare,Buffered.Reliance.fare, show (F.E j).funds=P.K.top.clip from (F.owns j (hi.trans F.probed)).fund.symm]; exact div_le_div_of_nonneg_left (strength_pos ..).le (by change 0<2*soaked b; unfold soaked; positivity) (mul_le_mul_of_nonneg_left H (by norm_num)) -- Namespace?
local notation "O"=> (Classical.choice (YM.Next.Rank.exists_budget SU.group))
local notation "occup"=> ((Fintype.card PlaqAxes:ℝ)/2)
local notation "TU"=> flagBill Λ (dleaf P.R.L x₀) (dleaf P.R.L x₀) kU

def surcharge (P:Preparation) := Carousel.costPlan P.V (cashU P.W.C) (Classical.choice (YM.Next.Rank.exists_budget SU.group)) + (Fintype.card PlaqAxes:ℝ)/2
omit W hi in
private lemma face_cap (N:Side): (Fintype.card (Face (Per N)):ℝ)=roomSite N* Fintype.card PlaqAxes:= by rw [show Fintype.card (Face (Per N))=Fintype.card (Site N)*Fintype.card PlaqAxes from Fintype.card_prod .., Nat.cast_mul]
-- D revision: expose raw billing comparison (c cancels) for multiply marks, enough to
-- pay despite no pointwise operator smallness, given the Fock estimate.
lemma raw_cap : Real.exp (flagBill Λ (dleaf P.R.L x₀) (dleaf P.R.L x₀) kU + (Fintype.card (Face (Per (More Λ))):ℝ)/2) * fullRate (Classical.choice (YM.Next.Rank.exists_budget SU.group)) (F.E j) P.K.top.paths P.V.W.bar (soaked (F.E j).beta) ≤ Real.exp (budgetCharge (F.E j) (soaked (hat P.R.L P.x j)) (surcharge P)):=by
 have hp:= P.height; obtain ⟨χ,hE⟩:= above_zone P j W
 let y:=hat P.R.L P.x j; let T:=temp y; let Z:= F.E j; let L:= F.Y j; let M':=cell m P.block P.R.L j; let N:=massMeter M'; let t:= Z.beta; let F':= soaked t; let w:=F.owns j (hi.trans F.probed); let q':= F.val.boot j; have hZ:Z.p.threshold=T:=show _ from w.width ▸ q'.1; have he:Z.funds= P.K.top.clip:= w.fund.symm
 obtain ⟨p0,pA,tq,v,qb⟩:=χ.budget t (F.sift j (hi.trans F.probed))
 have hβ: F' ≤ Z.p.threshold:= hZ ▸ pA; let hone:=amplifier t tq; obtain ⟨-,_,hu,b⟩:=hone
 let β':=upperMoney O P.K.top.paths P.V.W.bar (strength P.K.top.clip) 1
 let k:=cashU P.W.C; let C:= 4*k+3*1*2^4+180*45*6*k; have hk:0≤k:= cash_v _; let γ0:= dleaf P.R.L y
 let face:ℝ := ↑(Fintype.card (Face (Per (More M'))))/2
 let K:=fullRate O Z P.K.top.paths P.V.W.bar F'
 let Y:= flagBill M' γ0 γ0 k
 change Real.exp (Y+face)*K ≤ _
 have hv: |Real.log F'|≤ N*1:=by rw [mul_one]; refine qb.trans ?_; exact le_trans (by push_cast; exact le_rfl : (radiusB (hat P.R.L P.x j):ℝ)+1≤ ((radiusB (hat P.R.L P.x j)+1:ℕ):ℝ)) (Carousel.epochAffordable P.V 1 2 6 P.N0 P.J q₀ P.h P.R0 P.δ F j)
 apply le_trans (mul_le_mul_of_nonneg_left (upperRate O Z (Period.wing_budget P.V) hu b hv (hZ.symm ▸ p0) _ (strength_pos P.K.top.clip) (by rw [he])) (Real.exp_pos _).le)
 rw [←Real.exp_add]; apply Real.exp_monotone; let T':ℝ:=SU.group.lieDim
 have he: strengthLog F' ≤ strengthLog (soaked y)+T'*2:= (mul_le_mul_of_nonneg_left v (Nat.cast_nonneg _)).trans_eq (mul_add T' (Real.log (soaked y)) 2)
 have hu : 0≤N:=zero_le_one.trans (money_pos _); have hf : face=N*occup:=by unfold face; rw [face_cap,← Period.same_room]; ring
 change Y+face+ N*(3*strengthLog F'+β') ≤ N*(3*strengthLog (soaked y)+((C+(β'+T'*2*3))+occup))
 have hC: flagBill M' γ0 γ0 k ≤ N*C:= flagBound _ 1 k _ _ hE hE zero_le_one hk; linarith only [hC,hf,mul_le_mul_of_nonneg_left he hu]
private lemma heavy {S:Support (More Λ)} {c:ℝ} (f : Buffered.Mark Λ)(p : Apt (slope P j) c S f):
    ‖Buffered.num0 P.U (F.E j) (F.Y j) f‖ ≤ c*Real.exp (budgetCharge (F.E j) (soaked (hat P.R.L P.x j)) (surcharge P)):=by
 have hp:= P.height; obtain ⟨χ,hE⟩:= above_zone P j W
 let y:=hat P.R.L P.x j; let T:=temp y; let Z:= F.E j; let L:= F.Y j; let M':=cell m P.block P.R.L j; let N:=massMeter M'; let t:= Z.beta; let F':= soaked t; let w:=F.owns j (hi.trans F.probed); let q':= F.val.boot j; have hZ:Z.p.threshold=T:=show _ from w.width ▸ q'.1; have he:Z.funds= P.K.top.clip:= w.fund.symm
 obtain ⟨p0,pA,tq,v,qb⟩:=χ.budget t (F.sift j (hi.trans F.probed))
 have hβ: F' ≤ Z.p.threshold:= hZ ▸ pA; let hone:=amplifier t tq; obtain ⟨-,_,hu,b⟩:=hone
 let β':=upperMoney O P.K.top.paths P.V.W.bar (strength P.K.top.clip) 1
 let k:=cashU P.W.C; let C:= 4*k+3*1*2^4+180*45*6*k; have hk:0≤k:= cash_v _; let γ0:= dleaf P.R.L y
 let face:ℝ := ↑(Fintype.card (Face (Per (More M'))))/2
 let K:=fullRate O Z P.K.top.paths P.V.W.bar F'
 have hx : ‖Buffered.num0 P.U Z L f‖ ≤ c* Real.exp (flagBill M' γ0 γ0 k + face)* K:=
    Buffered.Reliance.tariff O Z L (Carousel.expense P.V 1 2 6 P.N0 P.J q₀ P.h P.R0 P.δ F j hi hp) (Carousel.footprint_B P.V 1 2 6 P.N0 P.J q₀ P.h P.R0 P.δ F j hi) (Carousel.loomActs P.V 1 2 6 P.N0 P.J q₀ P.h P.R0 P.δ F j) hu b hβ (P.J.gran.trans (F.roof _).size) hp ((level_p _).le) hk f p (slope_n P j W).le (lateβ P j F W hi)
 let Y:= flagBill M' γ0 γ0 k
 apply hx.trans; rw [mul_assoc c]; exact mul_le_mul_of_nonneg_left (raw_cap P j F W hi) (apt_pos p)

omit W hi in
lemma metric_mass (N:Side) : massMeter N=sites N:=by unfold massMeter sizes sites; rw [Nat.cast_pow]
variable {A:ℝ}(pA:Tableau (mesh m P.R.L j) (F.E j) (F.Y j) P.U (soaked (hat P.R.L P.x j)) A)
include pA
lemma tender {S:Support (More Λ)} {c:ℝ}(f:Buffered.Mark Λ)(p:Apt (slope P j) c S f):
    ‖Buffered.markedRead f (F.Y j) (denZ (F.E j) P.U (F.Y j)) / partitionZ (F.E j) P.U (F.Y j)‖ ≤ c*Real.exp ((surcharge P+A)*sites Λ):=by
 rw [←Buffered.same_ratio,norm_div]; let X:= Buffered.vac0 P.U (F.E j) (F.Y j); let H:=soaked (hat P.R.L P.x j)
 have hx:Real.exp (budgetCharge (F.E j) H (-A)) ≤ ‖X‖:=pA.lowB
 apply (div_le_iff₀ ((Real.exp_pos _).trans_le hx)).mpr -- left divide by X; tune exponent
 apply (heavy P j F W hi f p).trans
 apply le_trans ?_ (mul_le_mul_of_nonneg_left hx (mul_nonneg (apt_pos p) (Real.exp_pos _).le)); apply le_of_eq; rw [mul_assoc,←Real.exp_add]; unfold budgetCharge; rw [metric_mass]; unfold H; ring_nf
end Universum
end Preparation
end LocalLimit
end YM.CF.Py.Rate
#print axioms YM.CF.Py.Rate.LocalLimit.Preparation.Universum.tender
