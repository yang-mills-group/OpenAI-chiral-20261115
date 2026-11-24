import GaugeFieldConstruction.BoxM
set_option autoImplicit false
set_option quotPrecheck false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 340000
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
open Pastry
variable {n:Side} {α β I E:Type}[LinearOrder I][Fintype I][Fintype α][Fintype β]
section
variable (σ:I→ Seat n) {S:α→ Support (More n)} {z:β→Force n}
namespace Grotto
variable (r:ℝ)(A:Grotto I S z)
local notation "P'"=> A.anchor
variable {p:BudgetPoint}(y:Seat n)(V:α→ℝ)(U:β→ℝ)(ht:0≤r)(u:0≤V)(v:0≤U)
variable {b:ℕ}{Ω a η:ℝ} {L:List (Site (More n))}
variable (l:Scales b a η L)(HP:∀ i:Seat n,postG S V (RedB b a η L) i≤ Ω)(HV:∀ i:Seat n,postG (plateI z) U (ColdB b a η L) i≤ Ω)(t:Cube_M b*Ω ≤1)(g:0≤Ω)
local notation "Θ"=> Summit b a (P').val.2
local notation "L0"=>Heart A.anchor S A.needs
local notation "T"=> Legist A.anchor S A.needs
local notation "PZ"=>RedB b a η L
local notation "ΩΠ"=>ColdB b a η L
local notation "G0"=>PZ A.anchor.val.2 * ridg b A.anchor.val.2^3
local notation "Δπ"=>respite b (a+2*ζd) η L (plateI z) U (P').val.1 y
local notation "Γπ"=>respite b (a+6*ζd) η L S V (P').val.1 y
local notation "gπ"=> Cube_M b* Ω
local notation "Mπ"=> windPulse b (P').val.1 y
def cloudP (P:Hub n):=P.val.2
def cloudK (P:Force n):= P.val.1.val.2
abbrev XE(I α:Type)(n:Side):=dues I (Hub n)→ α -- careful α : Type
abbrev KK(I α:Type)(n:Side):=dues I (Force n)→ α
local notation "φℝ"=>exp_R σ A r V
local notation "φF"=>exp_Y σ A r V U
include u ht l -- general white using location
lemma XP_white (H:A.needs=0):pointX cloudP (φℝ) PZ y ≤ (r*Θ)* Mπ:=by
 unfold exp_R; rw[pointX_sum]; let Z':= T
 have he(x:L0): T x=A.anchor:=by
    apply Subtype.ext; change (A.anchor.val.1,lengthQ A.anchor.val.2 S x.val)= _
    haveI:IsEmpty (Fin A.needs):=by rw [H]; infer_instance
    simp only [lengthQ,univ_eq_empty,biUnion_empty, union_empty]
 have e(t:L0):(∏ i,V (t.val i))=1:=by
    haveI:IsEmpty (Fin A.needs):=by rw [H]; infer_instance
    simp
 have p(t:L0):pointX cloudP (clipK σ (T t) (A.fromR t) (r*∏ i,V (t.val i))) PZ y ≤ r*Θ*Mπ:=by
    rw[e,mul_one]; apply (allot_le _ _ _ _ _ ht _ (fun _=>Temp_p ..|>.le) _).trans; rw [he]; split; swap; next h=> exact mul_nonneg (mul_nonneg ht (Real.exp_pos _).le) (pulse_pos ..|>.le)
    next h=>
     change r*PZ A.anchor.val.2≤_
     let x:=ridg b (P').val.2; have hC:1≤x:=ridg_one ..
     have K:= redB_place (P').val.2 l
     have k':PZ A.anchor.val.2≤ (Summit b a A.anchor.val.2)*Mπ:=by
       have m:1≤ Mπ*x:=pulse_core b _ _ (P').property h
       have huΛ:PZ A.anchor.val.2*x ≤ Θ:= (mul_le_mul_of_nonneg_left (le_self_pow₀ hC (by norm_num: (9:ℕ)≠0)) (Temp_p ..|>.le)).trans K
       nlinarith only [mul_le_mul_of_nonneg_left m (Temp_p b (a+6*ζd) η L (P').val.2|>.le),mul_le_mul_of_nonneg_right huΛ (pulse_pos b (P').val.1 y|>.le)]
     exact (mul_le_mul_of_nonneg_left k' ht).trans_eq (mul_assoc ..).symm
 apply (sum_le_sum (fun i _=>p i)).trans; rw [sum_const,nsmul_eq_mul,card_univ]
 have hx:Fintype.card L0≤1:=by
    letI: IsEmpty (Fin A.needs):=by rw [H]; infer_instance
    letI: Subsingleton L0:= show Subsingleton ↥(LeadQ (P').val.2 S A.needs) from inferInstance; exact Fintype.card_le_one_iff_subsingleton.mpr inferInstance
 exact mul_le_of_le_one_left (mul_nonneg (mul_nonneg ht (Real.exp_pos _).le) (pulse_pos ..|>.le)) (by exact_mod_cast hx)
omit u ht
lemma G_le : G0 ≤ Θ:= (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (ridg_one ..) (by norm_num:3≤(9:ℕ))) (Temp_p ..|>.le)).trans (redB_place _ l)
include t g v u ht HP HV
lemma fiscal_gray : let E: dues I (Hub n) → ℝ:= if A.needs>0 then exp_R σ A r V else 0
 pointX cloudP E PZ y+pointX cloudK φF ΩΠ y ≤ r*Θ*(2*Mπ*gπ+4*η⁻¹*(Δπ+ Γπ)):=by
 intro E
 have H' : pointX cloudP E PZ y ≤ r*(G0*(Mπ*gπ+2*(η⁻¹*Γπ))):=by
    unfold E; split; next h=> have K:= exp_r σ A r V y u ht l HP t g; rw[if_neg (Nat.ne_of_gt h)] at K; exact K
    rw [pointX_0]; exact mul_nonneg ht (mul_nonneg (mul_nonneg (Temp_p ..|>.le) (pow_nonneg (ridg_pos ..|>.le) _)) (add_nonneg (mul_nonneg (pulse_pos ..|>.le) (mul_nonneg (cube_M_pos ..|>.le) g)) (mul_nonneg zero_le_two (mul_nonneg (inv_pos.mpr l.pos).le (respite_0 S V u _ _ _ _ _ _ l.pos.le)))))
 have K:= add_le_add H' (exp_f σ A r V U y u v ht l HP HV t g); apply K.trans
 let π:=Mπ; let X:=gπ; let Δ:=Δπ; let G:=Γπ; have hπ:0≤π:= (Real.exp_pos _).le; have hx:0≤X:=mul_nonneg (cube_M_pos ..|>.le) g; have hΔ:0≤Δ:=respite_0 _ _ (fun i=>v i) _ _ _ _ _ _ l.pos.le
 have hG:0≤G:=respite_0 _ _ (fun i=>u i) _ _ _ _ _ _ l.pos.le
 let Z:=G0; have hr:0≤Z:=mul_nonneg (Temp_p ..|>.le) (pow_nonneg (ridg_pos ..|>.le) _); let Q':=Θ; have he:Z≤ Q':= G_le A l
 change r*(Z*(π*X+2*(η⁻¹*G)))+r*(Z*((π*X+2*(η⁻¹*G))+η⁻¹*Δ))≤ r*Q' * (2*π*X+4*η⁻¹*(Δ+G))
 have uη:= inv_pos.mpr l.pos
 apply le_trans _ (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left he ht) (show 0≤2*π*X+4*η⁻¹*(Δ+G) by positivity))
 nlinarith only [mul_nonneg (mul_nonneg ht hr) (mul_nonneg uη.le hΔ)]
end Grotto
end
end YM.CF.Scree.Ing
end
