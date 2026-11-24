import GaugeFieldConstruction.GastronQ3
set_option autoImplicit false
set_option quotPrecheck false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 60000
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
open Pastry Grotto
namespace Ivey
open Sault Leaf Sour
open Ladder3 Drapes Tenant Palot Rue Iona
attribute [local instance] loreM loreN
variable {n: Side}{I α β γ G:Type}[LinearOrder I][Fintype I][Fintype α][Fintype β][Fintype γ]
-- old bank
namespace ShoreQ
open Tuner Ladder3 Branch Tenant XGarden.MastTin
variable (F:RegLime I α n)(Q:LeaseQ γ n)(k:I)(M:Mica I β n){J:Type}[Fintype J](C:J→Factor3 n)
section
variable (P:BudgetPoint)(L:ℕ)
section
local notation "Γ"=> Actors Q C
def Platform(i:J):=pad3 Q (C i) P L
def nucleQ (x:Actors Q C):= core3 Q (C x.1) x.2.1
def spark3 (x:Actors Q C):=pad3 Q (C x.1) P L x.2.1
variable (S:Ids n)
lemma placeH (i:Actors Q C): (Craft3 F Q k M C (Platform Q C P L) S i).anchor=spark3 Q C P L i:=by unfold Craft3 κhop; split_ifs <;> rfl
variable {u:γ→ℝ}{p:J→ℝ}{c b ℓ δ v d:ℝ}
variable (X:KPower Q c v u)(Yt:∀ i, BasePower (C i) (p i))(V: (∑ i:J, p i* Branch.rent (3*c) (C i).H.val.2) ≤ ℓ)(w:0<c)(Wg:∀ i,Q.H i ⊆ Q.X i)(a:0≤v)(hr:0≤ d)
local notation "rΔ"=> Branch.rent c
include X Yt V w a hr
abbrev moneyΓ(a c r G:ℝ):= 3*(Fintype.card ↥(pts₃ 2):ℝ)*(r*4*overflow₃ a c^2)* G
lemma Forensic: (∑ i:Actors Q C, Win3 Q C d u p i *rent c (nucleQ Q C i).val.2)≤ moneyΓ c v d ℓ:=by
 let B(i:J):=p i * rent (3*c) (C i).H.val.2; let A0:= d*4*overflow₃ c v ^2; let Y:=Fintype.card ↥(pts₃ 2)
 unfold Actors; rw[Fintype.sum_sigma]
 refine le_trans (sum_le_sum (g:=fun i:J=>3*(Y:ℝ)*A0*B i) (fun i _=>?_)) ?_
 · have h0:= (Yt i).pos; let A:= C i; let Llim:= tank3 Q A d (p i) u; rw [Fintype.sum_prod_type]; change (∑ x:AV3 Q A,∑ b:Bool, _* _ )≤ _
   let ex(x:AV3 Q A)(b:Bool):=Win3 Q C d u p ⟨i,x,b⟩ * rent c (nucleQ Q C ⟨i,x,b⟩).val.2
   let f(x:AV3 Q A):= Llim x *rΔ (core3 Q A x).val.2
   have hp(x: AV3 Q A): (∑ b:Bool,ex x b) =3*f x:=by rw [Fintype.sum_bool]; change 2*Llim x *rΔ (core3 Q A x).val.2+ f x=_ ; unfold f; ring
   change ∑ x:AV3 Q A,∑ b,ex x b≤_; simp_rw[hp]; unfold AV3; rw [Fintype.sum_sigma]
   apply le_trans (sum_le_sum (s:= (univ:Finset (BD3 A))) (g:=fun _=>3*(A0*B i)) (fun j _=>?_))
   · rw[sum_const,nsmul_eq_mul]; have he: Fintype.card (BD3 A)≤Y:=by unfold Y; simp only [BD3,Fintype.card_coe]; apply card_le_card; intro i h; exact (specs₃ ..).2 (((specs₃ ..).1 h).trans (fade_sz A))
     have hu:0≤A0:= mul_nonneg (mul_nonneg hr (by norm_num)) (sq_nonneg _); have hw:0≤ B i:=mul_nonneg h0 (Real.exp_pos _).le
     exact (mul_le_mul_of_nonneg_right (show ((univ:Finset (BD3 A)).card:ℝ)≤ Y from (by rw [card_univ]; exact Nat.cast_le.mpr he)) (by positivity)).trans_eq (by ring)
   rw[← Finset.mul_sum]; exact mul_le_mul_of_nonneg_left (shore_A A Q c v u X w _ _ hr h0 a j) (by norm_num)
 rw[←Finset.mul_sum]; exact mul_le_mul_of_nonneg_left V (mul_nonneg (by positivity) (mul_nonneg (mul_nonneg hr (by norm_num)) (sq_nonneg _)))
omit V a
lemma πpot (i:Actors Q C) : 0≤Win3 Q C d u p i:=by
 unfold Win3 γhop; split_ifs with h
 exact mul_nonneg zero_le_two (spaceG (C i.1) Q c v u X _ _ hr (Yt i.1).pos _)
 exact spaceG (C i.1) Q c v u X _ _ hr (Yt i.1).pos _
include Wg
lemma portPatch (i:Actors Q C)(y:Win3 Q C d u p i ≠0): Grove (terr _) (nucleQ Q C i).val.2:=by
 let A:=C i.1; let x:=i.2.1
 have h:tank3 Q A d (p i.1) u x≠0:=fun t=>y (by unfold Win3 γhop; split_ifs <;> first|exact t|exact mul_eq_zero_of_right 2 t)
 let ρ:=∑ i:J,p i
 refine grow_v3 Q A x ((Yt i.1).grow (fun u=>h ?_)) (fun j=> X.edge _ (fun u=>h ?_)) (fun j=> Wg (x.2.val j))
 · unfold tank3 zcost3; rw [u,mul_zero,zero_mul,zero_mul]
 unfold tank3 zcost3; rename_i j h'; rw[prod_eq_zero (mem_univ j) u,mul_zero]
local notation "ϕ"=> Win3 Q C d u p
local notation "Θ"=> ThermalH L
local notation "Ψ" i:max=> spark3 Q C P L i
include V a
lemma A_Furn {a0:ℝ}(h:0≤ a0)(hp:a0*2*Yaw.χ (ThermalH L) ≤ P.B*(c/2)) : (∑ i:Actors Q C, ((ϕ i)* March P.B a0 (Ψ i).val.2)* rent (c/2) (nucleQ Q C i).val.2) ≤ Real.exp (a0*Yaw.χ Θ)*moneyΓ c v d ℓ:=by
 refine le_trans ?_ (mul_le_mul_of_nonneg_left (Forensic Q C X Yt V w a hr) (Real.exp_pos _).le); rw[mul_sum]; apply sum_le_sum; intro i _; let Vx:= (Ψ i).val.2; let S:= (nucleQ Q C i).val.2; let E:= Real.exp (a0*Yaw.χ Θ); let t:= ϕ i; by_cases t':t=0; · change t*_* _ ≤ _*(t*_); rw[t',zero_mul,zero_mul,zero_mul,mul_zero]
 let M:=March P.B a0 Vx; let R:= rent (c/2) S
 have he:M≤ E*R:=crust Θ P.B P.B_pos a0 _ h hp (by positivity) Vx S (portPatch Q C X Yt w Wg hr i t') (pad_cover ..) -- arguments tune
 change t*M*R≤ E*(t* (rΔ S)); have hx:t*M≤t*(E*R):=mul_le_mul_of_nonneg_left he (πpot Q C X Yt w hr i)
 apply (mul_le_mul_of_nonneg_right hx (Real.exp_pos _).le).trans_eq
 have hu:R*R=rΔ S:=by unfold R Branch.rent; rw[←Real.exp_add]; congr 1; ring
 rw[←hu]; change t*(E*R)*R=E*(t*(R*R)); ring
lemma furnish {a0:ℝ}(h:0≤ a0)(hp:a0*2*Yaw.χ (ThermalH L) ≤ P.B*(c/2)) : (∑ i:Actors Q C, (ϕ i)* March P.B a0 (Ψ i).val.2) ≤ Real.exp (a0*Yaw.χ Θ)*moneyΓ c v d ℓ:=by
 refine le_trans (sum_le_sum (g:=fun i:Actors Q C=> (ϕ i)*March P.B a0 (Ψ i).val.2 * rent (c/2) (nucleQ Q C i).val.2) ?_) (A_Furn Q C P L X Yt V w Wg a hr h hp)
 exact fun i _=> le_mul_of_one_le_right (mul_nonneg (πpot Q C X Yt w hr i) (Real.exp_pos _).le) (Real.one_le_exp (by positivity))
end
end
end ShoreQ
end Ivey
end YM.CF.Scree.Ing
end
