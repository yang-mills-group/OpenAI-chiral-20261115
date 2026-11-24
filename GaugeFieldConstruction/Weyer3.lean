import GaugeFieldConstruction.Dickens3
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
variable (P:BudgetPoint)(L K:ℕ)(S:Ids n)
local notation "G"=> Actors Q C
local notation "B"=> P.B
local notation "Φ" i:max=> C (i:Actors Q C).1
local notation "V0" i:max=> spark3 Q C P L i
local notation "Zπ" i:max=> core3 Q (Φ i) i.2.1
local notation "H" i:max=> (V0 i).val.2
variable {c ℓ r h p δ δ' η Λ:ℝ}{U:γ→ℝ}{A V:J→ℝ}
open Py Py.Riant Push.AbsoluteSums Nor
variable (X:KPower Q δ c U)(Yt:∀ i, BasePower (C i) (A i)) (v:∀ i,Act3 (C i) P K h (A i))(W:Leased Q P K h U)
variable (t:1≤ h)(d:0 <r)(w:0<δ)(wc:Frosty Q P U h η)(uη:0≤ η)(Uη: η≤1)
variable (j₀:ℕ)
local notation "P'"=> KeyUp P
local notation "Δ"=> ThermalH L
local notation "Θ"=> Win3 Q C r U A
variable (Tκ:∀ i,Sugar (C i) P h (V i) S)
local notation "αΞ"=> Antique Q C P L j₀ r h η U A V
variable (o:Seat n)(y:Seat n)(hz:∀ i,(C i).H.val.1=o)(a:ℝ)(z₁:0≤a)(m:ℕ)
variable (ht:(belt3 2 a)*2*↑(Yaw.χ (ThermalH L)) ≤ (P.B:ℝ)*(δ/2))(h0:ζd*2*(Yaw.χ 0:ℝ)≤j₀*(δ/2))(hk: 0 < j₀)
include X t d w Yt W v ht h0 hk uη Tκ z₁ hz
local notation "αμ"=> moment3 Q C P L a δ r U A
local notation "z0"=>reserveT (KeyUp P).power P.order P.B ζd
local notation "Lp"=>windPulse P.B
local notation "L0"=> windPulse P.B o y
-- White sum second.A.Bounds
noncomputable def dot_Λ(C:J→Factor3 n)(P:BudgetPoint)(L:ℕ)(r δ:ℝ)(A V:J→ℝ)(a:ℝ)(j₀:ℕ)(i:J):ℝ:= if (C i).pure then r*V i*Real.exp a else tune3 δ a j₀ L P.order*r*(A i*Branch.rent (3*δ) (C i).H.val.2) -- explicit variable h.r implicitly not in def types! Lean won't infer.Body variables lean binder.
lemma lam0(i:J): 0≤ dot_Λ C P L r δ A V a j₀ i:=by
 unfold dot_Λ; split
 next h=> have he:0≤ V i:=(SecX P' (zero_le_one.trans t) n).posG _ _ _ ((Tκ i).light h).1; positivity
 exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (starQ P j₀) (Real.exp_pos _).le) (Real.exp_pos _).le) d.le) (mul_nonneg (Yt i).pos (Real.exp_pos _).le)
local notation "Xκ" i:max=> dot_Λ C P L r δ A V a j₀ i
local notation "H0"=> separation o y≤ ThermalH L*P.B
def LumpE (i:Actors Q C):Prop:= Ponly Q C i∧ i.2.2=false
lemma bridgeTax (i:Actors Q C)(u:i∈ IIW Q C) : (if y∈ H i then αΞ i*March P.B a (H i) else 0) ≤ (if separation o y≤ThermalH L*P.B then z0 * η*(αμ i)+(if LumpE Q C i then Xκ i.1 else 0) else 0) + z0*curve_p δ P.B*(windPulse P.B o y)*(αμ i):=by
 let M:= moment3 Q C P L a δ r U A i
 let W0:= z0*η; let Z:=z0; have Hm:0 ≤ αμ i:= concave_L Q C P L K X Yt W d w a i
 let Y:=z0*curve_p δ P.B*(Lp o y)*M; have hY:0≤Y:= mul_nonneg (mul_nonneg (mul_nonneg (starQ P P.B) (Real.exp_pos _).le) (Real.exp_pos _).le) Hm
 have hP:0 ≤ (if LumpE Q C i then Xκ i.1 else 0):= ite_nonneg (lam0 Q C P L K S X Yt v W t d w uη j₀ Tκ o hz a z₁ ht h0 hk i.1) le_rfl
 let Wp:= if H0 then z0*η*M+(if LumpE Q C i then Xκ i.1 else 0) else 0; have hw:0 ≤ Wp:= ite_nonneg (add_nonneg (mul_nonneg (mul_nonneg (starQ ..) uη) Hm) hP) le_rfl
 change (if _ then _ else 0)≤Wp+ Y; split; swap; · exact add_nonneg hw hY
 next g=>
    by_cases b:B< (Zπ i).val.2.card
    · exact (curvy3 Q C P L K X Yt W d w j₀ a o y i b g hz).trans (le_add_of_nonneg_left hw)
    refine le_trans ?_ (le_add_of_nonneg_right hY)
    by_cases u': Θ i=0; · rw[show αΞ i=0 from if_pos u',zero_mul]; exact hw
    let k':=AgeQ Q (C i.1) i.2.1
    have he:=portPatch Q C X Yt w W.later d.le i u'; have hg:H0:=by
       obtain ⟨j,p,v⟩:= halo_spec.mp (pad_near Q _ _ _ _ he (Nat.not_lt.mp b) g); exact ((mem_singleton.mp p).trans (hz i.1)) ▸ v -- tune 
    unfold Antique Wp; dsimp only; rw [if_pos hg] -- tune
    by_cases hb:k'>0
    · -- αΞ term.T
      rw [if_neg u',if_neg b,if_pos hb]; apply le_trans ?_ (le_add_of_nonneg_right hP)
      let K:= March P.B (belt3 2 a) (H i); let m:= Θ i; have hm: 0 ≤ m:=πpot Q C X Yt w d.le i; let R:=m*K
      have h: L0 ≤1:=Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (Nat.cast_nonneg _)) (by positivity))
      have hr:0≤R:=mul_nonneg hm (Real.exp_pos _).le; have ha:R≤M:=le_mul_of_one_le_right hr (Real.one_le_exp (by positivity))
      have h0:0≤Z:=starQ ..; have he:= concave_cost Q C P L X Yt d w a o y i g hz
      refine le_trans (le_of_eq (b:= η*(fareX P.B P' (H i)*Θ i *March P.B a (H i))) (by ring)) (le_trans (mul_le_mul_of_nonneg_left he uη) ?_)
      change η*(Z*L0*R) ≤ Z*η*M; nlinarith only [mul_le_mul_of_nonneg_right h (show 0≤ η*Z*R from mul_nonneg (mul_nonneg uη h0) hr),mul_le_mul_of_nonneg_right ha (show 0≤η*Z from mul_nonneg uη h0)]
    rw[if_neg u',if_neg b,if_neg hb]; let v0:i.2.1.1.val.1=0:= Nat.eq_zero_of_le_zero (le_of_not_gt hb); rw [if_pos (show LumpE Q C i from ⟨Prod.ext v0 (mem_filter.mp u).2.1,(mem_filter.mp u).2.2⟩)]
    have hx:A i.1≠0:=fun h=>u' (by rw [(hue_B Q C P K S X Yt v W t d i u v0).2.2.1,h,zero_mul])
    exact (rib_q Q C P L K S X Yt v W t d w j₀ Tκ a z₁ ht h0 hk i u v0 (le_of_not_gt b) hx).trans (le_add_of_nonneg_left (mul_nonneg (mul_nonneg (starQ ..) uη) Hm))
end
end ShoreQ
end Ivey
end YM.CF.Scree.Ing
end
