import GaugeFieldConstruction.Weyer3
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
variable (o:Seat n)(y:Seat n)(hz:∀ i,(C i).H.val.1=o)(a:ℝ)(z₁:0≤a)
variable (ht:(belt3 2 a)*2*↑(Yaw.χ (ThermalH L)) ≤ (P.B:ℝ)*(δ/2))(h0:ζd*2*(Yaw.χ 0:ℝ)≤j₀*(δ/2))(hk: 0 < j₀)
include X t d w Yt W v ht h0 hk uη Tκ z₁ hz
local notation "αμ"=> moment3 Q C P L a δ r U A
local notation "z0"=>reserveT (KeyUp P).power P.order P.B ζd
local notation "Lp"=>windPulse P.B
local notation "L0"=> windPulse P.B o y
local notation "Bk"=> dot_Λ C P L r δ A V a j₀
variable (m u:ℝ)(uU:(∑ i:Actors Q C, moment3 Q C P L a δ r U A i) ≤ m)(vV:(∑ i:J, dot_Λ C P L r δ A V a j₀ i)≤ u)
include uU vV
lemma Money3: (∑ i∈ IIW Q C, (if y∈ H i then αΞ i * March P.B a (H i) else 0)) ≤ (if separation o y ≤Δ*P.B then z0*η*m+u else 0)+z0*curve_p δ P.B*L0*m:=by
 apply le_trans (sum_le_sum (fun i a' => bridgeTax Q C P L K S X Yt v W t d w uη j₀ Tκ o y hz a z₁ ht h0 hk _ a'))
 let p:= separation o y≤Δ*P.B; let Z:=z0 *η; let S':=z0*curve_p δ P.B*L0
 have he:0≤ Z:=mul_nonneg (starQ ..) uη; have hs:0 ≤ S':= mul_nonneg (mul_nonneg (starQ ..) (Real.exp_pos _).le) (Real.exp_pos _).le
 have hzm: (∑ i∈IIW Q C,αμ i) ≤ m:= (sum_le_sum_of_subset_of_nonneg (subset_univ _) fun i _ _=> concave_L Q C P L K X Yt W d w a i).trans uU
 rw [sum_add_distrib]; refine add_le_add ?_ ?_ -- order
 · split_ifs with h; swap; · simp only [sum_const_zero,le_refl]
   rw [sum_add_distrib,←Finset.mul_sum]; refine add_le_add (mul_le_mul_of_nonneg_left hzm he) (le_trans ?_ vV)
   rw[←Finset.sum_filter]; -- inject over J
   let Sz:=(IIW Q C).filter fun i=>LumpE Q C i
   let f(i:Actors Q C):= i.1
   have hp : Set.InjOn f Sz:=by
      rintro ⟨i,⟨u,z⟩⟩ hu ⟨j,v,s⟩ hv rfl' -- pattern tunes
      change i=j at rfl'
      subst j; obtain ⟨p,rfl⟩ := (show LumpE Q C ⟨i,u,z⟩ from (mem_filter.mp hu).2); obtain ⟨q,rfl⟩:= (show LumpE Q C ⟨i,v,s⟩ from (mem_filter.mp hv).2)
      congr -- tune
      rcases u with ⟨x,t⟩; rcases v with ⟨y,r⟩; change x.val=_ at p; change y.val=_ at q
      have hx : x=y:= Subtype.ext (p.trans q.symm)
      subst y
      haveI:IsEmpty (Fin x.val.1):= by rw [show x.val.1=0 from congrArg Prod.fst p]; infer_instance
      rw [show t=r from (show Subsingleton ↥(LeadQ _ _ _) from inferInstance).elim t r]
   rw [←Finset.sum_image (g:=f) (s:=Sz) (f:=Bk) (fun _ p _ q=>hp p q)] -- tune args. 
   exact sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun i _ _=>lam0 Q C P L K S X Yt v W t d w uη j₀ Tκ o hz a z₁ ht h0 hk i) -- shadow
 rw[←Finset.mul_sum]; exact mul_le_mul_of_nonneg_left hzm hs
end
end ShoreQ
end Ivey
end YM.CF.Scree.Ing
end
