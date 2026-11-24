import Bay.Deck.Stage
import SatinThinPlant
import SatinThinFund
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

open YM.CF.Pannier.Chancel
open Py Py.Rate Py.Rate.LocalLimit Preparation Pitching.Focus
open Pitching Push.SectorMeasure
open SectorNext.Remainder.Scales
namespace D

/-- headroom implies Cistern (for the external Thin tariff). merit≤x^(-1/4).
    Compare pays_m. -/
lemma cisternFrom (P:Preparation)(p:Meritorious P):
   Cistern P.J Chi.canonical P.h P.P P.N0:=by
 constructor; intro t ht
 filter_upwards [p.toll t ht,eventually_gt_atTop (0:ℝ)] with x h hx m n w v u l b G a g c
 unfold Heed
 have he: x≤y SU.group P.R.L x:=le_add_of_nonneg_right (mul_nonneg (Work.E07.slope_nonneg _) (Real.log_nonneg (by exact_mod_cast P.R.L.property)))
 have hs: merit P.R.L x ≤ x^(-(1/4:ℝ)):= by
   refine le_of_pow_le_pow_left₀ (n:=4) (by decide) (by positivity) ?_
   rw [←Real.rpow_mul_natCast hx.le, show -(1/4:ℝ) * (↑(4:ℕ):ℝ)= -1 by norm_num, Real.rpow_neg_one]
   rw [show (merit P.R.L x)^4=(SectorNext.Remainder.Scales.g SU.group P.R.L x)^2 from (pow_mul (merit P.R.L x) 2 2).trans (congrArg (·^2) (Real.sq_sqrt (SectorNext.Remainder.Scales.gauge _ _ (hx.trans_le he)|>.le)))]
   . rw [←show _⁻¹=_ from eq_inv_of_mul_eq_one_right (yg2 _ _ (hx.trans_le he))|>.symm]
     exact inv_anti₀ hx he
 exact (h m n w v u l b G a g c).trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hs ht.le) (zero_le_one.trans (sites_pos _)))

def DryDock (P:Preparation):Prop:= Meritorious P ∧
  ∃ ε a C D:ℝ, ∃ v b:ℕ, Papal.Convent P ε a C D v b

lemma commission {F:Preparation→Prop} (f:CommissionVector F):
   CommissionVector (fun P=>F P ∧
       ∃ ε a C D:ℝ, ∃ v b:ℕ, Papal.Convent P ε a C D v b):=by
 constructor; intro e z p Q
 obtain ⟨d,a,C,v,k⟩:=finishingLine 4 (by decide)
 obtain ⟨D,j,b,w⟩:=Rapids.assemblesAt 4 (by decide)
 let t:=(C+1)*(45*(D+1))
 let Y:Supplier:=fun r y u j x i v w m l n h=>max (Q r y u j x i v w m l n h) t
 obtain ⟨P,x,h,B,V,g,l,u,m,n,T,s⟩:=f.purchased (min e d) z (lt_min p k.health) Y
 

 change max (decorate Q P x h) t ≤ P.h at V
 refine ⟨P,x,h,B,(max_le_iff.mp V).1,g,l.trans (min_le_left ..),u,m,n,
    ⟨T,d,a,C,D,v,b,⟨?_,j,?_,l.trans (min_le_right ..),(max_le_iff.mp V).2⟩⟩,s⟩
 · rw [P.kJ]; exact k
 rw [P.kJ]; exact w
end D
end YM.CF.Bay
