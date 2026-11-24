import VerifiedSatinGroundInteraction
import YM.SU5.Selected.Dais.Saga
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4500
set_option maxHeartbeats 650000
set_option quotPrecheck false
noncomputable section

namespace YM.CF.Buffered.Afterglow.Tower.Selection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory
open RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder
open scoped InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark OS.Semigroup MeshClock
open Vacancy

open CF.Pannier.Chancel Tapestry Papal SatinVerification
open CF.Pannier.Chancel.Lantern CF.Pannier.Chancel.Lantern.Bulb CF.Pannier.Chancel.Lantern.Bulb.Mezz
open Crest.Airy (Coast Wq)
open Mileage
attribute [local instance] opCStarAlgebra
namespace Season
attribute [local instance] opCStarAlgebra
open LocalLimit.Rundle
abbrev DStar:ℝ := (Dais.Span.delay (show 1≤ (4:ℕ) by decide)).choose
private lemma star_shift {j:ℕ}(h:1 ≤ j)(x:j=4): (Dais.Span.delay h).choose=DStar:=by subst j; rfl
lemma tipS (Λ:Preparation): season_tip (Λ:=Λ)=DStar:= star_shift (by rw [Λ.kJ]; decide) Λ.kJ
theorem Newtopia (x γ ε Ω:ℝ)(p0:10000 ≤ Ω)(p:0<γ)(hv0:0<ε) (z:Supplier) :
    ∃ (Λ' : Preparation) (l' : ℕ) (Z : ℝ), x < Λ'.x ∧ Λ'.d ≤ γ ∧ decorate z Λ' l' Z ≤ Λ'.h ∧ Λ'.d≤ Mileage.austere∧ Scooped Λ' ∧ Λ'.nominated (VolumeCape.Dream.Nimbus l') ∧
    ∃ (H : Real.exp 1 ≤ Λ'.x) (Y : Course Λ' (VolumeCape.Dream.Nimbus l')),
      wavering Y ε ∧ (∃ t:ℝ,0<t∧t≤1∧t⁻¹≤Λ'.h ∧ eternal Y t ε)∧ (∃ z', Usable (D:=Λ'.δ) Λ'.V Λ'.W Λ'.J Λ'.N0 z' Λ'.delay Y.meter) ∧
      (∀ i k, ((Y.voyage i).X k).Prepared Λ'.P Λ'.delay) ∧
      (∀ i j:ℕ, Buffered.Advance.LoomLaw ((Y.voyage i).CapeT j) (YM.SU5.FiniteGaugeData.Audit1102.lawRadius (VolumeCape.Dream.plot l').C)) ∧
      ∃ (q d w : ℕ) (c : ℝ) (D0 : Council.Choir Y H q d w c Z Ω)
      (i k : ℕ → ℕ) (I : ℕ → Family (tent Y H) → ℕ → ℂ) (E : ℕ → Family (tent Y H) → ℂ)
      (L0 : Rack Λ' l') (P0 : Clay Λ' l') (T' : ℕ→ℕ→Tariff) (t : ℕ→Tariff) (V : Fashion Y H i k I E L0 P0 T' t) (Q' : SatinVerification.GroundExtension (i := i) (k := k) (E := E) Y H)
      (b v n : ℕ)(γ' A E':ℝ)(Φ:Mezz)(X X' Z': Coast→ Wq Φ.marks)(u:Mileage.Effigy Y H Ω b v γ' A E' Φ n X X' Z'),
      SeasonCert Y H V ∧ Nonempty (∀ v : Axis,Arena Y H Q'.history.circuit v 0 false) ∧
        ∀ (C : ∀ v : Axis,Arena Y H Q'.history.circuit v 0 false) (a : ℕ),
        ∃ (Ψ:Horizon Y H V.univ_ Q'.history Q'.clipped 3 false (C 3)) (x:Ψ.X) (s m m':ℕ)(L:∀ W:Window.Family,Bool→ Sermon Φ (tent Y H) W)(Z:SU.Slot→Family (tent Y H)), a ≤ s ∧ Fern.TimeLine Y H V.univ_ Q'.history Q'.clipped C s m m' Ψ V.toExhibition u L q d w Z x:=by
 let d:= DStar; have hd:0<d:= (Dais.Span.delay (show 1 ≤ (4:ℕ) from by decide)).choose_spec.1
 let ψ:=Real.sqrt (ε/(d+1)); let τ:= min ψ (1:ℝ); have ht:0<ψ:=by unfold ψ; positivity
 have he:0<τ:=lt_min ht zero_lt_one
 let z':Supplier:=fun K p X V B d T W M J l Z=> max (z K p X V B d T W M J l Z) τ⁻¹
 obtain ⟨Λ,l,Z,g,pβ,hσ,sc,h,H,Y,ca,q,w,q₀,u,m,c,X,i,k,I,E,r,v,T,t,V,Q,b,y,w₀,a₀,G,d_0,L,z₀,x₀,y',W,p',v',F⟩:= SkySprint x (min γ Mileage.austere) Ω p0 (lt_min p Mileage.aust_p) z'
 have ht:τ⁻¹≤Λ.h:=le_trans (le_max_right ..) hσ; have hε: eternal Y τ ε:= by
    apply eternal_m Y (frost_voice Y τ he (min_le_right ..) (pβ.trans (min_le_right ..)) sc); rw [tipS]; change (d+1)*τ^2 ≤ _; apply le_trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ he.le (min_le_left ψ _) 2) (by positivity)); unfold ψ; rw [Real.sq_sqrt (by positivity), mul_div_cancel₀ _ (by positivity : d+1 ≠ 0)] -- tune
 exact ⟨Λ,l,Z,g,pβ.trans (min_le_left ..),le_trans (le_max_left ..) hσ,pβ.trans (min_le_right ..),sc,h,H,Y,minute Y he (min_le_right ..) ht hε,⟨τ,he,min_le_right ..,ht,hε⟩,ca,q,w,q₀,u,m,c,X,i,k,I,E,r,v,T,t,V,Q,b,y,w₀,a₀,G,d_0,L,z₀,x₀,y',W,p',v',F⟩ -- d conflict etc.
end Season
end YM.CF.Buffered.Afterglow.Tower.Selection
#print axioms YM.CF.Buffered.Afterglow.Tower.Selection.Season.Newtopia
