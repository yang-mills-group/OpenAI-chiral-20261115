import GaugeFieldConstruction.AvenidQc
/-
# Full (89) also d=3 (not needed in U4 lift proofs which use joint d=4 inclusive). Ingredient spectral probes.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 9900
set_option maxHeartbeats 270000
noncomputable section
namespace YM.GaugeFieldConstruction.Ember.Hulse
open Calibration Raw Cauchy LabelAction Empire Fathom Payroll Function Filter Set TopologicalSpace Analysis MeasureTheory Points Bulb Palace Salam
open Floor Sailing Module
open scoped Topology BigOperators ContDiff Classical Matrix.Norms.Frobenius
attribute [local instance] iG iF iX iU iT2 iW2 iV iS
local notation "l"=> UV five
local notation "l5"=> Calibration.lift Floor.five
local notation "l3"=> Calibration.lift Floor.three
local notation "l4"=> Calibration.lift Floor.four
local notation "ℓ"=> Calibration.lift
variable {S:City}(Y:AreaQc S)(N:NickleQc) {P:Axis→Across} (L:Sheds S P)(C:Supplies L)(h: Scope L)
variable (w m:ℕ→ℝ)
structure AcePV :Prop where
 D: Tendsto (fun i=>(N.e i)⁻¹*w i) atTop (𝓝 0)
 Q: Tendsto (fun i=>(N.e i)^3*m i) atTop (𝓝 0)
 T:∀ x:UV three,FundsQc (Calibration.lift four) N w Y (Empire.one five) (Calibration.lift three x)
 S_:∀ (x:UV three)(b:UV four),FundsQc (Calibration.lift four) N m Y (Calibration.lift three x) (Calibration.lift four b)
-- canonical injection
noncomputable def Go3PV : UV three→ₗ[ℂ] UV four where
 toFun u:= (u.1,⟨u.2.1.val, (show SG three≤ SG four from bot_le) u.2.1.property⟩,
   fun j=>⟨(u.2.2.1 j).val,(show SF three≤ SF four from le_sup_left) (u.2.2.1 j).property⟩,
   fun j=>⟨(u.2.2.2 j).val,(show SX three≤SX four from bot_le) (u.2.2.2 j).property⟩)
 map_add' _ _:= rfl
 map_smul' _ _:=rfl
lemma goes3PV (x:UV three) : l4 (Go3PV x)=l3 x:=rfl
variable (v: AcePV Y N w m)
include h v
lemma Book3PV (a:Axis): ∃ T : UV three →ₗ[ℂ] UV four,(l4) ∘ₗ T=P a ∘ₗ Go3PV:=by
 have H(x:UV three):∃ i:UV four,l4 i=P a (Go3PV x):=by
    obtain ⟨F,O⟩:= RampQc Y N w l4 (l3 x) h.short (Go3PV x) (Calibration.inject four) (goes3PV x) (BootTagQc Y _ _ _ _ _ (v.T x)) v.D a
    exact ⟨F,pierPaidQc h.short _ _ _ _ O (L.money _ _)⟩
 choose p hp using H
 refine ⟨{ toFun:=p, map_add':=fun x y=>Calibration.inject four (by rw [map_add,hp,hp,hp,map_add,map_add]), map_smul':=fun a x=>Calibration.inject four (by rw [map_smul,hp,hp,map_smul,map_smul]; rfl)}, LinearMap.ext fun x=>hp x⟩
lemma Tock3PV (a:Axis): ∃ T:(Tot S P L)→ₗ[ℂ] (UV three→ₗ[ℂ] UV four), ∀ x, (l4) ∘ₗ T x=C.theta x a ∘ₗ Go3PV:=by
 have H(t:Tot S P L)(x:UV three):∃ i:UV four, l4 i=C.theta t a (Go3PV x):=by
   obtain ⟨K,u⟩:= VentureQc Y h.short N (postage a) (prints t.val) (fun n w=>stand L w t) (JetPaperQc a) 0 (fun j x=>basis a j) (fun n=> ToastQc a) m v.Q l4 (l3 x) (fun k i=> BootTagQc Y _ _ _ _ _ (v.S_ x (pens t.val k i))) (Calibration.inject four)
   exact ⟨K, uniqueReachQc h.short _ _ _ _ _ u (C.law t (Go3PV x) a)⟩
 choose T ht using H
 let R := LinearMap.mk₂ ℂ T (fun b c x=> Calibration.inject four (by rw[map_add,ht,ht,ht,map_add]; rfl)) (fun d b x=> Calibration.inject four (by rw[map_smul,ht,ht,map_smul]; rfl)) (fun a x y=> Calibration.inject four (by rw[map_add,ht,ht,ht,map_add,map_add])) (fun d a x=> Calibration.inject four (by rw[map_smul,ht,ht,map_smul,map_smul]))
 exact ⟨R,fun x=>LinearMap.ext fun y=>ht x y⟩
#print axioms Book3PV
#print axioms Tock3PV
end YM.GaugeFieldConstruction.Ember.Hulse
