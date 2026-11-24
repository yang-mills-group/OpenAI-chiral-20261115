import YM.SU5.Assay.Issuing
import YM.SU5.Assay.RawTransfer
import YM.SU5.Assay.Belt
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4900
set_option maxHeartbeats 420000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance
namespace Spine
open Aria Set OS.Semigroup
variable (P:Spine)(j:Axis)(x:P.Spectrum0 j)
local notation "K"=> P.calibration
local notation "H"=> P.ColorHil j x
local notation "B"=> P.ManyF j x
local notation "X"=> (P.ColorHil j x).Op
local notation "Y"=> (P.ManyF j x).Op
local notation "Lag"=>ℝ→ℝ→(P.ManyF j x).Op
local notation "S"=> P.seasons j x
local notation "U"=> P.physicalEnergy j x
local notation "ω"=> (P.seasons j x).wax
local notation "W"=> P.cartage j x
local notation "θ"=> P.tableau j x
local notation "E"=> P.enter j x
local notation "R"=> P.wealth j x
local notation "Vac"=> P.colorZero j x
local notation "Ω"=> P.heaven j x
/-! Measure across a belt seam at this very height. Also controls all lags outward, even
 immediately at joint enrollment. -/
variable (D:P.Apron){a b c d:ℝ}
local notation "τ"=>P.tock
local notation "β"=>P.rawBase j x
local notation "ρ"=> P.charter j x
local notation "𝔤"=>P.Grips j x
local notation "δ"=>D.realWidth P j
lemma grips_fixed (p:δ≤a)(q:δ≤b):𝔤 D.s (-a) b D.F (β D a b):=by
 let s:=D.s; let w:=D.u j
 have h₁:τ s (-(w:ℤ))= -δ:=by rw [←zero_sub (w:ℤ), P.tock_sub,P.tock_zero,zero_sub];rfl
 have h₂:τ s (-(w:ℤ)+((w+w:ℕ):ℤ))=δ:=by rw [Nat.cast_add,←add_assoc,neg_add_cancel,zero_add];rfl
 let g:=D.admit j
 refine Sill.grips (m:=-(w:ℤ)) (w:=w+w)
   ⟨by erw [h₁]; exact neg_le_neg p,by erw [h₂];exact q,⟨by rw [neg_neg];exact g,D.realM⟩,?_⟩
 erw [h₁,h₂,costing,neg_neg]
 rw [show -δ- -a=a-δ by abel,P.rawBase_engineAxle];rfl
lemma native_place (y:Cover): P.issuing D.s D y=P.chartAll y D.F:=by unfold issuing Apron.full;rw [Nat.sub_self];rfl
lemma grips_place (y:Cover)(p:δ≤τ D.s (y j)-a)(q:δ≤b-τ D.s (y j)):
 𝔤 D.s a b (P.chartAll y D.F) (ρ (P.vtile D.s y) (β D (τ D.s (y j)-a) (b-τ D.s (y j)))):=by
 let t:=P.issuing_grips j x D.s D y le_rfl p q
 rw [native_place,P.raze_align] at t
 exact t

local notation "ζ"=>P.rawUnit j x
lemma rawUnit_step (p:0≤a)(q:0≤b)(t:a≤c)(v:b≤d):
  ζ c d=(U).sand (ζ a b) (c-a) (d-b):=by
 unfold sand rawUnit
 rw [wax_sq (U) (by linarith) (by linarith),wax_sq (U) (by linarith) (by linarith),show c-a+(a+b)+(d-b)=c+d by abel]
lemma rawBase_unit_cost (p:δ≤a)(q:δ≤b)(t:a≤c)(v:b≤d):
 ‖β D c d-ζ c d‖≤‖β D a b-ζ a b‖:=by
 let k:0≤δ:=(D.real_width_pos P j).le
 rw [P.rawBase_step j x D p q t v,P.rawUnit_step j x (k.trans p) (k.trans q) t v,←sand_sub]
 exact sand_pay ..

variable {P j}{s w:ℕ}
namespace Glaze
variable {A C:P.Glaze}(p:A.w≤w)(q:C.w≤w)
local notation "χ"=>P.tock s
local notation "m"=>χ w
local notation "o"=>pinDiagonal w
local notation "n"=>χ (pinOut w)
local notation "g"=>P.vtile s o
include p q in
private lemma belt_slots (u:χ (pinPay w)≤a)(v:χ (pinPay w)≤b):
 χ A.w ≤ m ∧ m ≤ a ∧ m ≤ b ∧ χ C.w ≤ m ∧ m ≤ n-m ∧ m ≤  b-n :=by
 have t:=P.tock_one s;have h:=P.macroStep_pos s
 have d:n=m+m+P.macroStep s:=by unfold pinOut;rw [Nat.cast_add,Nat.cast_add,Nat.cast_one,P.tock_add,P.tock_add,t]
 have k:0 ≤ m:=by rw [P.tock_when];positivity
 have e:χ (pinPay w)=n+m:=by unfold pinPay;rw [Nat.cast_add,P.tock_add]
 exact ⟨by rw [P.tock_le];omega,by linarith, by linarith, by rw [P.tock_le];omega, by linarith, by linarith⟩
lemma belt_price (u:χ (pinPay w) ≤ a)(v:χ (pinPay w) ≤ b):
 β ((belt p q).apron s) a b=β (A.apron s) a m * ρ g (β (C.apron s) (n-m) (b-n)):=by
 obtain ⟨r,t,y,f,l,k⟩:=belt_slots p q u v
 exact (P.grips_fixed j x ((belt p q).apron s) u v).unique
   ((P.grips_fixed j x (A.apron s) (r.trans t) r).join
     (P.grips_place j x (C.apron s) o (f.trans l) (f.trans k)))

lemma belt_cost (u:χ (pinPay w) ≤ a)(v:χ (pinPay w) ≤ b)
 (h:χ A.w ≤ c)(t:χ C.w ≤ c)(r:c ≤ m):
 ‖β ((belt p q).apron s) a b-β (A.apron s) a b‖ ≤ 
  ‖β (A.apron s) c c‖*‖β (C.apron s) c c-ζ c c‖:=by
 let α:=β (A.apron s); let η:=β (C.apron s)
 obtain ⟨j₀,j₁,j₂,z,l,k⟩:=belt_slots p q u v
 have Y':α a b= α a m * ρ g (ζ (n-m) (b-n)):=by
   unfold α rawUnit
   have h': (A.apron s).realWidth P j ≤ m:=j₀
   calc
     _=(U).sand (α a m) (a-a) (b-m):=P.rawBase_step j x (A.apron s) (h'.trans j₁) h' le_rfl j₂
     _=_:=by unfold sand;rw [P.charter_wax,show n-m+(b-n)=b-m by abel,sub_self,wax_zero,one_mul]
 unfold α at Y'
 rw [belt_price x p q u v,Y',←mul_sub,←P.charter_sub]
 refine (norm_mul_le ..).trans ?_
 rw [P.charter_cost]
 have h': (A.apron s).realWidth P j ≤ c:=h
 exact mul_le_mul (by change ‖β (A.apron s) a m‖ ≤ _;rw [P.rawBase_step j x (A.apron s) h' h' (r.trans j₁) r]; exact sand_pay ..)
     (P.rawBase_unit_cost _ _ _ t t (r.trans l) (r.trans k)) (norm_nonneg _) (norm_nonneg _)
end Glaze
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
