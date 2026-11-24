import YM.SU5.FiniteGaugeData.Seld.AngleK
import YM.SU5.FiniteGaugeData.Seld.Pretzel
set_option autoImplicit false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy.Seld.Leal
open Function Filter Metric Complex Set MeasureTheory Lattice Mist Celeritas Land OS OS.Semigroup
open scoped Topology BigOperators NNReal ENNReal InnerProductSpace ComplexOrder ContDiff
variable {K:Axis→Hilbert}(W:∀ a:Axis, OS.Semigroup (K a) a)(Ω:(i:Axis)→(K i).space) {H:Hilbert} {a:Axis}
namespace Breve
variable (a b:Axis)(L A B R:Shrine K) (m n:ℕ) (o y x z:E4)(t:ℝ)
local notation "S" u:max=> sites_r o (jeer a y u) x z
local notation "Θ"=> choice4 L A B R
local notation "I" i:max o:max t:max=> orbit_on W i o t
local notation "J"=> Ω b
local notation "Y"=> W b
local notation "ι"=> parabola (W b)
local notation "η"=> Par (W b)
local notation "d"=> OS.Semigroup.duration
local notation "Γ" x:max=> coast W b (week m n) (Θ) x
variable (e:b≠a) (P': Cinema (W b))
abbrev HiL := Hi (Θ) (sites_r o y x z) b
local notation "Z"=> HiL b L A B R o y x z
-- hL yaw. Explicit formula LEFT prefix no y except spectator x + fixed o.Z def investINDEP
abbrev prefixT : (K b).Op:= orbit_on W b x L * Par (W b) m (Real.toNNReal (startX' A o-endX' L x))* orbit_on W b o A
 where startX'(A:Shrine K)(x:E4):= x b - ↑(A.t b)
       endX'(A:Shrine K)(x:E4):= x b + ↑(A.t b) -- parenth
local notation "uL"=> prefixT W b L A m o x
local notation "Lv"=> star (uL) J
local notation "Rv"=>orbit_on W b z R (Ω b)
def scope (s:ℝ≥0) (v:ℂ):= sprawl (Y) (Lv) (Rv) s (orbit_on W b y B) P' (fieldQ a b e) (field_v ..).le (m+n) n (Z 1 2) (Z 2 3) v
variable (s w:ℝ≥0)(v₀ : 0<s)(k:s<HiL b L A B R o y x z 1 2)(k':s<HiL b L A B R o y x z 2 3)
include v₀ k k'
lemma bright : scope W Ω a b L A B R m n o y x z e P' s (t:ℂ)=chalk W Ω b (week m n) (Θ) (S t) porder:=by
 unfold scope; rw [sprawlR _ _ _ t _ _ _ _ _ _ _ _ _ v₀ k k']; change inner ℂ ((uL).adjoint J) _= _; rw [ContinuousLinearMap.adjoint_inner_left]; let U':= actO W Θ (S t) b; let V:= Γ (S t); let D:= Hi Θ (S t) b; have he(i j:FHorizon): D i j= Z i j:=by
       unfold D HiL Hi startX endX; have hp(i:FHorizon): ((S t) i) b=(sites_r o y x z i) b:=by fin_cases i <;> first|rfl|exact jeer_other a b y t e.symm
       rw [hp,hp]
 have h₂: V 0 1= η m ((Z) 0 1):=by unfold V coast; rw [show week m n 0 + week m n 1=m from Nat.zero_add m, show Hi (Θ) (S t) b 0 1= HiL b L A B R o y x z 0 1 from he ..]
 have h₃: V 2 3= η n (Z 2 3):=by unfold V coast; rw [show week m n 2 + week m n 3=n from rfl,show Hi (Θ) (S t) b 2 3= HiL b L A B R o y x z 2 3 from he ..]
 have h₄: V 1 2= η (m+n) (Z 1 2):=by change Par (Y) (m+n) (D 1 2)=_; rw [he]
 change _=inner ℂ J (U' 0 (V 0 1 (U' 1 (V 1 2 (U' 2 (V 2 3 (U' 3 J))))))); rw [h₂,h₃,h₄,show U' 2=(W b).U (t • fieldQ a b e)*(orbit_on W b y B)*(W b).U (-t • fieldQ a b e) from orbit_b ..]; rfl
#print axioms bright
end Breve
end YM.CF.Buffered.Afterglow.Hierarchy.Seld.Leal
