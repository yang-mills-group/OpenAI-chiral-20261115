import YM.CF.Sour.Pie
import YM.CF.Ione.Rake
import YM.CF.Exa.Water
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Sour
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open Skye Scree Cadre Palot
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open Cube Lat Tulip Fock Rush Scroll Paige Vault Phase Acorn Spire
open Pastry Vow Rue
attribute [local instance] opCStarAlgebra
variable {n:Side}
local notation "SA"=> Seat n
local notation "VX"=> Aura n
local notation "Hk"=> hook SA
open Hake Jet Sault Stax
attribute [local instance] loreM loreN
variable {P:BudgetPoint}{X Y Z:Aura n}{V W:Firing n}{D:Support (More n)}
open Branch Tenant Drapes Rill Sault
attribute [local instance] Rill.boreKSpace Rill.boreXN
local notation "JS"=> Single n
local notation "SO"=> Support (More n)
local notation "Γ"=> (FC (Dwell n))
open Exa Tap Dial
-- sweep weight.TIO. openc slice.S.inverse. erosion
open Levier Thera Urn Nacre Salt
variable (s t:Sweep n)(a:ℝ)
abbrev γS(s:Sweep n):= siteU (castX s) s.charge (spinU s.charge s.s) n
abbrev ech(s:Sweep n):= sings s.charge (siteU (castX s) s.charge (spinU s.charge s.s) n)
abbrev bolt(s:Sweep n):Op (Single n) → Op (Single n):= Sault.hitL s.charge (detX s.s) (γS s)
abbrev foeL(s:Sweep n):Op (Single n) → Op (Single n):= Sault.doveL s.charge (detX s.s) (γS s)
local notation "p₀"=> s.charge
local notation "x₀"=> castX s
local notation "T"=> γS s
local notation "Ω"=> Openc (More n) a
lemma sigW(A:Shape)(b:Bool)(U:UNI SpinIdx)(Y:Op JS):sings b (siteU (castX (Levier.ray (N:=n) b A)) b U n) Y=sings b (siteU A b U n) Y:=by
 let B:=wrap n A.t; let z:= fee (Rush.periods n (Lattice.lift B)-Rush.periods n A.t); have he: (siteU (castX (ray b A)) b U n).val= z • (siteU A b U n).val:=utu n b _ _ _ _ (wrap_lift _)
 rw [singT,singT,twist_formula,twist_formula,he,star_smul]; simp only [Matrix.mul_smul, Matrix.smul_mul, smul_smul,show star z=z from fee_real _,←pow_two,show z^2=1 from (pow_two _).trans (fee_one ..),one_smul]
lemma poll(A:Shape)(b:Bool)(X:Op (Single n))(V W:UNI SpinIdx)(p:JetS A.s b (detX A.s) V)(q:JetS A.s b (detX A.s) W): sings b (siteU A b V n) X=sings b (siteU A b W n) X:=by
 have ht:= Cour.turn_r A b V W X p q; unfold Cour.yank Thera.jazz at ht; split at ht; exact star_injective (neg_injective ht); exact ht
lemma paceK(X:Op JS):ech t (ech s X)=ech (s*t) X:=by
 unfold ech; rw [wake_r,Levier.turns]; let a:=castX s; let b:=castX t; let U:=spinU t.charge t.s; let V:=spinU p₀ s.s; let Z:=U * whiten t.charge V; let P:=joinX a b
 have hx: (s*t).s=P.s:=rfl; let c:=s.charge.xor t.charge; have hv: (s*t)=Levier.ray (N:=n) c P:=by unfold P c; rw [←ray_join,show Levier.ray (N:=n) p₀ a=s from ray_i s,show Levier.ray (N:=n) _ b=t from ray_i t];
 change sings c (siteU P c Z n) X= sings c (siteU (castX (s*t)) c (spinU c P.s) n) X; rw [hv, sigW]; exact poll _ _ _ _ _ (shineU p₀ a t.charge _ _ _ (spinZ ..) (spinZ ..)) (spinZ ..) -- tune signature
lemma beat_x(X:Op JS): ech 1 X=X:=by
 have he:=paceK 1 1 X; rw [one_mul] at he; exact (show Injective (ech (n:=n) 1) from (twist _).injective) he -- tune
lemma wardE(g: Seat n→ SU.E):ech s ((tradew n g).val)= (tradew n (Levier.starG s.charge (castX s) g)).val:=by
 let X:=tradew n g; let W:=tradew n (Levier.starG s.charge (castX s) g); let H:=γS s
 have hp:H * whiten s.charge X=W*H:=by unfold X W H γS; rw [site_ui,Hive.tr_s]; exact Nacre.envoy ..
 have he: windX s.charge X.val=(whiten s.charge X).val:=by cases b:s.charge <;>rfl
 change twist H (windX s.charge X.val)= _; rw [twist_formula,he]; change (H*whiten s.charge X).val *star H.val = W.val; rw [hp]; change W.val*H.val*star H.val=_; rw [mul_assoc, show H.val*star H.val=1 from H.property.2,mul_one]; -- tune
local notation "V"=> (forum n a)
def fog (s:Sweep n)(a:ℝ)(x:↥(Openc (More n) a)):↥(Openc (More n) a):=⟨gateC s.charge (castX s) x.val,by
 obtain ⟨U,q,h⟩:=x.property
 exact ⟨stir (xtra s.charge) (castX s) U,keepC _ _ _ _ q,by rw [veil_p,gate_n]; exact h⟩ ⟩
lemma sway(K: Seat n→ SU.E)(x:↥Ω):fog s a ((forum n a).drive K x)=(forum n a).drive (Levier.starG p₀ (castX s) K) (fog s a x):= Subtype.ext (covB p₀ _ _ _)
-- Support permutation actY k
lemma tock (X:SO): roarD n x₀ X=actY s⁻¹ X:=by unfold roarD actY; rw [sitU]; rw [map_eq_image]; rfl -- tune locations
lemma rite(D:SO)(x y:↥Ω):(forum n a).eval (actY s D) (fog s a x) (fog s a y)=(forum n a).eval (actY s⁻¹ (actY s D)) x y:=by change fare _ _ _/_= fare _ _ _ / _; unfold fog; rw [roseC, tock] -- orientation for suite? choose H(x)=ech_s inverse applied to F at fog s x; needs inequality EXPO new at S' where OLD S; uses F expo(evaluate old S). `roseC old= new`. need Snew=actY s⁻¹ S?? indeed check. Parent_x sign.
lemma gate_v:Continuous (fog s a):=Continuous.subtype_mk ((gate_c ..).comp continuous_subtype_val) _
end YM.CF.Sour
