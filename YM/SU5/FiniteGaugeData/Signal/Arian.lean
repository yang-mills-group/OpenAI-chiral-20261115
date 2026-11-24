import YM.SU5.FiniteGaugeData.Signal.RedSeal
/-! # New target: rooted strict centered reflection.

This reduction is on the already mixed hierarchy & around THESE NEW candidates.
It asks for square-billing (signed), not postulating any comparison through changing gates/models;
uses uncentered finite prices with ∥ ∥ certificate and no extra W. Also translates to Γ-halo
so one can aim positivity from full kernel telescope. Remains an open estimate!
 -/
set_option autoImplicit false
set_option linter.flexible false
set_option maxHeartbeats 760000
set_option synthInstance.maxSize 24000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Signal
open Function Filter NormedSpace MeasureTheory Finset Lattice RG Wilson Fock Lat Cube SU Scroll Spire Tulip
open Window Mir Skye Scree Rush Dial Laic Thera Nacre Drapes Paige Vault Peaks Cascade Hive
open Buffered Buffered.Afterglow Buffered.Advance Reef Hom Tenant Branch Buffered.Concord Buffered.Afterglow.Satin Lifted
open MeasureTheory Push.SectorMeasure Girt
open scoped Topology ContDiff InnerProductSpace BigOperators Matrix MatrixOrder ComplexOrder Kronecker Classical Matrix.Norms.L2Operator ComplexConjugate Pointwise
attribute [local instance] opCStarAlgebra
open Supplies Sparkle Sparkle.Condense Sparkle.Portage Sparkle.Circuit Pastel Momentum Furnace
open Scherzo Kinetic Play Py Py.Rate LocalLimit Preparation Skyscraper IgnoreFog Vale Period
open Buffered.Reliance Buffered.Reliance.ShortWave Afterglow Afterglow.Journey
open Boon Graph Pressure Esti Jade.Earn Phase CF.Laic CF.Ember
open Escalator Concord Boon Parfume
namespace Ovation
variable {P:Preparation}{k' d q r Ul b kd l':ℕ}(Y:Course P (VolumeCape.Dream.Nimbus l'))(H:Real.exp 1 ≤ P.x){g C Ω z a:ℝ}
open CF.Signal.Interval
variable {i k:ℕ→ℕ}{F:ℕ→Buffered.Family (tent Y H)→ℕ→ℂ}{E:ℕ→Buffered.Family (tent Y H)→ℂ}{Q:Playhouse P l'}
local notation "K"=> tent Y H
local notation "U"=> wing (tent Y H) 3 0 (tent Y H).ℓ
local notation "π"=> haloRule Y H 3 0
variable (W:Traced Y H i k F E Q)(s:ℕ)
local notation "Pr"=> portfolio Y H W
local notation "V·" i:max=>intake Y H s W.own i

variable (f:junior (tent Y H))
include W
local notation "Θ"=> Interval.upside (tent Y H)
private def rootPos : U →ₗ⋆[ℂ] (U→ₗ[ℂ]ℂ) where
 toFun f:= { toFun g:=intake Y H s W.own (upside (tent Y H) f.val * g.val)
             map_add' := fun x y=> by change V· (_*(x.val+y.val))=_; rw [mul_add,map_add]
             map_smul' := fun a x=> by change V· (_*(a • x.val))=_; rw [Algebra.mul_smul_comm,map_smul]; rfl }
 map_add' x y:=by apply LinearMap.ext; intro t; change V· (Θ (x.val+y.val)*t.val)= (intake Y H s W.own (Θ x.val*t.val))+intake Y H s W.own (Θ y.val*t.val); rw [map_add Θ, add_mul,map_add]
 map_smul' a x:=by apply LinearMap.ext; intro t; change V· (Θ (a • x.val)*t.val)=star a • (intake Y H s W.own (Θ x.val*t.val)); rw [map_smulₛₗ (f:=Θ), Algebra.smul_mul_assoc,map_smul]; rfl
local notation "P'"=> rootPos Y H W s
private lemma stemZ (x:U): 0 ≤ (P') x x:= by
 have hp:0=Heat.gaugeShift P.block 0:=by unfold Heat.gaugeShift; ring; -- tune
 change 0 ≤ intake Y H s W.own (turn K 3 0 _*_); nth_rw 1 [hp]; exact diagonals Y H s 3 0 W.own x.val (by rw [←hp]; exact x.property)
variable (u:f∈wing (tent Y H) 3 0 (tent Y H).ℓ)
local notation "ξ"=> intake Y H s W.own f
abbrev Tinted:= Interval.tint (tent Y H) f (intake Y H s W.own f)
local notation "F'"=> Tinted Y H W s f
local notation "Ω'" x=> imprint (tent Y H) x x
lemma untint : portfolio Y H W (cameo Y H s (Tinted Y H W s f))=0:=by
 rw [Banner.placing Y H W,←intake_eq Y H s W.own]; unfold Tinted Interval.tint; rw [map_sub,map_smul,intake_one]; change ξ-ξ*(1:ℂ)=0; rw [mul_one,sub_self]
private lemma springs: intake Y H s W.own (Interval.tint (tent Y H) f (ξ)) =0:=by have he:=untint Y H W s f; rw [Banner.placing Y H W, ←intake_eq Y H s W.own] at he; exact he
include u
private lemma harmony : intake Y H s W.own (upside K f)=star ξ:=by
 have he:= Consent.herm P' (stemZ Y H W s) (1:U) (⟨f,u⟩:U); change star (intake Y H s W.own (turn K 3 0 1*f))= intake Y H s W.own (Θ f*1) at he; rw [turn_one, one_mul,mul_one] at he; exact he.symm
lemma rooted_bill : intake Y H s W.own (imprint (tent Y H) (Tinted Y H W s f) (Tinted Y H W s f)) = (V· (imprint K f f))- (↑(‖intake Y H s W.own f‖^2:ℝ):ℂ):=by
 let E:=intake Y H s W.own
 unfold Tinted imprint Interval.tint
 rw [map_sub Θ, map_smulₛₗ (f:=Θ), starRingEnd_apply, show Θ 1=1 from turn_one .., _root_.sub_mul,mul_sub (Θ _),map_sub,map_sub,Algebra.smul_mul_assoc,map_smul,Algebra.mul_smul_comm,map_smul,mul_one,harmony Y H W s f u,one_mul,show intake Y H s W.own (f-(ξ) • 1)=0 from springs Y H W s f, smul_zero, sub_zero,←Complex.normSq_eq_norm_sq, Complex.normSq_eq_conj_mul_self]; simp only [smul_eq_mul, mul_comm ξ]; rfl

def Escrow (u w: ℕ→ℕ)(c:ℝ):Prop:= ∃ᶠ n in ConeFilter Y u w,c ≤ (Banner.sample Y H s (u n.1) (w n.2) (imprint (tent Y H) f f)).re - (‖Banner.sample Y H s (u n.1) (w n.2) f‖^2:ℝ)
lemma sustains (c:ℝ)(p:0<c)(r:Escrow Y H s f i k c): 0 < portfolio Y H W (cameo Y H s (Ω' (Tinted Y H W s f))):=by
 have hW:F'∈ U:=(U).sub_mem u ((U).smul_mem (U).one_mem _)
 have ht := stemZ Y H W s ⟨F',hW⟩
 have h:(0:ℂ) ≤ V· (Ω' F'):= ht -- prop conv tune
 rw [Banner.placing Y H W, ← intake_eq Y H s W.own]; apply Complex.lt_def.mpr; refine ⟨?_,(Complex.le_def.mp h).2⟩
 have hr:c≤ (intake Y H s W.own (Ω' f)).re-(‖intake Y H s W.own f‖^2:ℝ):=by
    have h:= Banner.cone_sample Y H W s f; have hx:= Banner.cone_sample Y H W s (Ω' f); rw [←intake_eq Y H s W.own f] at h; rw [←intake_eq Y H s W.own (Ω' f)] at hx
    by_contra! v; exact r (((Tendsto.sub (Filter.Tendsto.comp Complex.continuous_re.continuousAt hx) (h.norm.pow 2)).eventually (gt_mem_nhds v)).mono (fun a h=> not_le.mpr (show _<c from h)))
 rw [rooted_bill Y H W s f u]; rw [Complex.sub_re, Complex.ofReal_re]; exact p.trans_le hr -- simplification
omit W u
lemma zero_step : steady P 0 s=0:=by rw [steady_aligned]; unfold Heat.gaugeShift; ring
include u
private lemma rendezvous : (cameo Y H s f).val∈ haloRule Y H 3 0:=by
 apply Style.to_pub _ s; apply resident (BookRule (tent Y H) 3 (steady P 0) (reserve P l')) s f; rw [BookRule, zero_step _]; exact u
/- Positivity already established, this is just embedding and identification -/
include W
lemma halos :
    ∃ x:haloRule Y H 3 0, Concord.input Y H 3 0 x=cameo Y H s f ∧ midway Y H 3 0 (Concord.input Y H 3 0 x)= cameo Y H s (upside (tent Y H) f)∧
    formPanel Y H W 3 0 x x= E s (imprint (tent Y H) f f).val:=by
 let x:haloRule Y H 3 0:=⟨(cameo Y H s f).val,rendezvous Y H s f u⟩; have ht:Concord.input Y H 3 0 x=cameo Y H s f:=rfl; have he:midway Y H 3 0 (Concord.input Y H 3 0 x)=_:= (by rw [ht,Banner.midway_turn,zero_step s] : midway Y H 3 0 _ = cameo Y H s (turn (tent Y H) 3 0 f))
 refine ⟨x,ht,he,?_⟩; change Pr (midway Y H 3 0 (Concord.input Y H 3 0 x) * Concord.input Y H 3 0 x)=_; rw [he,ht, ←map_mul, Banner.placing Y H W]; rfl
end Ovation
end YM.CF.Signal
#print axioms YM.CF.Signal.Ovation.sustains
#print axioms YM.CF.Signal.Ovation.halos
