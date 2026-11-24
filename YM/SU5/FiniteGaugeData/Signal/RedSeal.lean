import YM.SU5.FiniteGaugeData.Signal.Parachute
import YM.SU5.FiniteGaugeData.Reliance.Result
/-! # Issue native support and convergence certificate. Echo & embedding. -/
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
namespace Interval
open Showcasing Concord Ovation
variable {ℙ:Preparation}{l:ℕ} {S T:Finset Cover} (K:Calibration){x y:junior K}{c u b C:ℝ} {i k:ℕ→ℕ}
variable (z:ℂ)

def tint (K:Calibration)(x:junior K)(z:ℂ): junior K:=x-z • 1
abbrev upside (K:Calibration) : junior K →ₗ⋆[ℂ] junior K := turn K 3 0

def imprint (K:Calibration)(x y:junior K):= upside K x*y
structure Burn (K:Calibration)(f:junior K)(S:Finset Cover)(C:ℝ):Prop where
 helpline : f∈club K S
 sing : f∈singlets K
 army (n:Side)(x:Fields (K.c n)): ‖f.val n x‖ ≤ C

variable (p: Burn K x T c) (v: Burn K y S u)
include p
lemma Burn.tints : Burn K (tint K x z) T (c+‖z‖):=by
 let Y:= club K T; let Z:= singlets K; refine ⟨Y.sub_mem p.helpline (Y.smul_mem Y.one_mem z),Z.sub_mem p.sing (Z.smul_mem Z.one_mem z),fun i t=>?_⟩
 change ‖x.val i t-z • (1:FC (Single (K.c i)))‖≤_; exact (norm_sub_le ..).trans (add_le_add (p.army ..) (by simp))
lemma Burn.up : Burn K (upside K x) (shadow 3 0 T) c:= ⟨turn_support _ _ p.helpline, turn_gauge _ _ p.sing,fun i t=> blade_bound 3 0 i (p.army i) t⟩
include v
lemma Burn.earns : Burn K (imprint K x y) (shadow 3 0 T∪S) (c*u):=by
 let z : Finset Cover:= shadow 3 0 T∪S; let Z:= club K z; have h:= Burn.up K p
 refine ⟨Z.mul_mem (lodge K _ subset_union_left h.helpline) (lodge K _ subset_union_right v.helpline),(singlets K).mul_mem h.sing v.sing,fun i t=>?_⟩
 exact (norm_mul_le (blade 3 0 x.val i t) _).trans (mul_le_mul (h.army i t) (v.army i t) (norm_nonneg _) ((norm_nonneg _).trans (p.army i t)))
omit p v

-- names physical support units; every native covering-located witness; certify distances
-- on selected common assignments robustly far enough (Land for all pairs in window).
def separationCost (x y:Cover):= univ.sup fun i=> ((x-y) i).natAbs
variable (S:Finset Cover)
def Located (ad:Side):= Hosp (tips S) (K.c ad) ∧ ∀ x∈S,∀ y∈ S,separation (wrap (More (K.c ad)) x) (wrap (More (K.c ad)) y) = separationCost x y

lemma distanceLease : ∀ᶠ m:Side in atTop,Located K S m:=by
 have H(x y:Cover):∀ᶠ m:Side in atTop,lift (wrap (More (K.c m)) (x-y))=x-y:=by
    let k:= separationCost x y; filter_upwards [(c_grows K).eventually_ge_atTop (2*k+1)] with m p; change _≤(K.c m).val at p; apply lift_eq_iff.mpr; refine ⟨rfl,fun i=>?_⟩; have h:((x-y) i).natAbs≤k:= Finset.le_sup (f:=fun i=> ((x-y) i).natAbs) (mem_univ _); rw [show (More (K.c m)).val=(K.c m).val*2 from rfl]; omega
 have hx:∀ᶠ m:Side in atTop,∀ x∈S,∀ y∈S,lift (wrap (More (K.c m)) (x-y))=x-y:= (Finset.eventually_all _).mpr (fun x p=>(Finset.eventually_all _).2 fun y v=> H x y)
 filter_upwards [hx,suitable (tips S) K] with m H l; refine ⟨l,fun x t y v=>?_⟩; unfold separation pdist; rw [←map_sub]; unfold separationCost; simp_rw [H x t y v]
-- cost positive guarantees fixed separation even leaning lease
lemma separation_physical {u v:Cover}(h:u≠v): 0< separationCost (nodeC u) (nodeC v):=by
 let U:=nodeC u; let V:=nodeC v; obtain ⟨i,t⟩:= Function.ne_iff.mp (show U≠V from fun p=> h (nodeC_inj p)); refine lt_of_lt_of_le ?_ (Finset.le_sup (f:=fun i=> ((nodeC u-nodeC v) i).natAbs) (mem_univ i)); exact Int.natAbs_pos.mpr (sub_ne_zero.mpr t)

variable (Y:Course ℙ (VolumeCape.Dream.Nimbus l))(H:Real.exp 1≤ℙ.x)
variable {I:ℕ→Buffered.Family (tent Y H)→ℕ→ℂ}{E:ℕ→Buffered.Family (tent Y H)→ℂ}{Q:Playhouse ℙ l}(W:Traced Y H i k I E Q)
variable (s n d:ℕ) {x:junior (tent Y H)} -- shadow
local notation "K0"=> tent Y H
variable (g: Burn (tent Y H) x T c)
include g
local notation "δ"=> cameo Y H s x
local notation "m★" v:max=> momentm Y v s
local notation "ν"=>side Y n s
-- sizes all supported marks on sharp frame; delivered tape geometry and finite equality.
lemma spangled (p:(Y.voyage n).kick ≤ d)(v:s≤Y.uv d):
    (cameo Y H s x).val∈limited (fun _=> singlets (tent Y H)) s ∧ (cameo Y H s x).val∈ physical (tent Y H) ∧
    let f:= cameo Y H s x; let g:= (realizeStage Y H n d s W f.val).val; let z:= realizeStage Y H n d (Y.uv d) W f.val
    g=observe Y H n s x.val ∧ AtSupport false (region T (side Y n s)) g ∧ (∀ x,‖g x‖≤c) ∧
    AtSupport false (region (area ℙ l T ((Y.uv d)-s)) (side Y n (Y.uv d))) z.val ∧
    covariant z.val ∧ (∀ y,‖z.val y‖≤ winch Y s n d (Y.uv d-s)*c) ∧ reader Y H n d (Y.uv d) W f.val=Banner.sample Y H s n d x:=by
 let F:= realizeStage Y H n d s W (Style.stepFactor s x)
 let m:=Y.uv d; have hk: s+(Y.uv d-s)=Y.uv d:=by omega
 have ht : (cameo Y H s x).val∈limited (fun _=>singlets (tent Y H)) s:= resident (fun _=>singlets K0) s x g.sing
 have He: (δ).val∈Style.atLeast s:=Style.stepAt s x
 have h:F.val=observe Y H n s x.val:=congrArg Subtype.val (stage_cameo Y H n d s W x p v)
 have hg:AtSupport false (region T (ν)) F.val:= h.symm ▸ observe_support Y H n s (show InTest K0 true T false x.val from g.helpline)
 have hv: ∀ i, ‖F.val i‖ ≤ c:=by rw [h,observe_formula]; exact (Copies.constantCost ..).mpr (g.army (momentm Y n s))
 have hz:= scenic_wind Y H W s n d T He hg p c hv (m-s) hk.le; unfold m at hz; rw [hk] at hz
 refine ⟨ht, Style.to_pub _ _ ht,h,hg,hv,hz.1,currently_gauge Y H W (Y.uv d) n d (cameo Y H s x).val (Style.to_pepper _ v ht) p le_rfl,hz.2,?_⟩
 rw [Banner.sample_port Y H W s n d x p v]; exact (memorable Y H n d s W v He p le_rfl).symm
include W
omit g
lemma crownTest (S : Finset Cover):
    (∀ᶠ n in atTop,Located K0 S (momentm Y n s) ∧ ∀ ε:ℝ, 0<ε→∀ᶠ j in atTop,
        Ready Y H S s n (k j) ∧∀ (x:junior (tent Y H))(c:ℝ), Burn (tent Y H) x S c→ ‖Banner.sample Y H s n (k j) x-I s x.val n‖ ≤ ε*c) ∧
    (∀ᶠ r in atTop, Located K0 S (momentm Y (i r) s) ∧ ∀ (x:junior (tent Y H))(c:ℝ),Burn (tent Y H) x S c→
        ‖I s x.val (i r)-E s x.val‖≤ Meter r*c ∧ ∀ d,legacy Y (i r) (k d) → Ready Y H S s (i r) (k d) ∧ ‖Banner.sample Y H s (i r) (k d) x-E s x.val‖≤ Meter r*c):=by
 have he:= (momentum Y s).eventually (distanceLease (tent Y H) S); constructor
 · filter_upwards [he,(Satin.boutique Y H W.own S s).1] with n e p
   refine ⟨e,fun ε h=>?_⟩; filter_upwards [p ε h,ready_row Y H S s W.own n] with d h k; exact ⟨k,fun x c t=> h _ t.helpline _ (roomy e.1) _ (t.army _)⟩
 filter_upwards [W.crimson S s,W.own.pick.grow_i.tendsto_atTop.eventually he,meshed Y H S s W] with r k v g
 exact ⟨v,fun x c t=>⟨(k.2 _ t.helpline _ (t.army _)).1,fun d p=> ⟨(g.2 d p).1,(k.2 _ t.helpline _ (t.army _)).2 d p⟩⟩⟩
end Interval
end YM.CF.Signal
#print axioms YM.CF.Signal.Interval.spangled
#print axioms YM.CF.Signal.Interval.crownTest
