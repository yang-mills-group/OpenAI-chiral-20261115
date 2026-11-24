import GaugeFieldConstruction.PangQc
/-!
# Derivative allocations from the paid estimate
-/
set_option autoImplicit false
set_option synthInstance.maxSize 7800
noncomputable section
namespace YM.GaugeFieldConstruction.Ember.Hulse
open Calibration Raw Cauchy LabelAction Empire Fathom Payroll Function Filter Set TopologicalSpace Analysis MeasureTheory Points Bulb Palace Salam
open Floor Sailing
open scoped Topology BigOperators ContDiff Classical
attribute [local instance] iG iF iX iU iT2 iW2 iV iS
local notation "l"=> UV five
variable {n : ℕ} {S:City} (Y:AreaQc S)
-- basis represent by directions all nonzero
local notation "dQ"=> ((3:ℝ)/4)
noncomputable def GalaQc (p:Axis→ Bool):E4:= WithLp.toLp 2 fun i=>if p i then dQ else -dQ
lemma galaOpenQc (p:Axis→Bool): guild (GalaQc p):=by intro i; cases k:p i <;> simp [GalaQc,k] -- tune
lemma galaNormQc (p:Axis→Bool):AnnulusQc 1 (GalaQc p):=by
 let x:= GalaQc p; have h: ∀ i:Axis, ‖x i‖=dQ:=by intro i; cases v:p i <;> simp [x,GalaQc,v] -- tune abs
 have v:‖x‖^2=9/4:=by rw[PiLp.norm_sq_eq_of_L2]; simp_rw[h,Finset.sum_const]; norm_num[Axis]
 have P:‖x‖=3/2:=by nlinarith [norm_nonneg x]
 change AnnulusQc 1 x; constructor <;> rw[P] <;> norm_num -- tune
lemma GaleDiffQc (i:Axis): (2/3:ℝ) • (GalaQc (fun j=>i= j)-GalaQc (fun _=>false))= basis i:=by
 ext1 a; by_cases p:i=a; · subst a; norm_num [GalaQc]
 simp [GalaQc,p,Ne.symm p]
lemma TiltScaleQc (q:HintQc)(b:l)(a:ℝ)(x y:E4): HeightTiltQc Y q b (a • (x-y))= (a:ℂ) * HeightTiltQc Y q b x - (a:ℂ) * HeightTiltQc Y q b y:=by
 let D (z:E4):= tilt (LonelyQc z) q.f
 have hv:D (a • (x-y))= (a:ℂ) • (D x-D y):=by
    have he:LonelyQc (n:=q.n) (x-y)= LonelyQc x - LonelyQc y:=by ext1 j; refine Fin.cases ?_ ?_ j <;> simp [LonelyQc,Points.cons]
    ext1 z; change tilt _ _ z=(a:ℂ)*(tilt (LonelyQc x) _ z-tilt (LonelyQc y) _ z); simp_rw [LoneSmQc,he,tilt_pays,YM.Analysis.D,map_smul,map_sub]; exact Complex.real_smul .. -- tune name
 let L:= Fathom.add b q.x; unfold HeightTiltQc; simp_rw [← Y.price]; change - S.fee _ L (D _) = _; rw [hv,map_smul,map_sub]; change - ((a:ℂ)*(_-_))= ↑a*(-_) - ↑a*(-_); ring
lemma LoneUnitQc (a:Axis):LonelyQc (n:=n) (basis a)= direction 0 a:=by ext1 i; refine Fin.cases ?_ ?_ i <;> simp [direction,LonelyQc,Points.cons]
lemma TiltFareQc (S:City)(s:Equiv.Perm (Fin n))(k : Fin n)(i:Axis)(p:Test n)(L:Fin n→l)(x:l): paid (s k) i (S.spot L (s k) x) p= paid k i (S.spot (L ∘ s) k x) (Fathom.perm s.symm p):=by
 rw [pays,pays,formHwQc S s]; congr 2; nth_rw 2 [←s.symm_apply_apply k]; rw[voyages s.symm] -- tune
variable (N:NickleQc)(w:ℕ→ℝ)
-- Owning derivative, generic
variable {X : Type*}[AddCommGroup X][Module ℂ X](L:X→ₗ[ℂ] UV five)(B:l)
variable (Z:∀ v:UV five,(∀ w (p:Foil),S.spot (other w) front v p.p=0)→v=0)
def PierQc (i:Axis)(V W:l):Prop:=∀ n (x : Fin n→l) k, S.spot x k W=paid k i (S.spot x k V)
include Z
lemma RampQc [Module.Finite ℂ X](P:X)(u:Injective L)(f:L P=B)(p: BloomQc Y L (Empire.one five) B w N)(R:Tendsto (fun i=> (N.e i)⁻¹*w i) atTop (𝓝 0)) (a:Axis): ∃ F:X, PierQc (S:=S) a B (L F):=by
 let A:=fun ρ=> HeightTiltQc Y ρ B (basis a); let G:= DriftQc S L
 obtain ⟨F,H⟩:=prismDoseQc G (DriftSeenQc S Z L u) A (fun I W v=>by
   have ht (x:Axis→Bool): (∑ j∈I,W j* HeightTiltQc Y j B (GalaQc x))=0:= TiltProofQc Y L N B w p R I id W v _ (galaOpenQc _) (galaNormQc _) P f -- tune
   let A':= GalaQc (fun j=> decide (a=j)); unfold A; rw[← GaleDiffQc]; simp_rw[TiltScaleQc, mul_sub, Finset.sum_sub_distrib, mul_left_comm (W _),←Finset.mul_sum,ht,mul_zero,sub_self]) -- tune
 refine ⟨F,fun n x k=>?_⟩; apply LinearMap.ext; intro t; cases n with
 | zero=> exact Fin.elim0 k
 | succ i=>
    let r:=Equiv.swap 0 k; have e:r 0=k:=Equiv.swap_apply_left ..; let B':= x ∘ r; let q:=perm r.symm t
    let ρ:= HintQc.mk i (Fin.tail B') q; have ht:=H ρ; change DriftQc S L F ρ=-(tilt (LonelyQc (basis a)) q).applyTo _ at ht; rw [DriftCostQc, LoneUnitQc, ←Y.price] at ht
    have hx:S.spot B' 0= S.tagged (Fin.tail B'):=by
       apply LinearMap.ext; intro V; rw[spot_cost,tagged_cost]; nth_rw 1 [← casedQc B']; congr 1; apply Fin.update_cons_zero
    rw [← e,formHwQc S r,TiltFareQc S r]; change S.spot B' 0 (L F) q=paid 0 a (S.spot B' 0 B) q; rw[hx, pays,tagged_cost,tagged_cost]; exact ht
lemma pierPaidQc (x y z:l)(u:Axis)(p:PierQc (S:=S) u x y)(q:PierQc (S:=S) u x z): y=z:=by
 apply sub_eq_zero.mp; refine Z (y-z) ?_; intro w g; rw [map_sub,p _ _ _,q _ _ _,sub_self]; rfl
#print axioms RampQc
end YM.GaugeFieldConstruction.Ember.Hulse
