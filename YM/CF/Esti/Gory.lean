import YM.CF.Esti.Pre
import YM.PhysicalNext.V9_JOINT_ENDPOINT_LOAD.Psalm.Baton
import YM.CF.Palot.End
import YM.CF.Appel.Sat
import YM.Next.FLUCTUATIONS.Grants
import YM.PhysicalNext.V9_JOINT_ENDPOINT_LOAD.Folio.Wind
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 600000
noncomputable section
namespace YM.CF.Esti
open Siete
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG PhysicalNext.JointLoad Heir Next.Foundations AnalyticBridge.SectorAffine AnalyticBridge.SectorAffine.Offset Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Classical Matrix.Norms.Frobenius
open AnalyticBridge.Annulus1AD
open Ac
variable {c f:Side}(S:StepData c f){r v:ℕ}
open CF.Jet
local notation "G"=> SU.group
variable {S}{n:ℕ}{θ a b m x t w K C d:ℝ}
def dram(P:Patch) := let R:=gun P+1; 2*(R+R+1)^4*25*Fintype.card PlaqAxes*81 -- estimate cardinal
lemma beam_size(i:Bond c): (beamV S i).card ≤ 2*((gun S.patch+1)+(gun S.patch+1)+1)^4:=by
 let R:= gun S.patch+1; have hp:(pinPos i).card≤2:=(Finset.card_insert_le _ _).trans (by simp)
 refine Finset.card_biUnion_le.trans ((Finset.sum_le_sum (g:=fun _=> (R+R+1)^4) fun i _=>?_).trans ?_); swap; · rw [sum_const,nsmul_eq_mul]; gcongr; exact_mod_cast hp
 simpa using (Lattice.Corona.halo_size {S.ratio.embed _} R)
lemma dam_size(i:Bond c): (nearT S i).card ≤dram S.patch:=by
 let X:=beamV S i; let R:=gun S.patch+1
 have hb :nearT S i⊆ (halo 2 X) ×ˢ (Finset.univ:Finset PlaqAxes):=by
    intro k h; obtain ⟨p,h,l⟩:= Finset.not_disjoint_iff.mp (mem_filter.mp h).2; exact mem_product.mpr ⟨halo_spec.mpr ⟨p,h, (separation_comm ..).trans_le (Work.E01.sep_touched k p l)⟩,mem_univ _⟩
 apply (Finset.card_le_card hb).trans; rw [card_product,card_univ]; refine (Nat.mul_le_mul_right _ ((Lattice.Corona.halo_size X 2).trans (Nat.mul_le_mul_right _ (beam_size i)))).trans ?_; unfold dram; dsimp only
 generalize gun S.patch=x; have ht: (2+2+1)^4≤25*81:=by norm_num
 calc
    _≤_* (25*81)*_:=Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ ht)
    _ = _ :=by ring
variable {G':Gauge}
lemma pawn{E:Type}[NormedAddCommGroup E][NormedSpace ℝ E]{f:E→G'.Mat}{x:E}{u:ℝ}(p:Allows n f x u):Allows n (fun x=> star (f x)) x u:=by
 let L:G'.Mat≃L[ℝ]G'.Mat:= starL ℝ
 rw [←one_mul u]; apply p.linear L.toContinuousLinearMap; apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one; intro x; change ‖star x‖≤_; rw [norm_star,one_mul]
section core
variable {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E]{A:Stores S}{U:E→ Config G f}{V:E→ Config G c}{q:Chi}{u:E}{k:S.Choices}
def Frolic (A:Stores S)(x:ℝ)(U:E → Config G f) (u:E):Prop:=∀ i:Bond c,onS A x i → ∀ᶠ v in 𝓝 u, Agrees (sideP S i) (U u) (U v)
lemma pervert {S:StepData c f}(A:Stores S)(U:E → Config G f){F:Forest S.ratio}(p:∀ᶠ v in 𝓝 u,∀ j: Bond f,(¬∃ a:Active A x F,j=a.val.val) → U u j=U v j)(hx:shovel S.patch+10 ≤ radiusB x): Frolic A x U u:=fun i h=>p.mono fun v p j l _=>p j (fun hp=>by obtain ⟨a,rfl⟩:=hp; exact husk hx h a l)
variable {M m':ℝ} (p:Frolic A x U u)(ht:FuelG _ U u n C)(ht':FuelG _ V u n C)(hq:Dane G n q M)(hS:S.patch.Branches S.kernel G)(g:Volo S n a b C m)(ha:0<a)(hp:1 ≤ M)(hm:0 ≤ m)(hv:1 ≤ C)
def horse(P:Patch)(n:ℕ)(C a M m:ℝ):= (SU.group.colorScale +2^n * (max 1 (zest n * dam G n (a/2) M C))^dram P *m)+1
include p hS ht g hq ha hp hm hv
lemma wears(i:Bond c) (k:S.Choices):Allows n (fun v=> Inure A x q k a i (U v)) u (horse S.patch n C a M m):=by
 unfold Inure; split; next w=>
    refine (allows_const u (C:=SU.group.colorScale) (v:=SU.group.mat (S.prediction (U u) k i)) (AnalyticBridge.SectorAffine.mat_paid ..).le|>.mono ?_).germ ?_
    · apply le_trans _ (le_add_of_nonneg_right (show (0:ℝ)≤1 from zero_le_one)); apply le_add_of_nonneg_right; exact mul_nonneg (by have h:=le_max_left 1 (zest n * dam G n (a/2) M C); positivity) hm
    filter_upwards [p i w] with v l; unfold StepData.prediction; rw [connector_p S G hS i k (U u) (U v) l]
 refine (abort_b (t:=0) S q k i ha hp (zero_le_one.trans hv) (g.wind k i) hq hm U ht).mono ?_ -- tune param extra
 apply le_trans _ (le_add_of_nonneg_right (show (0:ℝ)≤1 from zero_le_one)); refine le_trans ?_ (le_add_of_nonneg_left SU.group.colorScale_pos.le); have hx:0≤ dam G n (a/2) M C:=by unfold dam Jet.composeCost Push.Uniform.priceCost Push.Uniform.travelCost Push.Uniform.composeCost; positivity
 have he:0≤ zest n:=zero_le_one.trans (zpos n); gcongr; exact le_trans (pow_le_pow_left₀ (by positivity) (le_max_right ..) _) (pow_le_pow_right₀ (le_max_left ..) (dam_size i))
include ht'
def trout(P:Patch)(x w a C M m:ℝ)(n:ℕ) :=let d:=w*fiery G x P.L; Jet.composeCost n M ((2/d^2)*Push.Uniform.priceCost G (purM G n*C*(horse P n C a M m)))
lemma earn(i:Bond c)(w:ℝ)(k:S.Choices) : Allows n (fun z=>tidal A x w a q (U z) (V z) k i) u (trout S.patch x w a C M m n) ∧ Zed n (fun z=>tidal A x w a q (U z) (V z) k i) u:=by
 let X:= horse S.patch n C a M m; have hx:=wears p ht hq hS g ha hp hm hv i k; have he: Allows n (fun z=>star (Inure A x q k a i (U z))) u X:= pawn hx
 let N:=purM G n*C*X; have hg:Allows n (fun z=>SU.group.mat (V z i)*star (Inure A x q k a i (U z))) u N:=(ht' i).bilinear _ he (le_refl ‖ContinuousLinearMap.mul ℝ SU.group.Mat‖)
 exact hq _ _ _ _ _ _ (fare_a hg)
omit ht' ht hq hS g ha hp hm hv p -- tune
lemma earn_f(i:Cell f) (ht:FuelG _ U u n C)(hq:Dane G n q M): Allows n (fun z=>tokenF A q x (U z) i) u (dam G n (fiery G x S.patch.L/4) M C) ∧ Zed n (fun z=>tokenF A q x (U z) i) u:=by
 let f(z:E):= SU.group.price (faceValue (U z) i); have ht:=trekP _ U ht (square i.2.val.1 i.2.val.2) i.1 4 le_rfl
 have hy: fareG G ∘ (fun z=>SU.group.mat (faceValue (U z) i))=f:=funext fun i=>fare_h ..; let L:= Push.Uniform.priceCost G (Push.Uniform.travelCost G n 4 C)
 have hl:Allows n f u L:=hy ▸ (fare_a (f:=fun z=>SU.group.mat (faceValue (U z) i)) ht)
 unfold tokenF AnalyticBridge.Annulus1AD.profile; split; · simp only [Pressure.toll,chooseB]; exact hq _ _ _ _ _ _ hl
 simp only [Pressure.toll,chooseF]; exact hq _ _ _ _ _ _ hl
end core
end YM.CF.Esti
