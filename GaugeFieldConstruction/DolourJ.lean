import GaugeFieldConstruction.CannonJ
import GaugeFieldConstruction.Enmity
import GaugeFieldConstruction.Quail
import YM.CF.Roots.East
import GaugeFieldConstruction.Overland
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 800000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Py.Rate
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open AnalyticBridge.Annulus1AD Ac Esti
open Atala Forge Cloak Rill Hive Fock Stilo Palot Scion
open Cube Lat Tenant Tulip
open Pastry Hake Levier Urn Peaks Fock Laic Branch Drapes
attribute [local instance] opCStarAlgebra
open Rush Scroll Paige Vault Phase Acorn Spire
attribute [local instance] opCStarAlgebra
open Tarn Cay Slate Esti Cour Hest Arena Reine Kennel Facet Broc Pec Push.SectorMeasure.Oriented
open Hom Vale Vale.Grace Next.Free Thera Nacre Dial Fock
open Tye Lich Stake Pail Pail.Dew
open Ione Beau Haro Cascade Fief
open Wray Oath Feu Feu.Corset Nor Yaw Pig Oise Jade Plume Push.AbsoluteSums
open Trees Lich.Muster Jet
set_option linter.flexible false
open Eire Girt
open VolumeRate
namespace Pitching
open Vow Bake Larch
namespace Focus
open Neon
open Mew Vow Rive Roots
open scoped YM.CF.Mew
namespace CoeffArc
section
variable {N:Side}{I Z D E : Type}[Fintype I][LinearOrder I][Fintype Z] [NormedAddCommGroup E][NormedSpace ℂ E][CompleteSpace E]
-- Amplify only desired NOW for key-charge.ALL payment F0 bigger.Post family.
open Scree.Ing Scree.Ing.Iona
variable (σ:I→Site N)(A:Finset I) (X:Cornea Z D E N)(H:∀ i,(X.Φ i).Nonempty)(u:Finset I→Z→ D→E)
variable {b K:ℕ}{s k L r:ℝ}
abbrev VastJ (P:Z→D→E)(t:ℝ): Prop:= ∃ F:Z→ℝ,(∀ i,X.Lux i (P i) (F i))∧ ∑ i,F i≤ t
lemma Vast_add {a b:ℝ}{F G:Z→D→E}(p:VastJ X F a)(q:VastJ X G b):VastJ X (F+G) (a+b):=by obtain ⟨Y,h,H⟩:=p; obtain ⟨Q,u,p'⟩:=q; refine ⟨Y+Q,fun i=>X.add _ _ _ _ _ (h i) (u i),?_⟩; simp only[Pi.add_apply,sum_add_distrib]; exact add_le_add H p'
lemma Vast_scale{a:ℝ}{F:Z→D→E}(p:VastJ X F a)(z:ℂ)(r:ℝ)(t:‖z‖≤ r) : VastJ X (z • F) (r*a):=by
 obtain ⟨Y,h,H⟩:=p; refine ⟨fun i=>‖z‖*Y i, fun i=>X.coin _ _ _ (h i) _,?_⟩; rw [←mul_sum]; exact mul_le_mul t H (sum_nonneg (fun i _=>X.posG _ _ _ (h i))) ((norm_nonneg _).trans t)
lemma Vast_sum {I:Type*}(S:Finset I){F:I→Z→D→E}{h:I→ℝ}(p:∀ i∈ S, VastJ X (F i) (h i)) : VastJ X (∑ i∈ S,F i) (∑ i∈ S,h i):=by
 induction S using Finset.induction_on with
 | empty=>rw [sum_empty,sum_empty]; exact ⟨0,fun i=> X.zero i 0 (fun _ _=>rfl),by simp⟩
 | @insert i s u ih=> rw[sum_insert u,sum_insert u]; exact Vast_add X (p _ (mem_insert_self _ _)) (ih fun j v=>p j (mem_insert_of_mem v))
private lemma vit (h:0≤ s)(p:Support N):1 ≤ dra_k b s p:= Real.one_le_exp (mul_nonneg h (Nat.cast_nonneg _))
lemma soloFee {vNote:I} (h:0≤ s)(p:ShelfK X (u {vNote}) b s k)(q:Ledges X σ u) : VastJ X (u {vNote}) k:=by
 obtain ⟨C,H,w⟩:=p; let A:= univ.filter (fun i=>σ vNote∈ X.Φ i); let F0: Z→ℝ:= fun i=>if i∈A then C i else 0; refine ⟨F0,fun i=>?_,?_⟩
 · unfold F0; split; exact H i; next t => exact X.zero _ _ (fun j p=> Classical.byContradiction (fun v=> t (mem_filter.mpr ⟨mem_univ _, (q i j p _ v).2 _ (mem_singleton_self _)⟩)))
 unfold F0; simp_rw [←sum_filter]; rw [filter_mem_eq_inter,univ_inter]; apply le_trans _ (w (σ vNote)); exact sum_le_sum fun i p=> le_mul_of_one_le_left (X.posG _ _ _ (H i)) (vit h _)
include H
-- Assert ShelfK all ledgers -> global with vol.
lemma VastOf {U:Z→D→E}(h:ShelfK X U b s k)(v:0≤ s): VastJ X U (Fintype.card (Site N)*k):=by
 obtain ⟨C,t,p⟩:= h; refine ⟨C,t,?_⟩
 apply le_trans (b:= ∑ j:Site N,∑ i∈ univ.filter (fun i=>j∈X.Φ i),dra_k b s (X.Φ i)*C i); swap; · refine le_trans (sum_le_sum (g:=fun _=>k) fun j _=>p j) (le_of_eq (by simp))
 simp_rw [sum_filter]; rw [sum_comm]; apply sum_le_sum; intro i _
 obtain ⟨j,z⟩:=H i; have hp:= single_le_sum (f:=fun j:Site N=> if j∈X.Φ i then dra_k b s (X.Φ i)*C i else 0) (fun j h=>by split; exact mul_nonneg (Real.exp_pos _).le (X.posG _ _ _ (t i)); exact le_rfl) (mem_univ j); rw [if_pos z] at hp; exact (le_mul_of_one_le_left (X.posG _ _ _ (t i)) (vit v _)).trans hp
variable (e:1≤ r)(f:8≤ b)
variable (w:BookT X u b (realm_C σ) (5/4) 1 s)(q:Ledges X σ u)(hp:Roots.Force_M b σ K)(v:Roots.Nice_B b K r (1/32))(l:0≤ s)
include f w q v l hp e
lemma τNow (z:Key I)(h:∀ i,‖z i‖ ≤ r)(p:∀ i∉A,z i=0)(t:u ∅=0): VastJ X (WritV σ u z) ((A.card:ℝ)*(r*s)+ (Fintype.card (Site N):ℝ)*Roots.hope_E b s):=by
 let S:= realm_C σ; let D:= S.filter (fun i=>1< i.card); let B:= S\D
 let G(i:Finset I):= Mew.pine i z • u i
 have hu(i)(v:i∈S): ShelfK X (u i) b (5/4) s:= BookUnit X w _ v
 have hv: BookT X u b D (9/8) r (Roots.hope_E b s):=by
   simpa only [one_pow,one_mul,show (9/8:ℝ)+ 1/8= 5/4 from (by norm_num)] using Book_many X σ q (filter_subset _ _) (η:=1) (S:=D) (fun i p=>show ShelfK X (u i) b (9/8+1/8) ((1:ℝ)^i.card*s) from (by rw [one_pow,one_mul, show (9/8:ℝ)+1/8=5/4 from (by norm_num)]; exact hu _ ((mem_filter.mp p).1))) (zero_le_one.trans e) (by simpa only [mul_one] using e) zero_lt_one hp.2 hp.1 (show Nice_B b K (r*1) (1/32) from (by simpa using v)) f l (fun i h=>(mem_filter.mp h).2) -- tune order
 have he: ∑ i∈B,G i=∑ i∈A,z i • u {i}:=by
    let D₀:=A.image fun i=>({i}:Finset I)
    rw [←sum_subset (s₁:=D₀) ?_ ?_]; · unfold D₀; rw [sum_image (fun i _ j _ h=>singleton_inj.mp h)]; apply sum_congr rfl; intro i p; unfold G Mew.pine; rw[prod_singleton]
    · intro i b; obtain ⟨i,p,rfl⟩:=mem_image.mp b; exact mem_sdiff.mpr ⟨meta_one σ _, fun t=>by have he:=(mem_filter.mp (show {i}∈ D from t)).2; simp at he⟩
    intro i g d; unfold G; obtain ⟨u',v⟩:= mem_sdiff.mp g; by_cases k:i.card=1; · obtain ⟨j,rfl⟩:= Finset.card_eq_one.mp k; rw [Mew.pine,prod_singleton,p j (fun p=>d (mem_image.mpr ⟨j,p,rfl⟩)),zero_smul]
    have he: i=∅:= Finset.card_eq_zero.mp (by have he:¬ 1< i.card:=fun p=>v (mem_filter.mpr ⟨u',p⟩); omega); rw[he,t,smul_zero]
 change VastJ X (∑ i∈ S,G i) _; rw[← Finset.sum_sdiff (s₁:=D) (filter_subset ..),he,show (A.card:ℝ)*(r*s)= ∑ _i∈ A,r*s from (by rw[sum_const,nsmul_eq_mul])]; refine Vast_add X (Vast_sum X _ fun i _=> Vast_scale X (soloFee σ X u (show (0:ℝ)≤ 5/4 by norm_num) (hu {i} (meta_one σ _)) q) _ _ (h i)) (VastOf X H (SB_eval (U:=u) _ hv z h) (show (0:ℝ) ≤9/8 by norm_num)) -- tune Bookunit use p.
#print axioms τNow
end
end CoeffArc
end Focus
end Pitching
end YM.CF.Py.Rate
end
