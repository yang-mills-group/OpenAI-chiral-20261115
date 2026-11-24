import YM.CF.Cloak.Norm
import YM.Further.ROOTED_INTERACTING_REMAINDER.Vault
import YM.CF.Cloak.Wear
import YM.CF.Cloak.Mint
import YM.CF.Rill.Oboe
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 600000
noncomputable section
namespace YM.CF.Cloak
open Siete
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG PhysicalNext.JointLoad Heir Next.Foundations AnalyticBridge.SectorAffine AnalyticBridge.SectorAffine.Offset Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree Esti
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Classical Matrix.Norms.Frobenius
open AnalyticBridge.Annulus1AD
open Ac
variable {c f:Side}(S:StepData c f){r v:ℕ}
open CF.Jet
local notation "G"=> SU.group
variable {S}{n:ℕ}{θ a b m x t w K C d:ℝ}
variable {K': Teller G}{A B:Stores S}{T:Tube G S}{V:Config G c}{U:Config G f}{k:S.Choices}{q:Chi}{E:Type}[NormedAddCommGroup E][NormedSpace ℝ E][Nonempty E]{x':E}
open AnalyticBridge.Annulus1AD Push.SectorMeasure.Oriented Pressure.Tube
variable {O:Stores S}{F: Forest S.ratio}{Y:LinkArray G (Frozen A x F)}{z:LogArray G (Active A x F)}{β Q γ D L M s:ℝ}{J:ChartRatio G}{P:Patch}
open Forge Reine Rill
open Vol Pressure.Tube
open Vol Cay Slate
variable {l:ℕ}{M:Monk G S}{s':ℝ}
open Further.RootedInteractingRemainder Precision Next.SectorChange
-- normative d-independent W. before width & threshold. Uniform for small Z, afterwards local clamp.
open Atala
lemma hush_f(M:Monk G S){p v:ℝ}(hp:M.key.flags= flags (temp x) M.V)(hk:Bell S M x T q d l β p v)(i:Bond c)(he:shovel S.patch ≤ radiusB x)(h:i.1∉ M.key.dome (14*radiusB x)) : ResV S (a:=p) i (M.sent x T q d l β):=by
 let U:=M.sent x T q d l β; rw [charged]; intro j z; by_contra! t; have ht:= hk.reach _ ((RG.flags_spec ..).mpr ⟨j,Work.E01.base_touched _,t⟩); exact h (dome_u ht (by rw [separation_comm]; have hx: separation i.1 _ ≤ shovel S.patch:= beam_up S i i.1 (mem_insert_self ..) j z (S.ratio.parent j.1) (mem_image_of_mem _ (Work.E01.base_touched j)); omega))
lemma borrows (i:Bond c)(p:0<a)(t:ResV S (a:=a/2) i U): tidal A x w a q U V k i= tokenB A q x w U V k i:=by
 have he: Inure A x q k a i U=SU.group.mat (S.prediction U k i):=by unfold Inure; split; rfl; exact abort_e _ _ _ i p _ t
 unfold tidal; rw [he,←SU.group.mat_inv, ← SU.group.mat_mul, fare_h]; split
 next g=> exact (chooseB ..).symm.trans (if_pos g).symm
 next g=> exact (chooseF ..).symm.trans (if_neg g).symm
lemma token_g(q:Chi)(p:0<t){a:ℝ}(h:0≤a)(u:a≤ t): q.innerShare t a=1:= q.to_one _ (pow_le_one₀ (div_nonneg h p.le) ((div_le_one p).mpr u))
def readyJ (M:Monk G S)(T:Tube G S)(q:Chi)(l:ℕ)(x d a β p:ℝ): Prop:=
 (∀ i:Bond c,i.1∉ M.key.dome ((l+70)*radiusB x) → tidal M.key x p a q (M.sent x T q d l β) M.V M.k i=1) ∧ (∀ i:Active M.key x M.park,S.ratio.parent i.val.val.1∉ M.key.dome ((l+70)*radiusB x) → broad q d (M.rich x T q d l β i)=1)
lemma anchor (K:Teller G)(P:Patch)(p:P.Branches K.bind G)(n l:ℕ)(hp:2 ≤ n)(hl:l≤18)(q:Chi)(W:Push.Uniform.Before G K.top.width K.top.paths K.j K.bind (n+2)) :∃ d C:ℝ,0<d∧0<C ∧∀ B a:ℝ,0<B →0<a →∃ r:ℝ,0<r ∧∀ᶠ x in atTop,∀ {c f:Side}(S:StepData c f)(T:Tube G S),Cert P K S T x →∀ (s:ℝ),s ≥ d →∀ p ≥ C,∀ (M: Monk G S),M.key.flags=flags (temp x) M.V → sizedP G P K S T M.park→∀ β∈Set.Icc (y G P.L x/2) (2*y G P.L x), let t:= fiery G x P.L;‖M.z‖ ≤ r*Scales.p G P.L x→ MossX n l x M.key M.park T M.V M.k B (s*t) t q→ readyJ M T q l x (s*t) a β p :=by
 obtain ⟨C,d,hC,hD,H⟩:=orn K P p n l hp hl q W; refine ⟨d,C,hD,hC,fun B a g h=>?_⟩
 obtain ⟨r,hP,H⟩:= H _ g; refine ⟨r,hP,?_⟩
 filter_upwards [H, threshold P n l (a/2) 1 B r (half_pos h) zero_lt_one g hP, Work.E01.radiusB_tendsto.eventually_ge_atTop (shovel P+100),(year G P.L).eventually (eventually_gt_atTop (0:ℝ))] with x hv he ht ht' c f S T hK s hs p hop M h₁ h₂ β hp t z u
 have hX:S.patch=P:=hK.got; obtain ⟨hT,hp'⟩:=hv S T hK M _ h₂ h₁ _ hp z u; have hY:0<t:=by unfold t; rw [Scales.fi]; exact mul_pos (Scales.gauge G _ ht') (Scales.pos ..)
 have hm:0<s:=hD.trans_le hs; have hj:0<p:=hC.trans_le hop; have he':40<c.val:=by have h:=hK.size; omega
 have hh:=he S T M hX (by rw [h₁]) he' β hp z (s*t) q u
 constructor
 · intro i g; let A:=M.key; have hz: ¬ i∈A.aisles:=fun h=>g (halo_subset _ _ (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨_,h,mem_insert_self ..⟩))))
   rw [borrows i h (hush_f M h₁ hh i (by rw [hX]; omega) (fun p=>g (AnalyticBridge.Annulus1AD.farther (by simp_rw [Nat.add_mul]; omega) p)))]; unfold tokenB AnalyticBridge.Annulus1AD.profile; rw [if_neg hz, hX]
   exact token_g q (mul_pos hj hY) (SU.group.chord_nonneg _) ((hT i g).trans (mul_le_mul_of_nonneg_right hop hY.le))
 intro i u; exact token_g q (mul_pos hm hY) (norm_nonneg _) ((hp' _ (fun k=>u (AnalyticBridge.Annulus1AD.farther (Nat.mul_le_mul_right _ (by omega)) k))).trans (mul_le_mul_of_nonneg_right hs hY.le))
end YM.CF.Cloak
