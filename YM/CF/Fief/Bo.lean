import YM.CF.Fief.Vex
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Fief
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.Frobenius
open AnalyticBridge.Annulus1AD Ac Esti
open Atala Forge Cloak Rill Hive Fock Stilo Palot Scion
open Cube Lat Tenant Tulip
open Pastry Hake Levier Urn Peaks Fock Laic Branch Drapes
open Stilo Palot Scion Function Levier Hake Urn Peaks Fock Laic Branch Drapes
open Rush Scroll Paige Vault Phase Acorn Spire Eire
open Tarn Cay Slate Esti Cour Hest Arena Reine Kennel Facet Broc Pec Push.SectorMeasure.Oriented
open Jet Lich Corne
variable {N P B:Side}(G:Ratio (mid N B) (mid P B))(S:StepData (Domain N B) (Domain P B))(x e:ℝ)(T:Tube SU.group S)
variable{k n j d:ℕ}
open Lich.Muster
attribute [local instance] opCStarAlgebra
variable{G S x e T}
variable(A:Muster G S x e T)
open Vol YM.Push.AbsoluteSums
open ConnectedActivityE6.Raw
variable (U: Monk SU.group S)
variable{s:ℝ}{l v:ℕ}
local notation "G₅"=> SU.group
local notation "N'"=> Domain N B
variable (Q:Patch){n':ℕ}{t w C c D v A' h₁ h₂ η σ Z J W L a s K:ℝ}{p:Teller SU.group}
-- trace layer.T.herm paid all. test under Vmove any aperture. proof aggregation.Tax.
def quotes(C θ t u x v':ℝ)(n l k:ℕ)(T:Tube G₅ S)(A:Muster G S x e T)(W:ℝ):Prop:=
 let χ(L):=costL A n C θ t u L
 ∀ M:Monk G₅ S,sizedP G₅ Q p S T M.park →M.key.flags=flags (temp x) M.V → Portus A M∧ (∀ i:Bit (Site (Domain N B)),0≤χ i∧ Allows n (fun y=>Lich.Muster.massX A (M.atop y x) i) 0 (χ i)) ∧ ∀ y:Site (Domain N B),(∑ i,tallyL y i v' (radiusB x)*χ i)≤ W
lemma filled_L(T:Teller G₅)(P:Patch)(B:P.Branches T.bind G₅)(l n k:ℕ)(hp:2 ≤ n)(hq:l≤18)(h:Push.Uniform.Before G₅ T.top.width T.top.paths T.j T.bind (n+1+1))(σ:ℝ)(hσ:0 ≤ σ):∃ Z A:ℝ,0<Z∧0<A∧∃ f g H:ℝ→ℝ,sizeK P.L 1 f ∧ sizeK P.L 1 g∧ sizeK P.L 3 H∧ ∀ᶠ x in atTop,∀ {N M b:Side}{G:Ratio (mid N b) (mid M b)}(S: StepData (Domain N b) (Domain M b))(R:Tube G₅ S),Cert P T S R x→∀(e:ℝ)(L:Muster G S x e R), L.post=l → quotes (p:=T) P Z A (f x) (g x) x σ n l k R L (H x):=by
 obtain ⟨θ,C,m,v,F,D,hθ,hC,hM,hv,hF,H⟩:=jumpW T P n l hp hq B h
 let f(x):=F*tipPay v x; let g(x):= (|D|+1)*Neige.lamp x; let t(x):= Scales.g G₅ P.L x; let W:= bill_l P C θ f g l n σ; have hf:sizeK P.L 1 f:= ((sizeK.tip _ v hv).low (show 1≤2 by omega)).scale F; have hg:sizeK P.L 1 g:= (sizeK.coin P.L).scale _
 have hx:∀ᶠ x in atTop, 0 ≤ f x ∧ 0 ≤ g x:=by filter_upwards [eventually_gt_atTop (0:ℝ)] with x ht; unfold f g Neige.lamp tipPay; have he:= Work.E09.temp_pos ht; constructor <;> positivity
 have he:∀ᶠ x in atTop,0<t x:=( (year G₅ P.L).eventually_gt_atTop 0).mono fun i p=> Scales.gauge _ _ p
 have hp' := grips (n:=n) (l:=l) P hσ hθ (hf.accrue (sizeK.main P.L)) (hg.accrue (sizeK.main P.L)) ((he.and hx).mono fun i ⟨p,u,k⟩=>⟨add_nonneg u p.le,add_nonneg k p.le⟩) (show 0 ≤ C+1 by linarith)
 refine ⟨C,θ,hC,hθ,f,g,W,hf,hg,score_q P C θ f g l n σ hθ hf hg,?_⟩; filter_upwards [hp',H,he,grips (n:=n) (l:=l) P hσ hθ hf hg hx hC.le, Work.E01.radiusB_tendsto.eventually_gt_atTop 0,hg.spine.eventually (gt_mem_nhds zero_lt_one),eventually_gt_atTop (0:ℝ)] with x hp_bad H he p i ty vip N M b G S R E e L z
 -- tune eventually `lt` !!
 intro A J P'; let U:=kist A; have heL:σ=σ:=rfl
 have ht:U.key.flags=flags (temp x) U.V:=(PhysicalNext.JointLoad.Heir.noFlags ..).symm
 let w:=D*Neige.lamp x; have ht':w≤g x:=by have h:=Work.E09.temp_pos vip; unfold g w; exact mul_le_mul_of_nonneg_right ((le_abs_self _).trans (le_add_of_nonneg_right (by norm_num))) (by unfold Neige.lamp; positivity)
 have hh(A':Monk G₅ S)(p:A'.key.flags= flags (temp x) A'.V)(j:sizedP G₅ P T S R A'.park) : ShardIncome n x v F m R A'.key A'.park A'.V A'.k ∧ NameX R A' x L.trot L.room l n C θ (f x) (g x) (2*D*D):=by
    obtain ⟨he,hZ⟩:= H.2.2.2 S R A'.key A'.park A'.V E p j A'.k; obtain ⟨q,r⟩:= hZ L.trot L.room (A'.bush x); exact ⟨he,⟨⟨r.center, r.core, r.modes.cheaper ht' ht', r.vertex, r.safe⟩,hθ,hC.le,H.1,H.2.1,ty⟩⟩
 obtain ⟨hp,h⟩:= hh A P' J; obtain ⟨u,k⟩:= hh U ht J; obtain ⟨g,m,W⟩:= talent L h k z E.got hp i p hp_bad he -- tune shadow
 refine ⟨?_,fun i=>⟨g i,m i⟩,W⟩
 rw [←z] at h k; have htB(n:ℕ):ratioB S n=Fief.loomP P n:=by unfold ratioB Fief.loomP; rw [E.got]
 simp_rw [←htB] at p
 exact plenty n L A h k p.pos_b p.pos_c (gproof p.rate p.act (mul_nonneg hC.le (Real.exp_pos _).le)) (gproof p.rate p.mat p.pos_b) (gproof p.rate p.cot p.pos_c)
end YM.CF.Fief
