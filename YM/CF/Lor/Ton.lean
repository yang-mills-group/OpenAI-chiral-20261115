import YM.CF.Lor.Swan
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Lor
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
open Lich.Muster
attribute [local instance] opCStarAlgebra
local notation "G₅"=> SU.group
open Pressure.Tube
open Vol
variable{c f N B:Side}{d n m l:ℕ}{a b K v v' u D D' κ τ τ' :ℝ}{p:BudgetPoint}{q:Chi}
-- common allowance-target category.Across any Horizon.S.True.N.Anchor.g
variable{E:Type}[NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E]
open Fief BoreP rates Braid Rel
variable(L:Side)(j n:ℕ){Q K F:ℝ→ℝ}{u v t:ℕ}{Z:ℝ}
lemma peak_v:sizeK L 1 (Arena.rankC Z):= ((((sizeK.Bcash L).powC 5).tint (sizeK.tempo L)).scale _).scale _
lemma peak_a (h:sizeK L v K)(u:ℕ){X:ℝ}(p:sizeK L 0 F) : sizeK L (min (v+u) (j+1)) fun x=> Jet.composeCost n (vatP u j n (F x) (K x) (Arena.rankC Z x)) X:=by
 have hp:sizeK L 1 (Arena.rankC Z) :=peak_v L; have hv(k:ℕ):sizeK L k fun x=> Arena.rankC Z x^k:=by simpa using hp.square k
 apply arm; apply sizeK.accrue; exact sizeK.low (sizeK.scale (h.tint (hv u)) _) (min_le_left ..); exact (p.tint (hv (j+1))).low (by omega)
lemma tempo_x(z:ℝ)(h:sizeK L 0 K): sizeK L 2 fun x=> Jet.composeCost n (vatP 1 1 n (K x) 0 (Arena.rankC z x)) (1/2):=by
 simp_rw [vatP,zero_mul,mul_zero,zero_add]; apply rates.arm; exact h.tint ((peak_v L).square _)
lemma beamZ {W:ℕ→ℕ}(h:CapY W)(U D:ℝ→ℝ)(p:BoreP U)(q:sizeK L 1 D): sizeK L 3 fun x=>Arena.compass n 2 x (U x) (D x) Z:= peak_a L 2 n q 2 (p.creditK L) -- tune binder
lemma beam_b {M:ℕ→ℕ}(h:CapY M)(R:ℝ→ℕ)(hv:BoreP fun x=>(R x:ℝ))(W:ℝ→ℝ)(p:sizeK L u W): sizeK L u fun x=> (plot (M (R x)))* W x:=by simpa only [Nat.zero_add,Function.comp_apply] using (((BoreP.nob R (Rel.plot_n h) hv).creditK L).tint p)
variable(l:ℕ)(h:5 ≤ l)
include h in
lemma sphere (D:ℝ):sizeK L 3 fun x=>D*temp x^(l+2-4) :=by exact ((sizeK.scale ((sizeK.tempo L).square _) D).low (by omega)) -- include h
include h in
lemma satV(z t C D:ℝ)(Q:ℕ→ℝ)(E:ℕ→ℕ)(p:nib Q)(hv:CapY E): let Vs (x:ℝ):=Cay.horn x l; let B(x):= Q (Vs x); let A(x):= D*temp x^(l+2-4); let u(x):= Arena.compass n 2 x (C*B x) (A x*B x) t; let q(x):=plot (E (Vs x))*u x
 sizeK L 3 u ∧ sizeK L 3 (fun x=>Arena.compass n 2 x C (A x) z+(q x+q x))∧ sizeK L 5 (fun x=> Arena.compass n 4 x (C*B x) (A x*B x) t):=by
 intro Vs B A u q; have hk:BoreP fun x=>(Vs x:ℝ):=by unfold Vs Cay.horn; push_cast; exact (BoreP.still _).grip radius_c
 have hB:sizeK L 0 B:= (BoreP.nob _ p hk).creditK L; have hA:= sphere L l h D
 have hp:sizeK L 3 u:=peak_a L 2 n (hA.tint hB) _ (hB.scale C); have hg:= beam_b L hv Vs hk u hp; exact ⟨hp,(peak_a L 2 n hA _ (sizeK.mild L C)).accrue (hg.accrue hg),peak_a L 4 n (hA.tint hB) _ (hB.scale C)⟩ -- inference theorem def min 3
variable (R:Patch)(T:Teller SU.group)(q:Chi)
include h in
lemma sing_k (hl:l≤18)(hg:l+78 ≤ j)(hp:5 ≤ n)(hv:R.Branches T.bind SU.group)(F:∀ i≤n+3, Push.Uniform.Before SU.group T.top.width T.top.paths T.j T.bind i):∃ V W:ℝ→ℝ,∃ E X,∃ r:ℕ,∃ C D σ:ℝ,sizeK R.L 1 V∧sizeK R.L 3 W ∧ CapY E∧ nib X∧0<C∧0<D∧0<σ∧ j ≤r ∧∀ᶠ x:ℝ in atTop,let Z:= X (Cay.horn x l); let a:=D*temp x^(l+2-4); let p:=E (Cay.horn x l); p ≤ (r-1)*radiusB x∧∀{c f:Side}(S:StepData (More c) f)(T':Tube SU.group S), Arena.Prime R T S T' x → (r+r+101)*radiusB x ≤ (More c).val→∀ d:ℝ, let F:=fun t:Tab S=> fame T' t q x d l; ∃ O,Arena.Woven F O p 2 n σ (C*Z) (a*Z)∧∀ (β:ℝ),β∈Set.Icc (y SU.group R.L x/2) (2*y SU.group R.L x) →∀ M:Monk SU.group S, M.key.flags=flags (temp x) M.V→∀ i:Site (More c), let X':=fun y=> -β*Cloak.issueC T' x (M.atop y x) q d l j O r i
 Allows n X' 0 (V x) ∧(i∉ M.key.dome (p+r*radiusB x)→ Allows n X' 0 (W x)):=by -- beta inside ∃ O wrong continuation. adjust.
 obtain ⟨w,P,t,a,b,C,D,σ,H,H',hs,h1,h2,h3,h4,h5,hX⟩:=saga T R q l n j h hl hg hp hv F; let L:=R.L; have hu:= satV L n l h a b C D w P H H'
 let Y(x):ℝ:=2*y SU.group L x; let p(x):ℕ:=P (Cay.horn x l); let B(x):= w (Cay.horn x l); let A(x):=D*temp x^(l+2-4); let u(x):= Arena.compass n 2 x (C*B x) (A x*B x) b; let q'(x):= plot (p x)*u x; let X(x):=Arena.compass n 2 x C (A x) a+(q' x+q' x); let X'(x):=Arena.compass n 4 x (C*B x) (A x*B x) b
 refine ⟨fun x=> Y x*X x,fun x=>Y x*X' x,P,w,t,C,D,σ,year_r L _ _ hu.2.1,year_r L _ _ hu.2.2,H',H,h3,h4,h5,hs,?_⟩
 filter_upwards [hX,(year SU.group L).eventually_gt_atTop 0] with x hx v; intro Z A' p'; refine ⟨hx.1, fun S T' i j' d=>?_⟩; intro F'; obtain ⟨O,a,p⟩:=hx.2 _ _ i d j'; refine ⟨O,a,fun β b M v' i=>?_⟩; intro X₀; obtain ⟨ht,hK⟩:= p i M.V (M.park,M.k) M.key v'; have he: |(-β)| ≤ Y x:=by rw [abs_neg,abs_of_pos ((half_pos v).trans_le b.1)]; exact b.2
 let U:= issued x j t F' O M.key (M.park,M.k) i ∘ Vmove x M.V
 have hp(G:ℝ)(p: Allows n U 0 G): Allows n X₀ 0 (Y x*G):=by
    apply (((p.linear Complex.reCLM (ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun i=>by rw [one_mul]; exact Complex.abs_re_le_norm i))).mono (one_mul _).le).smul (-β)).mono (mul_le_mul_of_nonneg_right he p.nonneg) -- tune abs
 exact ⟨hp _ ht,fun i=>hp _ (hK i)⟩
end YM.CF.Lor
