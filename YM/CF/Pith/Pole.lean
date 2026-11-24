import YM.CF.Pith.LogP
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Larch
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
open Jet Yaw Nor Prism Font Push.AbsoluteSums Wray
variable{n:Side} {P: BudgetPoint}{x y a b h c d:ℝ}{k m:ℕ}
local notation "DN"=>tangD n
local notation "E'"=>SU.group
-- second grade corrections.L General receipt.One-ball log-tail. split off constants or scalar portal. reserve α budgeting.
open Trees Ursell Push.AbsoluteSums.Graph
open Lilt Bake Vow
variable {F G E Q:Pax n}(Y:Aura n)(V:Orbit n) {A C H W L':Aura n→ℝ}{z u γ δ q v β:ℝ}
-- F - E_oldQ - G_scalar = Paid_H
local notation "N'"=> P.B
local notation "wP"=> (P.supportExponent+1)
variable (α:ℝ)(hu:1 ≤α)(ht:Ready Palot.stern P.B A (P.supportExponent+1+1) γ δ q)(hy:1 ≤ h)(Z:GrainP G)
variable (u0:∀ X,Medal P X.val ∅ (F X) h (A X))(hv: ∀ X,Medal P X.val ∅ (G X) h (A X))(hp:∀ X,Medal P X.val ∅ (F X-G X) h (α⁻¹*A X))(WDX:∀ X:Aura n,Medal P X.val ∅ (F X-G X-E X) h (W X))
-- Order-one quadratic pure $
include ht hy hv
lemma moon(i:Aura n): Medal P i.val ∅ (branch_P G i) h (A i+spanD i A 0):=by
 have hx:= Vow.glomM (m:=0) i ht (show 0 ≤ P.supportExponent+1+1 from (add_pos (add_pos P.exponent_pos zero_lt_one) zero_lt_one).le)
 refine (hv i).plus (?_:Medal P i.val ∅ (funge i G 0 1) h (spanD i A 0)); apply Medal.big (a:=∑ j:Tuple (Aura n) 1, sepV A i 0 ⟨1,j⟩) (Medal.sumP _ _ _ (fun j _=>ponder i ⟨1,j⟩ hy hv 0))
 rw [spanD,hx.tsum_sigma]; let V(k:ℕ):= ∑ j:Tuple (Aura n) k, sepV A i 0 ⟨k,j⟩; simp_rw [tsum_fintype]; have hu: Summable V:=by simpa only [tsum_fintype] using hx.sigma
 exact hu.le_tsum 1 (fun j _=> sum_nonneg fun u _=> (ponder i ⟨j,u⟩ hy hv 0).wage (zero_le_one.trans hy))
omit ht hy hv
lemma ready_x (p:0 < γ)(h:degreePrice P.B γ 1 < 1)(hv:0 ≤ A)(t:∀ o:Seat n,tallB A P.B (P.supportExponent+1+1+1) o ≤ γ): Ready Palot.stern P.B A (P.supportExponent+1+1) γ 1 (degreePrice P.B γ 1):=by
 refine ⟨p,zero_lt_one,le_rfl,h,fun i=>hv i,fun i=>?_⟩; let F(j:Aura n):=if i∈j.val then A j * currency P.B (P.supportExponent+1+1+1) j.val else 0; have hx(j):0 ≤ F j:=by unfold F; split; exact mul_nonneg (hv j) (Real.exp_pos _).le; exact le_rfl
 apply budget_of_sum hx; intro X; exact (sum_le_sum_of_subset_of_nonneg (subset_univ X) (fun j _ _=>hx j)).trans (by unfold F; rw [←Finset.sum_filter]; exact t i)
-- packaging.Struct: admiss receipts. includes real constants. Costs A all, full budget. a.S consumes.P.pot. Good for Pole.Beta.H.Th.Audit.
local notation "θ"=> (degreePrice P.B γ 1)
structure Wisp (P:BudgetPoint)(F E:Pax n)(h γ c d:ℝ):Prop where
 keep:∃ (G R: Pax n)(L C A: Aura n→ ℝ), GrainP G ∧ Ready Palot.stern P.B A (P.supportExponent+1+1) γ 1 (degreePrice P.B γ 1) ∧ (∀ i,Medal P i.val ∅ (F i) h (A i)) ∧ (∀ i,Medal P i.val ∅ (G i) h (L i)) ∧ (∀ i,Medal P i.val ∅ (R i) h (C i)) ∧ (∀ o:Seat n,tallB L P.B (P.supportExponent+1+1) o ≤ c)∧ (∀ o:Seat n,tallB C P.B (P.supportExponent+1+1) o ≤ d) ∧ (∀ (i:Aura n)(v:Orbit n), visible P i.val ∅ v.1 → FeeD P F i v= G i v + E i v+R i v) ∧ Bake.Turf R
lemma tall_add(F G:Aura n→ℝ)(d:ℝ)(o:Seat n):tallB (F+G) k d o=tallB F k d o+tallB G k d o:=by unfold tallB; simp_rw [Pi.add_apply,add_mul,sum_add_distrib]
lemma tall_s(F:Aura n→ℝ)(d:ℝ)(o:Seat n):tallB (a • F) k d o=a*tallB F k d o:=by unfold tallB; simp_rw [Pi.smul_apply,smul_eq_mul,mul_assoc,mul_sum]
lemma tall_m(F:Aura n→ℝ)(p:0 ≤ F)(u:a ≤ b)(o:Seat n):tallB F k a o≤ tallB F k b o:= sum_le_sum fun i _=>mul_le_mul_of_nonneg_left (Real.exp_monotone (mul_le_mul_of_nonneg_right u (Nat.cast_nonneg _))) (p i)
lemma turfP (q:Turf G)(x:Aura n)(v:Orbit n)(A:Ids n) : funge x G k m v=funge x G k m (v.1,A):=by
 unfold funge; rw [Finset.sum_apply,Finset.sum_apply]; refine sum_congr rfl fun i _=>?_ ; unfold sta; split; swap; · rfl
 unfold guava; simp only [Pi.smul_apply, Finset.prod_apply]; exact congrArg _ (prod_congr rfl fun z _=>q _ _ _)
lemma taro_v (p:Turf F)(s:Turf G)(w:Turf E) : Turf (taper_R F G E P):=by
 intro i Y V; unfold taper_R; simp only [Pi.add_apply,Pi.sub_apply]; rw [p i Y V,s i Y V,w i Y V,turfP p i Y V,turfP s i Y V]; unfold spinD lasting zenS; split; rotate_left; · rfl
 refine congrArg _ ?_; apply tsum_congr; intro j; exact turfP p i Y V -- congr Arg _ inf
variable (Lx v0 vV:ℝ)(kh:∀ X,Medal P X.val ∅ (F X) h (H X))(lf:∀ X,Medal P X.val ∅ (E X) h (L' X))(hL:∀ o:Seat n,tallB H P.B (P.supportExponent+1+1+1) o ≤ Lx)(hℓ:∀ o:Seat n,tallB L' P.B (P.supportExponent+1+1+1) o ≤ v0)(hz:∀ o:Seat n,tallB W P.B (P.supportExponent+1+1+1) o ≤ vV)(γt:0 <γ)(κt:degreePrice P.B γ 1 < 1)(ha:Lx+α*(vV+v0)≤ γ)(p:Turf F)(s:Turf E)
include hy Z hu WDX kh lf hL hℓ hz γt κt ha p s
lemma soar_t: Wisp P F E h γ (γ+ γ*θ^0*(1-θ)⁻¹) (Caph α vV θ γ):=by
 let A:= H + α • (W+L'); let hR:= zero_le_one.trans hy; have hz0(X:Aura n):0 ≤ W X:=(WDX X).wage hR; have hv(X:Aura n): 0 ≤ L' X:=(lf X).wage hR; have hQ(X:Aura n):0≤ H X:=(kh X).wage hR; have h'X(i):0≤ W i+L' i:=add_nonneg (hz0 _) (hv _); let ht:=zero_le_one.trans hu; have he(X:Aura n): 0 ≤ A X:= add_nonneg (hQ _) (mul_nonneg ht (h'X _))
 have h2(X): Vow.Medal P X.val ∅ (F X-G X) h (W X+L' X):=by simpa using (WDX X).plus (lf X)
 have hb(i): Vow.Medal P i.val ∅ (F i) h (A i):=(kh i).big (le_add_of_nonneg_right (mul_nonneg ht (h'X _))); have hp(i): Vow.Medal P i.val ∅ (G i) h (A i):=by
    let h:= h2 i; rw [show G i= F i+-(F i-G i) by abel]; refine ((kh i).plus h.negT).big (add_le_add_right ?_ _) -- tune side
    exact le_mul_of_one_le_left (h'X _) hu
 have hg(i): Vow.Medal P i.val ∅ (F i-G i) h (α⁻¹*A i):=by
    refine (h2 i).big ?_; rw [inv_mul_eq_div]; apply (le_div_iff₀ (zero_lt_one.trans_le hu)).mpr; exact (mul_comm ..).trans_le (le_add_of_nonneg_left (hQ _))
 have hT(o:Seat n): tallB A P.B (P.supportExponent+1+1+1) o ≤ γ:=by unfold A; rw [tall_add,tall_s,tall_add]; exact (add_le_add (hL _) (mul_le_mul_of_nonneg_left (add_le_add (hz _) (hℓ _)) ht)).trans ha
 have hx:= ready_x γt κt he hT; let L:= A+(fun i:Aura n=>spanD i A 0)
 refine ⟨⟨branch_P G,taper_R F G E P,L,Cap_p A W α,A,stem_P Z,hx,hb,moon hx hy hp,stick_H α hu hx hy hb hp hg WDX,fun i=>?_ ,fun i=>years_C α hu hx hy hb hp hg WDX i (hz _),fun i v t=>tone_G v hx hy hb i t, taro_v p (fun i v V=>by obtain ⟨x,H⟩:= Z i; rw [H]) s⟩⟩ -- arg order v preced
 unfold L; rw [tall_add]; exact add_le_add ((tall_m A he (le_add_of_nonneg_right zero_le_one) i).trans (hT i)) (thinX hx (add_pos (add_pos P.exponent_pos zero_lt_one) zero_lt_one).le i 0)
end YM.CF.Larch
