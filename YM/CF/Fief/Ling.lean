import YM.CF.Fief.Core
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
variable(U: Monk SU.group S)(n)
local notation "θ"=> A.room
local notation "j"=> A.loft
local notation "β"=> A.beta
local notation "q"=> A.trot
local notation "α"=> A.ang
local notation "γ"=> A.fee
local notation "l"=> A.post
local notation "F"=> U.sent x T q θ l β
local notation "Y"=> (U.park,U.k)
local notation "K"=> U.key.dome (j*radiusB x)
local notation "YY"=> A.Beds
local notation "N₁"=>(Fintype.card SU.group.ColorIndex:ℝ)
local notation "Vw"=> Vmove x U.V
local notation "O"=> neo T x U.k U.key U.park ∘ Vw
local notation "η"=> emptyA T x U.k U.key U.park ∘ Vw
local notation "σ"=> perZ T x U.k U.key U.park ∘ Vw
local notation "ρ"=> acc T x U.k U.key U.park q θ (U.bush x) l ∘ Vw
variable {C a b c g:ℝ}
local notation "Z₀"=> kist U
local notation "m"=> Domain N B
local notation "b₀"=> ratioB S (3*radiusB x)
open AnalyticBridge.RelativeLogdet Ink Matrix Further.CurvedGaussianJets.Tracks PhysicalNext.OrderedAffine2B.SymFare Order
structure Flex (n:ℕ)(C a b c:ℝ)(v: Directions SU.group (Domain N B)):Prop where
 heel : PriceW η σ n v C (C*tipPay a x)
 leg : PriceW O (simplest O) n v b b
 arm : PriceW ρ (simplest ρ) n v c c
variable(T)
lemma gatherH (p: NameX T U x q θ l n C a b c g) {c':ℝ}{v t:ℝ}(hv: C<c')(hu:b<v)(ht:c<t)(h:ContinuousAt η 0):∀ᶠ i in 𝓝 (0:Directions SU.group (Domain N B)),Flex A U n c' a v t i:=by
 have he : IsCompact Isle:=isCompact_Icc
 have hh :(0:ℝ)∈ Isle:=Set.left_mem_Icc.mpr zero_le_one
 have hz{κ:Type}[Fintype κ][DecidableEq κ]{W:Directions SU.group (Domain N B) → Matrix κ κ ℝ}{Z D:ℝ}(p:PriceW W (simplest W) n 0 Z D):ContinuousAt W 0:=(transX ((p.paid 0 hh).1.germ (f':=fun y=>paintO (W y)) (Eventually.of_forall fun y=> congrArg paintO (Matrix.mul_one _)))).continuousAt
 filter_upwards [sprain p.price.center (k:=(mul_lt_mul_of_pos_right hv (Real.exp_pos _))) hv h,sprain p.price.core hu hu (hz p.price.core),sprain p.price.modes ht ht (hz p.price.modes)] with i h u v using ⟨h,u,v⟩
variable {y:Directions SU.group (Domain N B)}
-- include kist growth at new constants.Separate. exploit per-$Z$ lens.
lemma wool (p:Flex A U n C a b c y)(hn : PriceW (emptyA T x (kist U).k (kist U).key (kist U).park ∘ Vmove x (kist U).V) (perZ T x (kist U).k (kist U).key (kist U).park ∘ Vmove x (kist U).V) n 0 C (C*tipPay a x))(hb:0≤b)(hx:0≤c)(hp:0≤C)(o:Site (Domain N B))(w:LinkS S k): Allows n (fun i=> leys A (U.atop i x) o w) y (fareI C a b c x n k) :=by
 let P(M:Monk SU.group S):=pave T x q θ l w M
 let u:=(2:ℝ)⁻¹
 have hg: |paveB (x:=x) T w Z₀| ≤ u*Lich.Muster.quota n k C (C*tipPay a x):=by
    by_cases he:∃ v:Run ((kist U).zoo x) (k+1), stave v=w
    · obtain ⟨v,rfl⟩:= he; rw [stationB]; have ht:= (bar_t hn v).value; change |vent (T:=T) Z₀ v|≤_; unfold vent; rw [abs_mul,abs_neg, abs_of_pos (by norm_num : (0:ℝ)< 1/2)]; unfold u; rw [one_div]; simp only [Function.comp_apply,Vmove,smul_zero,Work.G07.at_zero_increment] at ht; exact mul_le_mul_of_nonneg_left ht (by positivity) -- tune
    rw [paveB,dif_neg he,abs_zero]; unfold u Lich.Muster.quota tipPay; positivity
 have he: Allows n (fun i=>P (U.atop i x)) y (u*Lich.Muster.quota n k C (C*tipPay a x)+ u*Lich.Muster.quota n k b b+Lich.Muster.quota n k c c):=by
    by_cases z:∃ v:Run (U.zoo x) (k+1),stave v=w -- tune
    · obtain ⟨v,rfl⟩:= z; have ht:= (bar_t p.heel v).smul (-u); have hi:= (bar_t p.leg v).smul u; rw [abs_neg,abs_of_pos (by unfold u; norm_num)] at ht; rw [abs_of_pos (by unfold u; norm_num)] at hi; apply ((ht.add hi).add (bar_t p.arm v)).germ; filter_upwards with i; unfold P; have he: pave T x q θ l (Tarn.stave v) (U.atop i x)= pes T x q θ l (U.atop i x) v:= paved ..; rw [he]; simp only [pes,u,one_div]; rfl
    refine (Jet.allows_const y (v:=(0:ℝ)) (C:=u*Lich.Muster.quota n k C (C*tipPay a x)+u*Lich.Muster.quota n k b b+Lich.Muster.quota n k c c) ?_).germ ?_
    · rw [norm_zero]; unfold u Lich.Muster.quota tipPay; positivity
    filter_upwards with i; change _=Tarn.pave _ _ _ _ _ _ _; have he : ¬∃ v:Run ((U.atop i x).zoo x) (k+1), stave v=w:= z; rw [pave,dif_neg he]
 have hm:= Newt.subtract_p he (Jet.allows_const y (v:=paveB (x:=x) T w Z₀) hg)
 refine ((hm.smul (plant S o w)).mono ((mul_le_of_le_one_left hm.nonneg plant_v).trans_eq ?_)) -- germ definitional
 unfold fareI u; ring
variable (C a b c) {T} in
abbrev note_g (L:Palot.leaf (Site (Domain N B)))(k:ℕ):= ∑ i:Site (Domain N B),∑ w∈finW i S x k with Lich.Muster.badge A w=L,fareI C a b c x n k
local notation "Q₀"=> note_g n A C a b c
lemma since {L:Palot.leaf (Site (Domain N B))}(p:0≤C)(h:0≤b)(u:0≤c)(H:Summable (fun k=> ((ratioB S 1*b₀^(k+1):ℕ):ℝ)*fareI C a b c x n k)) : Summable (fun k=>Q₀ L k):=by
 refine summable_sum (s:=Finset.univ) (f:=fun i: Site m=>fun k:ℕ=>∑ w∈finW i S x k with Lich.Muster.badge A w=L,fareI C a b c x n k) (fun i _=> Summable.of_norm_bounded H ?_)
 intro k; have hz : 0 ≤fareI C a b c x n k:=by unfold fareI Lich.Muster.quota tipPay; positivity
 rw [sum_const, nsmul_eq_mul,Real.norm_of_nonneg (by positivity)]; exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr ((card_le_card (filter_subset ..)).trans (hearty i k))) hz
-- simultaneous costs. E.Psp.
lemma birth (p: NameX T U x q θ l n C a b c g)(p': NameX T Z₀ x q θ l n C a b c g) {c' v t:ℝ}(hv: C<c')(hp:b<v)(hc:c<t)(h₀:ContinuousAt η 0)(hz:0≤b)(hy:0≤c) (h1: (b₀:ℝ)*N₁*2^n*(c'*tipPay a x)<1)(h2:(b₀:ℝ)*N₁*2^n*v<1)(h3:(b₀:ℝ)*N₁*2^n*t<1) (L:Palot.leaf (Site (Domain N B))): Allows n (fun i:Directions SU.group m=> massX A (U.atop i x) L) 0 (∑' k:ℕ, Q₀ L (k+3)):=by
 have he := (since T n A (p.posT.trans hv.le) (hz.trans hp.le) (hy.trans hc.le) (metro n b₀ (ratioB S 1) (p.posT.trans hv.le) (hz.trans hp.le) (hy.trans hc.le) h1 h2 h3) (L:=L)); have hh:= since T n A (L:=L) p.posT hz hy (metro n b₀ (ratioB S 1) p.posT hz hy (lt_of_le_of_lt (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hv.le (Real.exp_pos _).le) (by positivity)) h1) (lt_of_le_of_lt (mul_le_mul_of_nonneg_left hp.le (by positivity)) h2) (lt_of_le_of_lt (mul_le_mul_of_nonneg_left hc.le (by positivity)) h3)); refine late_sum (n:=n) ?_ ((summable_nat_add_iff 3).mpr he) ((summable_nat_add_iff 3).mpr hh) ?_
 · filter_upwards [gatherH T n A U p hv hp hc h₀] with i z jX; exact Jet.allows_sum (s:=Finset.univ) (fun k _=> Jet.allows_sum (fun m' v'=> wool T n A U z (p'.price.center.cheaper hv.le (mul_le_mul_of_nonneg_right hv.le (Real.exp_pos _).le)) (hz.trans hp.le) (hy.trans hc.le) (p.posT.trans hv.le) k m')) -- tune order
 intro i; exact Jet.allows_sum (s:=Finset.univ) fun k _=> Jet.allows_sum (fun m' v=> luxeS T n A U m' k p p' hz hy)
end YM.CF.Fief
