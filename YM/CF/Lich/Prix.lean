import YM.CF.Lich.Lune
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Lich
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open AnalyticBridge.Annulus1AD Ac Esti
open Atala Forge Cloak Rill Hive Fock Stilo Palot Scion
open Cube Lat Tenant Tulip
open Pastry Hake Levier Urn Peaks Fock Laic Branch Drapes
open Stilo Palot Scion Function Levier Hake Urn Peaks Fock Laic Branch Drapes
attribute [local instance] opCStarAlgebra
open Rush Scroll Paige Vault Phase Acorn Spire Eire
open Tarn Cay Slate Esti Cour Hest Arena Reine Kennel Facet Broc Pec Push.SectorMeasure.Oriented
-- separate path ledger Φ.M.Target.S.P
variable {N P B:Side}(G:Ratio (mid N B) (mid P B))(S:StepData (Domain N B) (Domain P B))(x e:ℝ)(T:Tube SU.group S)
variable{r n j d:ℕ}
namespace Muster
variable{G S x e T}
variable(A:Muster G S x e T)
variable(U: Monk SU.group S)(V W:Rent0 G e) -- V true W at ζ=0
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
local notation "Q'"=> A.LawQ
local notation "YY"=> A.Beds
-- account per site
-- far components plus interior.Optional momentum.
open Corne
open Jet
variable(n)
local notation "μ"=> More (mid N B)
local notation "b₀"=> ratioB S (3*radiusB x)
local notation "Y₀"=> kist U
variable{z b C a c:ℝ}(p:NameX T U x A.trot A.room A.post n C a b c z)(h:NameX T (kist U) x A.trot A.room A.post n C a b c z)(hx:0≤b)(hq:0≤ c)
include p h hx hq
lemma fares (k:ℕ)(i:Site μ)(Z:Palot.leaf (Site μ)):‖want k A U i Z‖ ≤ ((ratioB S 1 * b₀^(k+1):ℕ):ℝ)*fareI C a b c x n k:=by
 unfold want; let u:=fareI C a b c x n k; let f(w:LinkS S k):=leys A U i w; let H:= (finW i S x k).filter fun w=> badge A w=Z
 have he: 0 ≤ u:=by unfold u fareI quota tipPay; have ht:=p.posT; positivity
 have hp(w:LinkS S k): ‖f w‖ ≤ u:= by
    have hy: ‖leys A (U.atop (0:Directions SU.group μ) x) i w‖ ≤ fareI C a b c x n k:= (luxeS T n A U w i p h hx hq).value
    rw [show U.atop 0 x=U from ?_] at hy; exact hy
    cases U; unfold Monk.atop Vmove; simp [Work.G07.at_zero_increment]
 refine (norm_sum_le ..).trans ((sum_le_sum (fun w _=> hp w)).trans ?_); change (∑ _w∈H,u)≤_; rw [sum_const,nsmul_eq_mul]; exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr ((Finset.card_le_card (filter_subset ..)).trans (hearty i k))) he
-- needs expose $w≈M⁴ monotone.Frame dims. UPPER sum$(Z,i) cost Tree tighten later
local notation "A'"=> (Fintype.card SU.group.ColorIndex:ℝ)
omit p h hx hq in
lemma sealS (W C D:ℝ)(p:0≤D)(hv:0≤ W)(h:W*A'*2^n*D<1):Summable fun k=> W^(k+1)*quota n k C D:=by
 -- rewrite geom
 apply ((summable_geometric_of_lt_one (r:=W*A'*2^n*D) (by positivity) h).mul_left (W*A'^(2:ℕ)*2^n*C)).congr; intro k; unfold quota; simp only [mul_pow,pow_succ]; ring
omit p h hx hq in
lemma metro (r f:ℕ)(hp:0≤C)(hb:0≤b)(hc:0≤c)(h1:(r:ℝ)*A'*2^n*(C*tipPay a x)<1)(h2:(r:ℝ)*A'*2^n*b<1)(h3:(r:ℝ)*A'*2^n*c<1) : Summable (fun k:ℕ=> (((f*r^(k+1)):ℕ):ℝ) * fareI C a b c x n k) :=by
 have ht:=sealS n (r:ℝ) C (C*tipPay a x) (mul_nonneg hp (by unfold tipPay; positivity)) (by positivity) h1
 apply (((ht.add ((sealS n (r:ℝ) b b hb (by positivity) h2).mul_left (2:ℝ)⁻¹)).add (sealS n (r:ℝ) c c hc (by positivity) h3)).mul_left (f:ℝ)).congr; intro i; unfold fareI; push_cast; ring
omit p h hx hq in
lemma climateQ {E:Type}[Fintype E] (F':E→ℕ→ℝ)(f:ℕ→ℝ)(h:Summable f)(hp:∀ k i, ‖F' i k‖ ≤ f k): Summable (fun k:ℕ=> ∑ i:E,F' i (k+3)):=by
 have he:∀ i, Summable (F' i):=fun i=>Summable.of_norm_bounded h (fun k=> hp k i)
 have hF:Summable (fun k:ℕ=>∑ i:E,F' i k):= summable_sum (s:=univ) fun i _=> he i
 exact (summable_nat_add_iff 3).mpr hF
omit p h hx hq in
lemma climate (f:ℕ→ℝ)(h:Summable f)(hp:∀ k:ℕ,∀ i:Site μ,∀ L:Palot.leaf (Site μ),‖want k A U i L‖ ≤ f k):Portus A U:= ⟨fun i=> climateQ (fun o k=>want k A U o i) f h (fun k o=>hp k o i)⟩
lemma plenty (h1: (b₀:ℝ)*A'*2^n*(C*tipPay a x)<1)(h2:(b₀:ℝ)*A'*2^n*b < 1)(h3:(b₀:ℝ)*A'*2^n*c<1): Portus A U:=
 climate A U _ (metro (C:=C) n b₀ (ratioB S 1) p.posT hx hq h1 h2 h3) (fares n A U p h hx hq)
end Muster
end YM.CF.Lich
#print axioms YM.CF.Lich.Muster.plenty
