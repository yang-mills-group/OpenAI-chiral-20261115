import YM.SU5.FiniteGaugeData.Lapis.Holiday
import YM.Work.F03.Flat
import YM.Work.G06.TurnSlot
/-! # Frame. Ambient tangent Gaussian and projection prices for growth occupancy.
-/
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 20000
set_option linter.flexible false
set_option quotPrecheck false
noncomputable section
namespace YM.SU5.FiniteGaugeData.Lapis
open Function Finset Filter MeasureTheory ProbabilityTheory Matrix Lattice Wilson RG Precision Tree Next.Fluctuations Work.F03
open Pressure Exterior Laurent Bloch Drachma Galope Avenue Galope.Press Wrist Poeme Haute Punch
open scoped Topology InnerProductSpace Matrix MatrixOrder RealInnerProductSpace ContDiff BigOperators NNReal ENNReal Kronecker Classical
namespace Lumi
open Dig Motion Real Affiche Artis Avenue Recruit Next.Rank Next.Rank.Spindle Syl Drachma.Tame Drachma.Tokens Poeme CF.Font RouteM
variable {ι:Type} [Fintype ι] [DecidableEq ι] {G:Gauge} (T:Duct G ι){n:Side}{C κ K L α t b Δ a β:ℝ}(s:Signed)(x:Site n) {g: LogField G n} {u:Stage}{p:BudgetPoint} {q:ℝ} {R':Bed}{R:PathData G}{V U:Config G n}{A:Finset (Cell n)}{M w k r:ℕ}{o y:Site n}{Z:Finset (Site n)}
open Lantern Lantern.Cup
local notation "m₀"=> macroK ι T
local notation "Z'"=> heightK p M
local notation "Yt"=> glow A (lic w)
local notation "Fq"=> T.seen
variable (W:R.Bounds u.clip u.width u.paths Δ)(B:Attached R' R)
local notation "DAY"=> heatC (billsC (coreN w) w (glow A (lic w))) W B
local notation "XDAY"=> heatC univ W B
local notation "Θ"=> κ*(Real.sqrt β)
open Cold
-- aperture true on actual all-phase orientations.
omit [DecidableEq ι]
private lemma concession (p:Intro n w)(A:Finset (Cell n)):
 let S:=leafBook A w; ((Sᶜ).card:ℝ) ≤ diamC/(w:ℝ)^2*tileC n + (tB (coreN w):ℝ)*A.card:=by
 intro S; let Z:=glow A (lic w); let T:=buy Z (coreN w); let I:=(coreN w); let d:=disc Z I; have he:T⊆ S ×ˢ Hor:=by
    intro x hx; obtain ⟨i,p,y⟩:= mem_biUnion.mp hx; obtain ⟨b,c⟩:=mem_product.mp y; exact mem_product.mpr ⟨mem_biUnion.mpr ⟨i,p,(mem_filter.mp b).1⟩,c⟩
 let r:=radiusB (0:ℝ); let v:ℝ:=tileC n; let x:ℕ:=(Sᶜ).card; have hv:x≤ d:=by
    have hh:T.card≤ S.card*3:=(card_le_card he).trans_eq (by rw [card_product,count_hor])
    have ht: x+S.card= tileC n:=by exact card_compl_add_card S -- wrong rw
    have he:= disc_book (glow_in A (lic w)) (v:=show coreN w ≤ lic w from by unfold lic; omega); change d+ T.card=3*tileC n+1 at he; omega
 have ht:0<(w:ℝ):=by exact_mod_cast lt_of_lt_of_le (by decide:0<(2:ℕ)) p.1
 refine le_trans (Nat.cast_le.mpr hv) ?_; apply le_of_mul_le_mul_right _ (pow_pos ht 2); rw [div_mul_eq_mul_div]; linarith only [qualify p A,show diamC*(tileC n:ℝ)/w^2*(w:ℝ)^2=diamC*(tileC n:ℝ) from div_mul_cancel₀ _ (pow_pos ht 2).ne', (show 0≤(w:ℝ)^2 from sq_nonneg _)] -- tune parentheses Int casting mismatch
-- weather high scale, Uniform. y*sqrt(theta) etc.W. 
lemma respite : soft (-1/2) Real.sqrt:=by
 have he:= soft.bare_rpow (-1/2); apply he.turned rfl; filter_upwards with x; rw [Real.sqrt_eq_rpow]; norm_num
lemma levity (h:0<α)(z:0≤b) (u:Stage): ∀ᶠ x in atTop, ∀ (β κ t:ℝ),x/2≤β→β≤2*x→|κ|≤2→|t|≤b→∀ p:BudgetPoint,p.threshold=temp x→∀ (n:Side) (S:Finset (Site n))(s:Signed)(R':Bed)(R:PathData G) (C:ℝ)(W:R.Bounds u.clip u.width u.paths C)(B:Attached R' R)(V:Config G n)(A:Finset (Cell n))(X:LogField G n), let w:=radiusB x; let M:=lic w; let Z:=glow A M; ‖X‖≤ heightK p M → (∀ i∈ RoomsM M Z, V i= represent X i) → ∀ j ∈ leafBook A w, |t*live T u.clip (κ*Real.sqrt β) s j V - t *view T s j ((κ*Real.sqrt β) • heatC (billsC (coreN w) w Z) W B X)| ≤ α :=by
 obtain ⟨C,d,hC,hd,hw⟩:=wake G (macroK ι T)
 let H:= 4*b*T.c*√u.clip.direct*C; have hH:0≤H:=by unfold H; exact mul_nonneg (mul_nonneg (mul_nonneg (by positivity) T.grant) (Real.sqrt_nonneg _)) hC
 let F(x:ℝ):= H * (√x * (Θb x * Θb x)); have he: Tendsto F atTop (𝓝 0):= (soft.price (respite.times (runθ.times runθ)) H hH).close (by norm_num)
 filter_upwards [eventually_gt_atTop (0:ℝ),Work.E01.radiusB_tendsto.eventually_ge_atTop (macroK ι T), (runθ.close (by norm_num)).eventually (ge_mem_nhds hd),he.eventually (ge_mem_nhds h)] with x hx y v f β κ t hβ htβ hκ ht p pp n S s R' R'C D W B V A X θ M Z hx₁ hx₂ j hv
 -- `X T horizon notation.B.`
 have hz:0≤β:= ((half_pos hx).trans_le hβ).le; have hb:‖κ*Real.sqrt β‖ ≤ 4*√x:=by rw [norm_mul]; apply le_trans (_root_.mul_le_mul hκ (show ‖√β‖≤2*√x from ?_) (norm_nonneg _) zero_le_two) (le_of_eq (by ring)); rw [Real.norm_of_nonneg (Real.sqrt_nonneg _)]; -- square
                                                                                    have hS:=Real.sqrt_nonneg x; apply (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity)).1; rw [mul_pow,Real.sq_sqrt hz,Real.sq_sqrt hx.le]; nlinarith only [htβ,hx]
 have hq : heightK p (lic (radiusB x))=Θb x:=by unfold heightK; rw [pp]
 have hy:‖X‖ ≤Θb x:=hq ▸ hx₁; have hθ:0 ≤ Θb x:= (norm_nonneg _).trans hy
 have hE:= drama T s j W B V hv y X hx₂ hC (fun i=> hw n X j _ (length_q T s i) (hy.trans v)) (κ*Real.sqrt β)
 rw [←mul_sub,abs_mul]; apply le_trans (_root_.mul_le_mul ht hE (abs_nonneg _) z) (le_trans ?_ f); unfold F Θb; change b* (T.c* (√u.clip.direct * _* (C*‖X‖^2))) ≤ H *(√x* (Θb x * Θb x))
 have hg: √u.clip.direct*‖κ*√β‖ * (C*‖X‖^2) ≤ √u.clip.direct*(4*√x)*(C*(Θb x)^2):=mul_le_mul (mul_le_mul_of_nonneg_left hb (by positivity)) (mul_le_mul_of_nonneg_left ((sq_le_sq₀ (norm_nonneg _) hθ).2 hy) hC) (mul_nonneg hC (sq_nonneg _)) (by positivity)
 apply (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hg T.grant) z).trans_eq;
 unfold H; ring
def makes (S: Clip)(t:ℝ)(r:ℝ)(D:Site n→ Signed)(Z:Finset (Site n))(V:Config G n):ℝ := t* ∑ i ∈ Z, live T S r (D i) i V
set_option maxHeartbeats 630000 in
lemma embarked (b:ℝ)(z:0≤b)(hp:0<α)(u:Stage) : ∀ᶠ x in atTop,∀ (β κ t:ℝ),x/2≤β→β≤2*x→|κ|≤2→|t|≤b→∀ p:BudgetPoint,p.threshold=temp x→∀ n:Side, Intro n (radiusB x)→ ∀ (S:Finset (Site n))(D:Site n→ Signed)(R':Bed) (R:PathData G)(C:ℝ)(W:R.Bounds u.clip u.width u.paths C)(B:Attached R' R)(A:Finset (Cell n)), let w:=radiusB x; let M:=lic w; let Z:=glow A M; Boat (makes T u.clip t (κ*√β) D S) W B p (touchR T D S t) A Z M (coreN w) w κ β α :=by
 let U'':ℝ:=2*b*T.h; have hu: 0≤ U'':=mul_nonneg (by positivity) T.charge; let Q:= α/2; have hq:0<Q:=half_pos hp
 have hw: Tendsto (fun x:ℝ=>U''*diamC/(radiusB x:ℝ)^2) atTop (𝓝 0):=tendsto_const_nhds.div_atTop ((tendsto_pow_atTop (n:=2) (by omega)).comp (tendsto_natCast_atTop_atTop.comp Work.E01.radiusB_tendsto))
 filter_upwards [levity T hq z u,posterior u (2*U'') (by positivity),eventually_gt_atTop (0:ℝ),hw.eventually (ge_mem_nhds hq)] with x g q0 p' x₀ β κ t h0 z0 v e p qq n hx S D R' R C W B A w M Z V ν X hp' hq' e' -- tune let binder
 let E:= u.clip; let F:=gauge ν V; let uP:= (κ * √β); let B':= leafBook A w; let Y:= heatC (billsC (coreN w) w Z) W B X; let V':=allowance p u A β α; let f(i:Site n):= t* live T E uP (D i) i V- t*view T (D i) i (uP • Y); let T':= (tileC n:ℝ); let K(i:Site n):= if i∈ B'ᶜ then U'' else 0
 have he(i:Site n): f i ≤ Q+K i:=by
    by_cases he:i∈B'; · rw [show K i=0 from if_neg (notMem_compl.mpr he),add_zero]; unfold f; rw [←lived_g T (D i) i E uP V ν]; exact le_of_abs_le (g β κ t h0 z0 v e p qq n S (D i) R' R C W B F A X hq' e' _ he)
    rw [show K i=U'' from if_pos (mem_compl.mpr he)]; apply le_trans (b:=U''); swap; · exact le_add_of_nonneg_left hq.le
    have hκ(i:ℝ)(h: |i|≤ T.h): |t*i|≤b*T.h:= (abs_mul t i).le.trans (mul_le_mul e h (abs_nonneg _) z)
    have hi:=le_of_abs_le (hκ (live T E uP (D i) i V) (T.enough _)); have hl:=neg_le_of_abs_le (hκ (view T (D i) i (uP • Y)) (T.enough _)); unfold f U''; linarith only [hi,hl]
 have hz(i:Site n):0≤K i:=by unfold K; split_ifs; assumption; exact le_rfl
 have hM: ∑ i∈ S, K i ≤ (B'ᶜ).card*U'' := calc
    _ ≤ ∑ i,K i:=sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun i _ _=>hz _)
    _ = _:= by unfold K; rw [← sum_filter,sum_const,nsmul_eq_mul]; rw [show univ.filter (fun i=> i∈ B'ᶜ)=B'ᶜ from Finset.ext (by simp)]
 obtain ht:= Cold.bonus_fit u x p' p qq h0
 have hl: U''*tB (coreN w)≤bonusK p u β/8:=by
    have hw:1≤(w:ℝ):=by exact_mod_cast hx.1.trans' (by norm_num)
    have hm: U''* tB (coreN w)≤ U''*w*tB (coreN w):=mul_le_mul_of_nonneg_right (le_mul_of_one_le_right hu hw) (by positivity)
    linarith only [q0, ht,hm]
 change makes T E t _ _ _ V ≤ touchR T D S t (uP • Y)+V'; apply sub_le_iff_le_add'.mp -- tune sub vs Goal; if goal A≤q+V, need sub_le_iff
 unfold makes touchR; simp_rw [mul_sum,← sum_sub_distrib]; refine le_trans (sum_le_sum (fun i _=> he i)) ?_; rw [sum_add_distrib,sum_const,nsmul_eq_mul]; have hS:(S.card:ℝ)*Q ≤ T'*Q:= mul_le_mul_of_nonneg_right (by change _ ≤ (Fintype.card (Site n):ℝ); exact_mod_cast card_le_univ S) hq.le
 let b':ℝ:= (B'ᶜ).card; unfold V' allowance fine; let η':ℝ:= A.card; have hu0:0≤η':=Nat.cast_nonneg _
 have hm0: b'*U'' ≤ (U''*diamC/w^2)* (tileC n:ℝ)+η'* (bonusK p u β/8):=by apply le_trans (mul_le_mul_of_nonneg_right (concession hx A) hu); rw [show (U''*diamC/w^2)*(tileC n:ℝ)=diamC/(w:ℝ)^2* (tileC n:ℝ)*U'' from by ring]; rw [_root_.add_mul]; apply add_le_add le_rfl; linarith only [mul_le_mul_of_nonneg_left hl hu0] -- tune
 linarith only [hS,hM,hm0, mul_le_mul_of_nonneg_right x₀ (show 0≤T' from Nat.cast_nonneg _),show α*T'= Q*2*T' from (by unfold Q; ring)] -- tune
end Lumi
end YM.SU5.FiniteGaugeData.Lapis
#print axioms YM.SU5.FiniteGaugeData.Lapis.Lumi.embarked
