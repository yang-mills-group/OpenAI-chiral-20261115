import YM.CF.Buffered.Brink
import YM.CF.Buffered.Edition
/-! Small strap read admitted on Anchor. Angle without offset, proof on actual action.
 Compare on sharp read (same path, F etc). Tower comparison needs simultaneous area.
-/
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option synthInstance.maxSize 21000
noncomputable section
namespace YM.CF.Buffered.Crust
open Function Filter Finset Lattice Wilson RG PathData Work.F03 Cube Region Roost Rush MeasureTheory Metric Girt Nova Analysis Pressure Tulip Lat Cube SU Emu Rush Scree Graph RG Scroll Peaks Drapes Cascade Vault Sods Spire Paige Kea Ember Mint Mint.Roe
open Grid
open scoped Topology ContDiff InnerProductSpace BigOperators Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {G: Gauge} {p: BudgetPoint}{c:Clip} {N P: Side}{F: PathData G}{a b r C L w:ℝ}
-- attach Angle at right norm instance (no matrices of G here)
lemma globe_price {I:GramM N}(h:I.path.Bounds I.funds a C L) : Grid.globe (More N) I.path I.funds I.p I.beta I.p.threshold= Graph.angle I:=by
 classical
 let f:=floorF (More N) I.path I.funds I.p I.beta I.p.threshold; let ht:Graph.dim I=f ∘ Prod.fst:=by funext i; by_cases p:i∈ Lace I; unfold Graph.dim; rw [Set.indicator_of_mem p]; exact (floor_hit i.1 I.p.threshold p).symm; unfold Graph.dim; rw [Set.indicator_of_notMem p]; unfold f; exact (Set.indicator_of_notMem (s:=Calm SU.group (More N) I.p.threshold) (a:=i.1) (fun u=>p u) (fun x=>Graph.past I x)).symm
 let S:=Wilson.prior SU.group (More N); have hp: MeasurePreserving Prod.fst (city N) S:=measurePreserving_fst
 change (∫ x,f x∂S)=_; rw [←hp.map_eq,Graph.angle,ht,integral_map hp.1.aemeasurable (floor_e h _ I.p I.beta I.p.threshold).meas.aestronglyMeasurable]; rfl
private lemma reduces_t(g:F.Bounds c a C L)(A:Config G N)(p:BudgetPoint)(h:0≤b)(u:flags p.threshold A=∅)(z: flags (p.threshold/2) A≠∅)(q:w ≤ c.linear): kinetic N p C L b w ≤ F.inChannels c p b A:= by
 have he (Y:Config G N)(u: flags p.threshold Y=∅)(z: flags (p.threshold/2) Y≠∅): kinetic N p C L b w ≤ F.principal c p b Y:= by
   rw [ne_eq, flags_calm] at z; obtain ⟨i,t⟩:= not_forall.mp z; let s:=G.chord (faceValue Y i)
   have hc:0<c.direct:= c.quadratic_pos; have hz: p.threshold/2 < s:=lt_of_not_ge t; have ht:0<p.threshold:=p.threshold_pos
   have hh(i:Face (Per N)):0 ≤ F.baseTerm c p Y i:=by rw [simple u]; positivity
   have hp:w*p.threshold^2≤∑ x,F.baseTerm c p Y x:=by
     apply (single_le_sum (fun i _=> hh i) (mem_univ i)).trans'; rw [simple u]; apply le_trans _ (le_add_of_nonneg_right (by positivity)); change _ ≤ c.direct*s^2/2; have he:= mul_le_mul_of_nonneg_right (show w≤ c.direct/8 by linarith [c.kink]) (sq_nonneg p.threshold); nlinarith only [he,mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (show 0 ≤ p.threshold/2 by positivity) hz.le 2) hc.le]
   obtain ⟨k,l⟩:= oath g p Y; unfold kinetic taxY PathData.principal; exact le_trans (le_of_eq (by ring)) (add_le_add (mul_le_mul_of_nonneg_left (add_le_add hp (neg_le_of_abs_le k)) h) (neg_le_of_abs_le l)) -- tune
 have hw (s:Signed)(x:ℝ) : flags x (pull s 0 A)=∅ ↔ flags x A=∅:=by classical rw [←Work.H03.flags_send (U:=A) s 0 x,Finset.image_eq_empty]
 let V:= kinetic N p C L b w
 unfold inChannels; refine le_trans ?_ (mul_le_mul_of_nonneg_left (sum_le_sum (fun s _=> he _ ((hw s _).2 u) (fun h=>z ((hw s _).1 h)))) (by positivity)); simp
lemma floor_loss (g:F.Bounds c a C L)(p:BudgetPoint)(h:0≤b)(q:w≤c.linear) : globe N F c p b p.threshold - globe N F c p b (p.threshold/2)≤ Real.exp (-(kinetic N p C L b w)):=by
 classical
 unfold globe; let Z(x:ℝ):=floorF N F c p b x; let V:= p.threshold; have ht:0<V:=p.threshold_pos
 rw [←integral_sub ((floor_e g N p b _).integrable _) ((floor_e g N p b _).integrable _)]
 apply le_trans (b:=∫ _x: Config G N,Real.exp (-(kinetic N p C L b w))∂ Wilson.prior G N) (integral_mono (((floor_e g N p b V).integrable _).sub ((floor_e g N p b (p.threshold/2)).integrable _)) (integrable_const _) (fun x=> ?_)); · simp
 change Z V x- Z (p.threshold/2) x ≤ _; by_cases v :flags p.threshold x=∅; swap; · rw [show Z V x=0 from Set.indicator_of_notMem (s:=Calm G N V) v _]; exact (sub_nonpos.mpr (floor_p ..)).trans (Real.exp_pos _).le
 by_cases h':flags (p.threshold/2) x=∅
 · rw [show Z V x=_ from (floor_hit (F:=F) (c:=c) (p:=p) (β:=b) x p.threshold v),show Z (p.threshold/2) x=_ from floor_hit (F:=F) (c:=c) (p:=p) (β:=b) x _ h',sub_self]; positivity
 rw [show Z V x=Real.exp _ from floor_hit _ _ v, show Z _ x=0 from Set.indicator_of_notMem (s:=Calm G N (p.threshold/2)) h' _, sub_zero]; exact Real.exp_le_exp.mpr (neg_le_neg (reduces_t g x p h v h' q))
