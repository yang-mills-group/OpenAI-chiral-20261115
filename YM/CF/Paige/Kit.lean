import YM.CF.Broc.Opera
import YM.CF.Reed.King
/-!
# Uniform κ-history/scalar portion, at finite lattice cutoff

Exact comparison of chiral determinant directions (including phase/integer
branches), nonperturbatively on coupled two-scale backgrounds; payoff at the
bare chiral RP cutoff is the same field. Volume independent graph projection and
exact open transmission (external arbitrary word) with its extensive scalar
support bill. See `Peaks.Scale` etc separately for open propagation estimates.

Still a step theorem, not a trajectory! Kinematics of block transform are not
claims of continuum renormalization. In this version "coherent" means broad
curvature and closeness of outputs to straight links. `fire` acts on the mixed
Wick evaluations, no estimates on the corresponding bosonic integrations
here. Local prices after drawing Stun in this lemma use continuity, not claimed
to apply on non-global small-field domains, or with link jets on rays. The
related small-field operation estimates before drawing use the analyticity
conventions of `Drapes`. Finite-regulator multiplicity explicit in bands and
all weights. We do *not* in this statement exclude mirrors in a continuum
answer by only knowing about these free/cutoff bands.
-/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Paige
open Function Filter Lattice Metric Lat Finset Tenant Branch Fock Dial MeasureTheory Phase Phase.Sample Brace Cube Peaks Tulip Rush Drapes Broc RP
open scoped Topology Matrix MatrixOrder BigOperators Matrix.Norms.L2Operator InnerProductSpace
attribute [local instance] opCStarAlgebra
variable {j:ℕ}{L: Side}{ho:Odd L.val}{T:Script Male}{Y:Pricing j L ho T}{B m r: Side}{e β c V p q d:ℝ}
variable(g:Grasp Y B e)(G:Ratio (CSide m B) (CSide r B))
def arcT(g:Grasp Y B e):ℝ:= inkp g/feeG (popV L B)
def arcV(g:Grasp Y B e):ℝ:= feeG (popV L B)* inkg g
abbrev Daily (U:nomA m r B)(M:Male):Prop:= let l:=unionP U; let P:=foal j true M G l; let H:=wh j L ho true M G l; let X:=ticketT T true M G l; let W:=ticketT T false M G l; let K:=pine j L ho T true M G l; let S:=pine j L ho T false M G l;
   proxyZ (reefS G true) (patchQ G) (adjust g G U.1 M) (tune g (upMale L ho M) U.2) P H K S X W ((sect0 G *chargeA T G M l)⁻¹) (Complex.exp (flakeL g G U M)) ∧ ∀ v, inner ℂ (mateK (CSide m B)) (fire T G M l v)=inner ℂ (oceanA G) v
structure Vial (g:Grasp Y B e)(R:RP.Reg β e B)(p q c V d: ℝ):Prop where
 valid : Reed.Cutoff R p q c V d g.baseY
 serial : ∀ m:Side,R.c m=northZ m B
 synchronized(m:Side)(h:g.roundZ≤(CSide m B).val)(U: Ave.Briar m B e): tune g firstM U.val=cartsL (helix _).symm (sound m B (R.c m) U.val)
 setting(m:Side)(M:Male)(h:g.roundZ≤(CSide m B).val):ContinuousOn (tune (m:=m) g M) {U|Guard U e}
 sea(m:Side)(M:Male)(h:g.roundZ≤(CSide m B).val)(U:Skin m B)(u:Guard U e): Sea (spar j M U) (tune g M U) ∧ ∀ t, tune g M (Lattice.gauge t U)=effectK (tradew _ t).val (tune g M U)
 commute(m r:Side)(M:Male)(G:Ratio (CSide m B) (CSide r B))(h:G.count=L)(u:g.roundZ≤(CSide m B).val)(x:Rent0 G e): Daily g G x.val M
 coherence(m r:Side)(M:Male)(G:Ratio (CSide m B) (CSide r B))(h:G.count=L)(u:g.roundZ≤(CSide m B).val): Seat (dressL G e) (fun i=> flakeL g G i.val M) (arcT g) (arcV g)
 posA : 0<arcT g
 posV : 0<arcV g
lemma capperL (h:0<e) {R:RP.Reg β e B}(t:Reed.Cutoff R p q c V d g.baseY)(v: R.c=(fun m=>anticut (CSide m B))): Vial g R p q c V d:=by
  refine ⟨t,congr_fun v, fun m k U=> ?_, fun m M k=> ?_,fun m M k U hx=> ?_,fun m r M G hG k x=> fortune g h G hG k x.val x.property M,fun m r M G hG k=>opas g G hG k h M,?_,?_⟩
  · rw [congr_fun v]; exact fundus g.topB g.baseY (g.couture k firstM) _ U.property
  · exact freezing g.topB h.le (g.couture k M) (g.broadness _ k M).continuousOn
  · let x:=starfish m B U (cue_from U).choose; have hp:=g.couture k M; have H:=g.broadness _ k M
    refine ⟨heartS g.topB h.le hp U hx (H.projection _ hx),fun t=>?_⟩; exact phase_g g.topB h.le hp U hx x (starK g.topB h.le hx (cue_from U).choose_spec) t H
  · exact div_pos (ink_pos g) (by unfold feeG; positivity)
  exact mul_pos (by unfold feeG; positivity) (inkp_price g)
theorem relevant (j:ℕ)(hj:Even j)(hm:1≤ j)(L:Side)(ho:Odd L.val) : ∃ (T: Script Male),Use j L T ∧ ∀ (c:ℝ),0<c→ ∃ Y: Pricing j L ho T,∃ b:Side,∃ n:ℕ,∀ B:Side,n≤B.val→(∃ K,b*K=B)→∃ ε p q V d:ℝ,0<ε∧0<p∧0<d∧d<1 ∧ ∀ e:ℝ,0<e→e≤ ε→∃ g:Grasp Y B e,∀ β:ℝ,∀ s:ℝ,0<s→∃ R:RP.Reg β e B,1-s<R.knob ∧ Vial g R p q c V d:=by
  let T:= Peaks.cloth j; let t :Use j L (Peaks.cloth j):= canUse j L ho -- tune
  refine ⟨_,t,?_⟩; intro k p
  obtain ⟨s,hσ,S,l,F⟩:= Reed.FiniteK k p
  obtain ⟨Y⟩:= prices j _ ho _ t hj hm; obtain ⟨b,n,P⟩:= grip Y hm
  refine ⟨Y,b,max l n,fun B hL hB=>?_⟩
  obtain ⟨x,Y',pK,K,u,v,R⟩:=F B ((le_max_left ..).trans hL)
  obtain ⟨y,Q,A⟩:=P B ((le_max_right ..).trans hL) hB
  refine ⟨min x y,pK,Y',K,s,lt_min u Q,v,hσ,S,fun e p he=>?_⟩
  obtain ⟨g,hg⟩:= A e p (he.trans (min_le_right ..)); obtain ⟨t,T'⟩:= R e p (he.trans (min_le_left ..));
  refine ⟨g,fun β a p'=>?_⟩; obtain ⟨R,h,H,C⟩:= T' β a p'; exact ⟨R,h,capperL g p H C⟩
end YM.CF.Paige
