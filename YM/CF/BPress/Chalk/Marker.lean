import YM.CF.BPress.Chalk.Mantel
/-! Eq:B-Madd. Path-brush & orientation prerequisites across whole gauge Marks. Drop one bandwidth of clamps whenever accepted. Exponential-in-own-card sup bound separate from angle densities and from primary countermark. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BPress.Chalk
open Function Filter Finset NormedSpace MeasureTheory Fock SU SU.Pair Lattice Cube Lat Spin Spin.Paint Spin.Stride Spin.Hole Pf Dial Nacre Tulip Branch Bias Fixed Net Meadow Skye Stamps Bands
open scoped Topology BigOperators Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace Kronecker Classical
attribute [local instance] opCStarAlgebra
variable {N:Side}
lemma principal_curve (x:Site N) : Continuous (pureUp x):=by
 letI : NormedAlgebra ℚ (FC (Single N)) := NormedAlgebra.restrictScalars ℚ ℂ (FC (Single N))
 let g(A: Op Slot):=exp (coupl (Yore x A)); have ht:Continuous g:= exp_continuous.comp (f:=fun A=>coupl (Yore x A)) (coupl_cont.comp (f:=fun A=>Yore x A) ((continuous_const.mul (Paint.coupling_cont.comp (continuous_pi fun _=>continuous_id))).mul continuous_const)) -- implicit?
 exact ((ht.mul continuous_const).mul ht.star).mul continuous_const
lemma lift_meas {D:Type*}[MeasurableSpace D](S:Support N)(H:D→ Paint (More N))(h:Measurable H):Measurable fun i=> shroud (H i) S:=(continuous_id.star (α:=FC (Single N))).measurable.comp (tomes_flour S (fun i=>liftPack (H i)) (fun i _=> (principal_curve i).measurable.comp ((measurable_pi_apply _).comp h))) -- frame
variable {B:BandWidth}(X:Bands (More N) B) (i:X.Index) {T:Sheet.Atlas}{y L C C':ℝ}{b:ℕ}(F:Net (More N) T L y C C' b) (k:Grid.Tiling (More N))
abbrev withinX (X:Support (More N)) : Support N:=univ.filter fun i=> node i∈X
lemma regions_v (S:Support (More N)): (withinX S).biUnion den ⊆ matterRegion N S:=by
 intro i p; obtain ⟨x,w,h⟩:=mem_biUnion.mp p; have hx:penX i=x:=(mem_filter.mp h).2; exact (mem_matterRegion ..).2 (show node (penX i)∈ S from hx ▸ (mem_filter.mp w).2) -- tune

def pairTest (x:Micro (More N)× Duo (More N)) : FC (Single N):= shroud (brush F x.1 x.2 k X i 2) (withinX (X.band i))
abbrev cost_site:= (Real.exp (ν^2))^2
local notation "K(" s ")"=>cost_site^(card (withinX s))
lemma guards : Extends F X i (pairTest X i F k) (K(X.band i)):=by
 have h:Measurable (pairTest X i F k):= lift_meas (withinX (X.band i)) (fun x: Micro (More N)× Duo (More N)=>Stamps.brush F x.1 x.2 k X i 2) (brush_m F k X i 2); refine ⟨fun p=> ⟨fun u v t=> ?_ ,fun U=>?_,h.comp (measurable_id.prodMk measurable_const),fun u=>?_ ⟩,h,?_⟩; swap
 · exact zoom ((tomes_even (N:=N) ..).contr) (regions_v _)
 · let b(x:Micro (More N)):= pairTest X i F k (x,p); apply congrArg (fun f:ℝ→Paint (More N)=> shroud (f 2) (withinX (X.band i))) (Stamps.roots F u p k X i v t).2
 · let U:=brush F u p k X i; have hz := (Stamps.paid F u p k X i).scheme 2; change ‖shroud (U 2) (withinX _)‖≤_; rw [shroud,norm_star]; exact tomes_cost _ _ _ (fun i _=> bears_κ i _ (hz (node i)))
 intro z U p h h' a; unfold pairTest; dsimp only; rw [staysH]; exact room_eq _ _ _ (fun t u=> (Stamps.follows F U p k X i a z).2 2 (mem_filter.mp u).2)

/-- no charge phase altered, works also when splitting H from that of nominal brush. -/
lemma pairRead (u : Micro (More N))(p:Duo (More N))(T:Support N)(H:Paint (More N))(v: Wave (Single N))(f: withinX (X.band i) ⊆ T)(t:∀ x:Site N,node x∈X.band i→ brush F u p k X i 2 (node x)=H (node x))(p':MatPlan H):let S:= withinX (X.band i)
 inner ℂ (braC (Locks T true) (Locks T false) (coupling H)) (acts (pairTest X i F k (u,p)) v)= inner ℂ (braC (Locks (T\ S) true) (Locks (T\ S) false) (coupling H)) v :=by
 intro S; rw [pairTest, room_eq _ S H (fun i p=>t i (mem_filter.mp p).2)]; exact candle H _ S f p' v
lemma slotN (K:Support (More N)): (withinX K).card≤K.card:= card_le_card_of_injOn node (fun i p=>(mem_filter.mp p).2) Tenant.needle.injOn
-- sup log expenditure `BodyNeed`
lemma bodyNeed : K(X.band i) ≤ Real.exp (2*(ν^2)*((B.marked.val+1)*(More N).val^3)):=by
 unfold cost_site; rw [←pow_mul, ←Real.exp_nat_mul]; apply Real.exp_monotone; have h:= slotN (X.band i); rw [Bands.band_card X i] at h; push_cast; refine le_trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr h) zero_le_two) (sq_nonneg _)) ?_; push_cast; exact Eq.le (by ring)
end YM.CF.BPress.Chalk
#print axioms YM.CF.BPress.Chalk.guards
#print axioms YM.CF.BPress.Chalk.pairRead
#print axioms YM.CF.BPress.Chalk.woven_mate
