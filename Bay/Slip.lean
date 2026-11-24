import Bay.Lantern
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 3000
set_option synthInstance.maxSize 24000
set_option quotPrecheck false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Bay
open Function Filter Topology NormedSpace Lattice Wilson Fock Pastry Scree Sault Sour Stax Skye Jet Scroll Finset Palot Cadre Vow
open RG MeasureTheory Rue
open Metric Drapes Tulip Lat Branch Cube Tenant
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Classical
attribute [local instance] opCStarAlgebra
open Rush SU Tap Levier Thera Oath Font Spire Dial Rill
open Kennel Swell


open StressExchange
variable {N:Side}{p:BudgetPoint}{K:Scree.Loom N}{o:Seat N}
lemma roost_spin (k:ℕ)(s:Sweep N):
 (roost k o).map (boxA s).toEmbedding=roost k (boxA s o):=by rw [roost,← paysT,map_singleton];rfl
lemma lampTurn (s:Sweep N)(V:Pane N): flashA s V∈setAwning p o ↔ V∈setAwning p (boxA s o):=by
 apply Iff.trans _ (Salt.glowA _ _ s V)
 have h: Salt.actY s (roost p.B (boxA s o))=roost p.B o:=by unfold Salt.actY; rw [←sitU,roost_spin,sitU,Equiv.symm_apply_apply]
 change _ ↔ pingS _ _ _;rw [h];rfl
variable {X:SOp N}{a c d:ℝ}{k:ℕ}
lemma trueJul (s:Sweep N)(V:Pane N)(H:Clearance p K k d)(G:BoxPay X o k c d):
 ech s (bayonet K p ((boxA s) o) (julStep s X) V) = bayonet K p o X (flashA s V):=by
 by_cases h:V∈ setAwning p (boxA s o)
 · let u:Orbit N:=(V,Classical.arbitrary _)
   have t: bayonet K p (boxA s o) (julStep s X) V= julStep s X (profile (K u)):=Set.indicator_of_mem h _
   rw [t,julius]
   refine (box_pass H G ((lampTurn _ _).mpr h) (flashD _ _ _ _ ?_) (keepC _ _ _ _ (H.onD u))).symm
   rw[roost_spin]; exact fun i e l=> (H.light (x:=u) h _ e l).symm

 rw [bay_nil h,bay_nil (mt (lampTurn _ _).mp h),ech,singT,win_z,map_zero]
lemma echTick (s:Sweep N):ech s (tickA N)=swapX (detX s.s) (tickA N):=by
 rw [touchP];exact tickR _ _ _ (spinZ _ _) _
/-- Exact poses of (130) operand in (128), even across fails (first argument!). -/
lemma toothMoves (x y:Site N)(H:Clearance p K k d)(G:BoxPay X (node x) k c d) (V:Pane N): let s:=taxiPlus (y-x); twist (quantU (γS s)) (tooth K p x y X V)= toothAt K p x X (flashA s V):=by
 intro s
 have hx:detX s.s=false:= det_i
 have ht:= echTick s; rw[hx] at ht;change twist (γS s) (tickA N)=tickA N at ht
 unfold tooth toothAt co_Ψ emMark
 rw [preMove,ht, show node y = boxA s (node x) from ?_] -- direction!
 · change preJ (tickA N) (ech s (bayonet K p (boxA s (node x)) (julStep s X) V)) = _
   rw[trueJul s V H G]
 unfold s;rw [platforms, add_sub_cancel]
end YM.CF.Bay
