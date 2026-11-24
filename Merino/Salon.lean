import Merino.Shuttle
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 600000
set_option synthInstance.maxSize 24000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Merino
open Function Filter Topology NormedSpace Lattice Wilson Fock Pastry Scree Sault Sour Stax Skye Jet NormedSpace Scroll Finset Palot Cadre Vow
open RG Mew Rive Nor Hake MeasureTheory Bake Rue Salt
open Metric Drapes Tulip Lat Branch Cube Tenant
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Classical
attribute [local instance] opCStarAlgebra
open Rush SU Prism Nacre Laic Tap Levier Thera Moto Oath Font Haro Spire Swell

variable {n:Side}
local notation "I"=> Single n
open Window Buffered StressExchange Dial


private lemma cleanTag (n:Side): ∃ t:Ids n,Injective (priorP t):=by
 letI:Encodable (Seat n):=Fintype.toEncodable (Seat n)
 refine ⟨fun i=>((Encodable.encode i:ℝ),1,1),?_⟩
 exact Nat.cast_injective.comp Encodable.encode_injective

lemma pass_move (p:BudgetPoint)(o:Seat n)(s:Sweep n)(V:Pane n):
    V∈pass p (boxA s o) ↔ flashA s V∈pass p o:=by
 have z:actY s {(boxA s) o}={o}:=by simp [actY]
 change pingS p.threshold (purse p.B (boxA s o)) V↔pingS p.threshold (Lattice.halo p.B {o}) _
 nth_rw 1 [← z]
 rw [walkA,glowA]

lemma tick_move (s:Sweep n):
    ech s (tickA n)=swapX (detX s.s) (tickA n):=by
 rw [touchP]
 exact tickR (castX s) (xtra s.charge) (spinU s.charge s.s) (spinZ s.charge s.s) n

variable {K:Scree.Loom n}{o:Seat n}{X:SOp n}{p:BudgetPoint}{a b d:ℝ}
/-- General short move. No assertion of mirror of **dg** without scalar
subtractions. `s` maps input posts at `o` to `(boxA s) o`. -/
lemma mask_move (s:Sweep n)(r:Skylit p d K)(ha:0≤a)(h:Trunk o X (p.B/10) a b d)
    (V:Pane n):
    ech s (masked K p (boxA s o) (julStep s X) V) =
     masked K p o X (flashA s V):=by
 by_cases v:V∈pass p (boxA s o)
 · obtain ⟨t,g⟩:=cleanTag n
   rw [mask_eq r ha (trunk_move h s) v t,mask_eq r ha h ((pass_move ..).mp v) (bun s t)]
   obtain ⟨_,_,_,R,_⟩:=r.box
   unfold ask
   rw [R.move _ _ _ g]
   exact julius s X (K (V,t))
 unfold masked
 rw [Set.indicator_of_notMem v,Set.indicator_of_notMem (mt (pass_move ..).mpr v)]
 unfold ech; rw [singT,show windX _ 0=0 from ?_,map_zero]
 simp [windX]

lemma tick_shift (t:Site n):twist (γS (taxiPlus t)) (tickA n)=tickA n:=by
 have p:=tick_move (taxiPlus t)
 change _=swapX (detX 1) _ at p
 rw [det_i] at p; exact p

lemma preJ_shift (t:Site n)(W:Op I):
    twist (quantU (γS (taxiPlus t))) (preJ (tickA n) W) =
      preJ (tickA n) (twist (γS (taxiPlus t)) W):=by
 unfold preJ; rw [map_add,twist_scalar,map_one,dg_cov,map_mul,map_mul,map_sub,
  map_one,tick_shift,show (tickA n)*twist (γS (taxiPlus t)) W =
  twist (γS (taxiPlus t)) ((tickA n)*W) from by rw [map_mul,tick_shift],trace_twist]

namespace Spool
/-- Translation operator, as diagnosed by pullback of the proposed placement,
including AP seam action. -/
def perches (F F':Evaluation n)(t:Site n):Prop:=
  ∀ V:Pane n,twist (quantU (γS (taxiPlus t))) (F' V)=F (flashA (taxiPlus t) V)

/-- The axis pieces in (128) really are poses of one physical insertion
per axis. This is not a law about independently chosen decorations. -/
lemma Hem.poses {y:Spool n}(h:Hem y K p a b d)(i:Axis)(x:Site n):
    perches (y.jPole K p i) (y.jShift K p i x) (x-y.origin):=by
 intro V
 unfold Spool.jPole Spool.jShift flowHead co_Ψ
 rw [Function.comp_apply,Function.comp_apply,preJ_shift]
 apply congrArg
 change ech (taxiPlus (x-y.origin)) _=_
 have m:=mask_move (taxiPlus (x-y.origin)) h.skylight h.sign (h.spurt i) V
 rw [show boxA (taxiPlus (x-y.origin)) y.post=node x from (by unfold post; rw [platforms,add_sub_cancel])] at m
 exact m

end Spool
end YM.CF.Merino

