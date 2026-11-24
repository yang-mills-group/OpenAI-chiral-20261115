import YM.CF.BPress.Spin.World
import YM.CF.BPress.Mount.True
import YM.CF.BPress.Lilac.Reveal
/-!
 ## Scope of the design purchases. `before`. Prechoices at B-gate.
 Phase schedule arity:

 * the first spectral-speed/d allowance (`Before`, names `qH qX δ` etc.)
   is issued on the Teller and costs of Grace and a given LOWER bound on
   the Pearl parameter q_P (may require equality in using the grants; this
   q_P has no h-dependence).
 * will consider EVERY application of the real history at that smaller d
   and with matching W, not requiring future data to have been bought
   uniformly in that d.
 * `.between` can enlarge the seam by a step and formatting-independent
   additional margin. In particular it works with l_B already fixed.

 Prior to height buys this and next file (`Escape`) will provide all the
 strong projection/log prices and `Wspin` driving the height demand (Pine).

 No pre-arithmetic restrictions on how big B∼λ^l may be at these assertions.
 No use of real calendar/horizon comparisons in buying these data. Use
 Eventually grants for order as in the proof.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.BPress.Calendar
open Function NormedSpace Metric Finset MeasureTheory Filter Lattice RG Precision Pressure
open Cube Py Vale Vale.Grace Paige Scree Skye Tulip Fock Fixed Dial Spire
open Spin Spin.Paint Spin.Pledge Pf
open Net Hazel Chrono Sugar Lilac Grid Mount Recital Habitat Driver Meadow Meadow.Tent Meadow.Frame Meadow.Stamps
open scoped Matrix Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology ContDiff Classical YM.CF.BPress.Habitat YM.CF.BPress.Habitat.Plain YM.CF.BPress.Habitat.Driver
attribute [local instance] opCStarAlgebra
variable {m s B:Side} {K:Teller SU.group}{R:Patch}{L:ChartRatio SU.group}
  (V:Grace K R L) {d:ℝ} {U:Grasp V.U B d}{W:GivenX V U} {Mstar:Side} (J:Robes Mstar V W) (p:ℝ)
local notation "A_"=> First V
local notation "B_"=> Second V
structure Before where
 qH:ℝ
 qX:ℝ
 H:Pledge
 n₀:ℕ
 e:ℝ
 tone:Side
 tone':Side -- finer/thinner patch in N.
 ok: Poses tone qX (η qH)
 markP: Poses tone' (soil tone) (η qH)
 pre: 0<qX
 slack : qX < p/2
 alive:0<e
 ν : Worthy H (First V) (Second V) K.j e qH heat n₀
variable {p} in
lemma before(h:0<p): Nonempty (Before V p):=by
 obtain ⟨A,e,q,m,hu,U⟩:= purchase_heat (First V) (Second V) _ (warmJ V) _ solid.1; let r:=p/4; have hv:0<r:= by unfold r; positivity
 obtain ⟨s,g⟩:= moist hv U.q_pos; obtain ⟨t,f⟩:= moist (by unfold soil; positivity : 0<soil s) U.q_pos; refine ⟨⟨q,r,A,m,e,s,t,g,f,hv,?_,hu,U⟩⟩; unfold r; linarith
-- demands $d≤min(e,earth)$. Offer heights after robes.J$.
variable {V p}
namespace Before
variable (P:Before V p)
def dcap:=min P.e (earth P.tone)
lemma q_H :0< P.qH:= P.ν.q_pos
lemma d_pos:0<P.dcap:=lt_min P.alive (earth_p _)
variable {J}
def period(G:GapSize) : Side:= ⟨(G.select 1).D,(G.select 1).D_pos⟩ -- tune
-- Supply coalesced $center budgets$. 
structure Between (e:ℝ)(k:ℕ) extends GapSize where
 z:Rental
 brighten: toGapSize.blank= (2*R.L:Side) -- possible Lean R implicit not used? P pulls V?
 period_f: lease P.tone P.qH (period toGapSize).val
 book: Booked e k z P.tone P.qH P.qX
 R:ℝ -- r compression margin 
 δ:ℝ
 ε:ℝ
 n:ℕ
 care: Voucher P.ν (period toGapSize) Ringmark 3 R z.P n ε δ
 widthM : ℕ
 strength:ℝ
 wage:0< strength
 wide: widthM≤ z.M
 age : ℕ
 bias (j:Fin 5)(p:j≠0): Supply K.j P.H (period toGapSize) ε widthM age strength j
-- even marker powers chosen after.
lemma supply_all (j:ℕ) (u:1≤j)(p:Pledge)(D:Side){t:ℝ}(g:0<t) : ∃ (m n:ℕ)(r:ℝ),0<r∧∀ z:Fin 5,z≠0→ Supply j p D t m n r z :=by
 -- induct finitely over centers.
 have he(s:Finset (Fin 5)) : ∃ (m n:ℕ)(r:ℝ),0<r∧∀ z∈s,z≠0→ Supply j p D t m n r z:=by
    induction s using Finset.induction_on with
    | empty=>exact ⟨0,0,1,one_pos,by simp⟩
    | @insert x s a h=>
       obtain ⟨m,n,r,w,k⟩:=h; by_cases p0:x=0; · rw [p0]; refine ⟨m,n,r,w,fun i q z=> k i ?_ z⟩; simpa [z] using q
       obtain ⟨m',n',r',k'⟩:=Supply.supplyZ u p D g x p0; let v:=lt_min w k'.right; refine ⟨m+m',n+n',min r r',v,?_⟩; intro i w h'; rcases mem_insert.mp w with rfl|q; exact k'.mono (by omega) (by omega) (min_le_right ..) v; exact (k _ q h').mono (by omega) (by omega) (min_le_left ..) v
 obtain ⟨m,n,r,v,k⟩:=he univ; exact ⟨m,n,r,v,fun i=>k i (mem_univ i)⟩
lemma between (e h:ℕ)(d:ℝ)(v:d≤P.dcap):∃ x:P.Between d e,h ≤ x.collar:=by
 obtain ⟨G,L,k,t⟩:= boxing P.tone h P.q_H (2*R.L:Side)
 obtain ⟨r,y,s,q,c,K⟩:= Voucher.buy P.ν solid.2 deepC.2.2 (by norm_num: (1:ℝ)≤3) (period G); obtain ⟨a,b,p,w,T⟩:= supply_all _ P.ν.above P.H (period G) K.alive; obtain ⟨U,m,hM,hk,hU⟩:= leap P.tone y e a P.q_H; subst y; exact ⟨⟨G,U,L,t,⟨P.ok,hU,v.trans (min_le_right ..),hM,P.q_H⟩,r,q,c,s,K,a,p,w,hk,b,T⟩,k⟩
namespace Between
end Between
end Before
end YM.CF.BPress.Calendar
