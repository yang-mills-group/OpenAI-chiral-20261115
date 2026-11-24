import YM.CF.Peaks.Elysian
import YM.CF.Sedge.Lantern
/-! The literal Fock projection calculation applies on the compatible sheets; no zero-mode chart cuts. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Peaks
open Function Filter Lattice Laurent Bloch Next.Free Metric Lat Finset Branch Cube Tenant SU Rush Drapes Fir Tulip Fock
open scoped Topology Matrix MatrixOrder BigOperators Matrix.Norms.L2Operator Kronecker InnerProductSpace
attribute [local instance] opCStarAlgebra
variable {N P:Side}(G:Ratio N P)
private noncomputable abbrev altK(n:Type*) [d:DecidableEq n](l:LinearOrder n): LinearOrder n:={l with
 toDecidableEq := d
 compare_eq_compareOfLessAndEq :=by
   letI:LinearOrder n:=l; have hp:d=l.toDecidableEq:=Subsingleton.elim _ _; rw [hp]; exact l.compare_eq_compareOfLessAndEq}
noncomputable instance jetH:LinearOrder (Single N):=altK _ (LinearOrder.lift' (Fintype.equivFin _) (Fintype.equivFin _).injective)
noncomputable instance rushW:LinearOrder (Iota G):=altK _ (LinearOrder.lift' (Fintype.equivFin _) (Fintype.equivFin _).injective)

def patchQ : Single N ↪ Iota G:=⟨rideG G,injG _⟩
lemma land(i:Iota G):en G i ↔ i∈ lows (patchQ G):=by
  constructor
  · intro h; exact mem_map.mpr ⟨modest G i, mem_univ _, ride_mod G i h⟩
  intro h; obtain ⟨j,-,rfl⟩:= mem_map.mp h; exact en_ride ..
lemma edgeDesk (A:Op (Single N)): desk (patchQ G) A=endorse G A:=by
  let f:= patchQ G; ext i j; by_cases h:i∈lows f <;> by_cases p:j∈lows f
  · obtain ⟨k,-,rfl⟩:=mem_map.mp h; obtain ⟨w,-,rfl⟩:=mem_map.mp p; rw [desk_at]; simp [f,patchQ,endorse,extendK]
  · have hv:= desk_out f (star A) j i p; rw [←desk_sh] at hv
    have hb : star (desk f A i j)=0:= hv
    rw [show desk (patchQ G) A i j=0 from star_eq_zero.mp hb]; simp [endorse,extendK,show ¬ en G j from fun l=> p ((land ..).mp l)]
  all_goals rw [desk_out _ _ _ _ h]; simp [endorse,extendK,show ¬ en G i from fun l=>h ((land ..).mp l)]
lemma lighthouse:hood G=cutM (lows (patchQ G)):=by rw [hood,←edgeDesk, level]
open Classical in
def reefS(u:Bool):= univ.filter fun i:Iota G=> i∉lows (patchQ G)∧ lobe G u i i=1
open Classical in
lemma reefS_deck(u:Bool): Deck (patchQ G) (reefS G u):=⟨Finset.disjoint_left.mpr fun i a b=> (mem_filter.mp b).2.1 a⟩
lemma goldLobe(u:Bool):lobe G u*(1-hood G)=cutM (reefS G u):=by
  let P:=lobe G u; let V:=lows (patchQ G)
  have hy(i):P i i=1 ∨ P i i=0:=by
    have h:=Matrix.ext_iff.mpr (lobe_sq G u).isIdempotentElem.eq i i; change (P*P) i i=_ at h; nth_rw 1 [show P=Matrix.diagonal _ from lobe_diag ..] at h; rw [Matrix.diagonal_mul] at h
    by_cases e:P i i=0; exact Or.inr e
    exact Or.inl (mul_left_cancel₀ e (by rw [mul_one]; exact h))
  rw [lighthouse]; ext i j; nth_rw 1 [lobe_diag]; rw [Matrix.diagonal_mul]; by_cases g:i=j
  · subst j; by_cases p:i∈V <;> rcases hy i with q|q <;> simp only [P] at q <;> simp [cutM,show lows (patchQ G)=V from rfl,reefS, q,p] -- tune
  simp [cutM,g]
variable (j:ℕ)(L:Side)(ho:Odd L.val)(T:Script Male)(u:Bool)(M:Male)
lemma pierce (x:Coil N P):wh j L ho u M G x=addS (patchQ G) (reefS G u) (skewE j (upMale L ho M) u _ x.2):=by rw [addS, wh,edgeDesk,goldLobe]
lemma court {x:Coil N P}(h:Along j L ho T u M G x):Clad (foal j u M G x) (wh j L ho u M G x) (ticketT T u M G x) (ticketT T (!u) M G x) (pine j L ho T u M G x):=⟨h.lead,h.beam,h.bridge,h.lowC,h.baseC,h.leftC,h.rightC⟩
set_option maxHeartbeats 800000
structure Peer (x:Coil N P) : Prop where
 carry :∀ (p : Wave (Iota G))(q:Wave (Single N)), Sea (foal j u M G x) p →Sea (skewE j (upMale L ho M) u N x.2) q →
     Projects (patchQ G) (reefS G u) p q (wh j L ho u M G x) (foal j u M G x) (ticketT T u M G x) (ticketT T (!u) M G x) (pine j L ho T u M G x) (pine j L ho T (!u) M G x)
lemma reaches (x: Coil N P)(hp:IsStarProjection (skewE j (upMale L ho M) u N x.2))(he:∀ u,Along j L ho T u M G x) : Peer G j L ho T u M x:=by
  constructor; intro p q h g
  have hv:=court G j L ho T (!u) M (he (!u)); rw [foil_neg,wh_neg,Bool.not_not] at hv
  exact lantern _ _ (reefS_deck ..) hp (pierce ..) (court G j L ho T u M (he u)) hv p q h g
omit M G
lemma flagged (hj:Even j)(hx:1≤j)(g:Use j L T):∃ e:ℝ,0<e ∧ ∃ k:ℕ,∀ {N P:Side}(G:Ratio N P),G.count=L→ k≤N.val→ ∀ M U, JointB G U e→ Peer G j L ho T u M (unionP U):=by
  obtain ⟨a,l,v,H⟩:=joined j L ho hj hx T g; obtain ⟨r,h,w,R⟩:=funde_q j hx
  refine ⟨min a r,lt_min l h,max v w,fun {N P} G he hv M U hp=>?_⟩
  refine reaches G j L ho T u M _ ?_ (H G he ((le_max_left ..).trans hv) M _ ⟨hp.fg.shrink (min_le_left ..),hp.cg.shrink (min_le_left ..),fun x=>(hp.follow x).trans (min_le_left ..)⟩)
  have he:= R (upMale L ho M) N ((le_max_right ..).trans hv) U.2 (hp.cg.shrink (min_le_right ..)); cases u
  · exact he.one_sub
  exact he
end YM.CF.Peaks
