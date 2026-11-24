import YM.CF.BProof.Tape.Gift
import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-! Our supports can operate on actual admissible-domain data. Borel implements, also
for integrations over Loom arguments. Moment supports never have to test all derivatives
of tangent parameters (larger `Ride` domain doesn't impose that).
-/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Tape
open Function Filter Fock Finset Branch Stint Align Wick Hearth Spin Tenant Lat Lattice Tulip Cube Fig
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Matrix.Norms.L2Operator Classical Hearth
attribute [local instance] opCStarAlgebra
variable {j:ℕ}{a b l r δ c v η:ℝ}{N:Side}{P: Ready j a b l r}{F:Core j a b l r N}(h:Honor P F δ)
scoped instance : MeasurableSpace (C(Beam,Stamp)) := borel _
scoped instance : BorelSpace (C(Beam,Stamp)) := ⟨rfl⟩
scoped instance : PolishSpace (C(Beam,Stamp)) := by
 -- tune explicit
 constructor
scoped instance : PolishSpace Thread:=inferInstanceAs (PolishSpace (Key→C(Beam,Stamp)))
scoped instance : BorelSpace Thread:=inferInstanceAs (BorelSpace (Key→C(Beam,Stamp)))
scoped instance (s:Side) : PolishSpace (Throne s) := by
 have he : TopologicalSpace.IsCompletelyMetrizableSpace (Throne s):= TopologicalSpace.IsCompletelyMetrizableSpace.pi_countable (X:=fun _:Site (More s)=>Thread); apply @PolishSpace.mk (Throne s) _ (@TopologicalSpace.instSecondCountableTopologyForallOfCountable (Site (More s)) (fun _=>Thread) _ _ _) he
scoped instance (N:Side) (d:ℝ): PolishSpace (Counter (More N) d):= (Phase.cover_closed _ _).polishSpace -- loop from instance unifier? index More stuck
scoped instance (N:Side) : BorelSpace (Throne N) := @Pi.borelSpace (Site (More N)) (fun _=> Thread) _ _ _ _ _
scoped instance (N:Side)(d:ℝ) : PolishSpace (Skein N d) := by
 let T:= {x:Throne N| Beneath x d}; have he(i: Site (More N))(k:Key) (u:Time): Continuous (fun x:Throne N=> ‖roam x k u.val i‖):= by unfold roam; let f(x:Throne N):= x i k; have hg:Continuous f:= (show Continuous (fun x:Thread=> x k) from continuous_apply _).comp (continuous_apply i); exact ((Continuous.eval hg continuous_const)).norm -- tune
 refine IsClosed.polishSpace (s:=T) ?_; unfold T Beneath; simp_rw [Set.setOf_forall]; exact isClosed_iInter fun i=> isClosed_iInter fun k=> isClosed_iInter fun t=> isClosed_le (he i k t) continuous_const
-- sigma after Proof stage. use explicitly, including cases filtered in applications.
include h
lemma MarketC (e:0<c)(v:c≤1) : PolishSpace (InRoad F δ c):=by
 obtain ⟨p,W⟩:= Core.earnsθ P; let D:= Counter (More N) δ × Piles N; let K(i:D):= F.θ i.1.val 1; have hk:Continuous K:= (W F h.1.minN h.1.shelter).cont.comp continuous_fst
 let S(t:Bool)(x:D):= bandCut x.2 t; have hs(t): Continuous (S t):= continuous_of_discreteTopology (f:=fun i:Piles N=> bandCut i t)|>.comp continuous_snd
 let A:={x:D| BoardH F x.1.val x.2 c}; refine IsClosed.polishSpace (s:=A) ?_
 let L(t:Bool)(E:D→ Op (Single N)):= {x:D| c • S t x ≤ S t x*E x*S t x}
 have Hh:A=L true K ∩ L false (fun i=>1-K i):=by
    ext x; constructor; intro y; exact ⟨(show Board .. from (show BoardH F _ _ _ from y)).holes,(show Board .. from (show BoardH F _ _ _ from y)).dots⟩; rintro ⟨p,q⟩; exact (show BoardH F _ _ _ from ⟨h.1.healthy x.1,cutM_idp _,cutM_idp _,duo _,p,q,e,v⟩)
 have ht(t:Bool)(E:D→Op (Single N))(h:Continuous E):IsClosed (L t E):=isClosed_le ((hs t).const_smul c) (((hs t).mul h).mul (hs t)); rw [Hh]; exact (ht _ K hk).inter (ht false _ (continuous_const.sub hk))
end YM.CF.BProof.Tape
