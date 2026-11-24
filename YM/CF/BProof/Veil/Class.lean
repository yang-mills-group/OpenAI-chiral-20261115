import YM.CF.BProof.Veil.Deli
/-! Off-Mark contributions vanish on support that sees neither a D bit
nor a flag. Do NOT rotate them by gauge averaging. -/
set_option autoImplicit false
set_option synthInstance.maxSize 16000
noncomputable section
namespace YM.CF.BProof.Veil
open Function Filter NormedSpace Finset MeasureTheory RecN
open Cube Lattice Tenant SU Lat Dial Tulip Fock Skye Spin Branch Hearth Tape Hero Stint Oasis Scree Palot Wick Crystal Garden
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Matrix.Norms.L2Operator Classical Hearth Tape Mark
attribute [local instance] opCStarAlgebra
variable {N:Side}{j:ℕ}{a b l r c δ v η o h:ℝ} {P:Spin.Ready j a b l r}{F:Core j a b l r N}{H: Honor P F δ}
local instance myFC {I:Type}[LinearOrder I][Fintype I]: MeasurableSpace (Op I):=borel _
local instance myFop {I:Type}[LinearOrder I][Fintype I]: BorelSpace (Op I):=⟨rfl⟩
variable {y:Pay}(M:Marks H y c v η)(D:GramM N)(q:Cargo D h o) (w:ℂ)
abbrev angle (x:Loft F δ c v η)(Y:Plant N)(S:Support N)(V:Orbit N)(Z:Fields N) := hotA D 1 (RateF D Z.1 V) V.1 (tokenJ S Z.2 w Y (coreB x))
lemma flag_def {S:Support (More N)}{i:Force N}(g:lot D.p i.val.1 ⊆ S)(u: Orbit N)(e:Disjoint S (RG.flags D.p.threshold u.1)):Disjoint i.val.2 (RG.flags D.p.threshold u.1):= e.mono_left (i.property.2.trans ((seeT ..).trans g)) -- compile direction
include q
lemma angleSpring(x:Loft F δ c v η)(Y:Plant N)(s:Support (More N))(S:Support N)(V:Orbit N)(i:Options N)(Z: Fields N)(p: Disjoint s (spot S))(f:Disjoint s (RG.flags D.p.threshold V.1))(g:(streets D.p i).val⊆s): angle D w x Y S V Z i= hotA D 1 0 V.1 0 i:=by
 rcases i with i|(i|i); · unfold angle hotA; simp only [Sum.elim_inl]; change tokenJ _ _ _ _ _ _=0; rw [tokenJ,if_neg (fun h=> Finset.disjoint_left.mp p (g (mem_singleton_self (node i.1))) ((spot_spec ..).2 h))] -- tune
 · unfold angle hotA; simp only [Sum.elim_inr]; rfl -- tune
 change RateF D Z.1 V i=0; unfold RateF; rw [q.vanF _ V (flag_def D g V f),show Pastry.crumb (0:Cipher N).val i.2.val=0 from rfl,mul_zero]
theorem busyQuiet (S:Support N)(x:Loft F δ c v η)(V:Orbit N)(Y:Plant N)(Z:Fields N)(i:Palot.Y (More N))(p:Disjoint i.val (spot S))(f:Disjoint i.val (RG.flags D.p.threshold V.1)): fBusy x M D Y V Z w S i=0:= by unfold fBusy; apply sub_eq_zero.mpr; exact Civic.gaugeRead (Oasis.plaza ..) (M.eye x) (M.eye x) (angle D w x Y S V Z) (hotA D 1 0 V.1 0) _ (fun _ _ _ _ _=>rfl) (fun v g=> angleSpring D q w x Y i.val S V v Z p f g)
omit q
lemma flEq (x x':Loft F δ c v η)(u u':Plant N)(i: OptionJ N)(Y Y': Pollen (Site N))(p p':Support N) (h:i.1∈p↔i.1∈p')(e:u.leaf i.1=u'.leaf i.1)(f:Y i.1=Y' i.1)(v:x.val.2.val (node i.1)=x'.val.2.val (node i.1)): tokenJ p Y w u (coreB x) i= tokenJ p' Y' w u' (coreB x') i:=by
 unfold tokenJ; rw [f,e]; by_cases d:i.1∈p;  · have he: coreB x = pair (roam x.val.2.val (false,false) 1):=rfl; rw [if_pos d, if_pos (h.mp d),he,show coreB x'=pair (roam x'.val.2.val (false,false) 1) from rfl]; rw [chef_eq i.1 (B:=roam x'.val.2.val (false,false) 1) (by unfold roam; rw [v]) i.2.property]; -- tune
 rw [if_neg d, if_neg (d ∘ h.mpr)]
include q in
lemma feeRProof(Z Z': Orbit N)(i:OptionF N)(b b':Pollen (Site (More N)))(p:Agrees (lot D.p i.1.val.1) Z.1 Z'.1)(k:Set.EqOn b b' ↑(lot D.p i.1.val.1))(g:Set.EqOn Z.2 Z'.2 ↑(lot D.p i.1.val.1)):
 RateF D b Z i= RateF D b' Z' i:=by -- include q
 unfold RateF; rw [q.dataF i.1 p g]; congr 1; unfold style; apply prod_congr rfl; intro j h; rw [k (seeT D.p _ (i.1.property.2 h))] -- tune
end YM.CF.BProof.Veil
