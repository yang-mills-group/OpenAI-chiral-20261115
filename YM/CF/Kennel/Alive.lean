import YM.CF.Kennel.Fire
import YM.Extra.ITERATION_NO_LOSS.Transport
set_option autoImplicit false
noncomputable section
namespace YM.CF.Kennel
open Function Filter Metric Lattice Wilson Laurent Precision Tree Finset Exterior Extra Bloch Lat Rush Cube Scroll SU Peaks Dial Fock Thera Nacre Branch Drapes Tulip Paige Spire Vault Font
section
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Matrix.Norms.Frobenius
lemma army_repr {n}:Stationary.Army (G:=SU.group) (represent (G:=group) (n:=n)) 0:=fun i=>(Work.F03.represent_smooth ..).contDiffAt
end
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {m A B L:Side}{j:ℕ}{ho:Odd L.val}{d a b:ℝ}{n:ℕ}
variable {N X:Side}{T:RG.StepData (More N) (More X)}{F:Forest T.ratio}{z:Cloud N→AxisChart SU.group F}
namespace Nativity
variable (H: Nativity F z)
include H
lemma icicle:Iteration.chartOf F z 0=0:=by obtain ⟨_,_,_,_,_,_,_,p,_⟩:=H.was; unfold Iteration.chartOf; rw [p.1]; exact congrArg Prod.snd (Work.F03.inclusion_zero (G:=group) F)
lemma kala: ContDiffAt ℝ ω (Iteration.chartOf F z) 0:=by obtain ⟨_,_,_,_,_,_,_,p,_⟩:=H.was; exact Iteration.chart_jet z p.2.1 p.1
lemma foldM:baby F z =ᶠ[𝓝 0] represent ∘ Iteration.chartOf F z :=by
 obtain ⟨_,_,_,_,_,_,_,p,_⟩:=H.was; have ht:= (Iteration.graph_jet z p.2.1).continuousAt.tendsto; rw [p.1, show ((0:Cloud N),(0: AxisChart group F))=0 from rfl] at ht
 filter_upwards [ht.eventually (Work.F03.inclusion_works (G:=group) F)] with x hx; unfold baby natJoint Stationary.encamp; rw [bornL, (Stationary.arm ..).apply_symm_apply]; exact hx.symm
lemma melod(x:ℝ):0<x→∀ (G:Ratio N X),∀ᶠ a in 𝓝 0, JointB G (ears F z a) x:=by
 intro p G; have ht : Stationary.Army (G:=group) (represent (G:=group) (n:=More N)) 0:= army_repr
 have he : ContinuousAt (ears F z) 0:= H.army.cont.fst.prodMk ht.cont
 have hh: ears F z 0= (1:Nom N X):=Prod.ext H.flat link_one
 exact (show Tendsto (ears F z) _ (𝓝 (1:Nom N X)) from hh ▸ he.tendsto).eventually (near_j G x p)
lemma tarnish : ContDiffAt ℝ ω (unionP ∘ ears F z) 0:= tundra _ _ H.army.1 army_repr

end Nativity
abbrev Dress (N:Side):= Bkg (More N)→ Op (Single N)
def relic(f:Dress N):Prop:=f 1=0 ∧ ContDiffAt ℝ ω (f ∘ (represent (G:=group))) 0
lemma relic_any {f:Dress N}(g:cFoot j (f ∘ (represent (G:=group))))(p:0<j)(h:ContDiffAt ℝ ω (f ∘ (represent (G:=group))) 0):relic f:=by
 refine ⟨norm_le_zero_iff.mp ?_,h⟩ -- check lemma
 have hm:‖iteratedFDeriv ℝ 0 (f∘ (represent (G:=group))) 0‖≤0:=by rw [g 0 p]; simp
 rw [norm_iteratedFDeriv_zero, Function.comp_apply,link_one] at hm; exact hm
lemma relic_zero : relic (0:Dress N) :=⟨rfl,contDiffAt_const⟩
lemma relic_up {f g:Dress N}(h:relic f)(p:relic g):relic (f+g):=⟨by rw [Pi.add_apply,h.1,p.1]; simp,h.2.add p.2⟩
lemma relic_r(j:ℕ)(g:0<j)(P:Toy j N): relic (cavil P)∧ relic (sumU (cavil P))∧∀ i, relic (foil i (cavil P)):=by
 let W:=represent (G:=group) (n:=More N); have ht(i):ContDiffAt ℝ ω (fun p:Cloud N=> group.mat (W p i)) 0:=(repr_m i).contDiffAt
 have he:= cantor (0:Cloud N) P W ht; have hx:= toneP P W 0 ht; have hp:relic (cavil P):= relic_any (asideF (he.of_le (m:=(j:WithTop ℕ∞)) le_top) _ (fun i=> peak_e i P)).1 g he
 refine ⟨hp,relic_any (asideF (hx.of_le (m:=(j:WithTop ℕ∞)) le_top) _ (fun x=> priced x P)).1 g hx,fun i=>?_⟩
 constructor
 · unfold foil; have hv:Yg (incX i⁻¹) (1:Bkg (More N))=1:=by rw [Ywin]; exact congrArg Prod.fst (Stationary.twistUniform_one (G:=SU.group) (f:=More N) (c:=More N) i⁻¹)
   rw [hv,hp.1,map_zero]
 let V(x:Cloud N):=Yg (incX i⁻¹) (W x); refine (ZoneH (n:=N) (incX i)).contDiff.contDiffAt.comp (0:Cloud N) (cantor _ _ _ ?_); intro e; change ContDiffAt ℝ ω (fun x=> group.mat (V x e)) 0; apply wind_q V; simp only [V,Ywin]; exact (Stationary.stationed_twist (G:=group) (f:=More N) (c:=More N) (U:=fun x:Cloud N=> (W x,1)) i⁻¹ (x:=0) ⟨army_repr,Stationary.Army.park _ _⟩).1
lemma combine(H:Nativity F z){f:Dress X}(p:relic f): ContDiffAt ℝ ω (f∘ baby F z) 0:=by
 have he:ContDiffAt ℝ ω (f∘ (represent (G:=group))) (Iteration.chartOf F z 0):=by rw [H.icicle]; exact p.2
 exact (he.comp _ H.kala).congr_of_eventuallyEq (H.foldM.mono fun x h=> congrArg f h)
end YM.CF.Kennel
