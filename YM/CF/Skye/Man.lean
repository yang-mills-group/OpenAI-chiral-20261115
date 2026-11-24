import YM.CF.Skye.Can
set_option autoImplicit false
noncomputable section
namespace YM.CF.Skye
open Function Filter Metric Lattice Wilson Laurent Finset Cube SU Fock Lat Spire Scroll MeasureTheory Mesa
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker
variable {n:Side}{u d:ℝ}
open scoped Matrix.Norms.Frobenius in
private lemma cf_infer {f:E→ℝ}(p:Continuous f){a:ℝ}(h:f 1<a):∃ x:ℝ,0<x∧∀ y:E,Mesa.lambda y ≤ x → f y ≤ a:=by
 let V:= {y:E | a≤ f y}; have hp:IsCompact V:=(isClosed_le continuous_const p).isCompact
 have he(y):f y ≥ a → Mesa.lambda y>0:=by
    intro hz; by_contra! hk; have hv:Mesa.lambda y=0:=le_antisymm hk (group.chord_nonneg _); suffices y=1 from h.not_ge (this ▸ hz)
    apply group.mat_injective; rw [Gauge.mat_one]; rw [lambda,Gauge.chord,div_eq_zero_iff] at hv; exact sub_eq_zero.mp (norm_eq_zero.mp (hv.resolve_right (Real.sqrt_pos.mpr (by exact_mod_cast group.dimPos)).ne'))
 by_cases g:V.Nonempty; swap
 · exact ⟨1,one_pos,fun y _=>(lt_of_not_ge fun k=> g ⟨_,k⟩).le⟩
 obtain ⟨y,hy,hs⟩:=hp.exists_isMinOn g ((show Continuous Mesa.lambda from group.continuous_chord).continuousOn)
 refine ⟨Mesa.lambda y/2,half_pos (he y hy),fun z t=>?_⟩; by_contra! hv; exact (lt_of_le_of_lt t (half_lt_self (he y hy))).not_ge (hs (show z∈V from hv.le))
open scoped Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
lemma taxon(h:0<d):∃ u:ℝ,0<u∧∀ (n:Side)(x:Pane n), RG.flags u x=∅→ Guard x d:=by
 let v(y:E):=‖(firstF y).val-1‖; let w(y:E):=‖(matter y).val-1‖; obtain ⟨s,hS,p⟩:= cf_infer (f:=fun y=>max (v y) (w y)) ((Continuous.norm (fund_cont.sub continuous_const)).max (Continuous.norm (matter_cont.sub continuous_const))) (show max (v 1) (w 1)<d from (by unfold v w; simpa using h))
 refine ⟨s,hS,fun n x g=>?_⟩; have ht(z i j)(hz:i<j):lambda (travel x z (square i j))≤s:=by
    by_contra! r; let c: Face _ := (z,⟨(i,j),hz⟩); have he:z∈RG.flags s x := (RG.flags_spec ..).mpr ⟨c,by simp [c,RG.touched,visits,square],r⟩; rw [g] at he; exact Finset.notMem_empty _ he
 have hl(z i j)(hz:i≠j):lambda (travel x z (square i j))≤s:=by
    rcases lt_or_gt_of_ne hz with h|h; exact ht _ _ _ h
    rw [show travel x z (square i j)=(travel x z (square j i))⁻¹ from ?_,show lambda _⁻¹= _ from group.chord_inv _]; exact ht z j i h
    rw [show square i j=Lattice.reverse (square j i) from rfl]; nth_rw 1 [←square_stop z j i]; rw [travel_reverse]
 exact ⟨fun i j k t=>(le_max_left ..).trans (p _ (hl i j k t)),fun i j k t=>(le_max_right ..).trans (p _ (hl i j k t))⟩
abbrev reach (n:Side):= Edge (Seat n)
abbrev win(s:ℕ)(e:reach n): Finset (Seat n):=halo s (ends e)
structure Basic (n:Side)(P:Pane n→Pane n)(u d:ℝ)(S:ℕ):Prop where
 legal(V):RG.flags d (P V)=∅
 meas:Measurable P
 covers(V)(e:reach n): Disjoint (RG.flags u V) (win S e)→P V e= V e
 shore(V W)(e:reach n):Agrees (win S e) V W→P V e=P W e
private lemma spanningL(e:reach n):∃ i:Axis, i≠ e.2:=by have hp : Nontrivial Axis:=inferInstance; exact exists_ne _
lemma broad(Y:Pane n)(t:ℝ)(p:∀ i:Face (Per (More n)),lambda (faceValue Y i) ≤t): RG.flags t Y=∅:=Finset.eq_empty_iff_forall_notMem.mpr fun i k=>by obtain ⟨v,-,h⟩:= (RG.flags_spec ..).mp k; exact h.not_ge (p v)
lemma repairB{B m:Side} (P:Au m B→Au m B)(h:Prequel m B d u P): Basic (CSide m B) P u d (2*B.val):=by
 have he(e:reach (CSide m B)):∃ y:Index m,e.1∈ room m B y ∧ e.1+step e.2∈room m B y:=by obtain ⟨j,h⟩:=spanningL e; obtain ⟨a,g,p,-⟩:= Mesa.spanning (i:=e.2) (j:=j) (x:=e.1) h.symm; exact ⟨a,g,p⟩
 have hx(e:reach (CSide m B))(y:Index m)(p:e.1∈room m B y)(j)(q:separation j (address m B y)≤B.val):j∈win (2*B.val) e:=by
    have hk:=separation_triangle e.1 (address m B y) j; have hA:=room_span p; rw [separation_comm (address m B y) j] at hk; exact halo_spec.mpr ⟨e.1,by simp,hk.trans (by omega)⟩
 refine ⟨fun V=> broad _ _ (h.2.1 V),h.1,?_,?_⟩
 · intro V e k; obtain ⟨y,h1,h2⟩:= he e; apply (h.2.2 y).1 V _ e h1 h2; intro j hz t; by_contra! hi; apply Finset.disjoint_left.mp k _ (hx e y h1 j hz); exact (RG.flags_spec ..).mpr ⟨(j,t),by simp [RG.touched,visits,square],hi⟩ -- infer x
 intro V W e k; obtain ⟨y,p,v⟩:= he e; apply (h.2.2 y).2 V W _ e p v; exact agrees_mono k (fun j u=> hx e y p j (room_span u))
def mend(P:Pane n→Pane n)(s:Sweep n)(V:Pane n):= flashA s⁻¹ (P (flashA s V))
lemma mends (P:Pane n→Pane n)(s:Sweep n)(a:Sweep n)(V:Pane n): mend P (s⁻¹*a) (flashA s V)=flashA s (mend P a V):=by simp [mend,lights]
lemma mine{P:Pane n→Pane n}{r:ℕ}(h:Basic n P u d r)(s:Sweep n): Basic n (mend P s) u d r:=by
 have ht(e:reach n) :win r (lane s⁻¹ e)=(win r e).map (boxA s⁻¹).toEmbedding:=by unfold win; rw [laneX,paysT]
 refine ⟨fun V=>by rw [mend,flagsA,h.legal]; simp, (revM s⁻¹).measurable.comp (h.meas.comp (revM s).measurable), ?_,?_⟩
 · intro V e k; nth_rw 2 [←revB s V]; rw [mend,flash,flash,h.covers]; rw [ht,flagsA,sitU]; apply Finset.disjoint_left.mpr; intro i hi hv; simp at hi hv; exact Finset.disjoint_left.mp k hi hv
 intro V W e k; rw [mend,mend,flash,flash,h.shore]; apply flashD s; rw [ht,sitU]; simp [k]
end YM.CF.Skye
