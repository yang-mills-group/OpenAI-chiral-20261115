import YM.CF.BProof.Oasis.Halo
import YM.CF.Girt.Light
/-! Budget per root CoverNumber → support of true masks & coefficients. h-weighted
for ordinary/force. -/
set_option autoImplicit false
set_option synthInstance.maxSize 16000
noncomputable section
namespace YM.CF.BProof.Oasis
open Function Filter Fock Finset NormedSpace Garden Align Wick Double Pastry Crystal MeasureTheory Dew
open Lattice Tenant Lat Cube Tulip Scree Skye Spin Branch Stint Hearth Tape Palot RG Push.AbsoluteSums
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator Classical Hearth ENNReal
attribute [local instance] opCStarAlgebra
variable {N:Side}{D:GramM N}
structure Cargo(D:GramM N)(h v:ℝ) where
 vouchR: Stem N → ℝ
 vouchF: Force N→ℝ
 press (i:Stem N): PressB D.p i.2 ((if i.1 then D.slip else D.F) i.2) h (vouchR i)
 force (i:Force N): ForceB D.p i (D.K i) h (vouchF i)
 coastR (i:Seat N)(s:Bool): ∑ j:Hub N,(if i = j.val.1 then D.p.mass j.val.2 (vouchR (s,j)) else 0)≤v
 coastF (i:Seat N): ∑ j:Force N,(if i∈ j.val.1.val.2 then D.p.mass j.val.1.val.2 (vouchF j) else 0)≤v
lemma carrier {Q:Spire.Sweep N→Prop}{h v:ℝ}(f:IncX Q D.F D.p h v)(s:IncX Q D.slip D.p h v)(u:Dark Q D.K D.p h v): Nonempty (Cargo D h v):=by
 obtain ⟨g,i,j⟩:=f.weight; obtain ⟨k,w,l⟩:=s.weight; obtain ⟨a,b,c⟩:=u.weight; refine ⟨fun y=> if y.1 then k y.2 else g y.2,a,?_,b,fun i s=>?_,c⟩; · rintro ⟨(-|-),r⟩; simp only [Bool.false_eq_true,ite_false]; exact i _; simpa only [ite_true] using w r
 cases s; simp only [Bool.false_eq_true,ite_false]; exact j _; exact l _
lemma tariffE(p:BudgetPoint)(x:Seat N){h b:ℝ}(v:0≤h)(w:0≤b)(g: b≤h)(i:Finset (Dwell N)): b^i.card≤Scree.tariff p x h i:=by unfold Scree.tariff; exact (pow_le_pow_left₀ w g _).trans (le_mul_of_one_le_left (pow_nonneg v _) (one_le_pow₀ (le_add_of_nonneg_right (by positivity))))
namespace Cargo
variable {h v:ℝ}(q:Cargo D h v)(p:1≤ h)
def annual (i:Stem N): Finset (Dwell N)→ℝ:= (q.press i).worth.choose
def far (i:Force N): Finset (Dwell N)→ℝ:= (q.force i).costP.choose
lemma annual_pos (i j):0≤ q.annual i j:= (q.press i).worth.choose_spec.1 _
lemma fend(i j):0≤ q.far i j:= (q.force i).costP.choose_spec.1 _
lemma ann_sum (i): ∑ j:Finset (Dwell N), Scree.tariff D.p i.2.val.1 h j * q.annual i j≤q.vouchR i := (q.press i).worth.choose_spec.2.2
lemma f_sum (i): ∑ j:Finset (Dwell N), Scree.tariff D.p i.val.1.val.1 h j * q.far i j≤q.vouchF i:= (q.force i).costP.choose_spec.2.2
include p
lemma tote (o:Seat N)(i:Finset (Dwell N)): 0≤ Scree.tariff D.p o h i:=by have ht:=zero_le_one.trans p; unfold Scree.tariff; positivity
lemma vp (i:Stem N):0≤ q.vouchR i := (sum_nonneg fun j _=> mul_nonneg (tote p _ _) (q.annual_pos ..)).trans (q.ann_sum i) -- tote not q (depends D implicit)
lemma vF (i:Force N):0≤q.vouchF i:=(sum_nonneg fun j _=> mul_nonneg (tote p _ _) (q.fend ..)).trans (q.f_sum _)
omit p
lemma annualCost (r) (i:Finset (Dwell N))(x:Pane N) : ‖crumb (readR D r x).val i‖≤ q.annual r i:=by
 unfold readR numbE; by_cases b:pingS D.p.threshold r.2.val.2 x
 · rw [Set.indicator_of_mem b]; simpa only [annual,iteratedFDeriv_zero_apply,show increment x 0=x from by simp] using ((q.press r).worth.choose_spec.2.1 x b i).token 0 (by omega) 0 (fun j=> j.elim0)
 rw [Set.indicator_of_notMem b,show crumb (0:Cipher N).val i=0 from rfl,norm_zero]; exact q.annual_pos ..
lemma farCost(f)(i:Finset (Dwell N))(x:Orbit N): ‖crumb (Scree.clamp D.p f (D.K f) x).val i‖≤ q.far f i:=by
 unfold Scree.clamp; split; rename_i v; · simpa only [far,Prod.mk.eta,iteratedFDeriv_zero_apply,Girt.openG_zero,show increment x.1 0=x.1 from by simp] using ((q.force f).costP.choose_spec.2.1 x v i).token 0 (by omega) 0 (fun j=> j.elim0)
 rw [show crumb (0:Cipher N).val i=0 from rfl,norm_zero]; exact q.fend ..
include q
lemma fitted: Fitted D:= by
 constructor; · intro i x; unfold readR numbE; by_cases e:pingS D.p.threshold i.2.val.2 x; rw [Set.indicator_of_mem e]; exact (q.press _).fitted x; rw [Set.indicator_of_notMem e]; exact Flour.trivial
 intro i x; unfold Scree.clamp; split; exact (q.force _).fitted x; exact Flour.trivial
lemma dataR(x:Stem N){u t:Pane N}(e: Agrees (lot D.p x.2) u t): readR D x u=readR D x t:=by
 unfold readR numbE; have he:= Chaff.fenceW x.2.val.2 (agrees_mono e (coe_subset.mpr (seeQ _ _ Subset.rfl))) D.p.threshold; by_cases g:pingS D.p.threshold x.2.val.2 u; · rw [Set.indicator_of_mem g, Set.indicator_of_mem (he.mp g)]; exact (q.press x).term u t (agrees_mono e (coe_subset.mpr (seeT ..)))
 rw [Set.indicator_of_notMem g,Set.indicator_of_notMem (g ∘ he.mpr)] -- tune
lemma dataF(i:Force N){u t:Orbit N}(e:Agrees (lot D.p i.val.1) u.1 t.1)(g:Set.EqOn u.2 t.2 ↑(lot D.p i.val.1)) : Scree.clamp D.p i (D.K i) u=Scree.clamp D.p i (D.K i) t:=by
 unfold Scree.clamp; have ht:= Chaff.fenceW (i.val.1.val.2 \ i.val.2) (agrees_mono e (coe_subset.mpr (seeQ _ _ sdiff_subset))) D.p.threshold; by_cases k:boundF i D.p u.1; · rw [if_pos k,if_pos (ht.mp k)]; exact (q.force i).values u.1 t.1 u.2 t.2 (agrees_mono e (coe_subset.mpr (seeT ..))) (g.mono (coe_subset.mpr (seeT ..))) -- tune
 rw [if_neg k,if_neg (k ∘ ht.mpr)]
lemma measR(i:Stem N): Measurable (readR D i):= (Girt.flow _ _ _ (q.press i)).meas -- tune
lemma measF(i:Force N):Measurable (Scree.clamp D.p i (D.K i)) := (Girt.tokM _ _ _ (q.force i)).meas
lemma vanF(i: Force N)(u:Orbit N)(h:Disjoint i.val.2 (RG.flags D.p.threshold u.1)): Scree.clamp D.p i (D.K i) u=0:=by
 unfold Scree.clamp; split; rename_i v; · by_contra t; obtain ⟨x,v⟩:=i.property.1; exact disjoint_left.mp h v ((q.force i).protect u t v)
 rfl
end Cargo
end YM.CF.BProof.Oasis
