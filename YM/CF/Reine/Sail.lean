import YM.CF.Girt.Tree
import YM.CF.Cay.Pric
import YM.CF.Arena.Yale
import YM.Push.ABSOLUTE_SUMS.Path
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 700000
noncomputable section
namespace YM.CF.Reine
open Siete
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG PhysicalNext.JointLoad Heir Next.Foundations AnalyticBridge.SectorAffine AnalyticBridge.SectorAffine.Offset Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree Esti Cay Slate Forge Bloch Exterior
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Classical Matrix.Norms.Frobenius
open AnalyticBridge.Annulus1AD
open Ac
variable {c f:Side}(S:StepData c f){r v:ℕ}
open CF.Jet
local notation "G"=> SU.group
variable {S}{n:ℕ}{θ a b m x t w K C d:ℝ}
variable {K': Teller G}{A B:Stores S}{T:Tube G S}{V:Config G c}{U:Config G f}{k:S.Choices}{q:Chi}{E:Type}[NormedAddCommGroup E][NormedSpace ℝ E][Nonempty E]{x':E}
open AnalyticBridge.Annulus1AD Push.SectorMeasure.Oriented Pressure.Tube
variable {s:Signed}
-- permission for physical mask at real V.S. actual input from payment.
def BoltP (A:Stores S)(O:Config G f)(V:Config G c)(x:ℝ):Prop:= (∀ s:Signed,∀ i∈RG.flags (fiery G x S.patch.L) (pull s 0 O), S.ratio.parent i∈(turnStore s A).place) ∧∀ s:Signed, RG.flags (temp x) (pull s 0 V)⊆ (turnStore s A).place
lemma bolt(V:Config G c)(U:Config G f)(p: total A x q U univ ≠0)(ht:A.flags=RG.flags (temp x) V)(he:0<fiery G x S.patch.L):BoltP A U V x:=by
 let t:=fiery G x S.patch.L
 refine ⟨fun s i h=> ?_,fun s i h=> Finset.mem_union_right _ ((flag_turn ..).2 (ht.symm ▸ (exact_turn ..).1 h))⟩
 obtain ⟨j,h,H⟩:= (RG.flags_spec ..).mp h; let k:= Face.send s 0 j; have hv:k∈nearFace S univ:= mem_filter.mpr ⟨mem_univ _,fun u=> Finset.disjoint_left.mp u (mem_image_of_mem _ (Work.E01.base_touched k)) (mem_univ _)⟩
 have hp:tokenF A q x U k≠0:=fun h=>p (Finset.prod_eq_zero hv h)
 have hk:j∈ (turnStore s A).costs:=by
    apply (costs_turn ..).2; by_contra g; have hh : Pressure.toll U k <2*(t/4):=(profile_charged _ _ _ (by change 0<t/4; positivity) _ hp (SU.group.chord_nonneg _)).2 g
    have hx:Pressure.toll (pull s 0 U) j=Pressure.toll U k:=Face.send_price U j s 0 SU.group.chord SU.group.chord_inv fun u w=>SU.group.chord_conj w u
    change t < Pressure.toll _ j at H; rw [hx] at H; change 0<t at he; linarith
 exact (planted_owns ..).mpr ⟨Sum.inl (Sum.inl j),hk, mem_image_of_mem _ h⟩
abbrev spanC (T:Tube G S)(x:ℝ):Prop:=∀ i:ℕ,temp x*Real.exp (i/T.low.relaxation)<2→ i≤ radiusB x
lemma capable (K:Teller G)(P:Patch): ∀ᶠ x:ℝ in atTop,∀ {c f:Side}(S:StepData c f)(T:Tube G S), S.patch=P→K.Funds S T→spanO T x ∧ spanC T x:=by
 filter_upwards [Work.E04.eventually_room 0 K.below.clip.relaxation K.below.clip.radius_pos, order_r K P] with x h hp c f S T p v
 refine ⟨hp _ _ p.symm v,fun i t=>?_⟩; rw [v.low] at t; have ht:= h.2 i (by simpa using t); omega -- tune
lemma afar_s (S:Support c)(y z:Site c)(h:y∉halo r S)(p: v+separation z y ≤ r): z∉halo v S:=by intro g; obtain ⟨w,hx,hv⟩:=halo_spec.mp g; exact h (halo_spec.mpr ⟨w,hx,(separation_triangle w z y).trans ((Nat.add_le_add_right hv _).trans p)⟩)
lemma reign {S:Support c}(h:flags t V ⊆ S)(i:Cell c)(p:i.1∉S): Pressure.toll V i ≤ t:=le_of_not_gt fun l=>p (h ((flags_spec ..).mpr ⟨i,Work.E01.base_touched _,l⟩))
lemma supplies_n (k:Clip)(s:ℝ)(i:ℕ)(h:0 ≤ s)(p:∀ j:ℕ,s*Real.exp ((j:ℝ)/k.relaxation)<2→j ≤ i)(x:Site c)(V:Config G c)(t:∀ a∈ RG.flags s V,i<separation x a) : pers ∅ k s V x ↔ PathData.kept k s x V:=by
 apply persR _ _ _ _ _ h; intro j hV
 have ht:= k.radius_pos; have hx:(k.relaxation>0):=ht; have hs := t j.1 ((flags_spec ..).mpr ⟨j,Work.E01.base_touched _,(le_mul_of_one_le_right h (Real.one_le_exp (by positivity))).trans_lt hV⟩); exact (hs.not_ge (p _ (hV.trans_le (SU.group.chord_le_two _)))).elim
end YM.CF.Reine
