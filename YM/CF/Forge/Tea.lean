import YM.CF.Forge.Word
set_option autoImplicit false
set_option maxHeartbeats 700000
noncomputable section
namespace YM.CF.Forge
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Classical Matrix.Norms.Frobenius
open AnalyticBridge.Annulus1AD Ac Esti
variable {G:Gauge}{c f:Side}{S:StepData c f}{r v l:ℕ}{w x β d:ℝ}{q:Chi}{T:Tube G S}
open Pressure.Tube Exterior Bloch Oriented Work.E03
lemma payBand (T : Tube G S) (R : ℕ) (V V' : Config G c) (i : Co c Gain) (j : Twin c) :
    (R<separation i.1 j.1.1 → T.N R V i j=0) ∧
    (AgreeNear id i.1 R V V' → T.N R V i j=T.N R V' i j) := by
  let L := S.patch.L.val
  have hl k (h : k*L ≤ R) : k≤R := le_trans (le_mul_of_one_le_right (Nat.zero_le _) S.patch.L.property) h
  let K := T.R.o
  change (R<_ → lane R L V K (i) (mesh j)=_) ∧ (_ → lane R L V K (i) (mesh j)=_)
  constructor
  · intro h; have hf (u : Cover) : Pressure.priced R L V K (i) (mesh j) u = 0 := by
      unfold Pressure.priced; split
      next hv =>
        have hx : stop (i).1 (route 0 u 1) = (mesh j).1 := by
          rw [hv.2]; simpa only [map_zero, add_zero] using Work.E03.stop_route (i).1 0 u
        have he : separation (i).1 (mesh j).1 ≤ R := by
          rw [← hx]; exact (sep_walk (fun x : Site c => x) sep_step ..).trans (hl _ hv.1)
        exact (h.not_ge he).elim
      next hv => rfl
    simp [Pressure.lane,hf]
  intro h; apply tsum_congr
  intro u; unfold Pressure.priced; split
  next ht => rw [rated,rated, travel_near id (fun y i => sep_step y i) _ _ (i).1 _ R (hl _ ht.1) h]
  next ht => rfl

section band
local notation "G"=>SU.group
variable {T:Tube G S}{r n:ℕ}{X:Support c}{U V:Monk G S}
variable (s:Signed)(h:Duo G S U V X)(hr:Ready T x)(hp:1000 ≤ radiusB x)(hz:shovel S.patch+10 ≤ radiusB x)
local notation "b"=>radiusB x
local notation "R"=>Stores.till x
local notation "U₀"=>U.sent x T q d l β
local notation "V₀"=>V.sent x T q d l β
local notation "Uc"=>pull s 0 U.V
local notation "Vc"=>pull s 0 V.V
local notation "Uf"=>pull s 0 U₀
local notation "Vf"=>pull s 0 V₀
lemma pers_b{P Q:Finset (Cell f)}{i:Site f}{A B:Config G f}(v:Clip)(x:ℝ)(L:ℕ)(h:∀ Z:Config SU.group f,∀ j:Cell f,x*Real.exp (separation i j.1/v.relaxation)< Pressure.toll Z j →separation i j.1 ≤ L)(p:∀ j:Cell f,separation i j.1 ≤ L → faceValue A j=faceValue B j∧ (j∈P↔j∈Q)):pers P v x A i ↔ pers Q v x B i:=by
 constructor
 · intro t j l; by_contra! he; obtain ⟨q,g⟩:=p j (h B j he); refine he.not_ge ?_; change SU.group.chord (faceValue B j) ≤_; rw [←q]; exact t j (g.mpr l)
 intro t j l; by_contra! he; obtain ⟨q,g⟩:=p j (h A j he); refine he.not_ge ?_; change SU.group.chord (faceValue A j) ≤_; rw [q]; exact t j (g.mp l)
lemma spanTake{P Q:Finset (Cell f)} {i:Twin f}{A B:Config G f} {v:Clip}{u:PathData G}{r₁ r:ℕ}(t:ℝ)(g: faceValue A i.1=faceValue B i.1)(p:i.1∈ P ↔ i.1∈Q)(h: pers P v t A i.1.1 ↔ pers Q v t B i.1.1)(b':plotted u v r₁ r A i=plotted u v r₁ r B i):taken P u v r₁ r t A i=taken Q u v r₁ r t B i:=by
 by_cases s:i.2=true
 · simp only [taken,s, ↓reduceIte,h,b']
 unfold taken; simp only [s,Bool.false_eq_true,↓reduceIte,b']; unfold thinned; simp only [s,Bool.false_eq_true,↓reduceIte,p, Pressure.toll,g]
 simp only [Pressure.shoot,g]
lemma paidZip{ι:Type}[Fintype ι]{V W: Config G c}(P: Config G c→ ι→Twin c→Pay G)(u v:ι→SU.group.Color)(p:ι→Site c)(i:Twin c)(R':ℕ)(H:∀(U V:Config G c)(z:ι)(j:Twin c),(R'<separation (p z) j.1.1→P U z j=0)∧(AgreeNear id (p z) R' U V→P U z j=P V z j))(hp:AgreeNear id i.1.1 (2*R') V W)(hf:∀ z,separation i.1.1 (p z)≤R' →u z=v z) : unzip (P V) u i=unzip (P W) v i:=by
 unfold unzip; refine sum_congr rfl fun z _=> ?_; by_cases g:separation i.1.1 (p z) ≤ R'
 · rw [hf z g,(H V W z i).2 (hp.shrink (by omega))]
 have hg:R'<separation (p z) i.1.1:=(separation_comm ..).symm ▸ lt_of_not_ge g
 rw [(H V W z i).1 hg,(H W V z i).1 hg,map_zero,_root_.zero_apply, _root_.zero_apply]
include s h hr hp
lemma cu_b(i:Site c)(p:Beat.shadows (o:=s.act i) X (r+13*radiusB x)): AgreeNear id i r Uc Vc:=coarse_turn (h.toBeat.scope (x:=x) (r:=r+1) (by omega) p).outer
lemma uf_b(i:Site c)(p:Beat.shadows (o:=s.act i) X (r+(l+64)*radiusB x)): AgreeNear S.ratio.parent i r Uf Vf:=by
 apply pulled_near; intro j t; exact h.toBeat.backF hr hp j (aroundBk X p (by simp_rw [Nat.add_mul]; omega))
lemma lo_b(i:Twin c)(p:Beat.shadows (o:=s.act i.1.1) X (16*radiusB x)):let Q:= traceZ (turnStore s U.key).flags; let Q':=traceZ (turnStore s V.key).flags; taken Q T.down T.low R S.patch.L.val (temp x) Uc i = taken Q' T.down T.low R S.patch.L.val (temp x) Vc i ∧ hallP Q T.low Uc i.1 (temp x)=hallP Q' T.low Vc i.1 (temp x)∧ T.Xn R Uc i=T.Xn R Vc i:=by
 intro Q Q'; let o:= i.1.1; have he:AgreeNear id o (3*b) Uc Vc:=cu_b s h hr hp o (by rw [show 3*b+13*b=16*b from by omega]; exact p)
 have hw(j:Cell c)(hx:separation o j.1 ≤ b): faceValue Uc j=faceValue Vc j ∧(j∈ Q ↔ j∈Q'):=by
    refine ⟨travel_near id sep_step _ _ j.1 _ 4 (le_of_eq rfl) (he.shrink (by simp only [id_eq]; omega)),?_⟩ -- tune sep
    simp only [Q,Q',traceZ,mem_filter,mem_univ,true_and,flag_turn]; rw [h.flags _ (h.toBeat.sees p (by rw [separation_signed]; unfold o at hx;  omega))]
 obtain ⟨hh,hT⟩:= hw i.1 (by simp [o]); have hg:T.Xn R Uc i=T.Xn R Vc i:=plotted_near id sep_step Uc Vc T.low T.down R S.patch.L.val i S.patch.L.property (he.shrink (by unfold o Stores.till; simp only [id_eq,separation_self]; omega)); refine ⟨spanTake _ hh hT (pers_b _ _ _ (fun Z j p=>Nat.le_trans (hr.mask Z _ _ p) (Nat.div_le_self ..)) hw) hg,?_⟩ -- fill pers
 · unfold hallP Pressure.toll; simp only [hT,hh,hg,and_self]
lemma hi_b(i:Twin f)(ht:spanO T x)(p:Beat.shadows (o:=s.act (S.ratio.parent i.1.1)) X ((l+68)*radiusB x)): let P:= (turnStore s U.key).costs; let Q:=(turnStore s V.key).costs; taken P T.up T.high R 1 (fiery G x S.patch.L) Uf i=taken Q T.up T.high R 1 (fiery G x S.patch.L) Vf i ∧ hallP P T.high Uf i.1 (fiery G x S.patch.L)=hallP Q T.high Vf i.1 (fiery G x S.patch.L)∧T.Xf R Uf i=T.Xf R Vf i:=by
 let o:=S.ratio.parent i.1.1; intro P Q; have he: AgreeNear S.ratio.parent o (4*b) Uf Vf:=uf_b s h hr hp o (by rw [show 4*b+(l+64)*b=(l+68)*b from by ring]; exact p)
 have hw(j:Cell f)(hx:separation i.1.1 j.1 ≤ b): faceValue Uf j=faceValue Vf j∧ (j∈P↔ j∈Q):=by
    have hg:= Work.E04.parent_separation S.ratio i.1.1 j.1
    refine ⟨travel_near S.ratio.parent (parent_step S) Uf Vf j.1 _ 4 (le_of_eq rfl) (he.shrink (by unfold o; omega)),?_⟩
    simp only [P,Q,costs_turn]
    exact h.cost (Face.send s 0 j) (fun z=> disjoint_left.mp z (show s.act (S.ratio.parent j.1) ∈ startPos S (Face.send s 0 j) from startPos_turn s j ▸ mem_image_of_mem _ (mem_image_of_mem _ (Work.E01.base_touched j))) (h.toBeat.sees p (by rw [separation_signed]; simp_rw [Nat.add_mul]; omega)))
 obtain ⟨hh,hT⟩:= hw i.1 (by simp); have hp' :R ≤ b:= Nat.div_le_self ..; have hg:T.Xf R Uf i=T.Xf R Vf i:=plotted_near S.ratio.parent (parent_step S) Uf Vf _ _ _ _ _ le_rfl (he.shrink (by change separation o o+_≤_; rw [separation_self]; omega))
 refine ⟨spanTake _ hh hT (pers_b _ _ _ (fun _ _ p=> ht _ (p.trans_le (SU.group.chord_le_two _))) hw) hg,?_ ⟩
 unfold hallP Pressure.toll; simp only [hT,hh,hg,and_self]
end band
end YM.CF.Forge
