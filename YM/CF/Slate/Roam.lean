import YM.CF.Slate.Dill
set_option autoImplicit false
set_option maxHeartbeats 700000
noncomputable section
namespace YM.CF.Slate
open Forge Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Push.Uniform (curve Slope tint partSpace meetVar)
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Classical Matrix.Norms.Frobenius
open AnalyticBridge.Annulus1AD AnalyticBridge.SectorAffine Oriented Esti Vol Bloch Exterior Jet
variable {G:Gauge}{c f:Side}{S:StepData c f}{r v l n:ℕ}{w x β d:ℝ}{q:Chi}{T:Tube G S}{F:Forest S.ratio}{E A:Type}[NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup A][NormedSpace ℝ A]
local notation "G"=>SU.group
variable {K:Teller SU.group}{U V:Monk G S} {T:Tube G S}{X:Support c}(h:Beat U V X)(hr:Ready T x)(hp:1000 ≤ radiusB x)
local notation "b_"=>radiusB x
local notation "A_"=>U.sent x T q d l β
local notation "Z_"=>V.sent x T q d l β
include h hr hp
lemma sightW (j:Bond c)(p:Beat.shadows (o:=j.1) X ((l+65)*b_)): S.prediction A_ U.k j=S.prediction Z_ V.k j:=by
 have hε:=hr.inputs; have ht: predReach S.patch ≤ b_:=by unfold span at hε; omega
 have hz(i':Bond c):= Work.E01.sep_step_le i'.1 i'.2
 have he:Agrees (Set.univ:Set (Site f)) A_ A_:=fun _ _ _=>rfl
 rw [prediction_near_eq hr.rules _ Z_ U.k j (fun i v=> h.backF hr hp i (aroundBk X p (by simp_rw [Nat.add_mul]; omega)))]; unfold StepData.prediction StepData.connector StepData.frames
 have hδ: pinPos j ⊆ X:= insert_subset (h.sees p (by simp)) (singleton_subset_iff.mpr (h.sees p ((hz j).trans (by simp_rw [Nat.add_mul]; omega))))
 rw [h.fr _ (hδ (mem_insert_self ..)),h.fr _ (hδ (mem_insert_of_mem (mem_singleton_self _))),h.fe _ hδ]
lemma glance(q':Signed)(i:Dill S)(p:Beat.shadows (o:=orientZ S q' i) X ((l+74)*b_)): Yaught T (Stores.till x) (fiery G x S.patch.L) (temp x) (pull q' 0 U.V) (pull q' 0 A_) (choice q' U.k) i= Yaught T (Stores.till x) (fiery G x S.patch.L) (temp x) (pull q' 0 V.V) (pull q' 0 Z_) (choice q' V.k) i:=by
 let R:=Stores.till x; have hk:R ≤ b_:= Nat.div_le_self ..; change Beat.shadows (o:=q'.act (leadD S i)) X _ at p
 apply ringT; swap
 · apply pulled_near; intro e u; exact h.backF hr hp e (aroundBk X p (by simp_rw [Nat.add_mul]; omega)) -- tune R ds
 · apply coarse_turn; exact (h.scope (x:=x) (r:=4*R+8+1) (by simp_rw [Nat.add_mul]; omega) p).outer
 rw [(carry q' hr.rules U.k A_).2,(carry q' hr.rules V.k Z_).2]; apply coarse_turn -- height r+1
 intro e v; exact sightW h hr hp e (aroundBk X p (by change separation _ e.1≤4*R+8+1 at v; simp_rw [Nat.add_mul]; omega))
lemma doll {a:Prices SU.group (U.zoo x)}{c':Prices SU.group (V.zoo x)}(i: Slots S)(p:∀ z:SU.group.ColorIndex,Beat.shadows (o:=down S (i,z)) X ((l+65)*b_))(H:∀ j j',PatchReads.lift (x:=x) (A:=U.key) (F:=U.park) j=PatchReads.lift (x:=x) (A:=V.key) (F:=V.park) j' → Beat.shadows (o:=front U.key U.park j) X ((l+62)*b_)→ a j=c' j'):
 wheel U.key U.park T x U.k q d (U.bush x) a U.V i=wheel V.key V.park T x V.k q d (V.bush x) c' V.V i:=by ext z; refine rimP (q:=q) (d:=d) h hr hp (i,z) (aroundBk X (p z) (by simp_rw [Nat.add_mul,separation_self]; omega)) fun j j' k l=> H _ _ k (aroundBk X (p z) (by simp_rw [Nat.add_mul]; omega))
omit h hr hp in
lemma gloss_p(s: Signed)(i: Dill S) (p:Beat.shadows (o:=orientZ S s i) X ((l+74)*radiusB x))(A B: Slots S→ℝ)(he:∀ j:Slots S,(∀ z:SU.group.ColorIndex,Beat.shadows (o:=down S («G»:=SU.group) (j,z)) X ((l+65)*radiusB x))→ A j=B j): Gloss S s A i=Gloss S s B i:=by
 rcases i with i|i|i; unfold Gloss; simp only [Sum.elim_inl]; refine sum_congr rfl fun j _=> he (s,.inl (i,j)) (fun z =>aroundBk X p (by change separation _ (orientZ S s (.inl i))+_≤_; simp_rw [separation_self,Nat.add_mul]; omega)); refine he (s,.inr i) (fun z=> aroundBk X p (by change separation _ (orientZ S s (.inr (.inl i)))+_≤_; simp_rw [separation_self,Nat.add_mul]; omega)); rfl
lemma vary (s: Signed)(i: Dill S)(p:Beat.shadows (o:=orientZ S s i) X ((l+74)*b_)): Slate.payer T x U q d l β s i=Slate.payer T x V q d l β s i:=by
 let G₁(i:Dill S)(M: Monk G S):=Yaught T (Stores.till x) (fiery SU.group x S.patch.L) (temp x) (pull s 0 M.V) (pull s 0 (M.sent x T q d l β)) (choice s M.k) i
 let M(A:Monk G S)(i:Slots S)(w:Prices SU.group (A.zoo x)):= media i (wheel A.key A.park T x A.k q d (A.bush x) w A.V); let Φ(A: Monk G S)(i: Slots S):= M A i (A.fuel x T q d l β)- M A i (liftN T x A.V A.k A.key A.park q d (A.bush x) l)
 have he(j:Slots S)(v:∀ z:SU.group.ColorIndex,Beat.shadows (o:=down S (j,z)) X ((l+65)*b_)): Φ U j= Φ V j:= congrArg₂ (·-·) (congrArg (fun x:SU.group.Color=> ‖Rows.slip⁻¹ • x‖^2/2) (doll (q:=q) (d:=d) (a:=U.fuel x T q d l β) (c':=V.fuel x T q d l β) h hr hp j v (fun _ _ k u=> h.reaction (β:=β) (q:=q) (d:=d) hr hp k u))) (congrArg (fun x:SU.group.Color=> ‖Rows.slip⁻¹ • x‖^2/2) (doll (q:=q) (d:=d) (a:=liftN T x U.V U.k U.key U.park q d (U.bush x) l) (c':= liftN T x V.V V.k V.key V.park q d (V.bush x) l) h hr hp j v (fun i i' k u=> liftN_read hr (h.scope (r:=(l+41)*b_) (by simp_rw [Nat.add_mul]; omega) u) k ))) -- tune congr
 change G₁ i U - Gloss S s (Φ U) i=G₁ i V - Gloss S s (Φ V) i
 apply congrArg₂ (fun a b:ℝ=>a-b) (glance (T:=T) (l:=l) (q:=q) (d:=d) (β:=β) h hr hp s i p)
 exact gloss_p s i p _ _ he
end YM.CF.Slate
