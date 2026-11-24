import GaugeFieldConstruction.Jury
import SatinThinShelter
set_option autoImplicit false
set_option maxHeartbeats 25000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Oath
open Nor
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open AnalyticBridge.Annulus1AD Ac Esti
open Atala Forge Cloak Rill Hive Fock Stilo Palot Scion
open Cube Lat Tenant Tulip
open Pastry Hake Levier Urn Peaks Fock Laic Branch Drapes
attribute [local instance] opCStarAlgebra
open Rush Scroll Paige Vault Phase Acorn Spire
attribute [local instance] opCStarAlgebra
open Tarn Cay Slate Esti Cour Hest Arena Reine Kennel Facet Broc Pec Push.SectorMeasure.Oriented
open Hom Vale Vale.Grace Next.Free Thera Nacre Dial Fock
open Tye Lich Stake Pail Pail.Dew
open Lich.Muster Lor
open Jet Vol Rel
open Cascade
open Fief
open Yaw Pig
open Lich.Muster Push.AbsoluteSums
open Iva Eire
open Wray Prism Font
open PhysicalNext.JointLoad PhysicalNext.JointLoad.Heir Siete
open Feu Feu.Corset Haro
open Jet Plume Eire.Dress
section
open Py Riant Lattice Prism Tap FlightFlux TableF Boom Axon Flot Taxi
open Lenten.ModuleB
open Trees Hake Vow Bake Rue Larch
open TableF Lenten.Bank Lenten
open Layout Fren
open TableF Lenten.Bank Lenten Lenten.Layout Fren
variable {N:Side}{P:BudgetPoint}{o:Seat N}{K H:Vow.Pax N}{h a v k b d:ℝ}{r l L n:ℕ} (Tp:Ids N)(M:Tulip.Male)
-- canonical.Core.Clock. root halo (actual supplied).
open Ione QuadClock Beau Salt
open scoped YM.CF.Mew
section
variable {E E':InkD N} (s:Sweep N) {J' W:Scree.Hub N}
abbrev Zvia (s:Sweep N)(A B:Zone N):Prop:= passingR N s A.1 B.1 ∧ passingU_n N s A.2.1 B.2.1 ∧ B.2.2=Spire.payZ s A.2.2
lemma Zvia.link {A B C D:Zone N}(p:Zvia s A B)(q:Zvia s C D):Zvia s (A+C) (B+D):= ⟨passingR.add s p.1 q.1,passingU_n.add s p.2.1 q.2.1, (congrArg₂ (·+·) p.2.2 q.2.2).trans (by simp [Spire.payZ,cSignX,ite_add_ite])⟩
lemma Zvia.none : Zvia s (0:Zone N) 0:= ⟨fun i x=>(map_zero (suit_Y s)).symm,fun i x h d e z=> (map_zero (suit_Y s)).symm, (show 0=Spire.payZ s 0 from (by unfold Spire.payZ; cases wageZ s <;> simp [cSignX]))⟩
lemma single_move (p:Turns s E E')(W:Scree.Hub N) : passingR N s (singleP W E) (singleP (moveHub s W) E'):=by
 intro i x; unfold singleP; by_cases h:i=W; · subst i; rw [Pi.single_eq_same,Pi.single_eq_same]; exact p.turns x
 have hu: moveHub s i≠ moveHub s W:= fun t=>h ((scope_q s).injective t) -- name
 rw [Pi.single_eq_of_ne h,Pi.single_eq_of_ne hu]; exact (map_zero _).symm
lemma locus_pass (p:Turns s E E')(W:Scree.Hub N):Zvia s (locusH W E) (locusH (moveHub s W) E') := ⟨single_move s p W,(Zvia.none s).2⟩
-- package includes W full. Zodiac.P
lemma via_sum {D G:Type*}{A:D→ Zone N}{A':G→Zone N}(U:Finset D)(V:Finset G)(i:D ≃ G)(v:∀ j,j∈U ↔ i j∈ V)(e:∀ j∈U,Zvia s (A j) (A' (i j))) : Zvia s (∑ j∈U, A j) (∑ j∈V,A' j):=by
 have hp:= sum_equiv i v (fun j _=>(rfl : A' (i j)=A' (i j))); rw [←hp]; clear hp v; induction U using Finset.induction_on with|empty => rw [sum_empty,sum_empty]; exact Zvia.none _| insert j u h ih=> rw [sum_insert h,sum_insert h]; exact Zvia.link _ (e j (mem_insert_self ..)) (ih fun i q=> e _ (mem_insert_of_mem q))
lemma load_Y (J:Scree.Hub N): lagE (moveHub s J)= moldA s (lagE J):=by rfl -- tune
lemma Ω_joint (J:Aura N)(D:Support (More N)): Disjoint (actY s D) (moldA s J).val ↔ Disjoint D J.val:=by
 change Disjoint (Finset.map _ _) (Finset.map _ _) ↔ _
 rw [Finset.disjoint_map] -- name
lemma flick_Δ (E F:InkD N)(p:Turns s E F)(x:Aura N)(V:Orbit N)(q:Support (More N)): Vow.flick (moldA s x) (oV F) (actY s q) (yellA s V)= suit_Y s (Vow.flick x (oV E) q V):=by
 unfold Vow.flick; by_cases h:Disjoint q x.val; · rw [if_pos h,if_pos ((Ω_joint s x q).mpr h)]; exact p.turns V.1
 rw [if_neg h,if_neg (mt ((Ω_joint s x q).mp) h)]; exact (map_zero _).symm
lemma Chasm_Δ (X:Aura N)(f g:Support (More N) → Copy N)(p:∀ V:Orbit N,∀ D,g (actY s D) (yellA s V)=suit_Y s (f D V)): passingU_n N s (chasmR X f) (chasmR (moldA s X) g):=by
 intro i y c D z h; unfold chasmR; by_cases e:i=X; · subst i; rw [Pi.single_eq_same,Pi.single_eq_same]; exact p y D
 rw [Pi.single_eq_of_ne e,Pi.single_eq_of_ne (fun q=> e ((moldA s).injective q))]; exact (map_zero _).symm
lemma Stroke_Δ (E F:InkD N)(p:Turns s E F)(x y z:Aura N): passingU_n N s (Vow.stroke x y z (oV E) (oV E)) (Vow.stroke (moldA s x) (moldA s y) (moldA s z) (oV F) (oV F)):= Chasm_Δ _ _ _ _ (fun V D=> (congrArg₂ (·-·) (flick_Δ s E F p x V D) (flick_Δ s E F p y V D)).trans (map_sub ..).symm) -- tune infer
lemma Prop_Δ (X Y:Scree.Hub N) (p:Turns s E E'):Zvia s (Propulse E X Y) (Propulse E' (moveHub s X) (moveHub s Y)):=by
 refine ⟨(Zvia.none s).1,?_,(Zvia.none s).2.2⟩; unfold Propulse; simp_rw [load_Y]; exact Stroke_Δ s _ _ p _ _ _
lemma ΔPal_zero (x:Signed)(b:Bool): (0:Pal)=ΔPal x b 0:= (map_zero (ℳPAL x b)).symm
private abbrev ClipQ {E F:Type}[NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup F][NormedSpace ℝ F](k:ℕ)(V: Ole E F):Ole E F:=(V.1,if 1≤k then V.2.1 else 0,if 2≤k then V.2.2 else 0)
lemma clip_b {E F:Type}[NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup F][NormedSpace ℝ F](k:ℕ)(V: Ole E F)(L:E→L[ℝ]E)(T:F→L[ℝ]F):ClipQ k (postF (pre V L) T)=postF (pre (ClipQ k V) L) T:=by
 unfold ClipQ; split_ifs <;> apply Prod.ext <;> first|rfl| apply Prod.ext <;> first|rfl|exact ContinuousLinearMap.ext (fun _=> Eq.symm (map_zero T))|exact Subtype.ext (ContinuousLinearMap.ext fun i=> ContinuousLinearMap.ext fun j=> (map_zero T).symm)
lemma mid_Q (V:Waves)(k:ℕ): chartF (MSlot k V)= ClipQ k (chartF V):=by
 unfold ClipQ MSlot; split_ifs <;> first|rfl| rfl -- tune
lemma lowMx (V:Waves)(k:ℕ)(p:¬1≤k)(x y:Gem): (bF4 (MSlot k V)).val x y=0:=by unfold MSlot; rw [if_neg p]; rfl
lemma hiMx(V:Waves)(k:ℕ)(p:¬2≤k)(x:Gem)(y:Sut): bF5 (MSlot k V) x y=0:=by unfold MSlot; rw [if_neg p]; rfl
-- high seam
lemma limb_zero (V:Waves)(k:ℕ)(p:¬2≤k)(x:Gem)(v:SU.group.Color) : (bm5 (MSlot k V)).val (TableF.hem x v)=0:=by unfold MSlot; rw [if_neg p]; rfl
lemma Slot_part (W T:Waves)(k:ℕ)(he:Thoughts s.s s.charge W T): Thoughts s.s s.charge (MSlot k W) (MSlot k T):=by
 constructor
 · intro i j; by_cases h:1 ≤ k; · unfold MSlot; simp only [if_pos h]; exact he.life i j -- rw both?
   rw [lowMx T k h,lowMx W k h]; exact (map_zero _).symm
 · intro i j; by_cases h:2 ≤ k; · unfold MSlot; simp only [if_pos h]; exact he.bond i j
   rw [hiMx T k h,hiMx W k h]; exact (map_zero _).symm
 · rw [mid_Q,mid_Q, he.part]; exact clip_b ..
 intro i j; by_cases h:2 ≤ k; · unfold MSlot; simp only [if_pos h]; exact he.limb i j
 rw [limb_zero T k h,limb_zero W k h]; exact ΔPal_zero ..
lemma Slot_sh (W: Waves)(k:ℕ):MSlot k (Mason s W)= Mason s (MSlot k W):= ThoughtU s.s s.charge (MSlot k W) _ _ (Slot_part _ _ _ k (sheen_v s.s s.charge W)) (sheen_v ..) -- tune
lemma CoinΔ (a:ℂ): Turns s (χGhost N a) (χGhost N (Spire.payZ s a)):=by
 constructor; intro x; change (Spire.payZ s a) • (1:Cipher N)=suit_Y s (a • (1:Cipher N)); rw [scar_y,map_one]
lemma χΔ (X:Scree.Hub N)(a:ℂ) : passingU_n N s (Ωχ X a) (Ωχ (moveHub s X) (Spire.payZ s a)):=by
 unfold Ωχ; rw [load_Y]; exact Chasm_Δ _ _ _ _ (fun V _=> (congrArg (-·) ((CoinΔ s a).turns V.1)).trans (map_neg ..).symm)
lemma ℓΔ (X:Scree.Hub N)(hv:Turns s E E')(p:PressB (KeyUp P) X E h a)(q:PressB (KeyUp P) (moveHub s X) E' h b)(f: Nonwrapping X.val.2 X.val.1)(u:0<h)(e:100<N.val)(r:ℕ) : Zvia s (ℓParcel r X P h M E) (ℓParcel r (moveHub s X) P h M E'):=by
 let Y:= moveHub s X; let K:= KeyUp P; let A:=Zhub X.val.1; let A':=Zhub Y.val.1
 let L:=SealT X E K h M; let T:=SealT Y E' K h M; let F:=splinter r X P h M E; let G:= splinter r Y P h M E';
 have hp:T=Mason s L:= (meter_sure (X:=Y) (M:=M) _ (fℓies s M E' p q hv u.le _ (meterL p u.le _) e f)).symm
 have ha:χE Y E'= Spire.payZ s (χE X E):=by
    have he:=hv.turns 1; rw [Facet.glacial] at he; exact (congrArg Pastry.pane he).trans ((HoldS s (E 1)).trans (castT ..))
 have hz:Turns s F G:=by
    change Turns s (shoulder _ K _ h (MSlot r L)) (shoulder _ K _ h (MSlot r T)); rw [hp,Slot_sh]; exact TsV ..
 have hb:A'=moveHub s A:= (move_Φ ..).symm
 refine ⟨?_,?_,ha⟩
 · change passingR N s (_+singleP A F) (_+singleP A' G); let t:=χE X E; rw [hb]; apply passingR.add s _ (single_move s hz A); apply single_move
   constructor; intro x; change E' _ - (χGhost _ (χE Y E') _ + G _)=suit_Y s (E x-(χGhost _ t x+ F x)); rw [ha,hv.turns,hz.turns,map_sub,map_add, show χGhost _ (Spire.payZ s _) (flashA s x)=_ from (CoinΔ s t).turns x] -- indentation tune
 change passingU_n N s (Vow.stroke _ (lagE A) _ _ _+Ωχ X _) (Vow.stroke (lagE Y) (lagE A') (lagE Y) _ _+Ωχ Y (χE Y E')); rw [hb]; rw [load_Y,load_Y,ha] -- duplicate tune
 exact passingU_n.add _ (Stroke_Δ _ _ _ hz _ _ _) (χΔ s X _)
end
end
end YM.CF.Oath
end
