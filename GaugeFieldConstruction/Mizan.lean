import GaugeFieldConstruction.Lustre
import GaugeFieldConstruction.Bough
import GaugeFieldConstruction.Kasol
import GaugeFieldConstruction.Bracer
import GaugeFieldConstruction.Savio
set_option autoImplicit false
set_option maxHeartbeats 400000
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
variable {N:Side}{P:BudgetPoint}{o:Seat N}{U:InkD N}{K H:Cusp N}{h t d a q:ℝ}{j m:ℕ}
-- scalar and support-move coupons. cost at ALL SEATS. Lens variables Sclock.S.G.Temp unused. Keep cutoff.
structure HasCopper (L:ℕ)(o:Seat N)(p:BudgetPoint)(h:ℝ)(K:Cusp N)(c:ℝ):Prop where
 width(i:Aura N) : K i≠0→ coverNumber p.B i.val ≤ L ∧ o∈i.val
 tally:∃ A:Aura N→ℝ, Larch.Anuk K A p h ∧(∀ i:Aura N,A i≠0→ o∈i.val) ∧ (∑ i:Aura N,Trees.currency p.B 3 i.val * A i)≤c
lemma HasCopper.shove (p₀:HasCopper j o P h K t)(v:t≤q):HasCopper j o P h K q:=by obtain ⟨W,C,a,g,t⟩:=p₀; exact ⟨W,C,a,g,t.trans v⟩
lemma HasCopper.till (p₀:HasCopper j o P h K t):∃ A:Aura N→ℝ,Larch.Anuk K A P h∧∀ i:Seat N,tallB A P.B 3 i ≤ t:=by
 obtain ⟨A,P',W,p⟩:=p₀.tally; refine ⟨A,P',fun i=>?_⟩; unfold tallB; apply le_trans _ p; simp_rw [mul_comm (A _)]; exact sum_le_sum_of_subset_of_nonneg (subset_univ ..) fun j _ _=>mul_nonneg (Real.exp_pos _).le (P'.1 j)
lemma HasCopper.add (p₀:HasCopper j o P h K t)(q:HasCopper j o P h H d): HasCopper j o P h (K+H) (t+d):=by
 obtain ⟨A,V,a₁,p⟩:=p₀.tally; obtain ⟨B,V',b₁,l⟩:=q.tally; refine ⟨fun i u=>?_,A+B,?_,?_,?_⟩
 · by_cases v:K i=0; · rw [Pi.add_apply,v,zero_add] at u; exact q.width _ u
   exact p₀.width _ v
 · exact ⟨add_nonneg V.1 V'.1,fun i D v h=>(V.2 i D v h).plus (V'.2 i D v h)⟩
 · intro i k; rw [Pi.add_apply] at k; by_cases v:A i=0; · rw [v,zero_add] at k; exact b₁ i k
   exact a₁ i v
 simp_rw [Pi.add_apply,mul_add,sum_add_distrib]; exact add_le_add p l
lemma HasCopper.zero : HasCopper j o P h 0 0:=by refine ⟨fun i p=>False.elim (p rfl),0, ⟨le_rfl,fun i D v h=> Medal.zeroT⟩,fun i p=>False.elim (p rfl),?_⟩; simp
lemma insertP (X:Aura N)(p:o∈X.val)(h₀:coverNumber P.B X.val≤j)(F:Support (More N)→ Copy N)(q:0≤a)(v:∀ D,D.Nonempty→D⊆ X.val→Medal P X.val D (F D) h a): HasCopper j o P h (chasmR X F) (Trees.currency P.B 3 X.val*a):=by
 refine ⟨fun i h=>?_, Pi.single X a, ⟨fun i=>?_,?_⟩,?_,?_⟩
 · by_cases g:i=X; · subst i; exact ⟨h₀,p⟩
   exact False.elim (h (by rw [chasmR,Pi.single_eq_of_ne g]))
 · rw [Pi.single_apply]; split; exact q; exact le_rfl
 · intro i D e u; by_cases p:i=X; · subst i; rw [chasmR,Pi.single_eq_same,Pi.single_eq_same]; exact v D e u
   rw [chasmR,Pi.single_eq_of_ne p,Pi.single_eq_of_ne p]; exact Medal.zeroT
 · intro i q; by_cases h:i=X; · exact h.symm ▸ p
   exact False.elim (q (by rw [Pi.single_eq_of_ne h]))
 simp [Pi.single_apply,mul_ite] -- tune
lemma strikeE {X:Scree.Hub N}{G H:InkD N}(p:PressB P X H h a)(q:PressB P X G h t)(v:0≤h): PressB P X (H-G) h (a+t):= Taxi.strike 0 _ (fun i=>Vale.rinse ..) v p q
lemma cut_further {X Y:Scree.Hub N}{F:InkD N}(p:PressB P X F h a)(t:X.val.2⊆ Y.val.2)(v:X.val.1=Y.val.1)(g:0≤h): PressB P Y F h a:= Taxi.farther_v 0 _ _ (fun i=> Vale.rinse ..) g Y (s:=p) t v
lemma transport_X (X Y:Scree.Hub N)(h₀:coverNumber P.B (Y.val.2) ≤j) (p:X.val.2⊆ Y.val.2)(e:Y.val.1=X.val.1) (v:PressB (KeyUp P) X U h t)(s:0 ≤ h)(hP:P.power=2): let x:=lagE X; let y:= lagE Y; let C:=chi_f P.order*t; PressB (KeyUp P) Y U h t ∧ HasCopper j X.val.1 P h (Vow.stroke x y y (oV U) (oV U)) (Trees.currency P.B 3 (lagE Y).val*(C+C)) ∧ HasCopper j X.val.1 P h (Vow.stroke y x y (oV U) (oV U)) (Trees.currency P.B 3 (lagE Y).val*(C+C)):=by
 intro x y c
 have ht:= cut_further (Y:=Y) v p e.symm s; have hv:= rimR (Hope.smallerP hP v s) s; have hp:=rimR (Hope.smallerP hP ht s) s; have hc:= hv.wage s; rw [←e]; refine ⟨ht,?_,?_⟩
 · apply insertP y Y.property h₀ _ (add_nonneg hc hc); intro D u h; rw [sub_eq_add_neg]; exact (flick_M x y p s hv D).plus ((flick_M y y (Subset.refl _) s hp D).negT)
 apply insertP y Y.property h₀ _ (add_nonneg hc hc); intro D u h; rw [sub_eq_add_neg]; exact (flick_M y y (Subset.refl _) s hp D).plus ((flick_M x y p s hv D).negT) -- tune
abbrev χGhost (N:Side)(γ:ℂ): InkD N:= fun _=> Pastry.hollow γ
abbrev Ωχ (X:Scree.Hub N)(γ:ℂ):= chasmR (lagE X) (fun _=> -(oV (χGhost N γ)))
lemma χCost (p:BudgetPoint)(h:ℝ)(γ:ℂ)(X:Scree.Hub N): PressB p X (χGhost N γ) h ‖γ‖:= by
 apply Moto.litho p X _ (L:=fun _=> γ) (p:= fun _ _ _=>rfl) (s:=fun i j=>rfl) (q:= measurable_const) (norm_nonneg _); exact fun _ _=>Prism.hail le_rfl
lemma ΦCost (s:0≤h)(X:Scree.Hub N)(p:coverNumber P.B X.val.2 ≤j)(γ:ℂ) : HasCopper j X.val.1 P h (Ωχ X γ) (Trees.currency P.B 3 X.val.2*(chi_f P.order*‖γ‖)):=by
 have hp:=rimR (χCost P h γ X) s; apply insertP (lagE X) X.property p _ (hp.wage s); intro D u h; obtain ⟨V,v,e,z⟩:= hp.pays;
 exact Medal.negT (show Medal P X.val.2 D (oV (χGhost N γ)) _ _ from ⟨hp.toThemeR,V,v,fun i k Y m=> e (1,i.2) (by simpa only [sdiff_empty] using ping_f P X.val.2) (empty_subset Y),z⟩)
lemma Φaccord (V:Orbit N)(G:FleetS P.threshold V.1)(X:Scree.Hub N)(γ:ℂ) : march P (lagE X) (oV (χGhost N γ)) V= Pastry.hollow γ + fuelV P (Ωχ X γ) V:=by
 unfold Ωχ; rw [shade_t,march_f V G]; let p:=Disjoint X.val.2 (flags P.threshold V.1); by_cases h:p; · rw [if_neg (show ¬ fuelH _ _ from fun i=> i h),if_pos (Disjoint.symm h),add_zero]; -- tune
 rw [if_neg (show ¬Disjoint (flags P.threshold V.1) (lagE X).val from fun i=> h i.symm),if_pos (show fuelH _ (lagE X) from h)]; exact (add_neg_cancel (Pastry.hollow γ:Cipher N)).symm
end
end YM.CF.Oath
end
