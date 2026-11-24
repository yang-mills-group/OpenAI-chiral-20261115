import YM.CF.Milo.Ice
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Sour
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
open Jet Yaw Nor Prism Font Push.AbsoluteSums Wray
variable{n:Side} {P: BudgetPoint}{x y a b h c d:ℝ}{k m:ℕ}
open Cadre Larch Vow Ione Trees Ursell Push.AbsoluteSums.Graph Stax
lemma parse(W:Aura n→ℝ)(k:ℕ)(L w t:ℝ)(o:Seat n):tallB W k (L-w*t) o=nook (W*loom_v L w (widthK n k) t) o:=rfl
local notation "V_"=> Aura n
abbrev urnL(B:blazeK n)(i:Aura n):= B i ∅
lemma age_t(F:blazeK n)(o:Seat n)(κ:ℝ): tallB (roofL F κ) k a o=tallB (urnL F) k a o+κ*tallB (Vow.hymn F) k a o:=by
 have hh: roofL F κ = urnL F+κ • Vow.hymn F:=by
    funext X; unfold roofL; rw [←add_sum_erase _ _ (show ∅ ∈ _ from mem_powerset.mpr (empty_subset _))]; have ht:X.val.powerset.erase ∅= Vow.fullD X:=by ext i; simp only [mem_erase,mem_powerset,fullD,mem_filter,mem_univ,true_and]; rw [nonempty_iff_ne_empty]
    unfold Cadre.duty; simp only [ht,Finset.not_nonempty_empty, ↓reduceIte,one_mul]; change _= F X ∅+κ*(_); unfold Vow.hymn; rw [mul_sum]; congr 1; exact sum_congr rfl fun i v=> by rw [if_pos (mem_filter.mp v).2.1]
 rw [hh,tall_add,tall_s]
variable {C':blazeK n} {z u δ:ℝ}
lemma lam_H(F:blazeK n)(o:Seat n)(r:ℝ)(k:ℕ)(a:ℝ)(ht:0<r)(c:∀ X:Aura n,∀ D⊆ X.val,0 ≤ F X D)(w:tallB (roofL F r) k a o ≤ b): tallB (urnL F) k a o≤ b∧ tallB (Vow.hymn F) k a o≤ r⁻¹*b:=by
 rw [age_t] at w; constructor; · exact (le_add_of_nonneg_right (mul_nonneg ht.le (sum_nonneg (fun i _=> mul_nonneg (sum_nonneg (fun j p=> c _ _ (mem_filter.mp p).2.2)) (Real.exp_pos _).le)))).trans w
 rw [le_inv_mul_iff₀ ht]; exact (le_add_of_nonneg_left (sum_nonneg fun i _=>mul_nonneg (c _ _ (empty_subset _)) (Real.exp_pos ..|>.le))).trans w
lemma ready_T {A:Aura n→ℝ}(p:0 < z)(d:0<δ)(h:degreePrice P.B z δ < 1)(hv:0 ≤ A)(t:∀ o:Seat n,tallB A P.B (a+δ) o ≤ z): Ready Palot.stern P.B A a z δ (degreePrice P.B z δ):=by
 refine ⟨p,d,le_rfl,h,fun i=>hv i,fun i=>?_⟩; let F(j:Aura n):=if i∈j.val then A j * currency P.B (a+δ) j.val else 0; have hx(j):0 ≤ F j:=by unfold F; split; exact mul_nonneg (hv j) (Real.exp_pos _).le; exact le_rfl
 apply budget_of_sum hx; intro X; exact (sum_le_sum_of_subset_of_nonneg (subset_univ X) (fun j _ _=>hx j)).trans (by unfold F; rw [←Finset.sum_filter]; exact t i)
lemma dutyK {A:Aura n→ℝ}(p:Ready Palot.stern P.B A a z δ (degreePrice P.B z δ))(o:Seat n):tallB A P.B (a+δ) o ≤ z:=by
 have hx:=(p.2.2.2.2.2 o).2.2; rw [tsum_fintype] at hx; unfold tallB; rw [sum_filter]; exact hx
lemma frame_v{F:Cusp n}(h:∀ X:Aura n,∀ D⊆ X.val,Fray P x (cipherK k) X D (F X D) (C' X D)):ArmsK P F C' x:=by
 refine ⟨fun i D _ p=>(h i D p).merit,fun i D q p=>⟨?_,fun y k=> ((h _ _ p).loaf _ k).2⟩⟩; intro t; funext l; by_contra m; exact t ((Yaw.touchK D).trans ((Corona.halo_mono (show 12 ≤ cipherK k by unfold cipherK; omega) (Subset.refl _)).trans ((h _ _ p).loaf l m).1)) -- tune namespace
variable {κ:Type}[TopologicalSpace κ]
lemma fee_C(X:κ→ Pax n)(V:Orbit n)(i:Aura n)(p:∀ j,Continuous fun k':κ=> X k' j V)(t:1≤h)(s: Aura n→ℝ)(q:Ready Palot.stern P.B s a x y z)(w:∀ l j,Medal P j.val ∅ (X l j) h (s j))(u:0 ≤ a):Continuous fun k':κ=> FeeD P (X k') i V:=by
 by_cases v:visible P i.val ∅ V.1; swap; · have hv(k':κ): FeeD P (X k') i V=0:= if_neg v; simp_rw [hv]; exact continuous_const
 unfold FeeD; simp_rw [Vow.spiritD _ _ t (w _) q u v]; obtain ⟨l,m,Q⟩:= v
 refine continuous_tsum (fun k=> ?_) (Vow.glomM (m:=0) i q u) (fun i' y=>?_) -- tune
 · unfold sta; split; swap; exact continuous_const
   unfold guava; simp only [Pi.smul_apply,Finset.prod_apply]; exact (continuous_const (y:=( _:ℝ))).smul (continuous_finsetProd _ fun j _=>p _)
 -- eta
 rw [(ponder i i' t (w y) 0).same V (l,V.2) Q (fun _ _=>rfl)]; exact (ponder i i' t (w y) 0).capF t _ m
end YM.CF.Sour
