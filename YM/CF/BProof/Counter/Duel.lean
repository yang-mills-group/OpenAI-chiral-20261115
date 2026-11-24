import YM.CF.BProof.Counter.Heat
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Taxi.Denn
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
local notation "DN"=>tangD n
local notation "E'"=>SU.group
variable {X D' Y Z:Support (More n)}{U:Pane n}
open AnalyticBridge.VerifiedReset Next.Foundations Push.Local PhysicalNext.JointLoad Heir
open Vow Rue Ione Larch Beau Floral
namespace Cart
abbrev CubeP(n:Side):= Skye.Seat n × Skye.Seat n
variable (C:Cart n m)
abbrev stem (j:CubeP n):=joined j.1 j.2
abbrev kWh(C:Cart n m)(j:CubeP n)(a:ℝ):= C.w j.1 j.2*a
abbrev patch(a:ℝ)(i:CubeP n):InkD n:= W i.2 (C.kWh i a)-W i.1 (C.kWh i a)
def Sr(a:ℝ):RegBudget n:= sunY univ stem (C.patch a)
def Zr (a:ℝ):Cusp n:= ∑ i: CubeP n, stroke (pur (block i.2)) (pur (block i.1)) (pur (stem i)) (oV (W i.2 (C.kWh i a))) (oV (W i.1 (C.kWh i a)))
lemma patch_turn (s:Sweep n)(t:C.Turns s)(A:Cipher n →ₐ[ℝ] Cipher n)(i:CubeP n): C.patch a ((boxA s).symm i.1,(boxA s).symm i.2) (flashA s U)=A (C.patch a i U):=by
 unfold patch kWh; dsimp only [Pi.sub_apply]; rw [t,W_turn (C:=A),W_turn (C:=A),map_sub]
lemma Zr_turn (s:Sweep n)(t:C.Turns s)(V: Skye.Orbit n)(A:Cipher n→ₐ[ℝ] Cipher n) : Zeal s V A (C.Zr a):=by
 intro i D p y; unfold Zr; simp only [Finset.sum_apply,map_sum]; symm
 refine Fintype.sum_equiv ((boxA s).symm.prodCongr (boxA s).symm) _ _ (fun j=>?_); rcases j with ⟨x,z⟩; rw [show ((boxA s).symm.prodCongr (boxA s).symm) (x,z)= ((boxA s).symm x,(boxA s).symm z) from rfl]; dsimp only [kWh,stem]; rw [t]; unfold stroke chasmR
 rw [joined_map,mould_map]; by_cases g:i=pur (joined x z); swap; · rw [Pi.single_eq_of_ne g,Pi.single_eq_of_ne ((moldA s).injective.ne g)]; change A 0=0; rw [map_zero] -- tune
 subst i; rw [Pi.single_eq_same,Pi.single_eq_same,Pi.sub_apply,Pi.sub_apply,map_sub]; apply congrArg₂ (·-·) <;> symm
 all_goals
   unfold Vow.flick; rw [block_map,mould_map]; simp only [moldA, Equiv.ofBijective_apply,Salt.actY,Finset.disjoint_map]; split_ifs; exact W_turn s _ A; exact (map_zero _).symm
lemma Sr_value (X:Scree.Hub n): C.Sr a X 1=0:=by unfold Sr sunY patch; simp [Finset.sum_apply]
abbrev chargeP (P:BudgetPoint)(m:ℕ)(Γ a:ℝ) := jet P m Γ a+jet P m Γ a
lemma pair_tag (Γ a:ℝ) (P:BudgetPoint) (i:CubeP n): jet P m Γ (C.kWh i a)= C.w i.1 i.2*jet P m Γ a:=by unfold jet kWh; rw [abs_mul,abs_of_nonneg (C.nn ..)]; ring
lemma pair_main (Γ a:ℝ) (P:BudgetPoint) (i:CubeP n): chargeP P m Γ (C.kWh i a)= C.w i.1 i.2 * chargeP P m Γ a :=by unfold chargeP; rw [pair_tag,mul_add]
lemma pair_press {Γ:ℝ}(p: DayT P.order Γ)(a:ℝ)(j:CubeP n): PressB P (stem j) (C.patch a j) h (chargeP P m Γ (C.kWh j a)):=by
 by_cases v:C.w j.1 j.2=0; · unfold patch kWh; rw [v,zero_mul,W_zero,W_zero,sub_zero]; rw [show chargeP P m Γ 0=0 from by simp [chargeP,jet]]; exact Vale.rinse .. -- kWh unfolded both?
 exact regular_sub (W_paid _ _ _ Finset.subset_union_right (C.far _ _ v) p) (W_paid _ _ _ Finset.subset_union_left (by change separation j.1 j.1 ≤ m; simp) p)
abbrev leafCost(P:BudgetPoint)(m:ℕ)(Γ a:ℝ):= Real.exp P.supportExponent*chargeP P m Γ a
lemma S_paid (P:BudgetPoint)(hk:m+2 ≤ P.B)(a:ℝ){Γ:ℝ}(g:0≤Γ)(t:DayT P.order Γ)(Q:Sweep n→ Prop)(u:∀ s,Q s→ C.Turns s): IncX Q (C.Sr a) P h (leafCost P m Γ a):=by
 let F:=C.patch a; let v(j:CubeP n):=chargeP P m Γ (C.kWh j a); let T:= leafCost P m Γ a; have he:=feat_v (h:=h) univ stem F v P T (fun i _=> pair_press C t a i) fun i=> ?_
 refine ⟨he.weight,fun s w V _ i x=> turn_sun s x i stem F ((boxA s).symm.prodCongr (boxA s).symm) (fun j=>joined_map ..) _ (fun j=> patch_turn C _ (u _ w) _ _)⟩
 rw [sum_filter, Fintype.sum_prod_type]; -- need tune
 change (∑ x:Skye.Seat n,∑ y:Skye.Seat n, if x=i then P.mass _ (v (x,y)) else 0) ≤ _; rw [sum_comm]; simp only [sum_ite_eq',mem_univ,if_true]; rw [← mul_one T, ← C.day i, Finset.mul_sum]; apply sum_le_sum; intro j _; by_cases v':C.w i j=0; · unfold v; rw [pair_main]; change P.mass _ (C.w i j*_ )≤ T*_; rw [v',mul_zero,zero_mul,BudgetPoint.mass,mul_zero]
 change P.mass (stem (i,j)).val.2 _ ≤ _; apply le_trans (mass_small (stem (i,j)).val.2 (cover_j P i j (C.far i j v') hk) (add_nonneg (jet_nn _ _ g _) (jet_nn _ _ g _))) (le_of_eq ?_); rw [pair_tag]; unfold T leafCost; ring
lemma S_spark (P:BudgetPoint)(hn:20*(m+10)< (More n).val) (a h:ℝ)(hp:1≤h){Γ:ℝ}(t:DayT P.order Γ) (L:ℕ): Ionic P L (C.Sr a):=by
 intro i hc hz; apply Beau.add_Z (X₀:=i) (S:=univ.filter fun t:CubeP n=>stem t=i) (C:=fun j=>chargeP P m Γ (C.kWh j a))
 · intro j p; rw [←(mem_filter.mp p).2]; by_cases z:C.w j.1 j.2=0; · unfold patch kWh; rw [z,zero_mul,W_zero,W_zero,sub_zero]; exact Beau.none_q _
   exact same_hessian P j.1 j.2 (by have:= C.far j.1 j.2 z; omega) _
 · exact fun j p=> (mem_filter.mp p).2 ▸ pair_press C t a j
 exact zero_le_one.trans hp
end Cart
end YM.CF.Taxi.Denn
