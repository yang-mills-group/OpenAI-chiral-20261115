import SatinThinCap
/- From Actual K. Can borrow even when not requiring SanB at same Frame, since using
  EXACT roomV arguments. Adapt. echo_B, Vow.Law & Fair. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Vow
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
variable {X D Y Z:Support (More n)}{U:Pane n}
-- all seeds use child scales $Y∈H$. cost numerator.Post.S.Unit. equations read even if paux markers.H.St.
open Trees
variable {K W:Cusp n}
variable {C:blazeK n}{G:Aura n→ℝ}
open Stax Rue
variable {δ:ℕ}(T:Finset (Palot.Duo (More n)))(p:ArmsK P K C h)
include p
lemma flameGem (r:∀ Y:Aura n,∀ D⊆Y.val,Lives P δ Y D (K Y D))
 (S:Aura n)(D:Support (More n))(hp:D⊆S.val) : Lives P δ S D (gemB D K W T (beamH S.val)) := by
 intro i v
 obtain ⟨lt,_,hd⟩:= enough_v S T hp p i v
 refine ⟨fun j hv=>?_,hd⟩; obtain ⟨x,hx,t⟩:= halo_spec.mp hv
 obtain ⟨g,u,y⟩:= deck_r S T hp lt _ hx
 have hg: K g (D∩g.val) i ≠ 0 := by intro he; apply v; rw [gear_v, if_pos lt,Pi.mul_apply,Finset.prod_apply,prod_eq_zero u he,zero_mul]
 exact (stun_v S T lt g u).2 ((r g _ inter_subset_right i hg).1 (halo_spec.mpr ⟨x,y,t⟩))
lemma flareGlow (r:∀ Y:Aura n,∀ D⊆Y.val,Lives P δ Y D (K Y D))
 (Y:Aura n)(D:Support (More n))(w:D⊆ Y.val) : Lives P δ Y D (glowV K W Y D) := by
 intro i v
 unfold glowV mintF at v; rw [if_pos w, Finset.sum_apply] at v; obtain ⟨l,_,q⟩:=exists_ne_zero_of_sum_ne_zero v; exact flameGem l p r Y D w i q
omit p
section unary
variable {hP κ':ℝ}
/- support earnings on the ACTUAL Force layout. -/
structure Flame (X:ForceBudget n)(P:BudgetPoint)(h:ℝ)(r:ℕ)(κ κ':ℝ)(K:Cusp n)(C: blazeK n):Prop where
 card : X=budgetR K
 dead : ∀ i:Aura n,K i ∅=0∧ C i ∅=0
 fray : ∀ X:Aura n,∀ D⊆X.val,Fray P h r X D (K X D) (C X D)
 arms : ArmsK P K C h
 tall : ∀ i:Seat n,tallB (hymn C) P.B (P.supportExponent+κ) i ≤ κ'
abbrev Dust (X:ForceBudget n)(P:BudgetPoint)(h:ℝ)(r:ℕ)(κ κ':ℝ):Prop:=∃ K C,Flame X P h r κ κ' K C
/- condense at rooted Halo. discard unused D=∅ entry. -/
def coDouse (K:Cusp n) : Cusp n := fun x D=> if D.Nonempty then K x D else 0
def coDouset (C:blazeK n) : blazeK n := fun x D=> if D.Nonempty then C x D else 0
variable {κ:ℝ}
lemma flameCard (p:ArmsK P K C h)(r:∀ X:Aura n,∀ D⊆ X.val,Lives P δ X D (K X D))(z:∀ i:Seat n,tallB (hymn C) P.B (P.supportExponent+κ) i ≤ κ') : Flame (budgetR K) P h δ κ κ' (coDouse K) (coDouset C) := by
 let X:=coDouse K; let F:=coDouset C
 have e1 (x:Aura n) (y:Support (More n)) (v:y.Nonempty):coDouse K x y=K x y:= by simp only [coDouse,v,↓reduceIte]
 have e2 (x:Aura n) (y:Support (More n)) (v:y.Nonempty):coDouset C x y=C x y:= by simp only [coDouset,v,↓reduceIte]
 refine ⟨?_,fun i=> ⟨if_neg Finset.not_nonempty_empty,if_neg Finset.not_nonempty_empty⟩,fun j D t=>?_,⟨fun i l v hp=>by rw [e1 _ _ v,e2 _ _ v]; exact p.price i l v hp,fun i l v hp=>by rw [e1 _ _ v]; exact p.claim i l v hp⟩,fun i=> ?_⟩
 · funext i; unfold budgetR; rw [e1 _ _ i.property.1]
 · by_cases u:D.Nonempty
   · rw [e1 _ _ u,e2 _ _ u]; exact ⟨p.price _ _ u t,r _ _ t⟩
   unfold coDouse coDouset; rw [if_neg u,if_neg u]; exact ⟨Medal.zeroT,fun i x=> (x rfl).elim⟩
 rw [show hymn (coDouset C)=hymn C from funext fun j=> sum_congr rfl (fun l w=> e2 _ _ (mem_filter.mp w).2.1)]
 exact z i
open Palot
variable {Kf:ForceBudget n}
lemma Flame.flight (f:Flame Kf P h δ κ κ' K C)(V:Orbit n)(u:FleetS P.threshold V.1) : Palot.hGas (flags P.threshold V.1) (hailV (flags P.threshold V.1) K V) = fueled P Kf V := by
 rw [f.card,←themeK V K u, Palot.hGas,beamP, Palot.Hac,highV]; let Ω:=flags P.threshold V.1
 symm; refine sum_subset (fun i p=> mem_filter.mpr ⟨mem_univ _,(mem_filter.mp p).2.1,(mem_filter.mp p).2.2.1⟩) ?_
 intro j h p; by_contra l
 apply p; refine mem_filter.mpr ⟨mem_univ _,(mem_filter.mp h).2.1,(mem_filter.mp h).2.2,fun y z i=>?_ ⟩
 exact l (prod_eq_zero z (by unfold hailV; rw [Finset.disjoint_iff_inter_eq_empty.mp i.symm,(f.dead _).1]; rfl))
lemma reserve_one_le (n m k:ℕ) : 1≤ reserveT n m k (1/2:ℝ) := by
 have v: 1≤ stilK k := by unfold stilK; linarith only [show 0≤ (k:ℝ) from Nat.cast_nonneg k]
 have l(x:ℕ): 1≤ (x.factorial:ℝ):= by exact_mod_cast Nat.factorial_pos x
 have h : 1≤ (1/(2:ℝ))⁻¹:= by norm_num
 unfold reserveT coin_n
 repeat' first | exact Real.one_le_exp (by norm_num) | exact l _ | exact v | exact h | exact zero_le_one | exact le_rfl | apply one_le_mul_of_one_le_of_one_le | apply one_le_pow₀
 all_goals norm_num
end unary
end YM.CF.Vow
#print axioms YM.CF.Vow.Flame.flight
