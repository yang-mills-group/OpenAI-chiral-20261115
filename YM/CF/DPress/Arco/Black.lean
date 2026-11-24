import YM.CF.DPress.Arco.Quests
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
set_option maxHeartbeats 400000
noncomputable section
namespace YM.CF.Py.Kay
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
open Wray
open Lich.Muster Push.AbsoluteSums
open Iva Eire
open Trees Footprint Iva Eire
open Jade
open Oath Feu Feu.Corset Ione Nor Haro Beau Siete PhysicalNext.JointLoad.Heir Vow
open AnalyticBridge.VerifiedReset
open DPress DPress.Fees Finance Rosy
open scoped YM.CF.Mew
open Larch Ione Taxi Bake Salt LinearT Sour Heath Docket Moral
namespace Arco
variable {n:Side}{X:Scree.Hub n}{Y:Cusp n}{L:ℕ}(P:BudgetPoint){a h b:ℝ}(t:1≤h)
structure Subzero (P:BudgetPoint)(K:ℝ) where
 g : ℝ -- γ*
 R : ℝ
 X : ℝ -- X_D
 S : ℝ -- H_c^
 pos : 0<g
 posX : 0 < X
 fit : 1 ≤ K
 q : degreePrice P.B g wΨ<1
 qX : degreePrice P.B X 1 <1
 A : S+rateΓ P g wΨ ≤1
 B : K*R+Real.exp 1*(rateΓ P g wΨ+ S) ≤ X
abbrev stipend(P:BudgetPoint)(F:Cusp n):Prop:=∀ (i:Aura n)(K:Support (More n)),K.Nonempty→K⊆i.val→Firm P i.val K (F i K)
lemma staff {F:Cusp n}(g:stipend P F)(t:stipend P Y):stipend P (F+Y):=by
 intro i A p v; obtain ⟨H,D⟩:=g i A p v; obtain ⟨u,d⟩:= t i A p v; constructor; · intro i'; change F i A+Y i A=0; rw [H i',u i',zero_add]
 intro j t; by_cases d':F i A j=0; exact d j (fun p=>t (by change F i _ _ +_=0; rw [d',p,add_zero])); exact D j d'
lemma team (t:stipend P Y)(z:ℂ):stipend P (z • Y):=by
 intro i K p v; obtain ⟨y,W⟩:= t i K p v; change Firm _ _ _ (z • _); exact ⟨fun i=>by rw [y i,smul_zero],fun i h=> W i fun p=>h (show z • Y _ _ i=0 from by rw [p,smul_zero])⟩
variable {T:Sweep n→Prop}
abbrev honest(T:Sweep n→Prop) (F:Cusp n):Prop:= ∀ s,T s→∀ i, Injective (priorP i.2) → Vow.Zeal s i (suit_Y s) F
abbrev Kir (P:BudgetPoint)(X Y:Cusp n): ForceBudget n:= budgetR (roomV P (EmptyD X) X Y)
variable {K:ℝ}
structure Chips (W:Subzero P K) (X Y :Cusp n)(h:ℝ):Prop where
 first: PactF P (ρL P) h (EmptyD X) W.g
 second: XL P h (ρL P) X W.R
 arm: stipend P X
 lease: ZL P h (lev2 P) Y W.S
namespace Chips
variable {P}{X Y:Cusp n}{W:Subzero P K}(v:Chips P W X Y h)
include v t
lemma amen : ∃ A, Ready Palot.stern P.B A (lev2 P) W.g wΨ (degreePrice P.B W.g wΨ) ∧ (∀ i:Aura n,Medal P i.val ∅ (X i ∅) h (A i)):=by obtain ⟨A,w,x⟩:=v.first; exact ⟨A,Sour.ready_T W.pos uΨ W.q (fun i=> (w i).wage (zero_le_one.trans t)) x,w⟩
lemma affirm(r:honest T X)(q:honest T Y)(w:∀ s,T s→∀ (i:Aura n)(v:Orbit n),EmptyD X (moldA s i) (yellA s v)=suit_Y s (EmptyD X i v)): Dark T (Kir P X Y) P h (Cog_P P W.X K):=by
 obtain ⟨x,pW,b⟩:= mantle _ _ _ t _|>.1 v.lease; obtain ⟨G,f,η⟩:= (vouchers _ _ _ t _).1 v.second; have hp: ArmsK P X G h:=⟨fun i D y k=> f i D (mem_filter.mpr ⟨mem_univ _,y,k⟩),v.arm⟩; obtain ⟨A,s,U⟩:= amen t v; have he:= add_nonneg P.exponent_pos.le zero_le_one
 have hv(i: Skye.Seat n):tallB (Vow.hymn G) P.B (lev2 P) i ≤ W.R:= (tall_m _ (fun i=> sum_nonneg fun j u=>(f i j u).wage (zero_le_one.trans t)) tiny2 _).trans (η i)
 apply dark_F (γ':=W.X) (Qm:=T) hp pW.2 pW.1 s he zero_lt_one U zero_lt_one t W.fit ?_ b hv le_rfl W.qX W.posX W.B
 · intro s i V q' m j; refine ⟨fun t v p h=>?_,fun t v p h=>?_,fun t=>?_⟩
   · rw [tama s _ j]; exact r s q' i m t v p h
   · rw [tama s _ j]; exact q s q' i m t v p h
   rw [tama s _ j]; exact w s q' t i
 intro i; obtain ⟨j,h⟩:= i.property; refine (add_le_add_left (le_trans ?_ (b j)) _).trans W.A; exact (le_mul_of_one_le_right (pW.1 i) (Real.one_le_exp (mul_nonneg (add_nonneg he zero_le_one) (by exact Nat.cast_nonneg (coverNumber P.B i.val))))).trans (single_le_sum (s:=Finset.univ.filter (fun i:Aura n=>j∈i.val)) (f:=fun i=>x i * Trees.currency P.B (lev2 P) i.val) (fun i _=>mul_nonneg (pW.1 i) (Real.exp_pos _).le) (mem_filter.mpr ⟨mem_univ _,h⟩))
end Chips
end Arco
end YM.CF.Py.Kay
