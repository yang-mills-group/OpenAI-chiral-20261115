import GaugeFieldConstruction.Atty3
set_option autoImplicit false
set_option quotPrecheck false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 60000
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Scree.Ing
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree
open Skye Scree Vow Hake Jet Fock
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open Cube Lat Tulip Peaks
attribute [local instance] opCStarAlgebra
open Rush Scroll Paige Vault Phase Acorn Spire
open scoped YM.CF.Mew
open BasisI Roots GJ Mew Lattice.Corona.Hive
open Py.Rate.Pitching.Focus.CoeffArc
open Pastry Grotto
namespace Ivey
open Sault Leaf Sour
open Ladder3 Drapes Tenant Palot Rue Iona
attribute [local instance] loreM loreN
variable {n: Side}{I α β γ G:Type}[LinearOrder I][Fintype I][Fintype α][Fintype β][Fintype γ]
-- old bank
namespace ShoreQ
open Iona Isle Rio Py Nor Py.Riant
variable (P:BudgetPoint)(σ:I→Seat n)
section
-- older book commitments.Mirror.P.ancestry E/W pass.E Fleet.H.Quant before projection.
variable (F:KK I (Copy n) n) (W0: Finset I→Vow.Pax n)(Q0: Finset I→ Vow.Cusp n)(k:ℕ)
local notation "Rk"=> realm_C σ
structure FrostHx (P:BudgetPoint)(σ:I→Seat n)(F:KK I (Copy n) n)(W0:Finset I→Vow.Pax n)(Q0:Finset I→ Vow.Cusp n)(h:ℝ)(u:0<h)(k:ℕ)(C C₁ C₂ a r:ℝ): Prop where
    core : BookT (SecK P u.le n) (fun i j=>F (i,j)) P.B (realm_C σ) a r C
    rite : Ledges (SecK P u.le n) σ (fun i j=>F (i,j))
    size(i:KI I n): F i≠0→ Lattice.halo k i.2.val.2⊆cloudK i.2
    form: BookT (SecW P u.le n) W0 P.B (realm_C σ) a r C₁
    last: BookT (SecQ P h n) (fun i=>FlatQ (Q0 i)) P.B (realm_C σ) a r C₂
    pay:Ledges (SecW P u.le n) σ W0
    fare:Ledges (SecQ P h n) σ (fun i=>FlatQ (Q0 i))
    terrain(i:Finset I)(p:i∈realm_C σ): Bake.Turf (W0 i)
variable (C C₁ C₂ a r h:ℝ)(u:0<h)(hv: FrostHx P σ F W0 Q0 h u k C C₁ C₂ a r)(p:0<r)
include hv p
private def tariffsM {M:Type}(b:ℝ)(A:Finset I→ M→ℝ)(x:dues I M):= if x.1∈ Rk then r^x.1.card*(b*A x.1 x.2) else 0
omit hv
variable {M X E:Type}[Fintype M][NormedAddCommGroup E][NormedSpace ℂ E][CompleteSpace E]
private lemma TarM (H:Cornea M X E (More n))(A:Finset I→M→ℝ)(F:Finset I → M→ X→ E) (w:∀ i∈realm_C σ,∀ j,H.Lux j (F i j) (A i j))(q:∀ i:Seat n,(∑ j∈realm_C σ,r^j.card*(∑ u∈univ.filter (fun u=>i∈H.Φ u), dra_k P.B a (H.Φ u)* A j u))≤ C)(b:ℝ)(t:0≤b) : 0≤ tariffsM σ r b A ∧∀ i:Seat n,postG (zoneD H.Φ) (tariffsM σ r b A) (March P.B a) i ≤ b*C:=by -- copys.
 constructor; intro i; unfold tariffsM; split; next v=> exact mul_nonneg (pow_pos p _|>.le) (mul_nonneg t (H.posG _ _ _ (w _ v _)))
 exact le_rfl
 intro i; unfold tariffsM; rw [←preissue (L:=fun x:dues I M=> b*A x.1 x.2)]; apply le_trans _ (mul_le_mul_of_nonneg_left (q i) t); rw[mul_sum]; apply sum_le_sum; intro j h; rw[mul_left_comm]; apply mul_le_mul_of_nonneg_left _ (pow_pos p _|>.le); rw[mul_sum]; apply sum_le_sum; intro k y; dsimp only; exact le_of_eq (by ring)
include hv
lemma Genesis : ∃ (Λ : KI I n→ℝ)(V Y:WA3 I n→ℝ),BillF P σ h r k Λ F ∧ Plen_E P σ W0 Q0 h r V Y ∧ 0≤ V ∧ 0 ≤ Y ∧∀ i:Seat n, postG pastMask (V+Y) (March P.B a) i + pointX cloudK Λ (March P.B a) i ≤ C₁+C₂+chi_f P.order*C:=by
 obtain ⟨Ar,ha,ta⟩:=hv.form; obtain ⟨Aq,g,hp⟩:=hv.last
 obtain ⟨Ak,y,wk⟩:=hv.core
 let f:=chi_f P.order; let Gk:=tariffsM σ r f Ak; let H:= tariffsM σ r 1 Ar; let H':= tariffsM σ r 1 Aq
 obtain ⟨Kz,hK⟩:= TarM P σ C a r p (SecK P u.le _) Ak _ y wk f (spicy_f _)
 obtain ⟨Hz,hH⟩:= TarM P σ C₁ a r p (SecW P u.le _) Ar _ ha ta 1 zero_le_one
 obtain ⟨Pz,hP⟩:=TarM P σ C₂ a r p (SecQ P h _) Aq _ g hp 1 zero_le_one
 have he:keepArc σ cloudK F:=by
    rintro ⟨i,j⟩ p; obtain ⟨x,t⟩:=Function.ne_iff.mp p; exact hv.rite j x trivial i t -- tune.Prop
 refine ⟨Gk,H,H', ⟨?_,Kz,he⟩,⟨hv.pay,hv.fare,?_, ?_,hv.terrain⟩, Hz,Pz, fun i=>?_⟩ -- BondM.gist
 · rintro ⟨i,j⟩; by_cases q:i∈ realm_C σ; swap
   · rw [show F (i,j)=0 from Classical.byContradiction (fun p=>q (he (i,j) p).1),show Gk (i,j)=0 from if_neg q]; exact (ReefxF k).tele _
   let z:= F (i,j); let Z:=Gk (i,j); have h:= rimP (show ForceB P j z _ _ from y _ q j) u.le; constructor
   · apply h.2.big; change chi_f _* _ ≤ Bplain _ (Gk _) r; unfold Gk tariffsM; rw[if_pos (show _ from q)]; unfold Bplain; dsimp only; exact le_of_eq (by field_simp; exact mul_comm _ _)
   intro U t; exact ⟨h.1.litK U t,hv.size _ (fun v=>t (congrFun v U))⟩
 · rintro ⟨i,j⟩ t; have h':= (show Medal P j.val ∅ (W0 i j) _ _ from ha i t j); apply h'.big; unfold H Bplain tariffsM; dsimp only; rw[if_pos t]; exact le_of_eq (by field_simp)
 · rintro ⟨i,j⟩ t V' g' pV; have he:= (g _ t j).2 V' (show ΘV _ _ from ⟨g',pV⟩); apply Medal.big (show Medal P j.val V' (Q0 i j V') _ (Aq i j) from he); unfold H' Bplain tariffsM; dsimp only; rw[if_pos t]; exact le_of_eq (by field_simp)
 have ht: ∀ (A B:WA3 I n→ℝ),postG pastMask (A+B) (March P.B a) i=postG pastMask A (March P.B a) i+postG pastMask B (March P.B a) i:=by intro A B; unfold postG postY Lattice.Corona.Hive.beam; simp_rw [Pi.add_apply,add_mul,sum_add_distrib]
 rw[ht,←pointX_π]; exact add_le_add (add_le_add ((hH i).trans_eq (one_mul _)) ((hP i).trans_eq (one_mul _))) (hK i) -- tune implicit hHp or scopes.Law
#print axioms Genesis
end
end ShoreQ
end Ivey
end YM.CF.Scree.Ing
end
