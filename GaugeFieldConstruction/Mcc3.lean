import GaugeFieldConstruction.MakeQ3
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
open Hest XGarden Ladder3 Branch Urn Tenant Nacre Drapes Salt Sour.SliceRoof Rill Rill.CreekX Broc Thera Jet CF.Forge
variable {R:Loom n}{k:ℕ}{t d a c b v:ℝ}{F:Elm n Unit d a c} {Q:BudgetPoint}
attribute [local instance] boreKSpace boreXN
local notation "S0"=> Support (More n)
local notation "SA"=> Seat n
variable (u:Roof n t d k R) (q:0<d)(y:hud_T 7 b)(b':0≤v)(e:coinH b v)(p:Hann Q k t)(h:ℝ)(vh:1≤h)
local notation "Ωt"=> MealD F R k t
local notation "dF"=> book_S d a c v F h
abbrev zeroStep (b:ℕ):ℕ:=(b+b+1)^4
abbrev low_η(b:ℕ)(d t:ℝ):ℝ:= t*(highCreek (b+1) (zeroStep b) d +1)
local notation "C'"=> DeskK v d+1
include u q y b' e p vh
lemma cram (V X:Support (More n))(D:Support (More n))(b₀:Lattice.halo (k+22) V⊆ X) (p₀:Lattice.halo (cipherK k) D⊆ X)(i j:Single n)(s:Lime Q X D): Allows Q.order (fun a:tangD n => uplift F R k D V t (citrus Q X D s a) i j) 0 ((DeskK v d+1) *Wloop F V i j):=by
 have ht := (stern_bill (F:=F) u p.pitch p₀ b₀ q s.property.2 p.rent p.crane y e b' i j s.property.1).1.order (show Q.order≤7 from by rw[p.canon]; decide)
 have hg:0≤DeskK v d:=by unfold DeskK composeCost; positivity
 exact ht.mono (mul_le_mul (le_add_of_nonneg_right zero_le_one) (expandW ..) ((F.coat V|>.1 ()).nonn ..) (add_nonneg hg zero_le_one)) -- tune nonneg
lemma carrotT (x:dry_E F)(hN:2*(Q.B+1)<(More n).val)(V X:Support (More n))(l: Seat n)(g:Lattice.halo (k+22) V⊆ Lattice.halo Q.B {l})(pL:Lattice.halo (Q.B+1) {l}⊆ X) :Medal Q X ∅ ((Ωt).issue V ∅) h (low_η Q.B d Q.threshold * dF V):=by
 let c₀:=DeskK v d; let b:= Q.B -- shadows
 let P:= highCreek (Q.B+1) (zeroStep b) d; have T:V⊆ Lattice.halo Q.B {l}:= (halo_subset _ _).trans g
 have ht:Lattice.halo (k+22) V⊆ X:= g.trans ((Corona.halo_mono (Nat.le_succ _) le_rfl).trans pL)
 have pt:Lattice.halo (cipherK k) (∅:S0) ⊆ X:=by simp[Lattice.halo]
 have hs:0≤ c₀:=by unfold c₀ DeskK composeCost; positivity
 have hP:0≤P:=by unfold P highCreek; have he:BPress.Spin.sphereRate≥0:= BPress.Spin.sphereRate_cost.positive.le; positivity; -- tune
 let Z':= low_η Q.B d Q.threshold; have hZ:0≤ Z':=mul_nonneg Q.threshold_pos.le (add_nonneg hP zero_le_one)
 let a'(i j:Single n):= Z'*(BudgetValve v d*Wloop F V i j)
 have he(i j:Single n)(m:Lime Q X ∅): let f:=fun a:tangD n=>uplift F R k ∅ V t (citrus Q X ∅ m a) i j; Allows Q.order f 0 (Z'*(c₀+1)*Wloop F V i j):=by
    intro f; let W:= Wloop F V i j; obtain ⟨A,H⟩:=stern_bill (F:=F) u p.pitch pt ht q m.property.2 p.rent p.crane y e b' i j m.property.1
    let w:m.val.1.1∈{v|pingS Q.threshold X v}:=by simpa only [Set.mem_setOf_eq,sdiff_empty] using m.property.1
    have hu: ‖f 0‖ ≤ W * Q.threshold * P:=by
       have hp:V.card ≤ zeroStep b:= (card_le_card T).trans (by unfold zeroStep b; simpa using Lattice.Corona.halo_size ({l}:Support _) Q.B)
       have h:= offer_T (P:=Q) u p.pitch ht q x l Q.B (show Q.B+1≤Q.B+1 from le_rfl) hN pL (U:=m.val.1) w T i j
       unfold f citrus; rw [show (pressQ Q m.val.2 m.val.1.1) 0 = m.val.1.1 from ?_]; swap; · simp [pressQ,gyrate]
       apply h.trans; apply mul_le_mul_of_nonneg_left _ (mul_nonneg (loop_p ..) Q.threshold_pos.le); unfold P highCreek; have he:=BPress.Spin.sphereRate_cost.positive; gcongr
    have hx:0≤W:=loop_p ..; have hw:Q.threshold≤ Z':=le_mul_of_one_le_right Q.threshold_pos.le (le_add_of_nonneg_left hP)
    have hg:Q.order ≤7:=by rw [p.canon]; decide
    refine ⟨(A.order hg).smooth,?_⟩; intro n' p'; cases n' with
    | zero=>
       change ‖iteratedFDeriv ℝ 0 f 0‖ ≤ _; rw [norm_iteratedFDeriv_zero]; apply hu.trans; unfold Z' low_η; let V0:= Q.threshold; change W*V0*_ ≤ (V0*(P+1))*(c₀+1)*W
       have he:=Q.threshold_pos; have hy:0≤(V0*(P+1))*W:=mul_nonneg hZ hx; nlinarith only [mul_le_mul_of_nonneg_left (show P≤P+1 by linarith) (show 0 ≤ W*V0 from mul_nonneg hx he.le), mul_nonneg hy hs]
    | succ i'=>
         apply (H _ (Nat.succ_pos _) (p'.trans hg)).trans; change (c₀*F.W _ _ _)*_ ≤ _
         calc
            _≤ (c₀*W)*Z':= mul_le_mul (mul_le_mul_of_nonneg_left (expandW ..) hs) hw Q.threshold_pos.le (mul_nonneg hs hx)
            _≤ _:=by nlinarith only [mul_nonneg hZ hx]
 apply Medal.big (V_M u q h vh V X ∅ ht pt (Zc:=a') (fun i j=>mul_nonneg hZ (mul_nonneg (mul_nonneg (by norm_num) (by exact add_nonneg hs zero_le_one)) (loop_p ..))) (fun s i j=>?_)) -- tune
 · unfold a' book_S ζΧ; simp_rw [←mul_sum]; exact le_of_eq (by unfold Z'; ring)
 have h:= (he i j s); apply (bare_p _ _ h).mono; rw[p.canon]; unfold a' BudgetValve; apply le_of_eq; norm_num; unfold c₀; ring
-- represent. real equality on fleet mask needs health when flags.S.cover.Nozzle test satisfied.
lemma Lease_barT {δ:ℝ}{j:ℕ}(pa: 0 < a)(p0:Tyrant k j δ a) : Leased (MealD F R k t) Q (cipherK k) h (book_S d a c v F h) ∧ KPower (MealD F R k t) δ ((BudgetValve v d*h^2)*CrownBill c j) (book_S d a c v F h):=by
 let f:= dF; let C:=BudgetValve v d; have hc:0≤C:=by unfold C BudgetValve DeskK composeCost; positivity
 refine ⟨⟨Lattice.halo_subset _,fun i S D pR q'=> V_base u q y b' e p h vh i S D pR q',fun i V T=>?_,fun i V=>life (V_apt u q i V),?_⟩,⟨fun i=> mul_nonneg (mul_nonneg hc (Hook_p ..)) (sq_nonneg _),?_,?_ ⟩⟩ -- order.I Tune
 · exact congrArg boat ((lift_empty (T:=T) (F:=F) (U:=V) (S:=i) u q).symm)
 · intro i S D W t' hH tL ε; have Wp: Disjoint (S\D) (flags Q.threshold W.1):= disjoint_left.mpr fun x p z=> (mem_sdiff.mp p).2 (ε ▸ mem_inter.mpr ⟨(mem_sdiff.mp p).1,z⟩);
   apply congrArg boat (show uplift F R k D i t W=releaseQ F i (R W) from if_pos ?_)
   exact payz p.pitch tL hH ((shoreK _ _ t' (S\D)).1 Wp)
 · intro s; apply le_trans _ (mul_le_mul_of_nonneg_left (LegendT k d a c F pa p0 s) (mul_nonneg hc (sq_nonneg _))); rw [Finset.mul_sum]; apply le_of_eq; change ∑ i:S0 with s∈i, _=_; apply Finset.sum_congr rfl; intro i y; change (C*_*h^2)* rent δ (Lattice.halo (k+22) i)= _; ring
 intro i p; exact XGarden.Ledger.crown_H (growΧ d a c F i (fun x=>p (by unfold book_S; rw[x,mul_zero, zero_mul]))) _
lemma FrostT (x:dry_E F)(hN:2*(Q.B+1)<(More n).val): Frosty (MealD F R k t) Q (book_S d a c v F h) h (low_η Q.B d Q.threshold):=⟨fun i x' X hp z=> carrotT u q y b' e p h vh x hN i X x' hp z⟩
#print axioms Lease_barT
#print axioms carrotT
end ShoreQ
end Ivey
end YM.CF.Scree.Ing
end
