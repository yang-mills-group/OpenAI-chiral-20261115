import Anomaly.Basis.Callus
import Anomaly.Rack.Facets
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 600000
set_option synthInstance.maxSize 24000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Swell.Porticus
open Function Filter Topology NormedSpace Lattice Wilson Fock Pastry Scree Sault Sour Stax Skye Jet NormedSpace Scroll Finset Palot Cadre Vow
open RG Mew Rive Nor Hake MeasureTheory Bake Rue Salt
open Metric Drapes Tulip Lat Branch Cube Tenant
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Classical
attribute [local instance] opCStarAlgebra
open Rush SU Prism Nacre Laic Tap Levier Thera Moto Oath Font Haro Spire Dial Rill
variable {N:Side}{Y:SOp N}{S:Sa N}{B:BudgetPoint}{a t d f h q' x₀ y:ℝ}{k q j:ℕ}{K:Scree.Loom N}
local notation "I"=> Single N
local notation "θ"=> More N
open Buffered
variable {V:SOp N}{o: Seat N}{φ μ g₀:ℝ}
local notation "Φ"=> tangD N
-- cardinal for Aura Census
abbrev haloSites(k:ℕ):ℕ:= ((k+k+1)^4)*Fintype.card (SpinIdx × SU.Slot)
lemma halo_pMs(o:Seat N): (modesIn N (halo k {o})).card≤ haloSites k:=by
 let S:=halo k {o}; let Q:=modesIn N S; let J(i:Q): S× SpinIdx × SU.Slot:=(⟨node i.val.1.1,(modes_at ..).mp i.property⟩,i.val.1.2,i.val.2)
 have hp: Q.card ≤ S.card* Fintype.card (SpinIdx × SU.Slot):=by rw [← Fintype.card_coe Q,←Fintype.card_coe S, ← Fintype.card_prod]; exact Fintype.card_le_of_injective J (fun i j v=> Subtype.ext (Prod.ext (Prod.ext (unaryN (congrArg (fun i:S × SpinIdx × SU.Slot=>i.1.val) v)) (congrArg (fun i=>i.2.1) v)) (congrArg (fun i=>i.2.2) v)))
 exact hp.trans (Nat.mul_le_mul_right _ (by simpa only [card_singleton,one_mul] using (Corona.halo_size ({o}:Support θ) k))) -- tune order
local notation "HubK"=> halo B.B {o}
variable (v:Trunk o V k a μ d)(s:0≤a)(p:Roof N t d q K)(g:0<d)(b:B.threshold≤t)(Z:Aura N)(u:halo B.B {o} ⊆ Z.val)(l:k+q+10 ≤ B.B)(hs:cipherK q≤ 5*B.B)(ht:3≤ B.B)(H:HopeT d g₀ x₀ B.order)(w:B.threshold≤ x₀)
local notation "L"=> (x₀ / B.threshold)
include v p b u l g s
lemma knotPlus (x:Orbit N)(e:x.1∈Sour.σX B Z ∅) (D:Support (More N)) (hs:cipherK q≤5*B.B)(ht:3≤B.B)(H:HopeT d g₀ x₀ B.order): let M:=modesIn N (halo k {o});
    ∃ A:Toll I,ledgerV A≤μ ∧ (∀ i j:I, A i j≠0→i∈M ∧ j∈ M)∧ ∀ i j:I, Allows B.order (fun y:Φ=> V (roller g p (pressQ B D x.1 (L • y),x.2)).val i j) 0 (A i j):=by
 obtain ⟨F,C,T,E,hV,r⟩:=v.home; let A:=∑ S:Sa N,C S; have hp(S:Sa N)(w:C S≠0): S⊆ halo k {o}:=footprintGeodesic (f_then (T S) w) (E S w).1 (E S w).2.le
 intro M; refine ⟨A,?_,fun i j h=>?_,fun i j=>?_⟩
 · refine le_trans ?_ hV; unfold A ledgerV; simp_rw [Finset.sum_apply,sum_comm (s:=(univ:Finset I)) (t:=(univ:Finset (Sa N)))]; apply sum_le_sum; intro i _; apply le_mul_of_one_le_left _ (rent_one s i); exact sum_nonneg (fun i' _=> sum_nonneg (fun j _=> (T i).nonn i' j)) -- rfl on ledger
 · unfold A at h; simp_rw [Finset.sum_apply] at h; obtain ⟨k,p,h⟩:= exists_ne_zero_of_sum_ne_zero h; have hv:=((T k).expo i j).triggered h; have hk:=hp k (fun p=>h (by rw [p]; rfl)); exact ⟨(modes_at ..).mpr (hk hv.2.1), (modes_at ..).mpr (hk hv.2.2)⟩
 let U(y:Φ):= roller g p (pressQ B D x.1 (L • y),x.2)
 simp_rw [r,Matrix.sum_apply]; unfold A; simp_rw [Finset.sum_apply]; apply allows_sum; intro S _; by_cases k':C S=0
 · rw [show (fun y:Φ=> F S (U y) i j)=fun _=>0 from funext fun v=> norm_le_zero_iff.mp ((T S).expo i j|>.bounded _|>.trans_eq (by rw [k']; rfl)), k']; exact allows_const _ (by change ‖(0:ℂ)‖≤0; simp) -- tune
 apply offerPlus (T S) p g b Z ?_ hs ht H x ∅ D (empty_subset _) e (by simp [Lattice.halo]); intro k h; obtain ⟨i,r,t'⟩:=halo_spec.mp h; obtain ⟨j,v,y⟩:=halo_spec.mp (hp S k' r); exact u (halo_spec.mpr ⟨j,v,(separation_triangle j i k).trans (by omega)⟩)

local notation "Φt"=>f*μ*(8*(k:ℝ)*B.threshold)
-- no dependence on x,hQ of consultation! common support subset.
variable (W:Sonar.mintQ φ f d B.order)(R: Next.Rank.Spindle.Rules SU.group)(L':4*(k:ℝ)*B.threshold≤R.c)(c:2*(k+1)<(More N).val)(hv:8*(k:ℝ)*B.threshold < φ)
private lemma Brisk (x:Orbit N)(q:x.1∈ Sour.σX B Z ∅): pingS B.threshold (halo B.B {o}) x.1:= grow_b u (by simpa only [sdiff_empty] using q.1)
include s W R L' c hv hs ht H w
-- explicit uniform smallness to pay Glyph costs. δ growth
lemma passPlus (x:Orbit N)(q:x.1∈ Sour.σX B Z ∅)(D:Support (More N)) (eV: ‖V (profile 1)‖≤y)(i j:I): let X:=y+Φt+B.threshold/x₀*μ;
 Allows B.order (fun z:Φ=> V (roller g p (pressQ B D x.1 z,x.2)).val i j) 0 X:=by
 let M(z:Φ):Op I:= V (profile (K (pressQ B D x.1 z,x.2))); let A(z):= M z i j; have h0:=B.threshold_pos; obtain ⟨v',V₁,C,u'⟩:= knotPlus v s p g b Z u l x q D hs ht H
 have h₁:1≤L:= (one_le_div h0).mpr w
 have hh: ‖A 0‖≤ y+Φt:=by
   have ht:pressQ B D x.1 0=x.1:=by rw [pressQ,smul_zero,YM.CF.Forge.born]
   unfold A M; rw [ht]; exact (norm_entry ..).trans ((flareMatrix v s p g b x (Brisk v s p g b Z u l x q) l W R L' c hv).trans (add_le_add_left eV _)) -- goal add? tune
 intro T; apply (flatGain (f:=A) h₁ hh (u' i j)).mono
 have hf: v' i j ≤ μ:=le_trans (le_trans (single_le_sum (f:=fun j=>v' i j) (fun j _=> (u' i j).nonneg) (mem_univ j)) (single_le_sum (f:=fun i=>∑ j:I,v' i j) (fun i _=>sum_nonneg (fun j _=> (u' i j).nonneg)) (mem_univ i))) V₁
 have hp:=H.peta; unfold T; rw [inv_div]; have hu:0 ≤B.threshold/x₀:=by positivity
 apply max_le; · exact le_add_of_nonneg_right (mul_nonneg hu (soakCostNN v.pay))
 exact (mul_le_mul_of_nonneg_left hf hu).trans (le_add_of_nonneg_left ((norm_nonneg _).trans hh))
-- Traces as linear aggregate. no need exposure to monomolecular ℓ.Shape
lemma passTrace (x:Orbit N)(q:x.1∈ Sour.σX B Z ∅)(D:Support (More N))(z:ℂ)(eV: ‖Matrix.trace (V (profile 1))-z‖≤y): let X:= y+Φt+B.threshold/x₀*(μ+‖z‖);
 Allows B.order (fun t':Φ=> Matrix.trace (V (roller g p (pressQ B D x.1 t',x.2)).val)-z) 0 X:=by
 let M(w:Φ):Op I:= V (profile (K (pressQ B D x.1 w,x.2))); let A(w):= (M w).trace-z; have h0:=B.threshold_pos; obtain ⟨v',V₁,C,u'⟩:= knotPlus v s p g b Z u l x q D hs ht H
 have h₁:1≤L:= (one_le_div h0).mpr w
 have hh: ‖A 0‖≤ y+Φt:=by
   have ht:pressQ B D x.1 0=x.1:=by rw [pressQ,smul_zero,YM.CF.Forge.born]; -- tune
   unfold A M; rw [ht]; exact (flareTrace v s p g b x (Brisk v s p g b Z u l x q) l W R L' c hv z).trans (add_le_add_left eV _)
 have hc:Allows B.order (fun i=> (M (L • i)).trace) 0 μ:=by
    refine (allows_sum (s:=univ) (fun i _=> u' i i)).mono ?_; exact le_trans (sum_le_sum fun i _=> single_le_sum (fun j (_:j∈(univ:Finset I)) => (u' i j).nonneg) (mem_univ i)) V₁
 intro T; let Vx:Allows B.order (fun i:Φ=>z) 0 ‖z‖:= allows_const 0 le_rfl; apply (flatGain (f:=A) h₁ hh (Newt.subtract_p hc Vx)).mono
 unfold T; have h:=H.peta; rw [inv_div]; exact max_le (le_add_of_nonneg_right (mul_nonneg (div_nonneg h0.le h.le) (add_nonneg hc.nonneg (norm_nonneg _)))) (le_add_of_nonneg_left ((norm_nonneg _).trans hh))
end YM.CF.Swell.Porticus
