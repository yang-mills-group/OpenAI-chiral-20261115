import Anomaly.Basis.Balm
import YM.SU5.Exchange.Stack.Louvre
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
variable {N:Side}{Y:SOp N}{S:Sa N}{B:BudgetPoint}{a τ t d f h q' x₀ y s:ℝ}{k q j c:ℕ}{K:Scree.Loom N}
local notation "I"=> Single N
local notation "θ"=> More N
open Buffered
variable {V:SOp N}{o: Seat N}{φ μ g₀:ℝ}
local notation "Φ"=> tangD N
-- aggregate inner footprints
variable (v:Trunk o V k a μ d)(T:DockPulse B K t d a h s j q) (l: k+q+10 ≤ B.B)(e₀:1 ≤ j)
def temple {N:Side}(k:ℕ)(X:BudgetPoint)(o:Seat N): Aura N:=⟨grooveB k X o,o, Finset.mem_of_subset (halo_subset ..) (mem_singleton_self _)⟩ -- tune underscore
local notation "Xφ"=> temple j B o
include e₀
private lemma avenue : halo B.B {o}⊆ (Xφ).val := Corona.halo_mono (Nat.le_mul_of_pos_left _ e₀) le_rfl -- include later
variable {J:Op (Single N)→FC (Dwell N)}{Z:Single N→ Single N→ FC (Dwell N)}(U:Glyph J Z h)
abbrev vaporB(B:BudgetPoint)(h μ:ℝ):ℝ:= (B.order+1:ℝ)* μ*h^2
abbrev shipInc (K:Scree.Loom N)(V:SOp N)(J:Op I→FC (Dwell N)) : Firing N:= fun x=> J (V (profile (K x)))
local notation "SΨ"=> shipInc K V J
include v T l Z U e₀
lemma unroll_core : Herb B q Xφ h SΨ (vaporB B h μ):=by
 obtain ⟨F,C,E,Q,p',x⟩:=v.home; let X:=Xφ
 let W(S):= Glyph.cure J T.roof T.pos (F S); let Fq(S):= Glyph.vest B h (C S)
 obtain ⟨f,a,H,hb⟩:=T.room
 have hr(S:Sa N): Herb B q X h (W S) (Fq S):=by
    by_cases r:C S≠0; swap
    · push Not at r; have hp: W S=0:= by
         funext i; unfold W Glyph.cure; rw [show F S _=0 from Matrix.ext fun j k=> norm_le_zero_iff.mp (((E S).expo j k).bounded _|>.trans_eq (by rw [r]; rfl)), U.whirl]; simp -- cursor bad
      rw [hp,show Fq S=0 from by unfold Fq Glyph.vest; rw [r]; simp [ledgerV]]; exact Herb.zeroR
    apply Herb.kernelR T.roof T.pos J Z (E S) U T.reach H hb T.fees T.most; intro i d; obtain ⟨u,t,y⟩:=halo_spec.mp d; obtain ⟨l',w,s⟩:=halo_spec.mp (footprintGeodesic (f_then (E S) r) (Q S r).1 (Q S r).2.le t)
    apply avenue e₀; exact halo_spec.mpr ⟨l',w,(separation_triangle l' u i).trans (by omega)⟩
 have hv': SΨ= ∑ i:Sa N,W i:=by funext i; unfold shipInc; rw [show V (profile (K i))=_ from x (roller T.pos T.roof i),Finset.sum_apply, U.whirl]; simp_rw [Matrix.sum_apply, W,Glyph.cure,U.whirl,sum_smul,sum_comm (s:=(univ:Finset I)) (t:=(univ:Finset (Sa N)))]
 rw [hv']; apply (Herb.whole _ _ _ (fun i _=> hr i)).large_r (zero_le_one.trans T.high); unfold Fq Glyph.vest vaporB; rw [←sum_mul]; simp_rw [←mul_sum]; refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (le_trans ?_ p') (by positivity)) (sq_nonneg _); exact sum_le_sum fun i _=> le_mul_of_one_le_left (sum_nonneg fun j _=> sum_nonneg fun u _=> (E i).nonn j u) (rent_one T.hint.le i) -- tune
-- Aura extracts using ON SITE for X. Flight may pack larger also, need only pay Fringe at Xφ itself for `dedicate`.
variable (W:Sonar.mintQ φ f d B.order) (R:Next.Rank.Spindle.Rules SU.group) (L:4*(k:ℝ)*B.threshold≤R.c) (c':2*(k+1)<(More N).val) (hv:8*(k:ℝ)*B.threshold < φ)
variable (H: HopeT d g₀ x₀ B.order)(w:B.threshold ≤ x₀)
include W R L c' hv H w
abbrev Φσ(b:BudgetPoint)(f μ:ℝ)(k:ℕ):=f*μ*(8*(k:ℝ)*b.threshold)
local notation "Dμ"=>y+Φσ B f μ k+B.threshold/x₀*μ
open Vow.TreasuryFog -- Fringe
lemma seminar (eV: ‖V (profile 1)‖≤ y) : AuraOp B Xφ ∅ SΨ h ((haloSites k:ℝ)^2 *((B.order+1:ℝ)*(y+Φσ B f μ k+B.threshold/x₀*μ)*h^2)):=by
 let X:= Xφ; let Q(i j:I)(x:Orbit N):= V (profile (K x)) i j • Z i j; let Vt:=(B.order+1:ℝ)*(Dμ); have hh:0≤ y+Φσ B f μ k+B.threshold/x₀*μ:=by let h':=T.hint.le; have ht:0≤y:=(norm_nonneg _).trans eV; have hv:=soakCostNN v.pay; have he:=H.peta; have hφ:=W.2.2.1; have hx:=B.threshold_pos; unfold Φσ; positivity
 let E:=modesIn N (halo k {o}); have hS(i j:I) : AuraOp B X ∅ (Q i j) h (Vt*h^2):= by apply AuraOp.sat h (P:=B) (fun x=> V (profile (K x)) i j) _ (U.arc i j) (mul_nonneg (by positivity) hh); exact fun x p D _=> bare_p _ _ (passPlus v T.hint.le T.roof T.pos T.reach X (avenue e₀) l T.fees T.most H w W R L c' hv x p D eV i j) -- tune
 have hz(i:Orbit N)(j k:I) (r:¬ (j ∈ E∧k∈E)): Q j k i=0:=by
    let x:=roller T.pos T.roof i; have hv:=trunkSupport v x; let M:= V (profile (K i)); change cutM E*M* cutM E=M at hv; unfold Q
    rw [show V _ _ _= _ from (show M j k=_ from Matrix.ext_iff.mpr hv.symm j k)]; unfold cutM; rw [Matrix.mul_diagonal,Matrix.diagonal_mul]; push Not at r; by_cases k:j∈E <;> simp [k,r]
 have hz': SΨ=∑ i∈E,∑ j∈E,Q i j:=by
    funext i; simp_rw [Finset.sum_apply]; unfold shipInc; rw [U.whirl]; change (∑ j:I,∑ k:I,Q j k i)=_; rw [←sum_subset (subset_univ E)]; swap; · intro j _ v; exact sum_eq_zero fun k _=>hz _ _ _ (fun u=>v u.1)
    exact sum_congr rfl fun j _=> (sum_subset (subset_univ E) fun k _ v=> hz _ _ _ (fun u=> v u.2)).symm
 rw [hz']; apply AuraOp.bigger (AuraOp.sumR _ _ _ (fun _=> ∑ j∈E,Vt*h^2) (fun i p=> AuraOp.sumR _ _ _ _ (fun j _=> hS i j))) (zero_le_one.trans T.high)
 simp only [sum_const,nsmul_eq_mul]; change (E.card:ℝ) * (E.card * (Vt * h^2 : ℝ)) ≤ _; rw [←mul_assoc,sq (haloSites k:ℝ)]; have h0:0 ≤ Vt:=mul_nonneg (by positivity) hh; exact mul_le_mul_of_nonneg_right (mul_le_mul (Nat.cast_le.mpr (halo_pMs o)) (Nat.cast_le.mpr (halo_pMs o)) (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (mul_nonneg h0 (sq_nonneg _))
omit Z U
lemma traceSeat (z:ℂ)(eV: ‖Matrix.trace (V (profile 1))-z‖≤y): let A:=(B.order+1:ℝ)*(y+Φσ B f μ k+B.threshold/x₀*(μ+‖z‖)); AuraOp B Xφ ∅ (fun x=> (Matrix.trace (V (profile (K x)))-z) • (1:FC (Dwell N))) h A:=by
 intro A; let i:ℝ:= y+Φσ B f μ k+B.threshold/x₀*(μ+‖z‖); have hh:0≤ i:=by unfold i Φσ; have v₁:=W.2.2.1; have h:=B.threshold_pos; have p':=H.peta; have hu:= (norm_nonneg _).trans eV; have hy:=soakCostNN v.pay; positivity
 have hp:0≤A:=mul_nonneg (by positivity) hh
 let V'(x:Orbit N):=Matrix.trace (V (profile (K x)))-z; let U:AuraOp B Xφ ∅ (fun x=> V' x • (1:FC (Dwell N))) h (A*1):=by
    apply AuraOp.sat h (P:=B) V' 1 (Ark.one _) hp; intro x p D u; exact bare_p _ _ (passTrace v T.hint.le T.roof T.pos T.reach Xφ (avenue e₀) l T.fees T.most H w W R L c' hv x p D z eV)
 rwa [mul_one] at U
end YM.CF.Swell.Porticus
