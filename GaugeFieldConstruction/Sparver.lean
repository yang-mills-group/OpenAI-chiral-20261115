import GaugeFieldConstruction.RiverS
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 300000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Sour
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open Skye Scree Cadre Palot
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open Cube Lat Tulip Fock Rush Scroll Paige Vault Phase Acorn Spire
open Pastry Vow Rue
attribute [local instance] opCStarAlgebra
variable {n:Side}
local notation "SA"=> Seat n
local notation "VX"=> Aura n
local notation "Hk"=> hook SA
open Hake Jet Sault Stax
attribute [local instance] loreM loreN
variable {P:BudgetPoint}{X Y Z:Aura n}{V W:Firing n}
open Branch Tenant Drapes Rill Sault
attribute [local instance] Rill.boreKSpace Rill.boreXN
local notation "JS"=> Single n
local notation "SO"=> Support (More n)
local notation "Γ"=> (FC (Dwell n))
open Exa Tap Dial
-- sweep weight.TIO. openc slice.S.inverse. erosion
open Levier Thera Urn Nacre Salt

namespace SliceRoof
open Vow Rue Rill CreekX Pressure CF.Forge XGarden Jet Broc
variable {P:BudgetPoint}{k:ℕ}{H:Scree.Loom n}{t d c a c0 K':ℝ}{F:Elm n Unit d a c}{A S D Y:Support (More n)}{U W: Orbit n}
local notation "Xρ"=> uplift F H k D S t
local notation "Sz"=> fun i:tangD n=> ((pressQ P Y U.1 i,U.2):Orbit n)
variable (u:Roof n t d k H)(p:P.threshold≤t)(hp:Lattice.halo (cipherK k) D⊆ A)(hg:Lattice.halo (k+22) S⊆ A)(w:0<d)
variable (vZ:D⊆ Y)(pZ:cipherK k ≤5*P.B)(ht:3 ≤ P.B)
variable (τ:hud_T 7 K')(t':coinH K' c0)(g:0≤c0)
include hp hg p vZ pZ ht u w τ t' g
lemma stern_bill (i j:Single n)(v:pingS P.threshold (A\D) U.1): let f:= fun y=> uplift F H k D S t (Sz y) i j; let c:=DeskK c0 d* F.W S i j; Allows 7 f 0 c∧∀ k:ℕ,0<k → k≤7 → ‖iteratedFDeriv ℝ k f 0‖ ≤ c * P.threshold :=by
 intro f C
 let L:=unrest Y P.B; let T:tangD n→L[ℝ] tangD n:=P.threshold • wakeB L; let G:=γCreek F H S i j U; let a:= G∘ T
 have pv:f=ᶠ[𝓝 0] a:= bloom_Ψ u p hp hg w vZ pZ ht τ i j v
 have z:‖T‖≤P.threshold:=by
    unfold T; rw [norm_smul,Real.norm_of_nonneg P.threshold_pos.le]; refine mul_le_of_le_one_right P.threshold_pos.le ?_; apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one; intro v; rw [one_mul]; apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2; intro j; rw [steadyB]; split; exact norm_le_pi_norm ..; rw [norm_zero]; exact norm_nonneg _
 have ht:Allows 7 G (T 0) C:= (map_zero T).symm ▸ (gamma_S u p hp hg w τ t' g i j) -- order tune
 refine ⟨(comps T ht (z.trans P.threshold_le)).germ pv.symm,?_⟩; intro k u v
 rw [(pv.iteratedFDeriv ℝ k).eq_of_nhds,show a=G ∘ T from rfl, Push.Uniform.iter_lin_at (L:=T) (ht.smooth.of_le (by exact_mod_cast v))]; apply (ContinuousMultilinearMap.norm_compContinuousLinearMap_le ..).trans (le_trans (mul_le_mul_of_nonneg_left _ (norm_nonneg _)) (mul_le_mul_of_nonneg_right (ht.norm_le k v) P.threshold_pos.le))
 simp only [prod_const,card_univ,Fintype.card_fin]; apply (pow_le_pow_left₀ (norm_nonneg _) z _).trans; exact (pow_le_pow_of_le_one P.threshold_pos.le P.threshold_le (show 1≤k from u)).trans_eq (pow_one _)
omit p vZ pZ ht τ t' g hp
open SU
open Nacre
-- local gain for T from using strict ping. B width.Lattice apex.
private lemma sails {Vx:ℕ}(o:Seat n)(r:ℕ)(l:r+1 ≤ Vx)(q:2*Vx < (More n).val)(b:Lattice.halo Vx {o}⊆ A)(v:pingS P.threshold A U.1):∃ z:Seat n→SU.E,
 ∀ T:Support (More n),nozzle k T ∅ t U.1 → (T⊆Lattice.halo r {o})→ BPress.chord.Close (Lattice.gauge z (H U)) 1 T (16*(2*(Vx:ℝ)+1)^5 * (Fintype.card PlaqAxes:ℝ) * P.threshold) :=by
 have h(y:Seat n)(g:separation o y≤Vx)(f:PlaqAxes): Pressure.toll U.1 (y,f)≤P.threshold:=by
    refine (v (y,f) (not_disjoint_iff.mpr ⟨_,b (halo_spec.mpr ⟨o,mem_singleton_self o,g⟩), Work.E01.base_touched _⟩)).le
 obtain ⟨z,g⟩:= Work.E08.axial_patch o U.1 r Vx l q _ P.threshold_pos.le h
 refine ⟨z,fun T uT pT j a b=>?_⟩
 rw [show (1:Pane n) j=1 from rfl,BPress.chord.one]; unfold Lattice.gauge; rw [sailsEmpty u uT j a b]; exact g j (by simpa only [halo_spec,mem_singleton,exists_eq_left] using pT a)
-- inflated rows Wpay
omit hg u w
def Wloop(F:Elm n Unit d a c)(S:Support (More n))(i j:Single n):=∑ v:SU.Slot,∑ w:SU.Slot,F.W S (i.1,v) (j.1,w)
lemma loop_p (i j:Single n):0≤ Wloop F S i j:= sum_nonneg (fun i _=>sum_nonneg fun j _=> (F.coat S|>.1 ()).nonn _ _)
lemma expandW (i j:Single n): F.W S i j ≤ Wloop F S i j:=by
    apply le_trans (single_le_sum (f:=fun j' :SU.Slot=> F.W S i (j.1,j')) (fun _ _=> (F.coat S|>.1 ()).nonn _ _) (mem_univ j.2))
    exact single_le_sum (f:=fun j':SU.Slot=> ∑ v:SU.Slot,F.W S (i.1,j') (j.1,v)) (fun _ _=> sum_nonneg (fun _ _=> (F.coat S|>.1 ()).nonn _ _)) (mem_univ i.2)
lemma twist_rate {A:Op (Single n)}{g: Seat n→SU.E}{B: Single n→Single n→ℝ}(h:∀ i j, ‖(twist (tradew n g) A) i j‖ ≤ B i j) (x y:Single n): ‖A x y‖≤ ∑ v:SU.Slot,∑ w:SU.Slot,B (x.1,v) (y.1,w):=by
 let T:= twist (tradew n g) A
 let R:= matter (g (terse x.1)); let S:= matter (g (terse y.1))
 have he: ni x.1 y.1 A=star R.val * ni x.1 y.1 T * S.val:=by
    unfold T; rw [twistW]; change _=star R.val*(R.val*_ * star S.val)* S.val; rw [←mul_assoc,←mul_assoc,R.property.1,one_mul,mul_assoc,S.property.1,mul_one]
 change ‖ni x.1 y.1 A x.2 y.2‖≤_; rw [he,Matrix.mul_assoc,Matrix.mul_apply]; apply (norm_sum_le ..).trans; apply sum_le_sum; intro i _; rw [norm_mul, Matrix.star_apply,norm_star]; refine (mul_le_of_le_one_left (norm_nonneg _) ((norm_entry (R.val) _ _).trans (le_of_eq (CStarRing.norm_of_mem_unitary R.property)))).trans ?_; rw [Matrix.mul_apply]; apply (norm_sum_le ..).trans; apply sum_le_sum; intro j _; rw [norm_mul]; exact (mul_le_of_le_one_right (norm_nonneg _) ((norm_entry S.val _ _).trans_eq (CStarRing.norm_of_mem_unitary S.property))).trans (h ..)
include p hg u w
variable {Vx:ℕ}
def highCreek (v r:ℕ)(d:ℝ):ℝ:= (BPress.Spin.sphereRate*(4*r*(16*(2*(v:ℝ)+1)^5 * (Fintype.card PlaqAxes:ℝ)))/ d)
lemma offer_T (q:dry_E F)(o:Seat n)(r:ℕ)(l:r+1≤ Vx)(b:2*Vx < (More n).val)(s:Lattice.halo Vx {o}⊆ A)(v:pingS P.threshold A U.1)(g:S⊆Lattice.halo r {o})(i j:Single n): ‖uplift F H k ∅ S t U i j‖ ≤ Wloop F S i j*P.threshold* highCreek Vx S.card d:=by
 have ht: Lattice.halo (cipherK k) (∅:Support (More n))⊆ A:=by simp[Lattice.halo]
 have he:nozzle k S ∅ t U.1:=payz p ht hg (by simpa only [sdiff_empty] using v)
 obtain ⟨z,h⟩:=sails (S:=S) u hg w o r l b s v -- order tune
 let C:Pane n:= (H U)
 let R:= uplift F H k ∅ S t U
 let M:= Lattice.gauge z C
 have hu:Guard M d:=(u.paid _).cov z
 let Y:= releaseQ F S M
 have hz: R=ivory F w C (u.paid _) S:=by unfold R uplift; rw[if_pos he,re_L]
 have hq:twist (tradew n z) R=Y:=hz ▸ ((norm_enter (H:=F) S _ (u.paid _) w z).trans (by rw [re_L F _ _ (u.paid _) w])).symm
 let T':= P.threshold*highCreek Vx S.card d; have p0:Guard (1:Pane n) d:=guard0 w.le
 have hW(x y:Single n):‖Y x y‖≤F.W S x y*T':=by
    unfold Y; rw[re_L F _ M hu w]
    have h':= variation_clip (F:=F) (show 0≤ _ from by have hv:=P.threshold_pos; positivity) w _ _ hu p0 S x y (h _ he g)
    rw[show ivory F w 1 p0 S=0 from q S _ rfl,Matrix.zero_apply,sub_zero] at h' -- tune implicit F
    apply h'.trans_eq; unfold T' highCreek; ring
 change ‖R i j‖≤_
 apply (twist_rate (A:=R) (g:=z) (B:=fun i j=> F.W S i j*T') (fun i j=> hq.symm ▸ hW i j) i j).trans_eq
 rw[mul_assoc]; unfold Wloop; simp_rw[sum_mul]; rfl -- tune
omit hg p u w
lemma hefty(F:Elm n Unit d a c): Branch.Ledger a (Wloop F) (Fintype.card SU.Slot*(Fintype.card SU.Slot*c)):=by
 let C₀:= Fintype.card SU.Slot
 have he(i j:Single n): saleM a (Wloop F) i j= ∑ v:SU.Slot,∑ w:SU.Slot, saleM a F.W (i.1,v) (j.1,w):=by
    unfold Wloop saleM; simp_rw [mul_sum]; rw[sum_comm]; refine sum_congr rfl fun v _=>Finset.sum_comm

 constructor
 · exact mul_nonneg (by positivity) (mul_nonneg (by positivity) F.bank.posP)
 · intro i; simp_rw [he]; unfold Single; rw [sum_comm]; apply le_trans (sum_le_sum (g:=fun _=>(C₀:ℝ)* c) ?_); swap
   · intro v w; rw [Fintype.sum_prod_type,sum_comm]; refine le_trans (sum_le_sum (g:=fun _=> c) (fun j _=>?_)) ?_
     · exact by have e:=F.bank.rows (i.1,v); unfold Single at e; rw[Fintype.sum_prod_type] at e; exact e -- tune dependent j not forgotten after sum_comm
     exact le_of_eq (by simp[C₀])
   simp[C₀] -- order.Scalar commute
 intro i; have h(x:Single n): saleM a (Wloop F) x i=∑ w:SU.Slot,∑ v:SU.Slot, saleM a F.W (x.1,v) (i.1,w):= by rw[he,sum_comm]; -- maybe fails pattern
 simp_rw [h]; unfold Single; rw [sum_comm]; apply le_trans (sum_le_sum (g:=fun _=>(C₀:ℝ)* c) ?_); swap
 · intro v w; rw [Fintype.sum_prod_type,sum_comm]; refine le_trans (sum_le_sum (g:=fun _=> c) (fun j _=>?_)) ?_
   · have e:=F.bank.cols (i.1,v); unfold Single at e; rw[Fintype.sum_prod_type] at e; exact e
   exact le_of_eq (by simp[C₀])
 simp[C₀]
#print axioms stern_bill
#print axioms offer_T
end SliceRoof
end YM.CF.Sour
end
