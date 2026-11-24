import YM.SU5.Relativistic.Marquee
import YM.SU5.FiniteGaugeData.Tower.Roomer
/-! # Layout options on cover. Angular clocks later. -/
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Pannier.Chancel.ScreeV
open Function Filter NormedSpace Metric Lattice Wilson Laurent Finset Cube SU Fock Lat Spire Scroll MeasureTheory ProbabilityTheory Peaks Drapes Rush Tulip Dial Pastry
open Buffered Lifted Afterglow Tapestry Branch Tenant Skye Cliplet RG Brace Crest Crest.Sleet Crest.Sleet.UpStart Satin Tower.SlabMark
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] opCStarAlgebra
variable (m:ℕ) {n:Side}
abbrev XGr(m:ℕ):=Fin (m^3)
noncomputable def axesNum : XGr m ≃ (Fin 3→Fin m) := Fintype.equivOfCardEq (by simp [XGr])
variable (d v A:ℕ) -- v≥1, ℓ penalty, A≥ v; d stride
noncomputable def driftV (m:ℕ)(i:XGr m): WalkA:=fun a=> ((axesNum m i a).val:ℤ)
lemma driftV_inj : Injective (driftV m):=by intro x y u; apply (axesNum m).injective; funext a; apply Fin.ext; have he:=congr_fun u a; unfold driftV at he; exact_mod_cast he -- weak
noncomputable def baseX (m d A:ℕ)(i:XGr m):Cover:=tack ((d:ℤ) • driftV m i) (4*(A:ℤ))
lemma base_right (i:XGr m) : nodeC (baseX m d A i) TA=8*(A:ℤ)+1:=by simp [nodeC,baseX]; ring
lemma base_left (i:XGr m)(a:Fin 3):nodeC (baseX m d A i) a.castSucc=2*((d:ℤ)*(driftV m i a))+1 := by simp [nodeC,baseX]
lemma drift_in (i:XGr m)(a:Fin 3): 0 ≤ driftV m i a ∧ driftV m i a < (m:ℤ) := ⟨Nat.cast_nonneg _,by unfold driftV; exact_mod_cast (axesNum m i a).isLt⟩
lemma base_span (i:XGr m)(a:Fin 3): let G:=nodeC (baseX m d A i) a.castSucc ; 1 ≤ G ∧ G≤2*((d:ℤ)*(m:ℤ))+1:=by intro G; unfold G; rw [base_left]; obtain ⟨x,v⟩:= drift_in m i a; refine ⟨by nlinarith only [mul_nonneg (Nat.cast_nonneg (α:=ℤ) d) x],by gcongr⟩ -- tune
lemma spike_grid (i:XGr m) : ∃ f:XGr m→WalkA,f i=0∧∀ z,baseX m d A z=baseX m d A i+tack ((d:ℤ) • f z) 0:=by
 refine ⟨fun z=>driftV m z-driftV m i,sub_self _,?_⟩; intro z; funext j; cases j using Fin.lastCases
 · simp only [baseX, Pi.add_apply, Crest.Sleet.tack, Fin.lastCases_last,add_zero]
 simp [baseX]; ring
lemma diverge (i j:XGr m)(h:i≠j): ∃ a:Fin 3, ((d:ℤ)*2) ≤ |nodeC (baseX m d A i) a.castSucc-nodeC (baseX m d A j) a.castSucc|:=by
 obtain ⟨a,e⟩:= not_forall.mp (show ¬ ∀ a,driftV m i a=driftV m j a from fun p=>h (driftV_inj m (funext p)))
 refine ⟨a,?_⟩; rw [base_left,base_left]; have hv: 1 ≤ |driftV m i a-driftV m j a|:= abs_pos.mpr (sub_ne_zero.mpr e)
 rw [show 2*((d:ℤ)*_)+1 - (2*(↑d*_)+1)=((d:ℤ)*2)*(driftV m i a-driftV m j a) from (by ring),abs_mul,abs_of_nonneg (show 0 ≤ (d:ℤ)*2 by positivity)]; exact le_mul_of_one_le_right (by positivity) hv

def archH (A:ℕ): Cover:= tack (0:WalkA) (10*(A:ℤ)+1)
/-- distinct soil and work: soil is the fermion X+Stencil (also includes spin 2 plane),
 zone for the aperture B excludes plane A. -/
abbrev slit (F:Waxy)(s:Finset ℤ):= (Finset.univ : Finset (XGr m)).biUnion (fun i=> district s (baseX m d A i) F)
def stains (F:Waxy):= Finset.univ.image (baseX m d A)∪ slit m d A F (TwistT A)
abbrev labB(F:Waxy)(s:Finset ℤ):=insert (archH A) (viabox (slit m d A F s) (archH A))
-- tally has local view to each X radius v; these unused extra window costs already purchased.
def loftH (V:ℕ)(F:Waxy):= labB m d A F (TwistT A) ∪ (stains m d A F).image nodeC∪ (Finset.univ : Finset (XGr m)).biUnion fun i=> (box V).image fun z=> z + nodeC (baseX m d A i)
local notation "S♢" r:max F:max=> loftH m d A r F
local notation "T" F:max =>stains m d A F
lemma base_stay (V:ℕ)(F:Waxy)(i:XGr m):baseX m d A i∈ T F∧nodeC (baseX m d A i)∈ S♢ V F:=by
 have ht:baseX m d A i∈ T F:=mem_union_left _ (mem_image_of_mem _ (mem_univ _)); exact ⟨ht,mem_union_left _ (mem_union_right _ (mem_image_of_mem _ ht))⟩
lemma slit_pass (F:Waxy){s:Finset ℤ}(i) : district s (baseX m d A i) F ⊆ slit m d A F s:= fun _ v=> mem_biUnion.mpr ⟨i,mem_univ _,v⟩
lemma via_pass(F:Waxy)(s:Finset ℤ)(i:XGr m): viabox (district s (baseX m d A i) F) (archH A) ⊆ labB m d A F s:=by
 intro x p; obtain ⟨y,h,t⟩:=mem_biUnion.mp p; exact mem_insert_of_mem (mem_biUnion.mpr ⟨y,slit_pass m d A F i h,t⟩)
lemma span_soil {V:ℕ}(F:Waxy) (x:Cover)(p:x∈ T F): nodeC x∈ S♢ V F:=mem_union_left _ (mem_union_right _ (mem_image_of_mem _ p))
lemma via_fur (V:ℕ)(F:Waxy)(s:Finset ℤ) (p:s⊆ TwistT A): labB m d A F s⊆ S♢ V F:=by
 intro x v; apply mem_union_left; apply mem_union_left; rcases mem_insert.mp v with v|v; exact v.symm ▸ mem_insert_self ..
 apply mem_insert_of_mem; obtain ⟨y,g,w⟩:= mem_biUnion.mp v; apply mem_biUnion.mpr; refine ⟨_,?_,w⟩; obtain ⟨i,_,h⟩:=mem_biUnion.mp g; apply slit_pass _ _ _ _ i; obtain ⟨j,_,d⟩:=mem_biUnion.mp h; obtain ⟨k,m,n⟩:= mem_biUnion.mp d; exact mem_biUnion.mpr ⟨j,mem_univ _, mem_biUnion.mpr ⟨k,p m,n⟩⟩ -- index change not mono
-- horizon tall bill elliptic
lemma sthickness (F:Waxy)(q:ℤ)(s:Finset ℤ)(p:∀ v∈s,q≤v)(h:s⊆ TwistT A)(x:Cover)(v: x∈slit m d A F s) :8*(A:ℤ)+1+2*q ≤ nodeC x TA∧ nodeC x TA≤10*(A:ℤ)+1:=by
 obtain ⟨i,_,h'⟩:=mem_biUnion.mp v; obtain ⟨a,_,l⟩:=mem_biUnion.mp h'; obtain ⟨j,t,k⟩:=mem_biUnion.mp l; obtain ⟨y,g,rfl⟩:=mem_image.mp k; obtain ⟨_,t₀⟩:= mem_Icc.mp (h t); have ht:=p j t; simp [nodeC,baseX]; omega
lemma withheld (F:Waxy)(q:ℤ)(s:Finset ℤ)(e:q ≤ (A:ℤ))(p:∀ v∈s,q≤ v)(h:s⊆ TwistT A)(x:Cover)(v:x∈ labB m d A F s) : 8*(A:ℤ)+1+2*q≤ x TA ∧ x TA≤10*(A:ℤ)+1:=by
 have ht: archH A TA=10*(A:ℤ)+1:= by simp [archH]
 have hv:8*(A:ℤ)+1+2*q≤ archH A TA := by rw [ht]; omega
 rcases mem_insert.mp v with v|v; subst x; exact ⟨hv,ht.le⟩
 exact via_lim _ _ _ _ _ hv ht.le (sthickness m d A F q s p h) x v
abbrev heightB (A:ℕ) := 12*(A+1)
lemma within_r (V:ℕ)(F:Waxy)(p:V≤ A)(K:Calibration)(h:K.ℓ≤A) : Tower.SlabMark.Between K TA 0 (ruler K.B*(heightB A)) (S♢ V F):=by
 intro x v; have hr:1≤ ruler K.B:=ruler_gene _; suffices hx: 6*(A:ℤ) ≤ x TA ∧ x TA≤ 10*(A:ℤ)+1 by
    unfold heightB; push_cast; have ht:= (mul_le_mul_of_nonneg_right hr (by positivity : 0 ≤ (12:ℤ)*((A:ℤ)+1))); omega -- multiplication coefficient via omega & one_mul
 rcases mem_union.mp v with u|u
 · rcases mem_union.mp u with v|v
   · obtain ⟨g,e⟩:= withheld m d A F (-(A:ℤ)) (TwistT A) (by omega) (fun _ h=>(mem_Icc.mp h).1) (subset_refl _) _ v; exact ⟨by omega,e⟩
   obtain ⟨z,p,rfl⟩:=mem_image.mp v; rcases mem_union.mp p with v|v
   · obtain ⟨i,_,rfl⟩:= mem_image.mp v; rw [base_right]; omega
   obtain ⟨g,e⟩:= sthickness m d A F (-(A:ℤ)) _ (fun _ h=>(mem_Icc.mp h).1) (subset_refl _) _ v; exact ⟨by omega,e⟩
 obtain ⟨i,_,t⟩:=mem_biUnion.mp u; obtain ⟨x,hx,rfl⟩:=mem_image.mp t; obtain ⟨e,g⟩:=box_test.mp hx; specialize e TA; specialize g TA; change 6*_ ≤ x TA + _ ∧ x TA+_ ≤ _; rw [base_right]; omega
end YM.CF.Pannier.Chancel.ScreeV
