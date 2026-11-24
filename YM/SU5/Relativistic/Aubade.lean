import YM.SU5.Relativistic.Garb
import YM.SU5.Relativistic.Inopportune
import YM.SU5.FiniteGaugeData.Pannier.PaleFace
/-!
# The planes on the Satin calibration. Supports are in COVER and fixed; starG
transport on B from a B vertex, no crossing to A. Column stamps only at large
native sides; normalFamily evaluation at every period regardless. Anchor common
within each baryon. 
-/
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Pannier.Chancel.ScreeV
open Function Filter NormedSpace Metric Lattice Wilson Laurent Finset Cube SU Fock Lat Spire Scroll MeasureTheory ProbabilityTheory Peaks Drapes Rush Tulip Dial Pastry
open Buffered Lifted Afterglow Tapestry Branch Tenant Skye Cliplet RG Brace Crest Crest.Sleet
open Reed (Fine)
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] opCStarAlgebra
variable {n:Side}

-- written on cover: no star sign obligations hidden. gauge anchor u.
abbrev TrackV(u z:Cover):=route u (nodeC z) 1
def viabox (D:Finset Cover)(u:Cover): Finset Cover := D.biUnion (fun z=> (visits u (TrackV u z)).toFinset)
lemma via_ok (u:Cover)(D:Finset Cover)(z:Cover)(p:z∈D) : nodeC z∈ viabox D u:= by
 apply mem_biUnion.mpr; refine ⟨z,p,List.mem_toFinset.mpr ?_⟩; nth_rw 1 [←route_end u (nodeC z) 1]
 apply show ∀ a:Cover, ∀ W:Lattice.Walk, stop a W∈visits a W from ?_
 intro a W; induction W generalizing a <;> simp_all [stop,visits]
lemma via_lim (D:Finset Cover)(u:Cover) (i:Axis)(p q:ℤ) (a:p≤u i)(e:u i≤q)(v:∀ z∈D,p≤(nodeC z) i ∧ (nodeC z) i ≤ q)(x:Cover)(g:x∈ viabox D u): p≤x i ∧ x i ≤ q:=by
 obtain ⟨z,t,l⟩:=mem_biUnion.mp g
 have he:BetweenY u x (nodeC z):= route_end u (nodeC z) 1 ▸ wy u z l -- tune
 obtain ⟨k,m⟩:= v z t; exact ⟨(le_min a k).trans (he.left _),(he.right _).trans (max_le e m)⟩
where wy (u z:Cover){x:Cover}(l:x∈(visits u (TrackV u z)).toFinset):BetweenY u x (stop u (TrackV u z)):= way_visit u _ _ (allAxes 1) ((List.nodup_finRange _).map (Equiv.refl _).injective) x (List.mem_toFinset.mp l) -- syntax

def rayon (K:Calibration)(u z:Cover)(d:Fin 3)(i:SpinIdx)(k:Ring5): Buffered.Family K:=
   ∑ l:Ring5, scalar K ((fun x:LinksC=> cc (fund ((travel x u (TrackV u z))⁻¹)) l k) ∘ Prod.fst) * creation K z i (barred d l)
lemma ray_test (K:Calibration)(S:Finset Cover)(u z:Cover)(l:(visits u (TrackV u z)).toFinset ⊆ S)
    (t:nodeC z∈ S)(d:Fin 3)(i:SpinIdx)(p:i∈plusHalf) (k:Ring5) : InTest K false S true (rayon K u z d i k):=by
 refine InTest.sum _ _ (fun j _=> (InTest.seed (Coeff.fromC false _ ?_ ?_)).mul (.creator _ p t))
 · simp_rw [cc_apply]; exact ((fund_cont.comp (Continuous.inv (Cube.travel_cont u _))).matrix_elem ..).star
 intro x y h; exact congrArg (fun x:SU.E=> cc (fund x⁻¹) j k) (travel_local _ _ x y (fun i hi hv=> h i (l (List.mem_toFinset.mpr hi)) (l (List.mem_toFinset.mpr hv))))
-- transporter covariance. cc(M anchor⁻¹) even at n wrapping
abbrev Cc (v:SU.E): Op Ring5:= cc (fund v)
lemma ccmul (a b:SU.E): Cc (a*b)=Cc a*Cc b:= cc_mul ..
lemma ray_send (K:Calibration)(u z:Cover)(d:Fin 3)(i:SpinIdx)(k:Ring5)(m:Side)(g:Seat (K.c m)→SU.E)(x:Fields (K.c m)):
    rayon K u z d i k m (simultaneous g x)= ∑ l:Ring5, Cc ((g (wrap (More (K.c m)) u))⁻¹) l k • twist (quantU (tradew (K.c m) g)) (rayon K u z d i l m x):=by
 let n:=K.c m; let G:= (wrap (More n)); let y:= travel (onC n x.1) u (TrackV u z)
 let w:=g (G u); let g':=g (G (nodeC z)); let U:= twist (quantU (tradew n g))
 let X(l:Ring5):= create (basisC n z i (barred d l))
 have hs(t:Ring5)(x:Fields n): rayon K u z d i t m x=∑ l:Ring5,Cc ((travel (onC n x.1) u (TrackV u z))⁻¹) l t • X l:=by
    unfold rayon; simp_rw [Finset.sum_apply, Pi.mul_apply]; exact sum_congr rfl fun l _=> by change ((_:ℂ) • (1:FC (Single n)))*X l=_; rw [Algebra.smul_mul_assoc,one_mul]; rfl
 have hx(j:Ring5):U (X j)= ∑ l:Ring5,Cc g' l j • X l:=by
    unfold U X; rw [twist_create,tradeG,map_sum]; exact sum_congr rfl (fun i _=>map_smul ..)
 have hv:travel (onC n (simultaneous g x).1) u (TrackV u z) = w*y*g'⁻¹:=by
    change travel (onC n (Lattice.gauge g x.1)) _ _= _; unfold y onC; rw [travel_at,travel_at,add_zero,travel_gauge, ← wrap_stop_cover,show stop _ (TrackV u z)=_ from route_end u (nodeC z) 1] -- wrap_stop namespace
 have ho (A B:Op Ring5)(i:Ring5): (∑ l:Ring5,B l i • (∑ j:Ring5,A j l • X j))=∑ j:Ring5,(A*B) j i • X j:=by simp_rw [Matrix.mul_apply,Finset.sum_smul,Finset.smul_sum,smul_smul]; rw [sum_comm]; simp_rw [mul_comm]
 rw [hs,hv, show _⁻¹=g'*y⁻¹*w⁻¹ from (show (w*y*g'⁻¹)⁻¹=g'*y⁻¹*w⁻¹ by group),ccmul, ccmul,←ho]
 refine sum_congr rfl fun l _=>?_ ; rw [hs]; congr 1; change _ = U (∑ j:Ring5,(Cc y⁻¹) j l • X j); rw [←ho,map_sum]; apply sum_congr rfl; intro j _; unfold U; rw [twist_scalar,hx] -- tune pp/RHS w

lemma b_up (n:Side)(i:SpinIdx)(p:i∈plusHalf)(u:Cover)(a:SU.Slot): withinM (Tset n) (basisC n u i a):=by unfold withinM basisC; rw [map_smul, within_basis _ (Lifted.index n u i a) ((Window.mem_Tset ..).mpr p)]
lemma b_down (n:Side)(i:SpinIdx)(p:i∉plusHalf)(u:Cover)(a:SU.Slot) : trim (hand true (cutM (Tset n))) (basisC n u i a):=by
 have h: withinM (Tset n)ᶜ (basisC n u i a) := by unfold withinM basisC; rw [map_smul,within_basis _ (Lifted.index n u i a) (mem_compl.mpr (fun w=>p ((Window.mem_Tset ..).mp w)))]
 unfold trim; change acts (1-cutM (Tset n)) _=_; rw [←dim_cut]; exact h
lemma b_broad (n:Side)(u:Cover)(S:Finset Cover)(v:nodeC u∈S)(i:SpinIdx)(a:SU.Slot): withinM (modesIn n (Satin.region S n)) (basisC n u i a):=by
 have he: Lifted.index n u i a∈ modesIn n (Satin.region S n):= (modes_at ..).2 (show node (wrap n u)∈ _ from (by rw [node_of]; exact mem_image_of_mem _ v))
 unfold withinM basisC; rw [map_smul,within_basis _ _ he]
lemma hand_basis (n:Side)(u:Cover)(i:SpinIdx)(a:SU.Slot): cardH false (cutM (Tset n)) (basisC n u i a)= if i∈plusHalf then basisC n u i a else 0:=by
 split_ifs with h; exact b_up n i h u a; let x:=basisC n u i a; have h':acts (1-cutM (Tset n)) x=x:= b_down n i h u a; rw [act_sub,act_one,sub_eq_self] at h'; exact h'
-- actual viewport identity at large host. use K.c
lemma ray_probe (K:Calibration)(u z:Cover)(d:Fin 3)(i:SpinIdx)(k:Ring5)(m:Side)
    (h:march (wrap (More (K.c m)) u) (wrap (More (K.c m)) (nodeC z)) 1 = TrackV u z) (x:Fields (K.c m)):
    rayon K u z d i k m x= create (acts (star (tradew (K.c m) (stampG (wrap (More (K.c m)) u) x.1)).val) (basisC (K.c m) z i (barred d k))):=by
 let n:=K.c m; let g:= stampG (wrap (More n) u) x.1; let Y:=tradew n g; let X(l:Ring5):=basisC n z i (barred d l)
 have he:travel (onC n x.1) u (TrackV u z)= g (wrap (More n) (nodeC z)):=by unfold onC; rw [travel_at,add_zero]; rw [←h]
 have hv: star Y = tradew n g⁻¹ :=by
    have hx : Y * tradew n g⁻¹=1:= (Hive.trade_c g⁻¹ g).trans (by rw [mul_inv_cancel,Hive.trade_p])
    exact mul_left_cancel (show Y*star Y = Y*tradew n g⁻¹ from (mul_inv_cancel Y).trans hx.symm)
 have hx:acts (star Y.val) (X k)=∑ l:Ring5, Cc ((g (wrap (More n) (nodeC z)))⁻¹) l k • X l:= by rw [show star Y.val=(tradew n g⁻¹).val from congrArg Subtype.val hv]; exact tradeG n g⁻¹ z i d k
 change rayon K u z d i k m x = create (acts (star Y.val) (X k)); rw [hx,map_sum]; unfold rayon; simp_rw [Finset.sum_apply,Pi.mul_apply]; apply sum_congr rfl; intro l _
 change (Cc ((travel (onC n x.1) u (TrackV u z))⁻¹) l k • (1:FC (Single n))) *create (X l)=create _; rw [Algebra.smul_mul_assoc,one_mul,map_smul,he]
end YM.CF.Pannier.Chancel.ScreeV
#print axioms YM.CF.Pannier.Chancel.ScreeV.ray_send
#print axioms YM.CF.Pannier.Chancel.ScreeV.ray_probe
