import YM.SU5.Relativistic.Aubade
/-!
# Calibrated objects f:Neutral and special form.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Pannier.Chancel.ScreeV
open Function Filter NormedSpace Metric Lattice Wilson Laurent Finset Cube SU Fock Lat Spire Scroll MeasureTheory ProbabilityTheory Peaks Drapes Rush Tulip Dial Pastry
open Buffered Lifted Afterglow Tapestry Branch Tenant Skye Cliplet RG Brace Crest Crest.Sleet Crest.Sleet.UpStart
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] opCStarAlgebra
variable {n:Side}(K:Calibration)
variable (u o:Cover)(F:Waxy)(A:ℕ)(d:Fin 3)
abbrev B₅(k:Ring5)(j:ℤ)(i:SpinIdx)(x:WalkA):=rayon K u (o+tack x j) d i k
-- stencil aggregation, overlap allowed
noncomputable def august (k:Ring5) : Buffered.Family K:=
   ∑ i∈plusHalf,∑ j∈ TwistT A,∑ l∈ (F i j).support, (F i j l) • B₅ K u o d k j i l
local notation "v" => august K u o F A d
lemma augustT (s:Finset ℤ)(h:∀ i∈plusHalf,∀ j:ℤ,j∉s→ F i j=0)(k:Ring5) : InTest K false (viabox (district s o F) u) true (v k):=by
 refine InTest.sum _ _ (fun i w=> InTest.sum _ _ (fun j p=> InTest.sum _ _ (fun l e=>.smul _ ?_)))
 have hv:o+tack l j∈ district s o F:=drive_entry o F i _ j (by by_contra w₀; rw [h i w j w₀] at e; simp at e) l e
 exact ray_test K _ u _ (fun a q=>mem_biUnion.mpr ⟨_,hv,q⟩) (via_ok _ _ _ hv) d i w k -- tune dots

private lemma YesSum {α I:Type*}[LinearOrder I][Fintype I] (l:Finset α) (f:α→FC I) (b:∀ i∈l,Marque false (f i)) : Marque false (∑ i∈l,f i):=by
 classical
 induction l using Finset.induction_on with
 | empty=> exact ⟨0,by unfold creed; simp⟩
 | insert i l p ih=> rw [sum_insert p]; obtain ⟨x,hx⟩:= b _ (mem_insert_self ..); obtain ⟨y,hy⟩:=ih fun a w=>b _ (mem_insert_of_mem w); exact ⟨x+y,by rw [hx,hy]; exact (map_add create ..).symm⟩
private lemma YesScalar {I:Type*}[LinearOrder I][Fintype I] (z:ℂ){F:FC I}(h:Marque false F):Marque false (z • F):=by obtain ⟨x,u⟩:=h; exact ⟨z • x,by rw [u]; exact (map_smul create ..).symm⟩
lemma august_yes (k:Ring5)(m:Side)(x:Fields (K.c m)): Marque false (august K u o F A d k m x):=by
 unfold august; simp_rw [Finset.sum_apply,Pi.smul_apply]; refine YesSum _ _ (fun i _=>YesSum _ _ (fun j _=>YesSum _ _ (fun l _=>YesScalar _ ?_)))
 unfold B₅ rayon; simp_rw [Finset.sum_apply,Pi.mul_apply]; apply YesSum _ _; intro a _; unfold scalar creation; rw [Algebra.smul_mul_assoc,one_mul]; exact YesScalar _ ⟨_,rfl⟩
lemma autumn (k:Ring5)(m:Side)(x:Fields (K.c m))(g: Seat (K.c m)→SU.E):
    v k m (simultaneous g x) = ∑ l:Ring5,Cc ((g (wrap (More (K.c m)) u))⁻¹) l k • twist (quantU (tradew (K.c m) g)) (v l m x):=by
 unfold august; let N:=K.c m
 simp_rw [Finset.sum_apply,Pi.smul_apply,map_sum,Finset.smul_sum]
 conv_rhs =>rw [sum_comm]
 apply sum_congr rfl; intro i w
 conv_rhs=>rw [sum_comm]
 apply sum_congr rfl; intro j p
 conv_rhs=>rw [sum_comm]
 apply sum_congr rfl; intro l h; unfold B₅; rw [ray_send, Finset.smul_sum]; exact sum_congr rfl (fun c _=> by rw [twist_scalar,smul_comm (F i j l)])
lemma august_probe (m:Side)(k:Ring5)(h:∀ z∈district (TwistT A) o F,march (wrap (More (K.c m)) u) (wrap (More (K.c m)) (nodeC z)) 1= TrackV u z)
    (x:Fields (K.c m)):
    v k m x=create (acts (star (tradew (K.c m) (stampG (wrap (More (K.c m)) u) x.1)).val) (cardH false (cutM (Tset (K.c m))) (strum (K.c m) o A F (barred d k)))):=by
 unfold august strum gust; let n:=K.c m
 simp_rw [Finsupp.sum,cardH,map_sum,map_smul, Finset.sum_apply,Pi.smul_apply]; symm; refine (sum_subset (subset_univ plusHalf) ?_).symm.trans ?_; swap
 · apply sum_congr rfl; intro i w; refine sum_congr rfl (fun j p=> sum_congr rfl (fun l u'=>?_))
   rw [show acts (hand false (cutM (Tset n))) (basisC n (o+tack l j) i (barred d k)) = _ from b_up n i w (o+tack l j) (barred d k)]; exact congrArg ((F i j l) • ·) (Eq.symm (ray_probe K u (o+tack l j) d i k m (h _ (drive_entry o F i _ j p l u')) x))
 intro i w g; refine sum_eq_zero (fun j p=> sum_eq_zero (fun l w₀=> ?_)); rw [show acts (hand false (cutM (Tset n))) (basisC n (o+tack l j) i (barred d k)) = 0 from (hand_basis n (o+tack l j) i (barred d k)).trans (if_neg g),map_zero,map_zero,smul_zero]

abbrev boundV(K:Calibration)(F:Ring5→Buffered.Family K): Buffered.Family K:= (List.ofFn F).prod
lemma bind_v (L:Side)(X:Ring5→ Buffered.Family K)(x: Fields (K.c L)): boundV K X L x=(List.ofFn (fun i=> X i L x)).prod:=by
 let U:= List.ofFn (@id Ring5); have he(V:List Ring5): ((V.map X).prod L x) = (V.map (fun i=> X i L x)).prod:=by induction V with|nil=> rfl | cons z V h=> rw [List.map_cons,List.map_cons,List.prod_cons,List.prod_cons,Pi.mul_apply,Pi.mul_apply,h]
 have hv:= he U; unfold U at hv; simp_rw [List.map_ofFn] at hv; exact hv
lemma bind_T {S:Finset Cover}{F:Ring5→Buffered.Family K}(p:∀ i,InTest K false S true (F i)): InTest K false S true (boundV K F):=by
 unfold boundV; rw [show List.ofFn F=[F 0,F 1,F 2,F 3,F 4] from ?_]; swap; · simp -- tune
 exact (p 0).mul ((p 1).mul ((p 2).mul ((p 3).mul ((p 4).mul (.one)))))
abbrev glebe := boundV K (v)
abbrev swell(k:Ring5):= removal K o 2 (barred d k)
abbrev gyre:=boundV K (swell K o d)
lemma glebe_T(s:Finset ℤ)(h:∀ i∈plusHalf,∀ j:ℤ,j∉s→ F i j=0) : InTest K false (viabox (district s o F) u) true (glebe K u o F A d):= bind_T K (fun _=>augustT K u o F A d s h _) -- syntax
lemma gyre_T : InTest K false {nodeC o} true (gyre K o d):= bind_T K (F:=swell K o d) (fun i=> .remover _ (by decide) (mem_singleton_self _))
lemma gyre_N : Neutral K (gyre K o d):=by
 intro n g x; unfold gyre; rw [bind_v,bind_v,map_list_prod, List.map_ofFn]; change _=(List.ofFn _).prod; symm; apply Eq.trans _ (fixF (K.c n) g o 2 d); congr 2; funext a; exact twist_remove ..
lemma glebe_N: Neutral K (glebe K u o F A d):=by
 classical
 intro m g x; let f:= simultaneous g x; let T:= quantU (tradew (K.c m) g); let G₀:= (Cc ((g (wrap (More (K.c m)) u))⁻¹)); let Q:=fun i=> v i
 choose X H using (fun i=>august_yes K u o F A d i m x); choose Z h using (fun i=>august_yes K u o F A d i m f)
 let x'(i):=acts (tradew (K.c m) g).val (X i)
 have hp(i): twist T (Q i m x)=creed false (x' i):= by rw [show Q i m x= _ from H i]; exact twist_create ..
 have hx:G₀.det=1:=by unfold G₀ Cc cc; rw [Matrix.det_transpose,Matrix.star_eq_conjTranspose,Matrix.det_conjTranspose, fund_det]; simp
 have hf := (enseal false x' Z G₀ hx (fun i=> by rw [← h,autumn K u o F A d i m x g]; exact sum_congr rfl fun j _=> congrArg (_ • ·) (hp j))).symm
 unfold glebe; rw [bind_v,bind_v,map_list_prod,List.map_ofFn]; change (List.ofFn (fun i=>v i m f)).prod=(List.ofFn (fun i=> twist T (Q i m x))).prod; simp_rw [hp,h]; exact hf
-- obey payment broad mark
end YM.CF.Pannier.Chancel.ScreeV
#print axioms YM.CF.Pannier.Chancel.ScreeV.glebe_N
#print axioms YM.CF.Pannier.Chancel.ScreeV.august_probe
