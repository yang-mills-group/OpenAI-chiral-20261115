import YM.SU5.Relativistic.Velith
import YM.CF.Fixed.Triangular
import YM.SectorNext.GAUSSIAN_SECTOR_CHANGE.Ledger
import YM.CF.BProof.Charge.Lamp
/-! # local tile pack. good branch Haar charge. -/
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 600000
noncomputable section
namespace YM.CF.Papyrus.Mosaic
open Function Finset Filter MeasureTheory Lattice Wilson Fixed.Pivots Precision RG Work.F03
open Next.SectorChange
open scoped Matrix BigOperators Topology ContDiff Matrix.Norms.Frobenius InnerProductSpace
variable (G : Gauge){W : Side}
local notation "X"=> Config G W
local notation "H"=> Face (Per W)
local notation "ι"=> livelies W
local notation "F"=> Lo W
local notation "Y"=> F→ G.El

private def orientF (U:X)(x:Site W):G.El:= if p:x=0 then 1 else let y:=parentLink x p; orientF U y.1 * U y
termination_by originSum x
decreasing_by exact Nat.lt_of_succ_le (reduced x (gapAxis x p) (gapAxis_nonzero _ _)).le
private lemma founded (U:X)(i: Link W)(h:Tree i): Lattice.gauge (orientF G U) U i=1:=by
 have hx:orientF G U (reach i)=orientF G U i.1*U i:=by conv_lhs=> rw [orientF,dif_neg (reach_tree i h),tree_reduces i h];
 unfold Lattice.gauge; rw [show _ + _=reach i from rfl,hx]; simp
private lemma ort_meas (p:Site W): Continuous (fun U:X=>orientF G U p):=by
 suffices v:∀ k:ℕ,∀ p:Site W,originSum p=k→ Continuous (fun U:X=> orientF G U p) by exact v _ _ rfl
 intro k; induction k using Nat.strong_induction_on with
 | h k ih=>
    intro p v; by_cases h:p=0; · subst p; rw [show (fun U:X=> orientF G U 0)=(fun _ => 1) from funext fun i=>by rw [orientF,dif_pos rfl]]; exact continuous_const -- danger loop simp
    let q:=parentLink p h; have ht:originSum q.1<k:= v ▸ Nat.lt_of_succ_le (reduced p (gapAxis p h) (gapAxis_nonzero _ _)).le; rw [show (fun U:X=>orientF G U p)=(fun U=> orientF G U q.1*U q) from funext fun i=>by rw [orientF,dif_neg h]]; exact (ih _ ht _ rfl).mul (continuous_apply q)
private lemma upright (p:X)(j:Link W)(g:j∈ι)(s:G.El) : orientF G (update p j s)=orientF G p:=by
 suffices v:∀ k:ℕ,∀ x:Site W,originSum x=k→ orientF G (update p j s) x=orientF G p x by exact funext fun x=> v _ _ rfl
 intro k; induction k using Nat.strong_induction_on with
 | h k ih=>
    intro x v; by_cases h:x=0; · rw [orientF,orientF,dif_pos h,dif_pos h]
    rw [orientF,orientF,dif_neg h,dif_neg h]; dsimp only; let y:=parentLink x h
    have hx:originSum y.1<k:=v ▸ Nat.lt_of_succ_le (reduced x (gapAxis x h) (gapAxis_nonzero _ _)).le
    rw [update_of_ne (show parentLink x h≠ j from fun e=>(mem_filter.mp (mem_filter.mp g).1).2.1 (e ▸ tree_is x h)), ih _ hx _ rfl] -- tune rw nesting

def layOut(p:Y)(a:Link W):G.El:=if h:a∈ι then p ⟨a,h⟩ else 1
def envoi (U:X)(i:F): G.El:= Lattice.gauge (orientF G U) U i
lemma lay_c : Continuous (layOut G (W:=W)):=by
 apply continuous_pi; intro i; unfold layOut; by_cases p:i∈ι; · simp only [dif_pos p]; apply continuous_apply
 simp only [dif_neg p]; exact continuous_const
lemma envoy :MeasurePreserving (envoi G (W:=W)) (prior G W) (piHaar G F):=by
 let S:= ι; let f(i:Link W)(U:X):= Lattice.gauge (orientF G U) U i
 let q:=fun x:X=>Fixed.Pivots.batch S f x
 have hp:MeasurePreserving q (prior G W) (prior G W):=by
    apply batch_preserves _ _ f (fun i _=> (((ort_meas G i.1).mul (continuous_apply i)).mul (ort_meas G (reach i)).inv).measurable) (fun _=>0)
    · intro i hi j hj _ he u v; unfold f Lattice.gauge; rw [upright G _ _ hi,update_of_ne he.symm]
    intro i hi x; unfold f Lattice.gauge; simp_rw [upright G _ i hi,update_self]; apply G.preserve_two_sided
 let p:=fun x:X=>fun i:F=>x i
 have he:MeasurePreserving p (prior G W) (piHaar G F):= by unfold piHaar; convert! measurePreserving_fst.comp (measurePreserving_piEquivPiSubtypeProd (fun _=> G.probHaar) (fun i:Link W=>i∈S)) using 1; congr 1; exact Subsingleton.elim .. 
 rw [show envoi G (W:=W)= p ∘ q from ?_]; · exact he.comp hp
 funext x i; unfold p q Function.comp; dsimp only [Fixed.Pivots.batch]; rw [if_pos i.property]; rfl

abbrev girth (U:X)(i:H):= G.chord (faceValue U i)
def crateB(U:X):= ∑ i∈ort W,girth G U i^2
lemma lengthsF (u:Y){s:ℝ}(hs:0≤ s)(h:∀ i∈ort W,girth G (layOut G u) i ≤ s)(i:F): G.chord (u i) ≤ (limit W :ℕ)*s:=by
 let U:=layOut G u
 have hp(q:Link W)(p:q∈ι):U q=u ⟨q,p⟩:=dif_pos p
 have ht(q:Link W)(g:Tree q):U q=1:=dif_neg (fun w=>(mem_filter.mp (mem_filter.mp w).1).2.1 g)
 have hv(k:ℕ):∀ i:Link W, originSum i.1=k→ indoors i→ G.chord (U i)≤ k*s:=by
    induction k using Nat.strong_induction_on with
    | h k ih=>
      intro i hi w; by_cases v:Tree i; · rw [ht _ v]; simpa using (show 0 ≤ k*s from by positivity)
      have g:Active i:= (indoors_m i w).2 v; have hl:=h _ (mark_ort i w g); obtain ⟨x,j⟩:=i
      let y:= tooth (x,j) g; let a:= x-step y; have he:y<j:=live_mark w g; obtain ⟨r,t,u⟩:=live_pins x j w g; have hz: originSum a+1=k:= (reduced x y (tooth_spec _ g).2.1).trans hi; let z:= originSum a
      have hm:= ih z (by unfold z; omega) (a,j) rfl u; let P:= mark (x,j) g
      have hx: U (x,j)=faceValue U P*U (a,j):=by
         unfold faceValue P mark PlaqAxes.ordered; change U (x,j)= travel U a (square (min j y) (max j y))* _; rw [min_eq_right he.le,max_eq_left he.le,square_formula,ht _ (show Tree (a,y) from r),ht _ (show Tree (a+step j,y) from t),show a+step y=x from sub_add_cancel ..]; group
      rw [hx]; exact (G.chord_triangle ..).trans ((add_le_add (show girth G U P≤ s from hl) hm).trans_eq (by rw [← hz,Nat.cast_add,Nat.cast_one]; unfold z; ring))
 rw [show u i=U i from (hp _ i.property).symm]; exact (hv (originSum i.val.1) i rfl (mem_filter.mp i.property).2).trans (mul_le_mul_of_nonneg_right (by exact_mod_cast (origin_lt_w i.val.1).le) hs)

variable (V:PathData G)(D:ℕ){σ A Λ:ℝ}{p:Clip}
def boxE (p:Clip)(U:X):= p.direct*crateB G U+∑ i∈plumb W D, ‖Pressure.shorten V D 1 U i‖^2
lemma box_pos (U:X): 0≤ boxE G V D p U:= add_nonneg (mul_nonneg p.quadratic_pos.le (sum_nonneg fun _ _=>sq_nonneg _)) (sum_nonneg fun _ _=>sq_nonneg _)
def Mild (W:Side)(G:Gauge)(t:ℝ): Set (Config G W):={x|∀ i∈ort W,girth G x i≤t} -- W_ capture? no
lemma mild_close (W:Side)(t:ℝ): IsClosed (Mild W G t):=by unfold Mild; simp only [Set.setOf_forall]; apply isClosed_iInter; intro i; apply isClosed_iInter; intro _; exact isClosed_le (by unfold girth faceValue; fun_prop) continuous_const
variable (B:V.Bounds p σ A Λ)
include B
lemma box_c: Continuous (boxE (W:=W) G V D p) := by
 unfold boxE crateB; exact (continuous_const.mul (continuous_finsetSum _ (fun i _=>by unfold girth faceValue; fun_prop))).add (continuous_finsetSum _ fun i _=> ((BProof.Charge.shorten_c p V D B i).norm).pow _)
open scoped Classical
lemma alongF (U:X) (t:ℝ) : boxE G V D p U=boxE G V D p (layOut G (envoi G U))∧ (U∈ Mild W G t ↔ layOut G (envoi G U)∈ Mild W G t):=by
 let Z:= Lattice.gauge (orientF G U) U; let Y':=layOut G (envoi G U)
 have hp(a:Link W)(v:indoors a):Z a=Y' a:=by
    by_cases h:Tree a; · rw [show Z a=1 from founded G U a h]; have h':a∉ι:=fun w=>(mem_filter.mp (mem_filter.mp w).1).2.1 h; unfold Y' layOut; rw [dif_neg h'] -- (dif_neg (fun t=> (mem_filter.mp (mem_filter.mp t).1).2.1 h)).symm
    have he:a∈ι:=mem_filter.mpr ⟨mem_filter.mpr ⟨mem_univ _, (indoors_m _ v).2 h⟩,v⟩; exact (show Y' a=(envoi G U) ⟨_,he⟩ from dif_pos he).symm
 have hv(i:H)(k:i∈ort W): girth G U i= girth G Y' i:=by
    rw [show girth G U i=girth G Z i by simp [girth,Z]]; unfold girth; rw [face_unique G Z Y' i (fun b h=>hp b (here_in _ (mem_filter.mp k).2 _ h))]
 have hf(i:H)(k:i∈plumb W D): ‖Pressure.shorten V D 1 U i‖ = ‖Pressure.shorten V D 1 Y' i‖:=by
    rw [←small_g Z Y' i D ((mem_filter.mp k).2) hp V, show Z= _ from (show Z=Lattice.gauge (orientF G U) U from rfl), BProof.Charge.shorten_gauge p V D U B, G.norm_adjoint]
 constructor
 · unfold boxE; rw [show crateB G U=crateB G Y' from sum_congr rfl (fun i k=>congrArg (·^2) (hv i k))]; exact congrArg (p.direct*crateB G Y'+·) (sum_congr rfl fun i k=> congrArg (·^2) (hf i k))
 refine ⟨fun e i k=>?_ ,fun e i k=>?_⟩; · rw [← hv i k]; exact e i k
 rw [hv i k]; exact e i k

def localPay (p:Clip)(t a:ℝ): X→ℝ:= (Mild W G t).indicator (fun x:X=> Real.exp (-a*boxE G V D p x/2))
lemma local_meas (t a:ℝ): Measurable (localPay (W:=W) G V D p t a) := ((by
 have ht:=box_c G V D B (W:=W); fun_prop) : Continuous (fun x:X=> Real.exp (-a*boxE G V D p x/2))).measurable.indicator (mild_close .. |>.measurableSet)
lemma local_tariff (t a:ℝ) : ∫ x:X, localPay G V D p t a x ∂prior G W = ∫ x:Y,localPay G V D p t a (layOut G x) ∂piHaar G F:=by
 let f(x:Y):=localPay G V D p t a (layOut G x); have he : localPay (W:=W) G V D p t a=f ∘ envoi G:=by
    funext x; obtain ⟨g,h⟩:=alongF G V D B x t; change localPay .. = localPay _ _ _ _ _ _ _; unfold localPay; by_cases v:x∈Mild W G t; · rw [Set.indicator_of_mem v,Set.indicator_of_mem (h.mp v), g]
    rw [Set.indicator_of_notMem v,Set.indicator_of_notMem (mt h.mpr v)]
 have hp:=envoy G (W:=W); change (∫ x:X,_∂prior G W)=(∫ x,f x∂piHaar G F); rw [he,←hp.map_eq]; exact (integral_map (f:=f) hp.aemeasurable ((local_meas G V D B t a|>.comp (lay_c G).measurable).aestronglyMeasurable)).symm
end YM.CF.Papyrus.Mosaic
#print axioms YM.CF.Papyrus.Mosaic.local_tariff
