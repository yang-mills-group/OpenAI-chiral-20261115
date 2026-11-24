import YM.SU5.Relativistic.Razor
import YM.SectorNext.GAUSSIAN_SECTOR_CHANGE.Gaussian
/-! # axial precision. positivity and Gaussian units; determinant monotonicity pulled from Gaussian densities. -/
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 600000
noncomputable section
namespace YM.CF.Papyrus.GaugeFlux
open Function Finset Filter MeasureTheory Lattice Wilson RG Precision Exterior MinorPins Tree Matrix Bid Laurent
open scoped Matrix BigOperators Matrix.Norms.Frobenius InnerProductSpace ContDiff
variable {N:Side}(G:Gauge)(B:Bed)
open Work.F03
section quadratic
variable {ι : Type}[Fintype ι][DecidableEq ι] {P Q:Matrix ι ι ℝ}
open Next.SectorChange Next.SectorChange.Gaussian
def coldFee (P:Matrix ι ι ℝ)(x:ι→ℝ):ℝ:=Real.exp (-(dotProduct x (P*ᵥ x))/2)
lemma gram_p (h:P.PosDef) : Integrable (coldFee P)∧ (∫ x,coldFee P x) = dome ι / Real.sqrt P.det := by
 have he:= under_cloud (C:=P⁻¹) (h.inv : P⁻¹.PosDef) (coldFee P)
 have hh(x : Gaussian.Vec ι): force P⁻¹ x=dotProduct x (P*ᵥ x):=by unfold force; rw [nonsing_inv_nonsing_inv]; exact isUnit_iff_ne_zero.mpr h.det_pos.ne'
 dsimp only at he; rw [show (fun x : Gaussian.Vec ι=> Real.exp (force P⁻¹ x/2) • coldFee P x)=(fun _ => (1:ℝ)) by funext x; rw [hh]; unfold coldFee; rw [smul_eq_mul, ←Real.exp_add,neg_div, add_neg_cancel,Real.exp_zero]] at he
 refine ⟨he.1.mpr (integrable_const _), he.2.trans ?_⟩
 rw [integral_const,probReal_univ,one_smul,smul_eq_mul,mul_one]; unfold coat; rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv,Real.sqrt_inv]; simp [div_eq_mul_inv]
lemma det_hike (p:P.PosDef)(q:Q.PosDef)(h:∀ x:ι→ℝ,dotProduct x (P *ᵥ x)≤ dotProduct x (Q *ᵥ x)) : P.det ≤ Q.det:=by
 obtain ⟨ht,x⟩:= gram_p p; obtain ⟨hv,y⟩:= gram_p q; have hp:= integral_mono hv ht (fun i=> Real.exp_monotone (div_le_div_of_nonneg_right (neg_le_neg (h i)) zero_le_two))
 rw [x,y] at hp; apply (Real.sqrt_le_sqrt_iff q.det_pos.le).mp; have h0:=(div_le_div_iff₀ (Real.sqrt_pos.mpr q.det_pos) (Real.sqrt_pos.mpr p.det_pos)).mp hp; exact le_of_mul_le_mul_left h0 dome_pos
-- packaging
lemma psd {P:Matrix ι ι ℝ}(h:P.transpose=P)(t:∀ x:ι→ℝ,x≠0→ 0<dotProduct x (P*ᵥ x)): P.PosDef :=by
 apply Matrix.PosDef.of_dotProduct_mulVec_pos ?_ ?_
 · exact Matrix.isHermitian_iff_isSymm.mpr h
 simpa using t
lemma obtain_f (p:P.PosDef)(q:Q.transpose=Q)(h:∀ x:ι→ℝ,dotProduct x (P *ᵥ x)≤ dotProduct x (Q*ᵥ x)):
 Q.PosDef ∧ P.det ≤ Q.det:=by
 have ht:= psd q (fun x t=> (show 0<dotProduct x (P*ᵥ x) from by simpa using p.dotProduct_mulVec_pos t).trans_le (h x))
 exact ⟨ht,det_hike p ht h⟩
end quadratic
open Fixed.Pivots (pivots mark originSum Active mark_inj mark_roll behind)
local notation "R_"=> ScrollB G N
local notation "c"=> fast G N
local notation "A"=> smear (fast G N)
lemma block_guard {κ:Clip}{x y:ℝ}(h:Floor B κ N x y): Matrix.IsSymm (blockD G B N):=by unfold Matrix.IsSymm blockD; rw [Matrix.transpose_submatrix, hess_symm G B h]
private lemma crest (i:ScrollB G N): Fixed.Pivots.Active i.val.1:= (mem_filter.mp ((mem_product.mp i.property).1)).2
private def tube (G:Gauge)(N:Side) (i:ScrollB G N) := (mark i.val.1 (crest G i),i.val.2)
private lemma tube_inj (G:Gauge)(N:Side) : Injective (tube G N):= fun i j e=> Subtype.ext (Prod.ext (Fixed.Pivots.mark_inj _ _ _ _ (congrArg Prod.fst e)) (show i.val.2=j.val.2 from (show (tube G N i).2=(tube G N j).2 from congrArg Prod.snd e)))
private def draw : (ScrollB G N →ℝ)→ₗ[ℝ](ScrollB G N→ℝ) where
 toFun x i:= Curl (fun p=> (A *ᵥ x) (p,i.val.2)) (tube G N i).1
 map_add' x y:=by funext i; unfold Curl; simp only [Matrix.mulVec_add,Pi.add_apply]; abel
 map_smul' t x:=by funext i; unfold Curl; simp only [Matrix.mulVec_smul,Pi.smul_apply,RingHom.id_apply,smul_eq_mul]; ring
local notation "M_" => LinearMap.toMatrix' (draw G (N:=N))
private lemma almost_e(i:R_)(x:R_→ℝ): (M_ *ᵥ x) i=Curl (fun p=> (A *ᵥ x) (p,i.val.2)) (tube G N i).1:=by rw [LinearMap.toMatrix'_mulVec]; rfl
private lemma xProbe(i:R_)(x:R_→ℝ): (A*ᵥ x) i=x i:=smear_t (e:=c) x i
private lemma xZero(i:Bond N)(j:G.ColorIndex)(h:¬Fixed.Pivots.Active i)(x:R_→ℝ): (smear (fast G N)*ᵥ x) (i,j)=0:=by
 apply smear_f; rintro ⟨y,p⟩; apply h; exact (show y.val.1= i from congrArg Prod.fst p) ▸ crest G y
-- if M*x=0 then X=0 by EXACT paid plaquettes. Don't need triangular rank estimate globally.
lemma process (p:2 ≤ N.val) (x:R_→ℝ)(h:M_ *ᵥ x=0):x=0:=by
 let Y:= A *ᵥ x
 have he(k:ℕ):∀ i:ScrollB G N,originSum i.val.1.1=k→ x i=0:=by
    induction k using Nat.strong_induction_on with
    | h k ih =>
      rintro ⟨⟨⟨a,b⟩,j⟩,e⟩ v; let i:R_:= ⟨((a,b),j),e⟩; have H:Active (N:=N) (a,b):=crest G i -- ambient
      let s:=Fixed.Pivots.tooth (a,b) H; let u:= a-step s; have hx:s≠b:=(Fixed.Pivots.tooth_spec _ H).1; set Ω:=Fixed.Pivots.support (mark (a,b) H)
      have hv(Gi:Bond N)(x':Gi ∈ Fixed.Pivots.window u b s)(ht:Gi≠ (a,b)):Y (Gi,j)=0:=by
         by_cases ht':Fixed.Pivots.Active Gi; · let l:ScrollB G N:=⟨(Gi,j),mem_product.mpr ⟨mem_filter.mpr ⟨mem_univ _,ht'⟩, mem_univ _⟩⟩; have he:originSum Gi.1<k:= v ▸ behind _ H Gi ht' ((Fixed.Pivots.mark_window a b H).symm ▸ x') ht; exact (xProbe G l x).trans (ih _ he l rfl)
         exact xZero G Gi j ht' _
      have hu:u+step s=a:=sub_add_cancel ..; have hX:u≠a:=by intro g; rw [g] at hu; have he:= congrFun hu s; simp at he; have k:= congrArg ZMod.val he; rw [ZMod.val_one_eq_one_mod,Nat.mod_eq_of_lt (by omega)] at k; simp at k
      have hM:= congrFun h i; rw [almost_e] at hM; change Curl (fun l=>Y (l,j)) (u,⟨(min b s,max b s),_⟩)=0 at hM; unfold Curl at hM; simp only at hM -- tune
      have hr:=hv (u,b) (by simp [Fixed.Pivots.window]) (fun x=> hX (congrArg Prod.fst x)); have hq:=hv (u,s) (by simp [Fixed.Pivots.window]) (fun x=> hx (congrArg Prod.snd x)); have hz:=hv (u+step b,s) (by simp [Fixed.Pivots.window]) (fun x=> hx (congrArg Prod.snd x)); have hw:Y ((a,b),j)=x i:=xProbe G i x
      change x i=0; rcases le_total b s with l|l
      · rw [min_eq_left l,max_eq_right l,hr,hq,hz,hu,hw] at hM; simpa using hM
      rw [min_eq_right l,max_eq_left l,hr,hq,hz,hu,hw] at hM; simpa using hM
 exact funext fun i=>he _ i rfl
private lemma steady_ps (p:2 ≤ N.val) {r:ℝ}(h:0<r):
    (r • ((M_).transpose*M_) : Matrix (ScrollB G N) (ScrollB G N) ℝ).PosDef:=by
 apply psd; · simp only [Matrix.transpose_smul, Matrix.transpose_mul,Matrix.transpose_transpose]
 intro x t; have he:M_*ᵥ x≠0:= mt (process G p _) t
 rw [Matrix.smul_mulVec,dotProduct_smul,smul_eq_mul,←Matrix.mulVec_mulVec,dotProduct_transpose_mulVec]; exact mul_pos h (show 0<dotProduct (M_*ᵥ x) (M_ *ᵥ x) by simpa using (PosDef.one (n:= R_) (R:=ℝ)).dotProduct_mulVec_pos he)
-- int: determinant M²≥1.
private lemma lore(i j:R_) : ∃ z:ℤ, M_ i j=(z:ℝ):=by
 let v:R_→ℝ := Pi.single j (1:ℝ); let f:= (smear (fast G N))*ᵥ v
 have he : InLattice f:=by
    intro i; by_cases t:i∈Set.range (fast G N)
    · obtain ⟨k,rfl⟩:=t; unfold f; rw [smear_t]; unfold v; by_cases p:k=j; subst j; exact ⟨1,by simp⟩; exact ⟨0,by simp [p]⟩
    exact ⟨0,(smear_f _ _ t).trans Int.cast_zero.symm⟩
 choose U h using he
 let Q:= (tube G N i).1; rw [show M_ i j= (M_ *ᵥ v) i from (by simp [v]), almost_e G]
 refine ⟨Curl (fun k=> U (k,i.val.2)) Q,?_⟩; change Curl (fun p=> f (p,i.val.2)) Q = _
 simp [h,Curl]
theorem fairDet (t:2≤ N.val) {p:Clip}{x y:ℝ}(h:Floor B p N x y){W:PathData G}{g f r:ℝ}(a:W.Bounds p g f r)(b:Attached B W) : PosDef (blockD G B N) ∧ p.direct^Fintype.card (ScrollB G N) ≤ costDet G B N:=by
 let T:= LinearMap.toMatrix' (draw G (N:=N)); let U:= p.direct • (T.transpose*T); have ht:PosDef U:= steady_ps G t p.quadratic_pos
 obtain ⟨hn,hR⟩:= obtain_f (Q:=blockD G B N) ht (block_guard G B h) (by
    intro i; unfold U blockD; rw [Matrix.smul_mulVec,dotProduct_smul, ←Matrix.mulVec_mulVec,dotProduct_transpose_mulVec, shade,tent_h,metric_pair B a b _ _ h]
    let F:= laced G (A*ᵥ i)
    have hw:= Finset.sum_nonneg (s:=Finset.univ) (f:=fun j:Face (Per N)=> inner ℝ (ellLine W j F) (ellLine W j F)) (fun i _=> real_inner_self_nonneg)
    rw [Finset.sum_add_distrib,← Finset.mul_sum]; apply le_trans _ (le_add_of_nonneg_right hw); apply mul_le_mul_of_nonneg_left _ p.quadratic_pos.le
    have hx(j): (T *ᵥ i) j=(faceCurl (tube G N j).1 F) (tube G N j).2:= (almost_e G _ _).trans ((atCurl G (A*ᵥ i) j.val.2 _).symm)
    change (∑ j,(T *ᵥ i) j*(T *ᵥ i) j)≤∑ j:Face (Per N),inner ℝ (faceCurl j F) (faceCurl j F); simp_rw [hx,inner_color]; exact (FreeResolvent.Cost.sum_comp_le (f:=tube G N) (tube_inj G N) (fun i:Face (Per N)×G.ColorIndex=> (faceCurl i.1 F i.2)*(faceCurl i.1 F i.2)) (fun i=> mul_self_nonneg _)).trans_eq (Fintype.sum_prod_type ..))
 have hp: p.direct>0:= p.quadratic_pos
 have hD: U.det=p.direct^ Fintype.card (ScrollB G N)*(T.det*T.det):=by unfold U; rw [det_smul,Matrix.det_mul,Matrix.det_transpose]
 refine ⟨hn,hR.trans' ?_⟩
 have he:= ht.det_pos; rw [hD] at he ⊢; apply le_mul_of_one_le_right (by positivity)
 choose X hx using lore (N:=N) G; let v:= Matrix.of X; have hq:T=v.map Int.cast:= Matrix.ext fun i j=>hx _ _
 rw [hq,show (v.map Int.cast).det= ((v.det:ℤ):ℝ) from ((Int.castRingHom ℝ).map_det v).symm] at he ⊢
 have hz : 0 < v.det*v.det:=by
    have hh : 0<(v.det:ℝ)*(v.det:ℝ):=pos_of_mul_pos_right he (by positivity)
    exact_mod_cast hh
 exact_mod_cast (Int.add_one_le_of_lt hz)
end YM.CF.Papyrus.GaugeFlux
#print axioms YM.CF.Papyrus.GaugeFlux.fairDet
