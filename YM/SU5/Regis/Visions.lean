import YM.Work.F03.Flat
import YM.SU5.Regis.Brass
/-! # Gaussian invariance under finite-volume orientation and shifts
 at tangent about the trivial connection. Uses Sworn for orientations. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option quotPrecheck false
set_option linter.unusedSimpArgs false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Regis.Head
open Function Lattice MeasureTheory Finset RG Wilson Tree Filter Metric Exterior Precision Next.Rank.Spindle Pressure Work.F03 ProbabilityTheory Submodule LinearMap
open Gleam Matrix
open scoped Matrix BigOperators Classical ContDiff Topology MatrixOrder ENNReal Kronecker Matrix.Norms.Frobenius
variable {n c:Side}{G:Gauge}{H:Bed}{m:ℕ}{η C S v δ : ℝ}{q:Clip}{Z:PathData G}

abbrev Dir(G:Gauge)(n:Side):=fieldDir G n 1 -- avoid conflict with `Dir` from Lattice?
lemma reflectedIso {A D:Type*}[AddCommGroup A][Module ℝ A][NormedAddCommGroup D][InnerProductSpace ℝ D][FiniteDimensional ℝ D](u:A→ₗ[ℝ] D)(f:A→ₗ[ℝ] A)(g:∀ i, ‖u (f i)‖= ‖u i‖): ∃ X:(LinearMap.range u)≃ₗᵢ[ℝ](LinearMap.range u), ∀ x, X (u.rangeRestrict x)= u.rangeRestrict (f x):=by
 let T:= u.rangeRestrict; obtain ⟨W,h⟩:= T.exists_rightInverse_of_surjective u.range_rangeRestrict
 have he(x:u.range): T (W x)=x:=congr($h x)
 have hu(i j:A)(t:T i=T j): T (f i)=T (f j):=by
    have hp: u i=u j:=congr_arg Subtype.val t; apply Subtype.ext; change u _=u _; have hx:=g (i-j); rw [map_sub,map_sub,map_sub,hp,sub_self,norm_zero] at hx; exact sub_eq_zero.mp (norm_eq_zero.mp hx)
 let F:= T.comp (f.comp W); have hx(x): ‖F x‖= ‖x‖:= (g _).trans (congrArg norm (he x) : ‖T (W x)‖=_)
 let X: u.range→ₗᵢ[ℝ] u.range:=⟨F,hx⟩; let V:= LinearIsometryEquiv.ofSurjective X (LinearMap.surjective_of_injective X.injective); -- tune
 refine ⟨V,fun i=>?_⟩; dsimp only [V]; rw [LinearIsometryEquiv.coe_ofSurjective]; exact hu _ _ (he (T i))
variable (s: Signed) (b:Site n) (B: Z.Bounds q η C S)(P:Attached H Z)(L:Floor H q n δ v)(O:Bid.Sworn H n G)
def dusk : Dir G n →ₗ[ℝ] Dir G n where
 toFun i:= Bid.pulled i s
 map_add' a c:=by funext x; change Bid.pulled (a+c) s x= Bid.pulled a s x+Bid.pulled c s x; unfold Bid.pulled; dsimp only; split_ifs <;> simp [*]; rw [add_comm] -- let
 map_smul' z c:=by funext x; change Bid.pulled (z • c) s x=z • Bid.pulled c s x; unfold Bid.pulled; dsimp only; split_ifs <;> simp

def arbor : Dir G n →ₗ[ℝ] Dir G n where
 toFun i x:= i (x.1+b,x.2)
 map_add' _ _:= rfl
 map_smul' _ _:= rfl
abbrev bank := (dusk s (G:=G) (n:=n)).comp (arbor b (G:=G))
lemma arbor_at (V:Dir G n)(r:ℝ) : represent (r • arbor b V)=pull 1 b (represent (r•V)):= by
 rw [pull_one]; funext i; unfold Lattice.translate; rw [represent_link,represent_link]; rfl
lemma bank_at (V:Dir G n)(r:ℝ) : represent (r • bank s b V)=pull s b (represent (r • V)):=by
 rw [bank, LinearMap.comp_apply,show dusk s (arbor b V)=_ from rfl]; change represent (r • Bid.pulled (arbor b V) s)=_; rw [← represent_pulled,arbor_at,pull_pull]; simp [affine]
lemma slot_drift (V:Dir G n)(i:Slot)(u:Site n): faceCurl (slotFace i u) (arbor b V)=faceCurl (slotFace i (u+b)) V:=by
 have ht := slot_deriv i u (arbor b V); simp_rw [arbor_at,Slot.atSite,expandAt_pull,pull_id] at ht; rw [show affine 1 b u=u+b by simp [affine]] at ht; exact ht.unique (slot_deriv ..)
lemma face_drift (V:Dir G n)(i:PlaqAxes)(u:Site n): faceCurl (u,i) (arbor b V)=faceCurl (u+b,i) V:=by
 let j:Slot:=⟨[],i⟩
 have he(x:Site n):slotFace j x=(x,i):=by simp [j,slotFace,Slot.offset,stop]
 rw [←he,←he]; exact slot_drift ..
include B P L in
lemma face_map (V:Dir G n) : ‖tiler B P V‖^2= Bid.gaugeFiscal H V V:=by
 rw [metric_pair H B P V V L,EuclideanSpace.real_norm_sq_eq,Fintype.sum_prod_type]; apply Finset.sum_congr rfl; intro i _; dsimp only; rw [show ∑ j:Bool×G.ColorIndex, (tiler B P V (i,j))^2=_ from tiler_color B P V i,research]; simp_rw [real_inner_self_eq_norm_sq]; ring
include B P L in
lemma arbor_steady (V:Dir G n) : ‖tiler B P (arbor b V)‖= ‖tiler B P V‖:=by
 have h: Bid.gaugeFiscal H (arbor b V) (arbor b V)=Bid.gaugeFiscal H V V:=by
    rw [metric_pair H B P _ _ L, metric_pair H B P _ _ L]; let T:= Equiv.prodCongr (Equiv.addRight b) (Equiv.refl PlaqAxes)
    let f:= fun i:Cell n=> q.direct* inner ℝ (faceCurl i V) (faceCurl i V)+inner ℝ (ellLine Z i V) (ellLine Z i V); change _= ∑ i, f i; rw [← Equiv.sum_comp T f]; apply Finset.sum_congr rfl; rintro ⟨a,p⟩ _; rw [face_drift, show T (a,p)=(a+b,p) from rfl, show ellLine Z (a,p) (arbor b V) = ellLine Z (a+b,p) V from tsum_congr (fun _=>congrArg _ (slot_drift b V _ a))]
 nlinarith only [norm_nonneg (tiler B P (arbor b V)),norm_nonneg (tiler B P V),(face_map B P L (arbor b V)).trans (h.trans (face_map B P L V).symm)]
include O P L in
lemma banked : ∃ W:(stamen B P n)≃ₗᵢ[ℝ] (stamen B P n), ∀ (V:Dir G n), W ((tiler B P).rangeRestrict V)= (tiler B P).rangeRestrict (bank s b V):=by -- `LinearIsometryEquiv ℝ` likely first param semilinear
 apply reflectedIso; intro i; rw [← arbor_steady b B P L i]; -- rewrites nested?
 have ht: ‖tiler B P (bank s b i)‖^2= ‖tiler B P (arbor b i)‖^2:= (face_map B P L _).trans ((O s _ _).trans (face_map B P L _).symm)
 nlinarith [norm_nonneg (tiler B P (bank s b i)),norm_nonneg (tiler B P (arbor b i))]

abbrev clouds (B:Z.Bounds q η C S) (P:Attached H Z) (W:Altar G n→ℝ) : ℝ:=∫ x : stamen B P n, W x.val ∂stdGaussian (stamen B P n)
lemma cloud_turn (W:Altar G n→ℝ) (p:Continuous W): ∫ x, W ((stamen B P n).starProjection x) ∂stdGaussian (Altar G n)= clouds B P W:=by -- parse comma parens
 let S:= stamen B P n -- rename
 change (∫ x, W (S.starProjection x) ∂_)=_; simp_rw [← Submodule.coe_orthogonalProjectionOnto_apply]; exact ((integral_map (Regis.curt S).aemeasurable (f:= fun x:S=> W x.val) (p.comp continuous_subtype_val|>.aestronglyMeasurable)).symm.trans (by rw [(Regis.curt S).map_eq]))
include O L in
lemma cover_calms (F E:Altar G n→ℝ)(a:Continuous F) (h:∀ V:Dir G n, F (tiler B P (bank s b V))=E (tiler B P V)) : clouds B P F=clouds B P E:=by
 let T:=stamen B P n; obtain ⟨W,hx⟩:= banked s b B P L O
 have hp(a:T) : F (W a).val=E a.val:=by obtain ⟨x,rfl⟩:= (tiler B P).surjective_rangeRestrict a; rw [hx]; exact h x
 unfold clouds; conv_rhs => arg 2; intro i; rw [←hp]
 let X:=stdGaussian T; have he:= integral_map (μ:=X) W.continuous.aemeasurable (f:=fun p:T=> F p.val) (a.comp continuous_subtype_val|>.aestronglyMeasurable)
 rw [stdGaussian_map W] at he; exact he
end YM.Regis.Head
#print axioms YM.Regis.Head.cover_calms
