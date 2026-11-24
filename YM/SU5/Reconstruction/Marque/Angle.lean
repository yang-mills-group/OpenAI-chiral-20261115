import YM.SU5.Reconstruction.Marque.Dark
set_option autoImplicit false
noncomputable section
namespace YM.Marque
open Function Set Filter Metric NormedSpace ContinuousLinearMap BridgeClub CrossedFrame Picket Spectral Analysis Multiplier MeasureTheory ComplexConjugate
open scoped ComplexOrder InnerProductSpace BigOperators Topology Classical Complex
variable {H D E K W:Hilbert} (Z:Clasp D H E)(F:Clasp K H W) {v:Wander H.space}{a:Bool}(p:Fleet v a)
local notation "P"=> Z.plume
local notation "P'"=> F.plume
variable {J L:Flash H}{Γ T:Set H.Op}{M N:Net H}{x y:H}
variable {A B:H.Op}
include p in
lemma Across.expo (h:Across v A B): Across v (NormedSpace.exp A) (NormedSpace.exp B):= by
 let z(n:ℕ):ℂ:=(n.factorial:ℂ)⁻¹; let S(c:H.Op)(n:ℕ):H.Op:=∑ i∈Finset.range n, z i • c^i;
 have he(n):Across v (S A n) (S B n):=by
   induction n with
   | zero=> rw [show S A 0=0 from Finset.sum_empty,show S B 0=0 from Finset.sum_empty]; exact fun x=> (p.bases).symm
   | succ n g=> simp only[S,Finset.sum_range_succ]; exact Across.adds g (by simpa only [show Hue a (z n)=z n from by cases a<;> simp[z]] using Across.scale (Across.power h n) p (z n)) p
 have hv(A:H.Op)(x:H): Tendsto (fun n=> S A n x) atTop (𝓝 (NormedSpace.exp A x)):= (ContinuousLinearMap.apply ℂ H.space x).continuous.continuousAt.tendsto.comp ((NormedSpace.exp_series_hasSum_exp' (𝕂:=ℂ) A).tendsto_sum_nat);
 exact fun x=> tendsto_nhds_unique_of_eventuallyEq (hv B _) (v.continuous.continuousAt.tendsto.comp (hv A x)) (Eventually.of_forall fun n=> he n x)
def beamRate (a:Bool)(t:ℝ):= if a then -t else t
local notation "Θ"=> beamRate a
noncomputable def axisMass(x:H):= pushed Z.motion Z.realF (Z.Left.symm x)
instance (x:H): IsFiniteMeasure (axisMass Z x):=by unfold axisMass; infer_instance
variable (x:H)(t:ℝ)
lemma asExp : charFun (axisMass Z x) t= inner ℂ x (NormedSpace.exp (((t:ℂ)*Complex.I) •P) x):= by
 obtain ⟨x,rfl⟩:= Z.Left.surjective x; rw [axisMass,LinearIsometryEquiv.symm_apply_apply,plays Z.motion Z.realF Z.measurable_realF,bounded_flow Z.motion Z.realF Z.tagF Z.angle_reads];
 let U:= Z.Left.toContinuousLinearEquiv.toContinuousLinearMap
 have he(w:D):U w= Z.Left w:=rfl
 have hv: U.comp (((t:ℂ)*Complex.I) • Z.angle)= (((t:ℂ)*Complex.I) • P:H.Op).comp U:= by
    ext1 v; rw[ContinuousLinearMap.comp_apply,ContinuousLinearMap.comp_apply,smul_apply,smul_apply,map_smul,he,he,(Club.pearlA Z v).1]
 rw [show (NormedSpace.exp (((t:ℂ)*Complex.I) • P)) (Z.Left x)= Z.Left (NormedSpace.exp (((t:ℂ)*Complex.I) • Z.angle) x) from (DFunLike.congr_fun (exp_comm hv) x).symm, LinearIsometryEquiv.inner_map_map]
variable (g:Across v  Z.plume F.plume)
include p g in
lemma sameMass : axisMass Z x= axisMass F (v x):= by
 apply Measure.ext_of_charFun; funext t
 have ht:Across v (NormedSpace.exp ((((Θ t:ℝ):ℂ)*Complex.I) • P)) (NormedSpace.exp (((t:ℂ)*Complex.I) • P')):= -- smul precedence! 
    Across.expo p ((show Hue a (((Θ t:ℝ):ℂ)*Complex.I)=(t:ℂ)*Complex.I from by cases a<;> simp [beamRate]) ▸ Across.scale g p _)
 rw[asExp F,ht,p.innerP,←asExp Z]; cases a<;> simp [beamRate,charFun_neg] -- tune
lemma fareAngle: inner ℂ x (Z.cLeft t x)= ∫ s, Clasp.river t s ∂ axisMass Z x:=by
 obtain ⟨x,rfl⟩:= Z.Left.surjective x; rw [Clasp.cLeft,LinearIsometryEquiv.conjStarAlgEquiv_apply_apply,LinearIsometryEquiv.symm_apply_apply,LinearIsometryEquiv.inner_map_map, (Z.Cabin_reads _).awakes]; unfold axisMass pushed; rw [LinearIsometryEquiv.symm_apply_apply, integral_map Z.measurable_realF.aemeasurable ((Clasp.river_price _).meas.aestronglyMeasurable)] -- needs hm μ pushed
 rfl
include p g in
lemma staysAngle : Across v (Z.cLeft t) (F.cLeft (Θ t)):= by
 let T:= (p.Form (Z.cLeft t)); have ht:= p.arr (Z.cLeft t)
 have he:F.cLeft (Θ t)= T:= by
    apply Rep.fact; intro x; obtain ⟨x,rfl⟩:= v.surjective x; rw[← inner_conj_symm, ← inner_conj_symm (T (v x)) (v x)]; apply congrArg; change inner ℂ (v x) (F.cLeft _ _)=inner ℂ (v x) (p.Form _ _); rw[ht,p.innerP,fareAngle,fareAngle,←sameMass Z F p x g] 
    cases a with
    | false=> rfl
    | true=>
      change (∫ s, Clasp.river (-t) s ∂ axisMass Z x) = conj (∫ s, _ ∂_) -- need notation
      rw [← integral_conj]; apply integral_congr_ae (Eventually.of_forall (fun s=> Chirp.neg_time ..)) -- tune
 rw[he]; exact ht
include p
variable {x:H} (m:Club Z J M x Γ)(w:Club F L N y T)(z:Conveys v M N)(k:v x=y)
include m w z k
lemma locks : Across v (Picket.boost Z t) (Picket.boost F (Θ t)):= by
 unfold Picket.boost; rw [show -Θ t/Real.pi=Θ (-t/Real.pi) from (by cases a<;> simp [beamRate] <;> ring)]; exact staysAngle _ _ p _ (groundPlume _ _ p m w z k)
end YM.Marque
