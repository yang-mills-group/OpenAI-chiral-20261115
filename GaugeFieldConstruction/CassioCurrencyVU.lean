import YM.SU5.Six.RawWard
/-!
# Intrinsic mixing: annihilator test, including linear span with DIFFERENT
endpoint gauge transforms. Illuminated non-unit weights have neither a
pure-gauge nor a gauge-invariant pure-matter shadow at any late enough side.
Pointwise statement: orthogonal to every simultaneous fixed op of the matter
twist (separately from transforming links) in the SAME finite volume. So where
a gauge-invariant such mark is nonzero, it contains matter AND varies on the
link gauge orbit (with matter held fixed).

This check is supplemental to the SameRawProduct continuum disqualification.
-/
set_option autoImplicit false
set_option quotPrecheck false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 300000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Six
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder ENNReal Classical
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent Next.Free Bloch Drapes Spire Lifted Skye Sound Precision Tree Push.SectorMeasure Next.SectorChange Common Fock
open Satin
attribute [local instance] opCStarAlgebra
open Mir Haro Tap Dial Cascade Girt Pastry
open Afterglow Tapestry Tower

abbrev GaugeQuietVU (m:Side)(B:FC (Single m)):Prop:= ∀ g:Skye.Seat m→SU.E, twist (quantU (tradew m g)) B=B
lemma scalarQuietVU(m:Side)(a:ℂ):GaugeQuietVU m (a • 1):= fun _=> by rw [twist_scalar,map_one]
private lemma read_runesVU {n: Type} [Fintype n] [DecidableEq n] (U:UNI n)(A:Op n): Matrix.trace (twist U A)=Matrix.trace A:=by rw [twist_formula,Matrix.trace_mul_comm,←mul_assoc,(U.property.1: star U.val * U.val=1),one_mul]

variable {K:Calibration}

def CurrencyVU(K:Calibration): Submodule ℂ (Buffered.Family K) where
 carrier:= setOf fun f: Family K => ∀ᶠ m:Side in atTop, ∀ (B:FC (Single (K.c m))), GaugeQuietVU (K.c m) B→∀ x, Matrix.trace (star B * f m x)=0
 zero_mem':=Eventually.of_forall fun m B p x=> by rw [Pi.zero_apply,Pi.zero_apply,mul_zero,Matrix.trace_zero]
 add_mem':=fun {f g} hf hg=>(show _ from (show ∀ᶠ m:Side in atTop, _ from (show f∈ _ from hf)).and (show ∀ᶠ m:Side in atTop, _ from (show g∈ _ from hg))|>.mono fun m h B p x=> by rw [Pi.add_apply,Pi.add_apply,mul_add,Matrix.trace_add,h.1 B p,h.2 B p,add_zero]) -- tune
 smul_mem':=fun c f h=>(show _ from (show ∀ᶠ m:Side in atTop, _ from (show f∈ _ from h)).mono fun m hx B p x=> by rw [Pi.smul_apply,Pi.smul_apply,Algebra.mul_smul_comm,Matrix.trace_smul,hx B p,smul_zero])
lemma CurrencySpecVU {f:Buffered.Family K}: f∈CurrencyVU K ↔ ∀ᶠ m:Side in atTop,∀ (B:FC (Single (K.c m))), GaugeQuietVU (K.c m) B→∀ x, Matrix.trace (star B*f m x)=0:=Iff.rfl
lemma paysCurrencyVU (T:Cover→SU.E)(a:ℂ)(v:a≠1){f:Dome K}(w:f∈ illuminated K T a): f.val∈ CurrencyVU K:=by
 let Q:= (CurrencyVU K).comap (screenHall K).val.toLinearMap; change f∈Q; refine Submodule.span_induction (p:=fun f _=> f∈Q) (fun f t=>?_) Q.zero_mem (fun _ _ _ _ x y=>Q.add_mem x y) (fun c _ _ x=>Q.smul_mem c x) w
 obtain ⟨g,b,q,l,r,rfl⟩:=t; obtain ⟨S,p,h,e⟩:=q
 obtain ⟨Y,u⟩:=findsBay K b; change (g*b).val∈ CurrencyVU K; apply CurrencySpecVU.mpr; filter_upwards [separates K Y] with m hm; obtain ⟨G,d⟩:=scoreTrace T (⟨hm⟩:Hosp Y (K.c m)); let U:=quantU (tradew (K.c m) G); intro B j x; let C:=b.val m x
 have R: C=twist U (a • C):=by
    have hr:= pennantTrace K Y T u; rw [r] at hr
    exact (show LinkIndependent K b.val from l) m x _|>.trans (hr m G d x)
 have TR:a*Matrix.trace (star B*C)=Matrix.trace (star B*C):= calc
    _ = Matrix.trace (star B * (a • C)):=by rw [Algebra.mul_smul_comm,Matrix.trace_smul]; rfl
    _ = Matrix.trace (twist U (star B * (a • C))):=(read_runesVU U _).symm
    _ = _:=by rw [map_mul, map_star, ←R, show twist U B=B from j G] -- rw hazard RHS R
 have hZ:Matrix.trace (star B*C)=0:= Classical.byContradiction fun n=> v (mul_right_cancel₀ n (TR.trans (one_mul _).symm))
 change Matrix.trace (star B*(g.val m x * C))=0
 rw[e]; change Matrix.trace (star B*((p _ • (1:FC _)) * C))=0; rw [Algebra.smul_mul_assoc,one_mul,Algebra.mul_smul_comm,Matrix.trace_smul,hZ,smul_zero]

lemma opDetectedVU {f:Dome K}(w:f∈enclave K)(h:f.val∈CurrencyVU K): ∀ᶠ m:Side in atTop,∀ x:Fields (K.c m),f.val m x≠0 → ∃ u:Skye.Seat (K.c m)→SU.E, f.val m (simultaneous u x)= twist (quantU (tradew (K.c m) u)) (f.val m x) ∧ f.val m (simultaneous u x)≠ f.val m x:=by
 filter_upwards [CurrencySpecVU.mp h] with m hm; intro x v; have hp:= (enclave_spec K).1 w m; by_contra! q
 have r:GaugeQuietVU (K.c m) (f.val m x):= fun g=> (hp g x).symm.trans (q g (hp g x))
 exact v (Matrix.trace_conjTranspose_mul_self_eq_zero_iff.mp (hm _ r x))
lemma velvetCoinVU {f:Dome K}(w:f∈enclave K)(h:f.val∈CurrencyVU K)(e:f≠0): ¬ PureGauge K f :=by
 rintro ⟨S,g,u,r⟩; apply e
 obtain ⟨X,hX⟩:=findsBay K f; obtain ⟨m,hm,q⟩:=( (separates K X).and (opDetectedVU w h)).exists
 apply Subtype.ext; apply looksLike (m:=m) (S:=X) ⟨hm⟩ ((locates ..).mp hX) InTest.zero; funext x; by_contra d
 obtain ⟨c,p,z⟩:=q x d; apply z; rw [p]; rw [r]; exact scalarQuietVU _ _ _
lemma velvetGramVU{f:Dome K}(w:f∈enclave K)(h:f.val∈CurrencyVU K)(e:f≠0): ¬ PureMatter K f:=by
 intro y; obtain ⟨X,hX⟩:=findsBay K f; obtain ⟨m,hm,q⟩:=((separates K X).and (opDetectedVU w h)).exists
 apply e; apply Subtype.ext; apply looksLike (m:=m) (S:=X) ⟨hm⟩ ((locates ..).mp hX) InTest.zero; funext x; by_contra d
 obtain ⟨c,p,z⟩:= q x d; exact z (y m _ x)
lemma literallyMixedVU {f:Dome K}(w:f∈enclave K)(h:f.val∈CurrencyVU K)(e:f≠0):∀ᶠ m:Side in atTop,∃ (x:Fields (K.c m)) (g:Skye.Seat (K.c m)→SU.E), f.val m x≠0 ∧ twist (quantU (tradew (K.c m) g)) (f.val m x)=f.val m (simultaneous g x) ∧ f.val m (simultaneous g x)≠f.val m x:=by
 obtain ⟨X,hX⟩:=findsBay K f; filter_upwards [separates K X, opDetectedVU w h] with m hm u; have hh: ∃ x,f.val m x≠0:=by
   by_contra! d; apply e; apply Subtype.ext; apply looksLike (m:=m) (S:=X) ⟨hm⟩ ((locates ..).mp hX) InTest.zero; exact funext d
 obtain ⟨x,d⟩:=hh; obtain ⟨g,p,r⟩:=u x d; exact ⟨x,g,d,p.symm,r⟩
#print axioms CurrencyVU
#print axioms velvetGramVU
#print axioms literallyMixedVU
#print axioms paysCurrencyVU
#print axioms opDetectedVU
#print axioms velvetCoinVU
end YM.CF.Buffered.Afterglow.Six
