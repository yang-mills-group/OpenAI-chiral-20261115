import YM.SU5.FiniteGaugeData.Tower.Control
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 6000
set_option maxHeartbeats 500000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(H:Real.exp 1≤Λ.x)
local notation "K" => tent Y H
variable {i k:ℕ→ℕ}{I:ℕ→Family (tent Y H)→ℕ→ℂ}{E:ℕ→Family (tent Y H)→ℂ}(V:Universal Y H i k I E)(s:ℕ)

/-! # Complete reflected forms on every positive box at fixed level

Not just time at one `K.plane0`, and acts on arbitrary finite sums of products
of even chiral local marks (including any bounded Borel pair coefficients),
so in particular restriction to gauge invariant even allowed. Same Λ.x,
β(0) identification and signed reading as `CrimsonLine.approx`; justify here
from the E limiting *those readings*, not a separately elected form. Keep the
buffer --- at every fixed observing level only; e.g. level-s probe stencils
in regions [buffer,∞) on gauge coordinate a for z=0. This does not make E a
state on any CAR C⋆-algebra.
-/
open Reed (Fine)

section rotations
variable {S:Finset Cover}(K':Calibration)(a:Axis)(z:ℤ)
def mirror (F:Family K'):Family K':=fun t=>reflMark a z (F t)
def region (d:ℕ)(S:Finset Cover) := ∀ x∈S,z+d≤x a
def reflectedBox (v:Finset Cover) := v.image ((plane a z).motion)
-- `InTest.reflection` generalized; same proof via `Lifted` basis formulas.
variable {F G:Family K'}
@[simp] lemma mirror_time : mirror K' 3 z F=reflected K' z F:=rfl
lemma mirror_plus :mirror K' a z (F+G)=mirror K' a z F+mirror K' a z G:=funext fun _=>funext fun _=>Fock.theta_add ..
lemma mirror_scale (c:ℂ):mirror K' a z (c • F)=star c • mirror K' a z F:=funext fun _=>funext fun _=>Fock.theta_smul ..
lemma mirror_times:mirror K' a z (F*G)=mirror K' a z F*mirror K' a z G:=funext fun _=>funext fun _=>Fock.theta_mul ..
lemma mirror_unit:mirror K' a z 1=1:=funext fun _=>funext fun _=>Fock.theta_one ..
local notation "Refl"=> mirror K' a z
variable {wide b:Bool}
private lemma refl_scalar (f : PairsC→ℂ) (p : Coeff wide S f) : InTest K' wide (reflectedBox a z S) false (Refl (scalar K' f)) := by
 let F := Lifted.moveC a z; let g(x:PairsC):=star (f (F x.1,F x.2))
 have ht: Refl (scalar K' f)=scalar K' g:= by funext m x; unfold scalar mirror reflMark; rw [Fock.theta_smul,Fock.theta_one]; apply congrArg (fun u :ℂ=> u • (1:Fock.FC (Single _))); unfold g; simp only [reflFields,Prod.map_fst, Prod.map_snd,reflect_onC]; rfl
 rw [ht]; refine .seed ⟨fun v=> ?_, Girt.pole_w _ star continuous_star (Env.along (g:=Prod.map F F) p.env ((move_cont ..).prodMap (move_cont ..)).measurable),fun x y c d=>?_⟩
 · obtain ⟨c,h,e⟩:= p.narrow v; refine ⟨fun x=>star (c (F x)),(h.comp (move_cont ..)).star,?_⟩; rw [show g=fun x=>star (f (F x.1,F x.2)) from rfl,e]; rfl
 exact congrArg star (p.locus (F x.1,F x.2) (F y.1,F y.2) (moved_agree _ _ c) (moved_agree _ _ d))
private lemma reflected_creation_eq (x : Cover) (i : SpinIdx) (b : SU.Slot) :
    Refl (creation K' x i b) = -Complex.I • ∑ j, star (Mir.pin a j i) • removal K' ((plane a z).flee x) j b := by
 funext m v; simp_rw [Pi.smul_apply,Finset.sum_apply,Pi.smul_apply]; unfold mirror reflMark creation removal
 rw [(flips_basisC a z (K'.c m) x i b).1]; unfold Fock.remove; simp only [map_sum,map_smul,star_sum,star_smul]
private lemma reflected_removal_eq (x : Cover) (i : SpinIdx) (b : SU.Slot) :
    Refl (removal K' x i b) = Complex.I • ∑ j, Mir.pin a j i • creation K' ((plane a z).flee x) j b := by
 funext m v; simp_rw [Pi.smul_apply,Finset.sum_apply,Pi.smul_apply]; unfold mirror reflMark creation removal
 rw [(flips_basisC a z (K'.c m) x i b).2]; simp only [map_sum,map_smul]
private lemma dualizes(a:Axis): twist (pinLift a) (Fock.cutM plusHalf)=Fock.cutM plusHalfᶜ:= by
 open Fock in rw [dim_cut,raising,Fir.Adef.symm]; exact angleX (mirrorX a) true
lemma axial (x:InTest K' wide S b F):InTest K' wide (reflectedBox a z S) b (mirror K' a z F):=by
 induction x with
 | @creator t i b h v=>
    rw [reflected_creation_eq]; refine .smul _ (InTest.sum _ _ (fun j _=>?_)); by_cases e:j∉plusHalf
    · refine .smul _ (.remover b e (mem_image.mpr ⟨_,v,Shape.mote ..⟩))
    rw [show Mir.pin a j i=0 from Fine.entry (dualizes a) h (by simpa using not_not.mp e),star_zero,zero_smul]; exact .zero
 | @remover t i b h v=>
    rw [reflected_removal_eq]; refine .smul _ (InTest.sum _ _ (fun j _=>?_)); by_cases e:j∈plusHalf
    · refine .smul _ (.creator b e (mem_image.mpr ⟨_,v,Shape.mote ..⟩))
    have ht: twist (pinLift a) (Fock.cutM plusHalfᶜ)=Fock.cutM plusHalf:= by
       open Fock in rw [dim_cut,map_sub,map_one,dualizes a,dim_cut]; abel
    rw [show Mir.pin a j i=0 from Fine.entry ht (by simpa only [mem_compl] using h) e, zero_smul]; exact .zero
 | seed p=> exact refl_scalar K' a z _ p
 | zero=> rw [show Refl 0=0 from funext fun _=>funext fun _=> Fock.theta_zero _]; exact .zero
 | one=> rw [mirror_unit]; exact .one
 | add _ _ i j=> rw [mirror_plus]; exact .add i j
 | mul _ _ i j=> rw [mirror_times]; exact .mul i j
 | smul c _ ih=> rw [mirror_scale]; exact .smul _ ih
lemma reversal (p:InTest K' wide S b F):mirror K' a z (mirror K' a z F)=F:= funext fun m=> (p.support m).refl_refl ..
end rotations
section band
variable {a:Axis}{z:ℤ}{S:Finset Cover}
variable (K':Calibration)
lemma recedes (h:region a z K'.ℓ S): ∀ᶠ m:Side in atTop, S.image (wrap (More (K'.c m))) ⊆ band (K'.c m) a z K'.ℓ:=by
 have ht:∀ᶠ m:Side in atTop, ∀ x∈S,x a+K'.ℓ≤ z+(K'.c m).val:=by
    rw [S.eventually_all]; intro x _
    let i:=x a+K'.ℓ - z; filter_upwards [(c_grows K').eventually (eventually_ge_atTop i.toNat)] with m w; change _≤ (K'.c m).val at w; unfold i at w; omega
 filter_upwards [ht] with m t q entry
 obtain ⟨x,hx,rfl⟩:= mem_image.mp entry
 apply (band_spec ..).mpr
 let i:= x a - z; let n:=K'.c m; have hp:= t x hx; have hu:= h x hx; have hz:0<(K'.c m).val:= (K'.c m).property
 have hg:0 ≤ i:=by unfold i; omega
 have hw:i.toNat<(More n).val:=by change _<n.val*2; unfold n i at *; omega
 rw [show (wrap (More (K'.c m)) x) a - (z : Per (More n))=(i.toNat:Per (More n)) from ?_, ZMod.val_natCast_of_lt hw]; swap; · rw [←Int.cast_natCast, Int.toNat_of_nonneg hg,show (i:Per (More n))=(↑(x a) : Per (More n)) - (z:Per (More n)) from Int.cast_sub ..]; rfl
 unfold i; omega
end band

section pos
open Heat
variable {a:Axis}{z:ℤ}
variable {S:Finset Cover}{f g:Family (tent Y H)}
local notation "t₀" z:max=> gaugeShift Λ.block z
local notation "φ" a:max z:max=> mirror K a (t₀ z)
include V
lemma boson_axial (p:InTest K true S false f)(h:region a (t₀ z) (K).ℓ S):
    0≤ E s ((φ a z) f * f):=by
 have hv:= (warm_limit Y H V s ((aux_test (axial (tent Y H) a (t₀ z) p)).mul (aux_test p)))
 apply ge_of_tendsto hv.periods
 filter_upwards [((momentum Y s).comp V.pick.grow_i.tendsto_atTop).eventually (recedes (tent Y H) h)] with r b
 apply ge_of_tendsto (hv.inner (i r))
 filter_upwards [V.pick.pass Y H s _] with t u
 unfold hot; rw [dif_pos u.depth]; exact (boxprice Y H _ _ u.depth s u.fire u.enters).fund a z _ ((p.support _).mono b)
-- use also at fixed periods only when *torus* support fits, not asserted before
lemma I_axial (a:Axis)(z:ℤ)(p:TestFamily K true f)(n:ℕ)(b:AtSupport false (band ((K).c (momentm Y n s)) a (t₀ z) (K).ℓ) (f (momentm Y n s))):0≤ I s ((φ a z) f*f) n:=by
 obtain ⟨x,h⟩:=p.paid
 apply ge_of_tendsto ((warm_limit Y H V s ((aux_test (axial _ a _ h)).mul p)).inner n)
 filter_upwards [V.pick.pass Y H s _] with t u; unfold hot; rw [dif_pos u.depth]; exact (boxprice Y H _ _ u.depth s u.fire u.enters).fund a z _ b

-- net over all supports beyond the forward face
omit V
def wing (K':Calibration)(a:Axis)(z:ℤ):Subalgebra ℂ (Family K') where
 carrier:= {f|∃ S:Finset Cover,InTest K' true S false f∧ region a z K'.ℓ S}
 add_mem' := by rintro F G ⟨S,w,p⟩ ⟨T,h,q⟩; exact ⟨S∪T,.add (w.mono subset_union_left) (h.mono subset_union_right),fun x z=> (Finset.mem_union.mp z).elim (p x) (q x)⟩
 mul_mem' := by rintro F G ⟨S,w,p⟩ ⟨T,h,q⟩; exact ⟨S∪T,.mul (w.mono subset_union_left) (h.mono subset_union_right),fun x z=> (Finset.mem_union.mp z).elim (p x) (q x)⟩
 zero_mem' := ⟨∅,.zero,by simp [region]⟩
 one_mem' := ⟨∅,.one,by simp [region]⟩
 algebraMap_mem' r:=⟨∅,by rw [Algebra.algebraMap_eq_smul_one]; exact .smul r InTest.one,by simp [region]⟩
variable (a z)
lemma exam (K':Calibration){G:Family K'}(p:G∈ wing K' a z): TestFamily K' true G ∧ TestFamily K' true (mirror K' a z G):=by
 obtain ⟨S,w,h⟩:= (p:∃ S:Finset Cover,InTest K' true S false G∧region a z K'.ℓ S)
 exact ⟨aux_test w,aux_test (axial K' a z w)⟩

include V
local notation "Π"=> (wing K a (t₀ z)).toSubmodule
lemma ribbon (f g:Π):TestFamily K true ((φ a z) f.val * g.val):= (exam a (t₀ z) (tent Y H) f.property).2.mul (exam a (t₀ z) (tent Y H) g.property).1

def form : (Π)→ₗ⋆[ℂ] (Π)→ₗ[ℂ] ℂ where
 toFun f:= {
    toFun:= fun g=> E s ((φ a z) f.val*g.val)
    map_add' := fun u v=>by rw [AddSubmonoid.coe_add,mul_add]; exact E_add Y H V s (ribbon Y H V a z f u) (ribbon Y H V a z f v)
    map_smul' := fun c u=>by rw [Submodule.coe_smul,Algebra.mul_smul_comm]; exact E_scale Y H V s (ribbon Y H V a z f u) c }
 map_add' f g:= LinearMap.ext fun k=>by change E s _= E s _+E s _; rw [AddSubmonoid.coe_add,mirror_plus,add_mul]; exact E_add Y H V s (ribbon Y H V a z f k) (ribbon Y H V a z g k)
 map_smul' c f:= LinearMap.ext fun k=>by change E s _=star c*E s _; rw [Submodule.coe_smul,mirror_scale,Algebra.smul_mul_assoc]; exact E_scale Y H V s (ribbon Y H V a z f k) _
local notation "read"=> form Y H V s a z
lemma boson_positive (f:Π):0≤ read f f:=by obtain ⟨S,w,p⟩:= (f.property:∃ S:Finset Cover,InTest K true S false _ ∧ region a (t₀ z) (K).ℓ S); exact boson_axial Y H V s w p
omit V
lemma halfSpaceSymm {T:Type*}[AddCommGroup T][Module ℂ T](R:T→ₗ⋆[ℂ] T→ₗ[ℂ] ℂ)(h:∀ f, 0≤R f f)(x y:T): star (R y x)=R x y:=by
 have t(x): (R x x).im=0:= (Complex.le_def.mp (h x)).2.symm; have e:=t (x+y); have E:=t (x+Complex.I • y)
 simp_rw [map_add,LinearMap.add_apply] at e E; rw [map_smulₛₗ (f:=R)] at E; simp only [LinearMap.smul_apply, map_smul,starRingEnd_apply, smul_eq_mul] at E
 simp [t,Complex.mul_re,Complex.mul_im] at e E; apply Complex.ext <;> simp <;> linarith
lemma halfSpaceKernel {T:Type*}[AddCommGroup T][Module ℂ T](R:T→ₗ⋆[ℂ] T→ₗ[ℂ] ℂ)(h:∀ f,0≤R f f){X:Type*}[Fintype X](f:X→T):Matrix.PosSemidef (Matrix.of fun i j=>R (f i) (f j)):=by
 apply Matrix.posSemidef_iff_dotProduct_mulVec.mpr; constructor
 · ext i j; exact halfSpaceSymm R h _ _
 intro b; have he := h (∑ j,b j • f j)
 rw [map_sum R,LinearMap.sum_apply] at he; simp_rw [map_sum,map_smulₛₗ (f:=R)] at he
 change 0 ≤ ∑ i, star (b i)*∑ j, R (f i) (f j)*b j
 simpa only [smul_eq_mul,starRingEnd_apply,map_smulₛₗ,LinearMap.smul_apply, RingHom.id_apply,Finset.mul_sum, mul_assoc,mul_comm,mul_left_comm] using he
include V
lemma boson_hermitian (f g:Π): star (read g f)=read f g:= halfSpaceSymm read (boson_positive Y H V s a z) _ _
lemma boson_allRP {X:Type*}[Fintype X](f:X→Π):Matrix.PosSemidef (Matrix.of fun i j=> E s ((φ a z) (f i).val * (f j).val)):= halfSpaceKernel read (boson_positive Y H V s a z) f

-- For unit-mixed diagonal, this gives the symmetry of E *on that band*.
-- At finite scale can't conclude arbitrary translation this way. But at the
-- limit can use two suitably aligned mirrors to get even-product translation
-- symmetry. Keep individual reflectivity lemma for now.
lemma mirror_band {F:Family K}(p:F∈ wing K a (t₀ z)) : E s ((φ a z) F)=star (E s F):=by
 let U:Π:=⟨1,(wing _ _ _).one_mem⟩; let v:Π:=⟨F,p⟩
 have e:= boson_hermitian Y H V s a z v U
 change star (E s (mirror K _ _ 1 * F))= E s (mirror K _ _ F*1) at e
 rw [mirror_unit,one_mul,mul_one] at e; exact e.symm
end pos

end YM.CF.Buffered.Afterglow.Tower
#print axioms YM.CF.Buffered.Afterglow.Tower.boson_allRP
