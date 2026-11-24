import YM.SU5.Relativistic.Fairs
import YM.SU5.Relativistic.Whirl
set_option autoImplicit false
set_option synthInstance.maxSize 26000
set_option maxHeartbeats 400000
set_option maxRecDepth 5000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.Reconstruction.FermionSlab
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Fock
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder NNReal ENNReal Classical InnerProductSpace
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat PhaseChoice SlabMark Vacancy Tapestry Tapestry.Altitude Tapestry.Exhibition Tower.Selected
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(H:Real.exp 1≤Λ.x)
local notation "K"=>tent Y H
variable {a b:ℕ→ℕ}{I:ℕ→Family (tent Y H)→ℕ→ℂ}{E:ℕ→Family (tent Y H)→ℂ}(V:Universal Y H a b I E)
variable (j:Axis)
section billing
noncomputable def Cabin (Z:Calibration)(j:Axis) : Submodule ℂ (Family Z) where
 carrier:={f |∃ S:Finset Cover, InTest Z true S true f ∧ Tower.region j 0 Z.ℓ S}
 zero_mem':=⟨∅,InTest.zero,by simp [Tower.region]⟩
 add_mem' :=by
    rintro f g ⟨S,h,p⟩ ⟨T,v,q⟩; exact ⟨S∪T,(h.mono subset_union_left).add (v.mono subset_union_right),fun i t=>(Finset.mem_union.mp t).elim (p i) (q i)⟩
 smul_mem':=by intro x f h; obtain ⟨S,h,v⟩:=h; exact ⟨S,InTest.smul _ h,v⟩
-- theta pair normalized by exp(+iπ/2)
variable (Z:Calibration)
lemma hutSpec (f:Cabin Z j): ∃ S:Finset Cover,InTest Z true S true f.val ∧ Tower.region j 0 Z.ℓ S:= f.property
lemma levied (f g:Cabin Z j): TestFamily Z true (mirror Z j 0 f.val * g.val):= by
 obtain ⟨S,h,v⟩:= hutSpec j Z f; obtain ⟨W,u,t⟩:= hutSpec j Z g
 exact aux_test (((axial Z j 0 h).mono (subset_union_left (s₂:=W))).mul (u.mono subset_union_right))
def chilly (Z:Calibration)(j:Axis)(p:Dome Z→ₗ[ℂ] ℂ) : Cabin Z j →ₗ⋆[ℂ] Cabin Z j→ₗ[ℂ] ℂ := by
 let G(f g:Cabin Z j):Dome Z := ⟨_, (levied j Z f g).scale Complex.I⟩
 let S:Cabin Z j→ₗ⋆[ℂ] Cabin Z j →ₗ[ℂ] Dome Z :=
  { toFun := fun f=> { toFun:=fun g=>G f g
                       map_add':=fun g h=>Subtype.ext (show Complex.I • (mirror Z j 0 f.val * (g.val+h.val))= _ from (by rw [mul_add,smul_add]; rfl))
                       map_smul':=fun a g=>Subtype.ext (show Complex.I • (mirror Z j 0 f.val * (a • g.val))=_ from (by rw [Algebra.mul_smul_comm,smul_comm Complex.I]; rfl)) }
    map_add' := fun f g=>LinearMap.ext fun k=>Subtype.ext (show Complex.I • (mirror Z j 0 (f.val+g.val)*k.val)= _ from (by rw [mirror_plus,add_mul,smul_add]; rfl))
    map_smul':= fun a f=>LinearMap.ext fun k=>Subtype.ext (show Complex.I • (mirror Z j 0 (a • f.val)*k.val)=_ from (by rw [mirror_scale,Algebra.smul_mul_assoc,smul_comm Complex.I]; rfl)) }
 exact { toFun:=fun f=> p.comp (S f)
         map_add' :=by intro x y; rw [map_add]; ext; simp
         map_smul':=by intro a x; rw [map_smulₛₗ]; ext; simp }
lemma chilly_at (p:Dome Z→ₗ[ℂ] ℂ)(x y:Cabin Z j): chilly Z j p x y= p ⟨_,(levied j Z x y).scale Complex.I⟩:= rfl
-- kinematic mesh relocate -- FULL double gauge shift. no need half; positivity of this exact polynomial on selected suffices (not buying single-step norm symmetry progeny via Jobs)
local notation "F₀"=>Cabin (tent Y H) j
variable (s:ℕ)
noncomputable def walkV (n:ℕ): Cabin (tent Y H) j →ₗ[ℂ] Cabin (tent Y H) j where
 toFun f:= by
    refine ⟨relocate K j (n:ℤ) f.val,?_⟩; obtain ⟨S,h,z⟩:=hutSpec j K f; refine ⟨plow K j (n:ℤ) S,flow_port K j _ h,?_⟩
    intro i u; obtain ⟨x,h,rfl⟩:= plow_stays K j (n:ℤ) S u
    rw [moves,if_pos rfl]; specialize z x h; have ht:0≤ ruler Λ.block*(n:ℤ):=mul_nonneg (ruler_gene _).le (by positivity); exact le_trans z (by change x j ≤ x j+ruler Λ.block*(n:ℤ); linarith)
 map_add' u v :=Subtype.ext (chime_plus ..)
 map_smul' a v := Subtype.ext (chime_scale ..)
local notation "α" => walkV Y H j
lemma steps_add (m n:ℕ)(x: F₀): α m (α n x)=α (m+n) x:=by
 apply Subtype.ext; obtain ⟨S,p,w⟩:= hutSpec j K x
 change relocate K j _ (relocate K j _ _)=relocate K j _ _
 unfold relocate; rw [hoops K j _ p]; unfold gaugeT Heat.gaugeShift; push_cast; congr 1 <;> ring -- order
lemma steps_orig (x:F₀): α 0 x=x:=by
 apply Subtype.ext; change chime K j (gaugeShift Λ.block (2*0)) x.val=_; rw [show gaugeShift Λ.block (2*0)=0 from by simp [gaugeShift]]; exact reversal K j 0 (hutSpec j K x).choose_spec.1
lemma beams(k:ℕ)(f g:F₀): relocate K j (k:ℤ) (Complex.I • (mirror K j 0 (α k f).val*g.val))=Complex.I • (mirror K j 0 f.val*(α k g).val):=by
 let a:= Heat.gaugeShift Λ.block (2*(k:ℤ)); let h:InTest K true _ true f.val:=(hutSpec j K f).choose_spec.1
 change chime K j a (Complex.I • (mirror K j 0 (chime K j a f.val)*g.val))=_
 rw [chime_scale,chime_product,counterSlide K j _ _ (flow_port K j _ h),hoops K j _ h,neg_add_cancel,reversal_ch]
 rfl
where reversal_ch{f:Cabin (tent Y H) j}:chime K j 0 f.val=f.val:= reversal K j 0 ((hutSpec j K f).choose_spec.1)
include V
noncomputable def unB : (F₀)→ₗ⋆[ℂ] (F₀)→ₗ[ℂ] ℂ := chilly K j (expect Y H V s) -- Dome coerces?
local notation "B₀" => unB Y H V j s
lemma frost_n (x:F₀):0≤ B₀ x x:=by
 obtain ⟨S,h,e⟩:=hutSpec j K x
 change 0≤ E s (Complex.I • _)
 have he:gaugeShift Λ.block 0=0:=by rw [Heat.gaugeShift,mul_zero]
 have hz:= chargedGram Y H s V h (show Tower.region j (Heat.gaugeShift Λ.block 0) (tent Y H).ℓ S from he.symm ▸ e)
 rw [he] at hz; exact hz
lemma unB_contract (x:F₀) (n:ℕ): ‖B₀ (α n x) (α n x)‖ ≤ ‖B₀ x x‖ :=by
 obtain ⟨S,h,v⟩:= hutSpec j K x
 obtain ⟨d,hx⟩:=Tower.sizes S; obtain ⟨C,hC⟩:=Journey.valuation Y H h
 let T:Set ℝ:= Set.range fun i:ℕ=> ‖B₀ (α i x) (α i x)‖; let U:=sSup T
 have hp:BddAbove T:=by
    refine ⟨Grip Y H s d*(C*C),?_⟩; rintro y ⟨w,rfl⟩
    let W:=α w x; let a:=Heat.gaugeShift Λ.block (2*(w:ℤ)); let P:=reflectedBox j a (reflectedBox j 0 S)
    have hW:InTest K true P true W.val:=axial K j _ (axial K j 0 h)
    have ht:CompactArc P d:= (hx.reflBox S j 0).reflBox _ j _
    have hA:pay W.val C:= chime_pay K j a C hC
    change ‖E s (Complex.I • (mirror K j 0 W.val* W.val))‖≤_
    rw [E_scale Y H V s (levied j K W W),norm_mul, Complex.norm_I, one_mul]; exact shot_pair Y H V s d (axial K j 0 hW) hW (ht.reflBox P j 0) ht C C (pay_flips K hA j 0) hA
 let B(i:ℕ):= ‖B₀ (α i x) (α i x)‖
 have hu(i:ℕ): B i≤ U:= le_csSup hp ⟨i,rfl⟩
 have hz:0≤U:= (norm_nonneg _).trans (hu n)
 have hi (i:ℕ): B i^2 ≤ ‖B₀ x x‖ * U:=by
    have hv: B₀ (α i x) (α i x)=B₀ x (α (i+i) x):=by
       rw [←steps_add Y H j i i]; change E s (Complex.I • (mirror K j 0 (α i x).val * (α i x).val)) = E s (Complex.I • (mirror K j 0 x.val * (α i (α i x)).val)); rw [←beams Y H j i x]; exact (SWay Y H V s j (2*(i:ℤ)) ((levied j K (α i x) (α i x)).scale Complex.I)).symm
    unfold B; rw [hv]; apply le_trans _ (mul_le_mul_of_nonneg_left (hu (i+i)) (norm_nonneg _));
    let w(f g:F₀):= B₀ f g
    obtain ⟨M⟩:= _root_.YM.Kernel.host (show _root_.YM.Analysis.NNKernel w from fun _ v=>halfSpaceKernel (B₀) (frost_n Y H V j s) v)
    change ‖w _ _‖^2≤ ‖w x x‖ * ‖w _ _‖
    rw [← M.measure,← M.measure,← M.measure, inner_self_eq_norm_sq_to_K,inner_self_eq_norm_sq_to_K,norm_pow,norm_pow]; simp
    have hh:=norm_inner_le_norm (𝕜:=ℂ) (M.plant x) (M.plant (α (i+i) x)); rw [←mul_pow]; exact pow_le_pow_left₀ (norm_nonneg _) hh 2 -- tune
 refine (hu n).trans ?_
 have hU: U≤ Real.sqrt (‖B₀ x x‖*U):= csSup_le ⟨_,⟨n,rfl⟩⟩ (by rintro _ ⟨i,rfl⟩; exact Real.le_sqrt_of_sq_le (hi i))
 have hg:= Real.sq_sqrt (mul_nonneg (norm_nonneg (B₀ x x)) hz)
 exact le_of_not_gt fun e=>by nlinarith [Real.sqrt_nonneg (‖B₀ x x‖*U),norm_nonneg (B₀ x x)] -- tune e
end billing
end YM.CF.Buffered.Afterglow.Tower.Reconstruction.FermionSlab
