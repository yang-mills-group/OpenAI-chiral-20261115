import YM.SU5.Six.Extinguish
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
variable (K:Calibration)
local notation "Ω"=> Dome K
variable (W:Bool)(S T D:Finset Cover)(g:Cover→SU.E)
/-!
# Charged pure pieces on both sides of a marginal test

A phase-average to arrange the gauge charge opposite the matter charge. K is
the physical calibration. As with Factorization the scalar raw gauge marks
here can in general use both panes. Bay locality paid on both factors.
-/
lemma royal_period : (SU.central)^5=1:= by
 have ht(n:ℕ): SU.group.mat (SU.central^n)= (SU.group.mat SU.central)^n:=by
    induction n with
    | zero=> simp
    | succ n h=>rw [pow_succ,SU.group.mat_mul,h,pow_succ]
 apply SU.group.mat_injective
 rw [ht, SU.group.mat_one]
 change (Matrix.diagonal (fun _ : F=> SU.z))^5=(1:Matrix F F ℂ)
 apply Eq.trans (Matrix.diagonal_pow (fun _ : F=>SU.z) 5); rw [show (fun _ : F=>SU.z)^5=(fun _=>1) from funext fun _=>SU.z_prim.pow_eq_one]
 rfl
lemma pname_period : phaseName W ^5=1:=by
 unfold phaseName
 rw [←pow_mul,mul_comm,pow_mul,SU.z_prim.pow_eq_one,one_pow]

variable {x y:Dome K}
lemma gaugePure_add (p:PureGauge K x)(h:PureGauge K y): PureGauge K (x+y):=by
 obtain ⟨A,f,hf,e⟩:=p
 obtain ⟨B,v,hv,r⟩:=h
 have h:=hf.mono (Finset.subset_union_left (s₂:=B)); have u:= hv.mono (Finset.subset_union_right (s₁:=A))
 refine ⟨A∪B,f+v,⟨(by simp),kitE _ _ (·+·) (by fun_prop) h.env u.env,
    fun _ _ a b=>congrArg₂ (α:=ℂ) (β:=ℂ) (·+·) (h.locus _ _ a b) (u.locus _ _ a b)⟩,?_⟩
 change x.val+y.val=_;rw [e,r]; funext i t
 exact (add_smul _ _ _).symm
lemma gaugePure_smul (p:PureGauge K x)(z:ℂ): PureGauge K (z•x):=by
 obtain ⟨A,f,h,e⟩:=p
 refine ⟨A,z•f,⟨(by simp),pole_w f (fun y:ℂ=>z•y) (by fun_prop) h.env,fun _ _ a b=>congrArg (fun y:ℂ=>z•y) (h.locus _ _ a b)⟩,?_⟩
 change z•x.val=_; rw [e]; funext i t
 change z • (f _ • (1 : FC _)) = (z • f _) • _; exact smul_smul z _ _

def silk : Submodule ℂ Ω where
 carrier:= {x|PureGauge K x}
 zero_mem':=by rw [show (0:Ω)=(0:ℂ)•(1:Ω) by simp]; exact gaugePure_smul K (pure_unit K).1 _
 add_mem' p q:=gaugePure_add K p q
 smul_mem' z f h:= gaugePure_smul K h z

-- *sum*, normalize at use
variable (q:ℂ)(a b:Dome K)
local notation "η"=> pennant K
def intaglio: Ω:=∑i∈ Finset.range 5,q^i• η (g^i) a
lemma intaglio_pure (v:a∈bay K D true)(p:PureGauge K a): intaglio K g q a∈ bay K D true ∧ PureGauge K (intaglio K g q a) :=
 ⟨Subalgebra.sum_mem _ (fun _ _=> (bay K D true).smul_mem (pennantLocal K D _ v) _),
   (silk K).sum_mem (fun _ _=>(silk K).smul_mem _ (pennantPure K _ p))⟩
lemma intaglio_charge (p:g^5=1)(h:q^5=1): η g (intaglio K g q a)= q⁻¹• intaglio K g q a:=by
 let f (i:ℕ):=q^i• η (g^i) a
 have ht: ∑ i∈Finset.range 5,f (i+1)=∑i∈Finset.range 5,f i:=by
    have he:f (4+1)=f 0:=by unfold f;change q^5• η (g^5) a=_;rw [h,p,pow_zero,pow_zero]
    change ∑i∈Finset.range (4+1),_=∑i∈Finset.range (4+1),_
    rw [Finset.sum_range_succ,he, Finset.sum_range_succ' f]
 have hn:q≠0:=by intro e; simp [e] at h
 apply smul_right_injective Ω hn
 change q • _=q • (_ : Ω)
 rw [smul_smul,mul_inv_cancel₀ hn,one_smul]
 unfold intaglio
 rw [map_sum,Finset.smul_sum]
 apply Eq.trans _ ht
 refine Finset.sum_congr rfl fun i _=> ?_
 unfold f
 rw [map_smul,pennantCompose, smul_smul,pow_succ' q,pow_succ g]
lemma intaglio_add : intaglio K g q (a+b)=intaglio K g q a+intaglio K g q b:= by
 unfold intaglio; simp_rw [map_add,smul_add,sum_add_distrib]
lemma intaglio_scale (c:ℂ): intaglio K g q (c•a)= c•intaglio K g q a:=by
 unfold intaglio;rw [Finset.smul_sum];refine Finset.sum_congr rfl fun i _=>?_ ; rw [map_smul,smul_comm (q^i)]
lemma pennant_raise (p:η g b=q•b)(i:ℕ): η (g^i) b=q^i• b:=by
 induction i with
 | zero=> rw [pow_zero g,pow_zero q,pennantId,one_smul]
 | succ i h=>rw [pow_succ,←pennantCompose,h,map_smul,p,smul_smul,pow_succ]
lemma intaglio_factor (p:η g b=q•b): intaglio K g 1 (a*b) = intaglio K g q a*b:= by
 unfold intaglio;rw [Finset.sum_mul];refine Finset.sum_congr rfl fun i _=> ?_
 rw [map_mul,pennant_raise K g q b p,one_pow,one_smul,mul_smul_comm,smul_mul_assoc]
lemma intaglio_full (h:η g b=b): b=(5:ℂ)⁻¹• intaglio K g 1 b:=by
 unfold intaglio
 have e:η g b=(1:ℂ)•b:=by rw [one_smul,h]
 simp_rw [pennant_raise K g 1 b e,one_pow,one_smul]
 rw [Finset.sum_const,Finset.card_range,show (5:ℕ) • b =(5:ℂ)•b by rw [←Nat.cast_smul_eq_nsmul ℂ]; push_cast; rfl]
 rw [smul_smul,inv_mul_cancel₀ (by norm_num:(5:ℂ)≠0),one_smul]
end YM.CF.Buffered.Afterglow.Six
