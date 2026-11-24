import YM.SU5.Selected.Rail.Porte
/-! # AP averages. Gram limit. -/
set_option autoImplicit false
set_option maxHeartbeats 350000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Crest.Rail
open Function Filter Metric NormedSpace Lattice Laurent Bloch Next.Free MeasureTheory
open Ember Jill Fir Shore Real Airy Fock Topology
open scoped Topology BigOperators Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace ComplexOrder NNReal ENNReal
local notation "I"=>Complex.I
local notation "φ" => 2*π
local instance : Fact (0<φ):= ⟨piRank⟩
attribute [local instance] opCStarAlgebra
open Finset Lat
lemma stem_one {N:Side}(x:Site N): pm x∈ stemGuard:= stemG.mpr ((pi_norm_le_iff_of_nonneg pi_pos.le).mpr (fun a=> abs_le.mpr ⟨(pm_zone x a).1.le,(pm_zone x a).2⟩))
lemma cargo_coe {N:Side}(x:Site N): harbor (pm x)= brim N x:= rfl
lemma rent_count : ferry4.real Set.univ= rent':=by
 have ht:=hang 0; simp_rw [perch,view,Function.comp,prefix_zero,integral_const,Complex.real_smul, mul_one,if_true] at ht; have hz:(rent':ℂ) ≠0:=by exact_mod_cast rent_pos.ne'
 refine Complex.ofReal_injective ?_; exact (mul_left_cancel₀ (inv_ne_zero hz) (ht.trans ((inv_mul_cancel₀ hz).symm))) -- dots tune
private abbrev D:= hill ×ˢ Set.Icc (-π) π
private abbrev cp_4 (f:Coast→ℂ)(t:Facet3 ×ℝ):= f (harbor (joinBin t))
lemma rest_four:ferry4=volume.restrict (hill ×ˢ Set.Icc (-π) π):=Measure.prod_restrict ..
lemma cp_c (f:Coast→ℂ)(h:Continuous f):Integrable (cp_4 f) ferry4:= by rw [rest_four]; exact (((h.comp harbor_c).comp join_cont).continuousOn).integrableOn_compact (hill_compact.prod isCompact_Icc)
lemma perch_add {f g:Coast→ℂ} (h:Continuous f)(p: Continuous g): perch (f+g)=perch f+perch g:=by unfold perch view; simp_rw [Function.comp,Pi.add_apply]; rw [integral_add (cp_c f h) (cp_c g p), mul_add]
lemma perch_sub {f g:Coast→ℂ} (h:Continuous f)(p: Continuous g): perch (f-g)=perch f-perch g:=by unfold perch view; simp_rw [Function.comp,Pi.sub_apply]; rw [integral_sub (cp_c f h) (cp_c g p), mul_sub]
lemma perch_smul (f:Coast→ℂ)(c:ℂ): perch (c•f)=c*perch f:=by unfold perch view; simp_rw [Function.comp,Pi.smul_apply,smul_eq_mul]; rw [integral_const_mul]; ring
lemma perch_norm (f:Coast→ℂ){ε:ℝ}(e:∀ x, ‖f x‖≤ε): ‖perch f‖≤ε:=by rw [perch,norm_mul,norm_inv,Complex.norm_of_nonneg rent_pos.le]; unfold view; have hp:= norm_integral_le_of_norm_le_const (μ:=ferry4) (Filter.Eventually.of_forall fun x=> e (harbor (joinBin x))); rw [rent_count,mul_comm] at hp; rw [inv_mul_le_iff₀ rent_pos]; exact hp
-- same Fourier `freeze`
variable (N: Side)
abbrev factorA:= ((N.val:ℂ)^4)⁻¹
def packA (f:Site N→ℂ):ℂ:=factorA N *∑ i:Site N, f i
lemma pack_one(c:ℂ): packA N (fun _=>c)=c:=by simp [packA,factorA,nsmul_eq_mul]
lemma pack_cost(f:Site N→ℂ){ε:ℝ}(p:∀ i, ‖f i‖≤ ε): ‖packA N f‖≤ ε:= by
 unfold packA; rw [norm_mul]; apply (mul_le_mul_of_nonneg_left ((norm_sum_le ..).trans (sum_le_sum (fun i _=> p i))) (norm_nonneg _)).trans; rw [factorA,norm_inv,norm_pow,Complex.norm_natCast,sum_const,card_univ,site_card,nsmul_eq_mul,Nat.cast_pow, ←mul_assoc, inv_mul_cancel₀,one_mul]; exact pow_ne_zero _ (Lat.nPos N).ne'
lemma pack_add (f g:Site N→ℂ): packA N (f+g)=packA N f+packA N g:=by simp [packA,sum_add_distrib,mul_add]
lemma pack_sub (f g:Site N→ℂ): packA N (f-g)=packA N f-packA N g:=by simp [packA,sum_sub_distrib,mul_sub]
lemma pack_smul (f:Site N→ℂ)(c:ℂ):packA N (c • f)=c*packA N f:=by simp only [packA,Pi.smul_apply,smul_eq_mul,←mul_sum]; ring
lemma pack_sum {F:Type*}(f:F→ Site N→ℂ)(s:Finset F):packA N (fun u=>∑ i∈s,f i u)=∑ i∈s,packA N (f i):=by unfold packA; rw [sum_comm,mul_sum]
-- same diagonal Fourier. useful for Gram final.
lemma trust (x y:Site N)(c:ℂ): factorA N*c=Fourier N x y * c * star (Fourier N x y):=by
 unfold Fourier Lat.normF; simp only [Matrix.of_apply,star_div₀,star_pow,star_natCast]; rw [show frequency y x /(_^_)* c * (star (frequency y x)/(_^_))= (star (Lat.frequency y x)*Lat.frequency y x)*c/((N.val:ℂ)^4) from ?_,Lat.frequency_unit]; rw [div_eq_mul_inv,one_mul,mul_comm]
 ring
abbrev AP (f:Coast→ℂ) := packA N (f ∘ brim N)
lemma Apse (w:Cover): ∀ᶠ N:Side in atTop, AP N (prefixG w)= if w=0 then 1 else 0:=by
 filter_upwards [Shore.raising w] with N v; by_cases p:w=0; · subst w; unfold AP comp; simp_rw [if_true,prefix_zero]; exact pack_one ..
 let Z:Site N:=0; rw [if_neg p]; unfold AP packA; rw [mul_sum]; apply (Finset.sum_congr rfl (fun (i:Site N) _=> trust N Z i _)).trans
 exact fareFee w Z Z (fun h=>by rw [show Z=0 from rfl,zero_add] at h; exact p (v.symm.trans ((congrArg (@lift N) h).trans (lift_origin N)))) -- name
lemma colore_c {Q:Cover→Prop}{f:Coast→ℂ}(p:Color Q f): Continuous f:= by induction p with| zero=> exact continuous_zero|mode v=>exact prefix_c _|smul p h v=>exact continuous_const.smul v|add p q u v=>exact u.add v
lemma color_charge {Q:Cover→Prop}{f:Coast→ℂ}(p:Color Q f):∀ᶠ n:Side in atTop, AP n f= perch f:=by
 induction p with
 | zero=> exact Filter.Eventually.of_forall (fun i=> by simp [AP,perch,comp,view,packA])
 | mode v h=> rw [hang]; exact Apse _
 | @add f g p q u v=> exact (u.and v).mono (fun i z=>by rw [perch_add (colore_c p) (colore_c q), ←z.1,←z.2]; exact pack_add i ..)
 | @smul q f p v=> exact v.mono (fun i z=>by rw [perch_smul,←z]; exact pack_smul i (f ∘ brim i) _)
lemma cost_grid {f: Coast→ℂ} (p:Continuous f): Tendsto (fun i:Side=>AP i f) atTop (𝓝 (perch f)):=by
 apply Metric.tendsto_nhds.mpr; intro ε h; obtain ⟨g,e,v⟩:= fromStone p (ε/3) (by positivity); filter_upwards [color_charge e] with i z; rw [dist_eq_norm]; apply lt_of_le_of_lt (b:=ε/3+ε/3) _ (by linarith); rw [show AP i f-perch f= AP i (f-g)-perch (f-g) from ?_]; exact (norm_sub_le ..).trans (add_le_add (pack_cost i _ (fun x=>v _)) (perch_norm _ v)) -- defeq
 rw [show AP i (f-g)=AP i f-AP i g from pack_sub i (f∘ brim i) (g∘ brim i), perch_sub p (colore_c e),z]; abel
end YM.CF.Crest.Rail
open YM.CF.Crest.Rail
#print axioms cost_grid
#print axioms rent_count
#print axioms trust
#print axioms pack_cost
