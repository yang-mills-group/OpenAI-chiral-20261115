import YM.CF.Roots.Sail
import YM.CF.Mew.Tube
set_option maxHeartbeats 240000
set_option autoImplicit false
noncomputable section
namespace YM.CF.Roots.Connect
open Function Filter Metric MeasureTheory Finset Mew
open scoped Topology ContDiff BigOperators Matrix
variable {I J T E:Type*}[Fintype I][LinearOrder I][Fintype J][LinearOrder J][DecidableEq T][NormedAddCommGroup E][NormedSpace ℂ E][CompleteSpace E]
#check Mew.port_C
variable {f:Key I→E}(p: River f)
variable {U: Finset I}{v A:Key I}(u:v∈hill I)
abbrev Routable (A:Key I)(u:Finset I):Prop:= ∀ j∉u,A j=0
include p u in
lemma crest_F : River (fun x:Key I => f (line_K v U x)):=by
 let F(z:Key I):= line_K v U z
 have h(z:Key I)(q:z∈hill I):F z∈hill I:=hill_i.mpr (fun i=>by
    by_cases hx:i∈U; · rw [show F z i=z i from if_pos hx]; exact hill_i.mp q i
    rw [show F z i=v i from if_neg hx]; exact hill_i.mp u i) -- indent
 have hc:Continuous F:=continuous_pi fun i=>by
    unfold F line_K; by_cases hx:i∈U; · simp_rw [if_pos hx]; exact continuous_apply i
    simp_rw [if_neg hx]; exact continuous_const
 refine ⟨p.shore.comp hc.continuousOn (fun x q=>h x q),fun z q i x e=>?_⟩; by_cases l:i∈U
 · have hu(w:ℂ):line_K v U (update z i w)=update (F z) i w:=by
      ext k:1; by_cases t:k=i; · subst k; simp [line_K,l]
      simp [line_K,F,t]
   change DifferentiableAt ℂ (fun w=>f (line_K v U (update z i w))) _; simp_rw [hu]; exact p.slope _ (h z q) _ _ e
 have he(w:ℂ):line_K v U (update z i w)=F z:=by
    ext k:1; unfold F; by_cases hx:k=i; · subst k; simp [line_K,l]
    simp [line_K,hx]
 change DifferentiableAt ℂ (fun w=>f (line_K v U (update z i w))) _; simp_rw [he]; exact differentiableAt_const _
include p u
variable (P:Routable A U)(ρ:∀ j∈ U,v j=0)
include P ρ
lemma crept : HasDerivAt (fun x:ℂ=> f (v+x • A)) (∑ i∈U,A i • cutI f i v) 0:=by
 let G(x:Key I):= f (line_K v U x)
 let a:ℝ:= (2*(‖A‖+1))⁻¹; let W:Key I:= a • A; have ha:0<a:=by unfold a; positivity
 have he:a*(2*(‖A‖+1))=1:=inv_mul_cancel₀ (by positivity)
 have hp:‖W‖ ≤ 1/2:=by rw [show ‖W‖=‖a‖*‖A‖ from norm_smul .., Real.norm_eq_abs, abs_of_pos ha]; nlinarith only [he,ha]
 let P(x:Key (Fin 1)):= x 0 • W -- shadow
 have ht(i:I): River (fun x:Key (Fin 1)=>P x i):= κscale (north_r (0:Fin 1)) (zeroR (W i))
 have hQ(x)(p:x∈hill (Fin 1))(i): ‖P x i‖ ≤ 1/2:=by change ‖x 0 * W i‖≤_; rw [norm_mul]; exact (mul_le_of_le_one_left (norm_nonneg _) (hill_i.mp p 0)).trans ((norm_le_pi_norm ..).trans hp)
 have hu: River G:= crest_F p u
 have hy:River (G∘P):= port_C _ hu P ht (by norm_num) hQ
 let Z:ℂ→ Key (Fin 1):= fun x=> update (0:Key (Fin 1)) (0:Fin 1) x
 have hZ(x:ℂ):P (Z x)= x • W:=congrArg (· • W) (update_self ..)
 have hz: tipI (G∘P) [0]= (a:ℂ) • ∑ i∈U,A i • cutI f i v:=by
    rw [cane G hu P ht (by norm_num) hQ (show P 0=0 from zero_smul ..)]; rw [smul_sum]
    have hx(i:I): tipI (fun y=>P y i) [0]=W i:=by
       let F(x:Key (Fin 1)):= P x i
       have hv: (fun x:ℂ=>F (Z x))=(fun x:ℂ=> x*W i):=funext fun x=>congrFun (hZ x) _ -- trans definitional
       have hp:HasDerivAt (fun x:ℂ=>F (Z x)) (tipI F [0]) 0:=mitt (ht _) roots 0; rw [hv] at hp; exact hp.unique (by simpa using (hasDerivAt_id' (0:ℂ)).mul_const (W i))
    simp_rw [hx]; refine (sum_subset (f:=fun i:I=>W i • tipI G [i]) (subset_univ U) ?_).symm.trans (sum_congr rfl (fun i he=>?_))
    · intro i _ u; rw [show W i=(a:ℂ)* A i from rfl, ‹Routable A U› i u, mul_zero,zero_smul]
    have hc(x:ℂ):line_K v U (update 0 i x)=update v i x:=by
       ext k:1; by_cases l:k=i
       · subst k; simp [line_K,he]
       by_cases g:k∈U<;>simp [line_K,l,g,ρ k]
    rw [show tipI G [i]=cutI f i v from ((mitt hu roots i).unique (show HasDerivAt (fun x:ℂ=>G (update 0 i x)) (cutI f i v) 0 from (by unfold G; simp_rw [hc]; exact mitt p u i))), smul_smul]; rfl
 let L:=∑ i∈U,A i • cutI f i v; let F(t:ℂ):= G (P (Z t)); let a':ℂ:=a; have hν:a'≠0:=by unfold a'; exact_mod_cast ha.ne'
 have hL:HasDerivAt F (a' • L) 0:= hz ▸ mitt hy roots 0 -- tune
 let D(x:ℂ):= x*a'⁻¹; have ht:D 0=0:=zero_mul _
 have hF(x:ℂ): (F∘D) x=f (v+x • A):=by
    unfold Function.comp F G; rw [hZ,show W=a' • A from rfl,smul_smul, show D x*a'=x from (by unfold D; field_simp)]; congr 1; ext k:1; by_cases g:k∈U
    · rw [line_K, if_pos g, Pi.add_apply,ρ k g,zero_add]
    unfold line_K; rw [if_neg g,Pi.add_apply,Pi.smul_apply,‹Routable A U› k g,smul_zero,add_zero] -- tune
 have hd:HasDerivAt D a'⁻¹ 0:=by simpa using (hasDerivAt_id' (0:ℂ)).mul_const a'⁻¹
 rw [←funext hF]; refine ((show HasDerivAt F (a' • L) (D 0) from ht.symm ▸ hL).scomp (0:ℂ) hd).congr_deriv (inv_smul_smul₀ hν _)
#print axioms crept
end YM.CF.Roots.Connect
end
