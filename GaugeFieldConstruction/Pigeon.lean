import YM.Next.FREE_KERNELS.Dispatch
set_option autoImplicit false
noncomputable section
namespace YM.Next.Free
open Filter Set Function Lattice Laurent Bloch Metric Exterior Matrix Precision RG Finset
open scoped Topology BigOperators ComplexConjugate Matrix InnerProductSpace
namespace Stretch
-- evaluate gauge bilinear price with any solutions, via inner edge pairing. conditional exact; supports later.
variable {c f S: Side} (s: StepData c f){H:Matrix (Body 2 f) (Body 2 f) ℝ}{H':Matrix (Body 2 c) (Body 2 c) ℝ}{W:Matrix (Body 1 f) (Body 1 c) ℝ}
include s
lemma execute (v:Inputs s W H H') {β J}(p:(K H') *ᵥ β=J) : K H *ᵥ (W *ᵥ β) = (mean s)ᵀ *ᵥ J:= by rw [mulVec_mulVec,v.primal,←mulVec_mulVec,p]
lemma funds (v:Inputs s W H H') {β J}(p:(K H') *ᵥ β=J)(I: form 1 c): (I ⬝ᵥ β)= s.kernel.penalty⁻¹*(I ⬝ᵥ J)+( ((mean s)ᵀ *ᵥ I) ⬝ᵥ (W *ᵥ β)):= by rw [mulVec_transpose,← dotProduct_mulVec,mulVec_mulVec,v.dual,sub_mulVec,one_mulVec,smul_mulVec,p,dotProduct_sub,dotProduct_smul]; ring -- tune
omit s
variable {ι θ t:Type*}[Fintype ι][Fintype θ][Fintype t][DecidableEq ι][DecidableEq θ]
abbrev reK (u:ι→ℝ):ι→ℂ:= fun i=> u i
lemma vecst (A:Matrix ι θ ℝ)(u:ι→ℝ): reK (u ᵥ* A)= (reK u) ᵥ* approached A:=by ext i; simp [reK,vecMul,dotProduct,approached]
lemma mullst (A:Matrix ι θ ℝ)(v:θ→ℝ): reK (A *ᵥ v)= approached A *ᵥ reK v:=by ext i; simp [reK,mulVec,dotProduct,approached]
abbrev stereo (F:Matrix ι θ ℂ)(a:ι→ℝ):= (reK a) ᵥ* F
lemma adjFund {F:Matrix ι θ ℂ}{v:ℂ}(h:Crew F v)(x y:ι→ℝ): ((x ⬝ᵥ y:ℝ):ℂ)=v⁻¹*(stereo F x ⬝ᵥ star (stereo F y)):=by
 unfold stereo; rw [star_vecMul, show star (reK y)=reK y by ext1 i; simp [reK]] -- star_vec gives Fh * reKY
 rw [← dotProduct_mulVec,mulVec_mulVec,h.2.1,smul_mulVec,one_mulVec,dotProduct_smul]; rw [smul_eq_mul, inv_mul_cancel_left₀ h.1]; simp [reK,dotProduct]
-- high spectral formula invert coexact
abbrev Fload (p:Momentum):= mirage 1 1 p * signal 1 1 p
lemma divisor_ch (p:Momentum) : (∑ i, tripQ 1 (-p) i*tripQ 1 p i)=divisor 1 p := by unfold divisor tripQ seedQ narrow; simp [mul_comm]
lemma squash (p:Momentum): Fload p= divisor 1 p • (1: Matrix (TypeFace 1) (TypeFace 1) ℂ)-signal 1 0 p*mirage 1 0 p:=by
 have he:= blade_price (tripQ 1 (-p)) (tripQ 1 p) fun _=>1
 rw [mask_one,mask_one] at he; simp only [Matrix.mul_one,Matrix.one_mul,one_mul,divisor_ch] at he; exact he
lemma baro {p:Momentum}(g: p∈baseCube): Fload p = (divisor 1 p)⁻¹ • (Fload p * Fload p):=by
 by_cases w:p=0; · subst p; simp [Fload]
 have he:Fload p*signal 1 0 p=0:=by unfold Fload; rw [Matrix.mul_assoc,signal_chain]; simp
 rw [show Fload p * Fload p=divisor 1 p • Fload p from calc
   _ = _ := congrArg (fun a=> Fload p * a) (squash p)
   _ = _ := by rw [Matrix.mul_sub,← Matrix.mul_assoc _ (signal 1 0 p),he,Matrix.zero_mul,sub_zero,Matrix.mul_smul,Matrix.mul_one]] -- fill infer
 rw [smul_smul,inv_mul_cancel₀ (divisor_ne 1 (base_subset_realCube zone_pos g) w),one_smul]
variable {g: Ratio c f}
abbrev priceZ := readings g (TypeFace 1) -- infer? needs binder g auto
lemma babylon (h:Odd g.count.val): Runs (priceZ (g:=g)) priceZ ((d 1 f)ᵀ*d 1 f) (braceAll g Fload):=by
 let z:= (cobound_true 1).fine g h
 have ht:= (z.back (readings_crew g _) (readings_crew g _)).product z
 rw [div_self (stage_ne f),one_smul] at ht; unfold braceAll Fload at *
 simp_rw [fiber_H,fiber_mult] at ht
 have he(p:Site c)(l:Site g.count):mirage 1 1 (aliasAt (mon p) l)=(signal 1 1 (aliasAt (mon p) l))ᴴ:=mirage_herm _ _ (alias_real (real_frequency _) _) _
 simp_rw [he]; exact ht
lemma fibre_q {b:Side}(z:Co b ι →ℂ)(u:Site b → Matrix ι θ ℂ)(i:Site b)(j:θ): (z ᵥ* fiber u) (i,j)=( (fun a :ι=>z (i,a)) ᵥ* u i) j :=by simp [vecMul,dotProduct,fiber,Fintype.sum_prod_type,mul_ite]
abbrev pack_R (g:Ratio c f)(j:form 1 f):= stereo (priceZ (g:=g)) j
lemma rising (g:Ratio c f)(h:Odd g.count.val){β j:form 1 f}(u: ((d 1 f)ᵀ*d 1 f) *ᵥ β=j)(p:Site c)(l:Site g.count) : (fun a=> pack_R g j (p,l,a))= (fun a=> pack_R g β (p,l,a)) ᵥ* Fload (aliasAt (mon p) l):=by
 let L:= (d 1 f)ᵀ*d 1 f; have he:j= β ᵥ* L:= by rw [←u,←mulVec_transpose]; simp [L,transpose_mul]
 have hk: pack_R g j= (pack_R g β ᵥ* (braceAll g Fload)):=by rw [he]; unfold pack_R stereo; rw [vecst,vecMul_vecMul, (show approached L*priceZ (g:=g)= priceZ*braceAll g Fload from babylon h),vecMul_vecMul] <;> rfl
 rw [hk]; funext a; unfold braceAll; rw [fibre_q]; rw [fibre_q] -- tune
lemma orientZ {A:Matrix ι ι ℂ} {p:Momentum}(q:p∈baseCube)(gA:Aᴴ=A)(h:A=(divisor 1 p)⁻¹ • (A*A))(β x:ι →ℂ) : ((x ᵥ* A) ⬝ᵥ star β)=(divisor 1 p)⁻¹*((x ᵥ* A) ⬝ᵥ star (β ᵥ* A)) :=by
 calc
  _ = (x ᵥ* ((divisor 1 p)⁻¹ • (A*A))) ⬝ᵥ star β:=congrArg (fun z=> (x ᵥ* z) ⬝ᵥ star β) h -- tune
  _ = _:=by rw [vecMul_smul,smul_dotProduct,←vecMul_vecMul,←dotProduct_mulVec,star_vecMul,gA,smul_eq_mul]
lemma harvest_flux {j k β ω₀:form 1 f}(u: ((d 1 f)ᵀ*d 1 f) *ᵥ β=j)(v: ((d 1 f)ᵀ*d 1 f) *ᵥ ω₀=k) (h:Odd g.count.val): ((k ⬝ᵥ β:ℝ):ℂ)= (stageVolume f)⁻¹*∑ p:Site c, ∑ l:Site g.count,(divisor 1 (aliasAt (mon p) l))⁻¹*((fun a=> pack_R g k (p,l,a)) ⬝ᵥ star (fun a=> pack_R g j (p,l,a))) :=by
 rw [adjFund (readings_crew g _)]; congr 1
 dsimp only [dotProduct]; simp_rw [Fintype.sum_prod_type]
 refine sum_congr rfl fun p _=>sum_congr rfl fun l _=> ?_; change ((fun a=> pack_R g k (p,l,a)) ⬝ᵥ star (fun a=> pack_R g β (p,l,a)))= _ * ( _ ⬝ᵥ star (fun a=> pack_R g j (p,l,a))) -- tune
 let F:=aliasAt (mon p) l; have he:F∈baseCube:=alias_base (mon_mem c p) _ h; rw [rising g h u, rising g h v]; refine orientZ he ?_ (baro he) _ _; unfold Fload; rw [mirage_herm _ _ he.1]; simp
end Stretch
end YM.Next.Free
end
