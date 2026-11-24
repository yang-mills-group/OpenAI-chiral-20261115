import YM.CF.Dial.Dame
/-! Stage-space definiteness. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Dial
open Function Filter Lattice Laurent Bloch Next.Free Metric Lat Finset Branch Cube Tenant SU Rush Drapes Fir Tulip Fock Peaks
open scoped Topology Matrix MatrixOrder BigOperators Matrix.Norms.L2Operator Kronecker InnerProductSpace
attribute [local instance] opCStarAlgebra
variable {n:Type*}[Fintype n][DecidableEq n][Nonempty n]{P N K C A: Op n}
def victory(P:Op n)(C D R:Op n):= R*C*Rᵀ+body (1-P) D
def straightC(P C D R:Op n)(v:ℝ) := ((1-(v:ℂ)):ℂ) • D+(v:ℂ) • victory P C D R
lemma norms_le_inv {e:ℝ}(h:0<e)(p:e • (1:Op n) ≤ P):∃ X,P*X=1∧ ‖X‖ ≤ e⁻¹ :=by
  have he:0≤P:=le_trans (smul_nonneg h.le zero_le_one) p; obtain ⟨U,d,rfl⟩:=spectral_exists _ (IsSelfAdjoint.of_nonneg he)
  have ht:e • (1:n→ℝ)≤ d:= (spectral_le U _ _).mp (by rwa [←spectral_smul,spectral_one])
  have hy (i):e≤d i:=by simpa using ht i
  let X:=spectral U (fun i=>(d i)⁻¹); have hx:0≤X:= by unfold X; rw [←spectral_zero U,spectral_le]; exact fun i=> inv_nonneg.mpr ((h.trans_le (hy i)).le)
  refine ⟨X,?_, (CStarAlgebra.norm_le_iff_le_algebraMap _ (inv_nonneg.mpr h.le) hx).mpr ?_⟩
  · unfold X; rw [spectral_mul,←spectral_one U]; congr 1; exact funext fun i=> mul_inv_cancel₀ (h.trans_le (hy i)).ne'
  unfold X; rw [Algebra.algebraMap_eq_smul_one, ←spectral_one U,spectral_smul,spectral_le]; exact fun i=>by simpa only [Pi.smul_apply,Pi.one_apply,smul_eq_mul, mul_one] using inv_anti₀ h (hy i)
lemma solid_p (h:IsStarProjection P){r:ℝ}(u:1≤ r) (e:‖K‖≤r)(hp:N*K=P): (r*r)⁻¹ • P ≤ N*star N:=by
  have he:K*star K ≤ (r*r) • (1:Op n):=by
    apply (op_le_norm_one (IsSelfAdjoint.mul_star_self K)).trans (smul_le_smul_of_nonneg_right _ zero_le_one); exact (norm_mul_le ..).trans (mul_le_mul e ((norm_star ..).le.trans e) (norm_nonneg _) (by linarith))
  have hv:= seal_up he N; rw [←mul_assoc N K (star K),mul_assoc (N*K),←star_mul, hp,h.isSelfAdjoint,h.isIdempotentElem, Algebra.mul_smul_comm,mul_one, Algebra.smul_mul_assoc] at hv
  have hr:0<r:=by linarith
  exact (smul_le_smul_of_nonneg_left hv (show 0≤(r*r)⁻¹ by positivity)).trans (le_of_eq (inv_smul_smul₀ (mul_pos hr hr).ne' _))
lemma sharp (h:IsStarProjection P)(p: P*C=C*cc P):stage P C=C:=sub_eq_zero.mp (norm_le_zero_iff.mp ((stage_gap h C).trans (by rw [p,sub_self,norm_zero]) |>.le))
lemma thud(h:IsStarProjection P)(p:P*C=C*cc P):body P C=P*C:=by rw [←stage_left h,sharp h p]
lemma outsideT(h:IsStarProjection P)(C:Op n) : body P (body (1-P) C)=0:=by nth_rw 1 [body]; rw [←body_left h.one_sub,←mul_assoc P, Porth h,zero_mul,zero_mul]
lemma firmly (h:IsStarProjection P) {X:Op n}(e:P*X=X)(p:X*cc P=X):stage P X=X:=by
  rw [stage,body,body,e,p,sub_mul,one_mul,e,sub_self,zero_mul,add_zero]
lemma stage_p(A B:Op n)(v t:ℂ): stage P (v • A+t • B)=v • stage P A+t • stage P B:=by simp only [stage,body,mul_add,add_mul, Matrix.smul_mul,Matrix.mul_smul,smul_add]; abel
-- S_t at vacuum. Orthogonality, dual. stage invariant on NN*C'
lemma win {r t:ℝ}(h:IsStarProjection P)(hN:P*N=N)(p:N*K=P)(hz:‖K‖≤r)(hr:1≤r)
    (hs:C∈unitary (Op n))(hg:P*C=C*cc P)(hk:N*A=C*cc N)(g:A∈unitary (Op n)) (ht:0≤t)(hf:t≤1):
 ∃ X, stage P (straightC P A C N t)*X=1 ∧ ‖X‖≤ r*r:=by
  have hi: N*A*Nᵀ=N*star N*C:=by -- need hk anti commute plus inverse N from complements to recover star relation: use CAR adjointed
    have he: star A*star N=star (cc N)*star C:=by rw [←star_mul,hk,star_mul]
    have hh:A*Nᵀ= star N*C :=by -- cc N star = Nt
      have hm:star A*star N*C=star (cc N):=by rw [he,mul_assoc, show star C*C=1 from hs.1,mul_one]
      rw [show Nᵀ=star (cc N) from (by rw [←cc_star,cc,star_star]),←hm,←mul_assoc,← mul_assoc,show A*star A=1 from g.2,one_mul]
    rw [mul_assoc,hh,mul_assoc]
  let Q:=1-P; let W:=N*star N+Q; have hQ:IsStarProjection Q:=h.one_sub
  have hh : victory P A C N=W*C := by rw [victory,hi, thud h.one_sub (by rw [sub_mul,cc_sub,cc_one, hg,one_mul,mul_sub,mul_one])]; unfold W; rw [add_mul]
  have hy : W*P=P*W:=by
    have hx:star N *P=star N:= by nth_rw 1 [←h.isSelfAdjoint]; rw [←star_mul,hN]
    unfold W Q; rw [add_mul,mul_add,mul_assoc,hx,←mul_assoc P N,hN,mul_sub,sub_mul,one_mul,mul_one]
  have he: stage P (victory P A C N)=W*C:=by rw [hh,sharp h]; rw [← mul_assoc,← hy,mul_assoc _ P,hg,mul_assoc] -- goal P*(W*C)=W*C*cc P, doesn't need cc_mul?
  let F:Op n:=(1-t) • 1+t • W
  have hd: stage P (straightC P A C N t)= F*C:=by rw [straightC,stage_p,he,sharp h hg]; unfold F; rw [add_mul ((1-t) • (1:Op n)),Algebra.smul_mul_assoc,Algebra.smul_mul_assoc,one_mul]; ext; simp [Complex.real_smul]
  let s:ℝ:=(r*r)⁻¹; have hrr:1≤r*r:=by nlinarith -- check
  have hs':0<s:= inv_pos.mpr (zero_lt_one.trans_le hrr); have ht':s≤1:=inv_le_one_of_one_le₀ hrr
  have hj:s • (1:Op n)≤W:= by unfold W; calc
    _ = s • P + s • Q:= by rw [← smul_add]; unfold Q; rw [add_sub_cancel]
    _ ≤ _:=add_le_add (solid_p h hr hz p) (smul_le_of_le_one_left hQ.nonneg ht') -- tune
  have hu:s • (1:Op n)≤F:=by calc
    _=(1-t) • (s • (1:Op n))+t • (s • (1:Op n)):=by rw [←add_smul]; simp
    _ ≤ _:= add_le_add (smul_le_smul_of_nonneg_left (smul_le_of_le_one_left zero_le_one ht') (sub_nonneg.mpr hf)) (smul_le_smul_of_nonneg_left hj ht)
  obtain ⟨T,l,w⟩:= norms_le_inv hs' hu
  exact ⟨star C*T,by rw [hd,←mul_assoc, mul_assoc F, show C*star C=1 from hs.2,mul_one,l],(norm_mul_le ..).trans (by rw [norm_star,CStarRing.norm_of_mem_unitary hs,one_mul]; simpa [s] using w)⟩
end YM.CF.Dial
