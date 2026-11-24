import YM.SU5.Reconstruction.Crease.Hahn
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.BridgeClub
open Function Set Filter MeasureTheory Spectral Analysis Metric ContinuousLinearMap Anvil Picket CrossedFrame
open scoped BigOperators Topology InnerProductSpace ComplexOrder NNReal ENNReal Complex Classical
variable {H:Hilbert}{M:Net H}{Ω:H}(a:ℂ)(k:a.re=1/2)
variable {N : H.Op}(q:N∈M.commutant)(m:‖N‖≤1)
include m q k
lemma allCash (Ω:H) : ∃ y:H.Op,Taut M y ∧ ‖y‖≤1 ∧ ∀ A:H.Op, Taut M A→ (inner ℂ (A Ω) (N Ω)).re=2*ear Ω a A y := by
 let τ:= {x:H.Op // Taut M x}; let S:= Finset τ; let l:Ultrafilter (Finset {x:H.Op // Taut M x} × ℕ) := Ultrafilter.of atTop -- reduc
 let δ(n:ℕ):ℝ:= ((n:ℝ)+1)⁻¹; have ht:Tendsto δ atTop (𝓝 0):= by simpa only [one_div] using (show Tendsto (fun n:ℕ=>1/((n:ℝ)+1)) atTop (𝓝 0) from tendsto_one_div_add_atTop_nhds_zero_nat) -- tune
 choose Y V r G using fun (F:Finset {x:H.Op // Taut M x} × ℕ)=> allot (M:=M) Ω a k q m (fun i:↥(F.1)=>(i.val).val) (fun i=> i.val.property) (δ F.2) (by unfold δ; positivity)
 obtain ⟨B,b,u⟩:= Limit_World l zero_le_one r
 have hg:Taut M B:=⟨staysClosed u (fun i=>(V i).1),staysSelf u (fun i=>(V i).2)⟩; refine ⟨B,hg,b,fun A e=>?_⟩
 let D:= ear Ω 1 A N
 have hδ(i:Nat):δ i ≥0:= by unfold δ; positivity
 have hv: Tendsto (fun j: Finset {x:H.Op // Taut M x} × ℕ=>2*ear Ω a A (Y j)) l (𝓝 (2*ear Ω a A B)):= tendsto_const_nhds.mul ((Complex.continuous_re.tendsto _).comp ((u.confirms (A Ω) Ω).const_mul (star a)))
 have hy:∀ᶠ i in (l:Filter (Finset {x:H.Op // Taut M x} × ℕ)), dist D (2*ear Ω a A (Y i)) ≤ δ i.2 := by
    apply Eventually.filter_mono (show (l:Filter (Finset {x:H.Op // Taut M x} × ℕ)) ≤ atTop from Ultrafilter.of_le _) (eventually_atTop.mpr ?_)
    exact ⟨(({⟨A,e⟩}:Finset {x:H.Op // Taut M x}),0), fun F v=> (G F ⟨⟨A,e⟩,v.1 (Finset.mem_singleton_self _)⟩).le⟩
 have he : dist D (2*ear Ω a A B) ≤ 0:= le_of_tendsto_of_tendsto (tendsto_const_nhds.dist hv) (((ht.comp (show Tendsto (Prod.snd : Finset {x:H.Op // Taut M x} × ℕ → ℕ) atTop atTop from ?_))).mono_left (Ultrafilter.of_le atTop)) hy
 · simpa only [D,ear,star_one,one_mul] using dist_le_zero.mp he
 apply Filter.tendsto_atTop.2; intro b; filter_upwards [eventually_ge_atTop ((∅: Finset {x:H.Op // Taut M x}),b)] with i h; exact h.2
omit m q k
lemma halves (M:Net H)(A:H.Op)(p:A∈M): ∃ x y:H.Op, Taut M x∧ Taut M y ∧ A=x + Complex.I • y:= by
 let x:= (1/2:ℂ) • (A+star A); let y:= (-(Complex.I/2)) • (A-star A)
 have e(c:ℂ):star (c • A)= star c • star A:= star_smul ..; refine ⟨x,y,⟨m_smul _ (add_mem p (star_mem p)),?_⟩,⟨m_smul _ (sub_mem p (star_mem p)),?_⟩,?_⟩
 · unfold x IsSelfAdjoint; simp [star_smul, add_comm] -- tune
 · unfold y IsSelfAdjoint; rw [star_smul, show star (- (Complex.I/2))=Complex.I/2 from ?_,star_sub,star_star]; module;
   simp [neg_div]
 unfold x y; rw [smul_smul, show Complex.I * -(Complex.I/2)=1/2 from (by rw [mul_neg,← mul_div_assoc]; norm_num)]; module
-- ensures *
include q k m
lemma allScripts (Ω:H)(h:IsSelfAdjoint N): ∃ y:H.Op,Taut M y ∧ ∀ A∈M, inner ℂ (A Ω) (N Ω)=star a * inner ℂ (A Ω) (y Ω)+ a*inner ℂ (y Ω) (star A Ω):=by
 obtain ⟨y,e,-,p⟩:=allCash a k q m Ω; let f(A:H.Op):= star a * inner ℂ (A Ω) (y Ω)+a*inner ℂ (y Ω) (star A Ω)
 have hv(A:H.Op)(v:Taut M A):inner ℂ (A Ω) (N Ω)= f A:=by
    have hz:= p A v; have ht:=noImag v.2 h (show Commute A N from VonNeumannAlgebra.mem_commutant_iff.mp q _ v.1) Ω; unfold ear at hz
    let w:= star a * inner ℂ (A Ω) (y Ω); have hy:f A=w+star w:= by unfold f w; rw [star_mul', star_star, v.2.star_eq, show star (inner ℂ (A Ω) (y Ω))=inner ℂ (y Ω) (A Ω) from inner_conj_symm _ _]
    rw [hy]; exact Complex.ext (by simp only [Complex.add_re,Complex.star_def,Complex.conj_re]; change _=w.re+w.re; change _= 2*w.re at hz; linarith) (by simp only [Complex.add_im,Complex.star_def,Complex.conj_im, add_neg_cancel]; exact ht)
 refine ⟨y,e,fun x v=>?_⟩; obtain ⟨d,A,hd,hA,rfl⟩:=halves M x v
 change _= f (d+Complex.I • A); rw [show f (d+Complex.I • A)=f d+star Complex.I * f A from ?_]
 · rw [add_apply,smul_apply,inner_add_left,inner_smul_left,hv d hd,hv A hA]; rfl
 unfold f; simp only [star_add,star_smul,Complex.star_def,add_apply,smul_apply,inner_add_left,inner_add_right,inner_smul_right,inner_smul_left,Complex.conj_I]; ring -- conj simplification
end YM.BridgeClub
