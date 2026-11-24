import YM.SU5.Circuit.Cliff
set_option autoImplicit false
noncomputable section
namespace YM.Regis.Circuit
open Function Filter Metric Lattice Laurent Next.Free Bloch Finset CF CF.Lat CF.Jill CF.Ember CF.Flare CF.Onyx CF.Fir
open Precision Exterior Matrix RG Work.F06
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix
variable {n:Side}{M:Bed}{q:Clip}{η σ C v:ℝ}
variable {ι υ γ:Type*}[Fintype ι][Fintype υ][Fintype γ][DecidableEq ι][DecidableEq υ][DecidableEq γ]
variable (x:Floor M q n v C)(L:M.covered σ C)(u:0<σ)
abbrev hector (A:Site n→ Matrix ι υ ℂ):= rotations n ι * fiber A * ((stageVolume n)⁻¹ • (rotations n υ)ᴴ)
lemma mix_of (A: Site n→Matrix ι υ ℂ){X:Matrix (Co n ι) (Co n υ) ℝ}(e: Expanse n A X): hector A = approached X:=by
 unfold Expanse Runs at e; rw [hector,←e, Matrix.mul_assoc, Matrix.mul_smul, (rotations_crew n υ).2.1,smul_smul,inv_mul_cancel₀ (stage_ne n),one_smul,Matrix.mul_one]
lemma hector_mul (A:Site n→Matrix ι υ ℂ)(B:Site n→Matrix υ γ ℂ): hector A*hector B=hector (fun i=> A i* B i) := by
 let X:= rotations n υ; have hx: ((stageVolume n)⁻¹ • Xᴴ)*X=1:=by rw [Matrix.smul_mul,(show Xᴴ*X=_ from (rotations_crew ..).2.2),smul_smul, inv_mul_cancel₀ (stage_ne _),one_smul]
 unfold hector; rw [← fiber_mult]; simp_rw [Matrix.mul_assoc]; rw [← Matrix.mul_assoc ((stageVolume n)⁻¹ • (rotations n υ)ᴴ),hx]; simp
lemma hector_herm (A:Site n→ Matrix ι ι ℂ)(h:∀ p,(A p).IsHermitian): (hector A).IsHermitian:=by
 unfold hector IsHermitian; rw [Matrix.mul_smul, Matrix.conjTranspose_smul,Matrix.conjTranspose_mul,Matrix.conjTranspose_conjTranspose, Matrix.conjTranspose_mul,fiber_H]; simp only [stageVolume,star_inv₀,star_pow,star_natCast,show (fun i:Site n=> (A i)ᴴ)=A from funext fun i=> (show _ from h i),Matrix.mul_assoc]
lemma comatic (N: Side): hector (fun i:Site N=> signal 1 1 (rubyM i))= approached (Exterior.d 1 N):=by
 have hh:= mix_of _ (expanse (cobound 1) (cobound_safe _) N); change _=approached ((cobound 1).acts N); rw [←hh]; congr 1; ext1 i; rw [tab,reading,signal_unit]
variable (M n)
def rimble : Matrix (Body 2 n) (Body 2 n) ℂ := hector fun i:Site n=> Cov M (rubyM i)
lemma rim_left : ∃ U:Matrix (Body 1 n) (Body 2 n) ℂ, rimble n M = approached (Exterior.d 1 n)*U:=by
 refine ⟨hector (fun i:Site n=> (cliffMap M (rubyM i))⁻¹ * mirage 1 1 (rubyM i)),?_⟩; unfold rimble Cov; rw [← comatic n,hector_mul]; simp_rw [Matrix.mul_assoc]
lemma rimflare (i j:Site n)(z:Cover)(e:i-j= wrap n z)(a b:TypeFace 2): rimble n M (i,a) (j,b)= (stageVolume n)⁻¹ *∑ p:Site n,charK (rubyOff n) p z * Cov M (rubyM p) a b:=by
 rw [rimble,hector,Matrix.mul_smul,Matrix.smul_apply,smul_eq_mul]; congr 1; rw [Matrix.mul_apply,Fintype.sum_prod_type]; apply sum_congr rfl; intro k _; rw [Finset.sum_eq_single b]; swap; · intro l _ he; simp [rotations,Ne.symm he]; -- tune
 swap; · simp
 rw [rot_fiber,← ruby_wrap,← e]; simp only [conjTranspose_apply, rotations, Matrix.of_apply,ite_true]; rw [Complex.star_def,cell_bar,cell_duality k (i-j),cell_sub,cell_duality i k,cell_duality j k]; ring
variable {M n}
include L u x
lemma rim_wins (e:Even n.val):rimble n M * (approached (M.metric.acts n))* approached (d 1 n)= approached (d 1 n):=by
 rw [← comatic n, ← mix_of _ (expanse M.metric (Row.rights σ C L.2.1 u.le) n)]; rw [rimble, hector_mul,hector_mul]; simp_rw [Cov, dizzy x L u _ e]
lemma rim_glows (e:Even n.val): (rimble n M).IsHermitian:= hector_herm _ (by intro i; unfold Cov; rw [mirage_herm 1 _ (ruby_pigment i)]; apply Matrix.isHermitian_mul_mul_conjTranspose; exact (clip_beam x L u i e).1.inv) -- tune
-- char real covariance comparator
lemma coin_down (e: Even n.val)(b:ℝ)(Y:Matrix (Body 2 n) (Body 2 n) ℝ)
 (W:Matrix (Body 1 n) (Body 2 n) ℝ) (w:Y=d 1 n*W) -- only cols needed
 (Lz:Y.transpose*M.metric.acts n*d 1 n=b•d 1 n): approached Y=(b:ℂ) • rimble n M:=by -- Lz orientation? want T=CM*T= C*Md*W... target via T^T*M*d=b*d transpose -> d^TM^T*T=b*d^T; need C=d*U, Cᴴ=C.
 let S:=d 1 n; let p:=M.metric.acts n; let C:= rimble n M; have h: C*approached p * approached S= approached S:=rim_wins x L u e
 have hx:C * approached p* approached Y=approached Y:=by rw [w,prom_mul,←Matrix.mul_assoc,h]
 have hw:approached p=(approached p)ᴴ:=by rw [←prom_adj, (show p.transpose=p from x.symmetric.1)]
 obtain ⟨K,Kx⟩:= rim_left n M; have hh:Cᴴ=C:= rim_glows x L u e
 calc approached Y=C*approached p*approached Y:= hx.symm
      _ = (approached Y.transpose * approached p*C)ᴴ := by nth_rw 2 [hw]; rw [prom_adj,conjTranspose_mul,conjTranspose_mul,hh,conjTranspose_conjTranspose,conjTranspose_conjTranspose]; rw [Matrix.mul_assoc]
      _ = _ := by
         have ht: approached Y.transpose * approached p*C = (b:ℂ) • C:=by rw [show C=_ from Kx, ←Matrix.mul_assoc, ←prom_mul, ←prom_mul, (show _=b • _ from Lz), show approached (b • d 1 n)=(b:ℂ)•approached (d 1 n) by ext i j; simp [approached],Matrix.smul_mul]
         rw [ht,Matrix.conjTranspose_smul,hh,Complex.star_def,Complex.conj_ofReal]
end YM.Regis.Circuit
#print axioms YM.Regis.Circuit.coin_down
#print axioms YM.Regis.Circuit.rimflare
