import YM.SU5.FiniteGaugeData.Drachma.Rehearse
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option synthInstance.maxSize 16000
set_option linter.flexible false
noncomputable section
namespace YM.SU5.FiniteGaugeData.Drachma
open Function Finset Filter Matrix Lattice Wilson RG Precision Exterior Tree Laurent Bloch
open Pressure Pressure.Tube Stores AnalyticBridge.MarginalMultiplier3b1d AnalyticBridge.LocalGaussianLaws AnalyticBridge.SectorAffine
 AnalyticBridge.NonflatCovarianceLocality.Matching PatchReads
open CF.Newt CF.Neige CF.Char Next.Fluctuations Next.SectorChange Next.SectorChange.Wisps Next.SectorChange.Schur PhysicalNext.JointLoad Work.F03
open SectorNext.Vacuum.FlatTree Next.SectorChange.Rows Push.SectorMeasure
open scoped Topology ContDiff BigOperators Matrix Classical InnerProductSpace Kronecker Matrix.Norms.Frobenius
variable {c f:Side}{G:Gauge} {S:StepData c f} {T:Tube G S}{p:Clip} {a A σ C Λ x:ℝ} {P Q:Bed}
local notation "λ₀" => S.kernel.penalty
variable (F : Forest S.ratio)

-- ∥tail∥ in flat or arbitrary angling array of colors at faces. Scheme with majorants pointwise useful later for nonlinear tails; no lower bound use on sharp lines yet.
namespace Toffee
variable {B:Type}[NormedAddCommGroup B][NormedSpace ℝ B][CompleteSpace B]
section
variable {n:Type}[Fintype n]
abbrev bin(A:n→B): PiLp 2 (fun _:n=> B):=WithLp.toLp 2 A
abbrev cash(A:n→ B):ℝ:= ‖bin A‖
omit [NormedSpace ℝ B] [CompleteSpace B] in
lemma pay(A:n→B): cash A^2 =∑ i:n, ‖A i‖^2:= PiLp.norm_sq_eq_of_L2 ..
omit [NormedSpace ℝ B] [CompleteSpace B] in
lemma pay_pos(A:n→B): 0 ≤ cash A:= norm_nonneg _
end
abbrev tar(σ:ℝ)(x:ℕ):ℝ:= Real.exp (-σ*x)
lemma tar_p(σ:ℝ)(x:ℕ):0<tar σ x:= Real.exp_pos _
variable {R:PathData G}
section
variable (W:Cell f → B) (X:ℕ → Site f→ B) (q:PlaqAxes)(w:ℕ)
omit [NormedSpace ℝ B] [CompleteSpace B] in
lemma back (u:RG.Slot): cash (fun i:Site f=> W (slotFace u i)) ≤ cash W:=by
 let b:=wrap f u.offset
 apply le_of_pow_le_pow_left₀ two_ne_zero (pay_pos W)
 rw [pay,pay,Fintype.sum_prod_type]; rw [show (∑ i:Site f, ‖W (slotFace u i)‖^2)= _ from Equiv.sum_comp (Equiv.addLeft b) (fun i:Site f => ‖W (i,u.plaq)‖^2)]; exact sum_le_sum fun i _=>single_le_sum (fun j _=> sq_nonneg ‖W (i,j)‖) (mem_univ _)
-- allowing built-in conditional angular rotations: e norm here permits arbitrary rotations and (pointwise) contractions on the cell W.
lemma earned (h:R.Bounds p σ C Λ)(e:∀ i (k:Site f), ‖X i k‖ ≤ if w<(R.row q i).2.length then |(R.row q i).1| * ‖W (slotFace (R.row q i).2 k)‖ else 0):
 (∀ j:Site f, Summable fun i:ℕ=> X i j) ∧ cash (fun k:Site f=> ∑' i:ℕ, X i k)≤ C*tar σ w*cash W:=by
 obtain ⟨M,u,v⟩:=h.rows q; let musY(i:ℕ):= tar σ w*(|(R.row q i).1| *Real.exp (σ*(R.row q i).2.length))
 have zu : Summable musY:= u.mul_left _; have zv : ∑' i:ℕ,musY i ≤ C*tar σ w:=calc
    _ = tar σ w* ∑' i:ℕ, (|(R.row q i).1| * Real.exp (σ*(R.row q i).2.length)):= tsum_mul_left
          (f:=fun i=> _) -- tune
    _ ≤ _:= by simpa only [mul_comm C] using mul_le_mul_of_nonneg_left v (tar_p σ w).le
 have zp(i:ℕ):0≤ musY i:=mul_nonneg (tar_p σ w).le (M i)
 have hC(i:ℕ)(j:Site f): ‖X i j‖ ≤ musY i* ‖W (slotFace (R.row q i).2 j)‖:=by
    apply (e i j).trans; split; next h'=>
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _); unfold musY; rw [mul_left_comm]; apply le_mul_of_one_le_right (abs_nonneg _); unfold tar; rw [←Real.exp_add]; apply Real.one_le_exp; have hy:=mul_le_mul_of_nonneg_left (show (w:ℝ)≤ (R.row q i).2.length by exact_mod_cast h'.le) h.width.le; linarith only [hy]
    exact mul_nonneg (zp i) (norm_nonneg _)
 let ellY(i:ℕ):=bin (X i)
 have he(i:ℕ): ‖ellY i‖ ≤ musY i * cash W:= calc
    _ ≤ musY i * cash (fun j:Site f=> W (slotFace (R.row q i).2 j)) := by
       apply le_of_pow_le_pow_left₀ two_ne_zero (mul_nonneg (zp i) (pay_pos _))
       change cash (X i)^2≤_; rw [pay,mul_pow,pay,mul_sum]; refine sum_le_sum ?_; intro j _; rw [←mul_pow]; exact pow_le_pow_left₀ (norm_nonneg (X i j)) (hC i j) _
    _ ≤ _:=mul_le_mul_of_nonneg_left (back W _) (zp i)
 have hm:=zu.mul_right (cash W); have ht: Summable fun i=> ‖ellY i‖:= Summable.of_nonneg_of_le (fun i=>norm_nonneg _) he hm; let V:=∑' i:ℕ,ellY i
 have hT(k:Site f):HasSum (fun i=>X i k) (V k):=by exact ((PiLp.proj (𝕜:=ℝ) 2 (fun _ : Site f=>B) k).hasSum ht.of_norm.hasSum)
 refine ⟨fun i=>(hT i).summable,?_⟩; rw [cash, show bin _=V from ?_]; swap; · ext k; exact (hT k).tsum_eq
 apply (norm_tsum_le_tsum_norm ht).trans ((ht.tsum_mono hm he).trans _); rw [tsum_mul_right]; exact mul_le_mul_of_nonneg_right zv (pay_pos _)
end
abbrev fray(p:Clip) (σ C x:ℝ):= ((Real.sqrt (Fintype.card PlaqAxes:ℝ))/Real.sqrt p.direct)*(|C| *tar σ (till x))
lemma fray_p(p:Clip)(σ C x:ℝ): 0≤fray p σ C x:=by unfold fray tar; positivity
variable (V: Directions G f)
lemma ficio (h:T.up.Bounds T.high σ C Λ) (s:Signed)(r:ℝ):
 ∑ i:Twin f ⊕ Bond c, ‖Flat.omitted T r V (s,i)‖^2 ≤ fray T.high σ C r^2* ∑ i:Twin f ⊕ Bond c, ‖Flat.ideal T V (s,i)‖^2:=by
 let a:=Bid.pulled (Flat.labels V) s; let Q(j:Cell f):= faceCurl j a
 let κ:= fray T.high σ C r; let t:=|C| *tar σ (till r); have hi(i:PlaqAxes):
    (∑ j:Site f, ‖Flat.omitted T r V (s,.inl ((j,i),true))‖^2)≤ t^2* cash Q^2:=by
    let u(m:ℕ)(k:Site f):G.Color:=if till r<(T.up.row i m).2.length then (T.up.row i m).1 • Q (slotFace (T.up.row i m).2 k) else 0
    let v(k:Site f):=∑' i,u i k; have he: cash v ≤ C*tar σ (till r)*cash Q:=(earned Q u i (till r) h (fun i j=>by unfold u; split <;> simp [*,norm_smul,Real.norm_eq_abs])).2
    have hh: C* tar σ (till r)≤t:=mul_le_mul_of_nonneg_right (le_abs_self C) (tar_p _ _).le; change (∑ j:Site f, ‖v j‖^2) ≤_; rw [←mul_pow,←pay]; exact pow_le_pow_left₀ (pay_pos v) (he.trans (mul_le_mul_of_nonneg_right hh (pay_pos _))) 2
 let I:=T.high.direct; have hI:0<I:=T.high.quadratic_pos; have hL : (Fintype.card PlaqAxes:ℝ)*t^2=κ^2*I:=by
    unfold t I κ fray; simp only [mul_pow,div_pow,Real.sq_sqrt (Nat.cast_nonneg _),Real.sq_sqrt T.high.quadratic_pos.le]; have hp:=T.high.quadratic_pos; field_simp
 have hm (i:Cell f): ‖Flat.ideal T V (s,.inl (i,false))‖^2=I* ‖Q i‖^2:=by
    unfold Flat.ideal xLin; simp only [Sum.elim_inl,Bool.false_eq_true,↓reduceIte,norm_smul,mul_pow, Real.norm_eq_abs, sq_abs,Real.sq_sqrt T.high.quadratic_pos.le] -- tune
    rfl
 rw [Fintype.sum_sum_type, Fintype.sum_sum_type]; rw [Fintype.sum_prod_type (f:=fun i:Twin f=>_), Fintype.sum_prod_type (f:=fun i:Twin f=> ‖Flat.ideal T V (s,.inl i)‖^2)]; simp_rw [Fintype.sum_bool]
 have h0(i:Cell f): ‖Flat.omitted T r V (s,.inl (i,false))‖^2=0:=by simp [Flat.omitted]
 have hF (i:Bond c): ‖Flat.omitted T r V (s,.inr i)‖^2=0:=by simp [Flat.omitted] -- tune
 simp_rw [h0,hF,add_zero, hm,sum_const_zero,add_zero,sum_add_distrib]; apply le_trans _ (mul_le_mul_of_nonneg_left (le_trans (b:=(∑ i:Cell f, ‖Flat.ideal T V (s,.inl (i,true))‖^2)+ (∑ i:Cell f,I* ‖Q i‖^2)) (le_add_of_nonneg_left (sum_nonneg fun i _=>sq_nonneg _)) (le_add_of_nonneg_right (sum_nonneg fun i _=>sq_nonneg _))) (sq_nonneg κ)); rw [←mul_sum,← pay Q,←mul_assoc,←hL,Fintype.sum_prod_type,sum_comm]; apply (sum_le_sum (s:=univ) (fun i _=>hi i)).trans_eq; rw [sum_const,card_univ,nsmul_eq_mul,mul_assoc]
end Toffee
end YM.SU5.FiniteGaugeData.Drachma
