import YM.SU5.Relativistic.NorthL
/-! # Energy aliases. Need CONTROL signs beyond given sponsorship.
 exp(sign σ*λ E). σ=1 at original future real contour. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Crest.Sleet
open Function Set Filter Topology NormedSpace MeasureTheory Metric Real Finset Lattice Next.Free
open Laurent Bloch Fir Jill Ember Shore
open scoped Topology BigOperators Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace
local notation "I"=>Complex.I

abbrev sg (b:Bool):ℝ:= if b then -1 else 1
def inkH (k: Behind)(j:WalkA):ℝ:= 2*(∏ a:Fin 3,Real.sinc (levelx k j a/2))^8
lemma leased (k: Behind)(j:WalkA): bleat k j=(inkH k j:ℂ):=by unfold bleat inkH skirt; push_cast; rfl
def nodes (b: Bool)(k:Behind)(j:WalkA)(n:ℤ):ℝ:= Real.exp (-amp k j*(sg b * n))
-- f sum column P reciprocal
private def vertexK (k: Behind)(j:WalkA)(b:Bool)(i:Axis) : ℂ:= (tack (fun i=> (levelx k j i : ℂ)) (Complex.I * ((sg b*amp k j:ℝ):ℂ))) i
def tears (k:Behind)(j:WalkA):ℝ:= inkH k j * sponsor (amp k j) 8
def axialB (k:Behind)(j:WalkA)(b:Bool)(i:Axis)(n:ℤ):= ((tears k j*nodes b k j n:ℝ):ℂ)*vertexK k j b i
variable {k:Behind}(p:k∈sunshine)(b:Bool) (n:ℤ)
include p
private lemma pull (j:WalkA)(h:4 ≤ sg b*n):
   let a:= amp k j
   integrated (smoothZip a 8) n=(↑(sponsor a 8*nodes b k j n:ℝ):ℂ) ∧ integrated (biasStamp (smoothZip a 8)) n= (↑((sg b*a)*sponsor a 8 * nodes b k j n:ℝ):ℂ) :=by
 intro a; have ha:=amp_pos p j; let s:= (n:ℝ)
 cases b
 · simp only [sg,Bool.false_eq_true,↓reduceIte,one_mul] at h
   simp only [sg,Bool.false_eq_true,↓reduceIte,nodes,one_mul]
   exact ⟨lapel ha _ (by push_cast; linarith),shifted ha 7 (by push_cast; linarith)⟩
 simp only [sg,if_true,nodes,neg_mul,one_mul, mul_neg,neg_neg] at h ⊢ -- sg simplifier nests
 have hf:= trough ha 8 (w:=-s) (by push_cast; linarith [show 4 ≤ -s from h]); have he:= downhill ha 7 (w:=-s) (by push_cast; linarith [show 4 ≤ -s from h]); simpa [sg,a,nodes,s] using And.intro hf he
private lemma yieldBill (j:WalkA)(i:Axis)(h:4 ≤ sg b*n) : integrated (liftH k i j) n=axialB k j b i n:=by
 have ⟨he,hf⟩:= pull p b n j h; let a:= amp k j
 induction i using Fin.lastCases with
 | last=>
    rw [show liftH k _ j=(fun t=> bleat k j* I*biasStamp (smoothZip a 8) t) from ?_]; swap; · funext t; unfold liftH tack; rw [Fin.lastCases_last]; unfold shortLap; rw [mul_left_comm,vertical_s,mul_assoc]
    unfold integrated; simp_rw [mul_left_comm (surge _ _)]; unfold integrated at hf; unfold a; rw [integral_const_mul,hf] -- reducibility
    unfold axialB vertexK tack; rw [Fin.lastCases_last]; rw [leased]; unfold tears; push_cast; ring
 | cast a'=>
    rw [show ∀ i:Fin 3,liftH k i.castSucc j=(fun t=> ↑(levelx k j i)*bleat k j* smoothZip a 8 t) from fun i=> by funext t; rw [liftH,shortLap,tack_left,mul_assoc]]; unfold integrated; simp_rw [mul_left_comm (surge _ _)]; unfold integrated at he; unfold a; rw [integral_const_mul,he]; unfold axialB vertexK tack; rw [Fin.lastCases_castSucc,leased]; unfold tears; push_cast; ring
lemma bladeV(i:Axis)(h:4 ≤ sg b*n) :HasSum (fun j=> axialB k j b i n) (pluse n (fun t=>heatLine k t i)) := by simp_rw [← yieldBill p b n _ i h]; exact radical p ..
omit p in
private lemma insect(k:Behind)(p:k∈sunshine)(j:WalkA)(a:Fin 3) : Real.sinc (levelx k j a/2)≠0:=by
 have hv:=whirlV p j a; have hp:=p a (Set.mem_univ _)
 rw [Real.sinc_of_ne_zero (div_ne_zero hv two_ne_zero)]; refine div_ne_zero ?_ (div_ne_zero hv two_ne_zero); unfold levelx; rw [show (k a+ 2*π*j a)/2=k a/2+(j a:ℝ)* π by ring, Real.sin_add_int_mul_pi]; simp only [mul_ne_zero_iff] -- orientation statement check
 refine ⟨zpow_ne_zero (j a) (show (-1:ℝ)≠0 by norm_num),?_⟩; exact (Real.sin_pos_of_pos_of_lt_pi (half_pos hp.1) (by linarith only [hp.1,hp.2])).ne'
lemma tear_pos (j:WalkA): 0<tears k j:=by
 have ha: (0:ℝ)<amp k j:=amp_pos p j; have hv: 0< inkH k j:= mul_pos (by norm_num) ((Even.pow_pos (by decide:Even 8)) (Finset.prod_ne_zero_iff.mpr (fun a _=>insect k p j a))) -- tune
 unfold tears sponsor; have hz:=weight_pos ha; positivity
-- sign at (2,0) = ? need direct
abbrev faceR (k:Behind)(t:ℝ):ℂ:= heatLine k t ((2:Fin 3).castSucc) - I * heatLine k t TA
def pulseCost (k: Behind)(b:Bool)(j:WalkA) := levelx k j 2 + sg b * amp k j
set_option maxHeartbeats 600000 in
lemma signedV (h:4 ≤ sg b*n) :HasSum (fun j:WalkA=> (↑(tears k j * pulseCost k b j*nodes b k j n):ℂ)) (pluse n (faceR k)):=by
 let i:Axis:= (2:Fin 3).castSucc; let f (i:Axis): ℝ→ℂ:=fun t=> heatLine k t i
 have hc (u:Axis) : IntegrableOn (f u) screen:=by
    have ht: ContinuousOn (fun t=>heatLine k t u) (Set.Icc (-π) π):= ContinuousOn.comp (f:=fun t:ℝ=> (k,t)) (heat_cont (U:={k}) isCompact_singleton (Set.singleton_subset_iff.mpr p) u) ((continuous_const.prodMk continuous_id).continuousOn) (fun x h=>⟨Set.mem_singleton _,h⟩)
    exact ht.integrableOn_Icc.mono_set Ioc_subset_Icc_self
 rw [show faceR k=(fun x=> f i x + (-I)*f TA x) from funext fun x=>by unfold faceR; rw [neg_mul, sub_eq_add_neg], pluse_add _ (hc _) (show IntegrableOn (fun x=> -I*f TA x) screen volume from (hc TA).const_mul _), pluse_const]; convert (bladeV p b n i h).add ((bladeV p b n TA h).mul_left (-I)) using 1
 ext1 j; simp only [i,axialB,vertexK,TA, tack,Fin.lastCases_last,Fin.lastCases_castSucc,pulseCost]; push_cast; ring_nf; simp
lemma strictV (j:WalkA) : 0<sg b*pulseCost k b j:=by
 have he : |levelx k j 2| < amp k j:=by
    have hQ: (levelx k j 2)^2 < (amp k j)^2:=by
       rw [amp_sq]; -- expand limited
       have hz:=sq_pos_of_ne_zero (whirlV p j 0); rw [Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ,Fin.sum_univ_zero]; change _ < levelx k j 0 ^2+(levelx k j 1 ^2+(levelx k j 2 ^2+0)); linarith [sq_nonneg (levelx k j 1)]
    exact (sq_lt_sq₀ (abs_nonneg (levelx k j 2)) (amp_pos p j).le).1 ((sq_abs (levelx k j 2)).symm ▸ hQ)
 obtain ⟨l,h⟩:=abs_lt.mp he; cases b<;>simp [sg,pulseCost]<;>linarith
omit p in
lemma axial_advance (k: Behind)(j:WalkA)(i:Axis)(q:ℤ) : axialB k j b i (n+q)=axialB k j b i n *(nodes b k j q:ℂ):=by
 have he:nodes b k j (n+q)=nodes b k j n * nodes b k j q:=by unfold nodes; rw [Int.cast_add,mul_add,mul_add,Real.exp_add]
 unfold axialB; rw [he]; push_cast; ring
lemma axial_length (j:WalkA)(a:Axis): ‖axialB k j b a n‖ ≤ ‖axialB k j b TA n‖:=by
 induction a using Fin.lastCases with
 | last=> exact le_rfl
 | cast a=> unfold axialB; rw [norm_mul,norm_mul]; refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
            have hx:= amp_ge k j a; unfold vertexK; rw [tack_left,tack_right,norm_mul,Complex.norm_I,one_mul]; simp only [Complex.norm_real,Real.norm_eq_abs,abs_mul]; have hl:=amp_pos p j; cases b <;> simpa [sg,abs_of_pos hl] using hx
lemma axial_vertical (j:WalkA): (-(↑(sg b):ℂ)*I)*axialB k j b TA n=(↑‖axialB k j b TA n‖:ℂ):=by
 unfold axialB vertexK; rw [tack_right,norm_mul,norm_mul,Complex.norm_I,one_mul]; have hx:=tear_pos p j; have ht:0<nodes b k j n:=Real.exp_pos _; have hp:=amp_pos p j
 rw [Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg (mul_pos hx ht).le, Real.norm_eq_abs,abs_mul,abs_of_pos hp]; cases b<;> simp [sg] <;> ring_nf <;> simp
end YM.CF.Crest.Sleet
