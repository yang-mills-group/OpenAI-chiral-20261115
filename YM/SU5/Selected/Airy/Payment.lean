import YM.SU5.Selected.Airy.Signal
import YM.CF.Lattice.Reference
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 300000
noncomputable section
namespace YM.CF.Crest.Airy
open Function Filter Topology Metric NormedSpace Lattice Laurent Bloch Next.Free MeasureTheory
open Ember Jill Fir Shore Real Finset Fock Rush Lat
open scoped Topology BigOperators Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace ComplexOrder
local notation "I"=>Complex.I
local notation "φ" => 2 * π
local instance : Fact (0<φ):= ⟨piRank⟩
attribute [local instance] opCStarAlgebra
local instance : CompactSpace grounds:= isCompact_iff_compactSpace.mp groundsCompact
def stakesize {n m:Type*}[Fintype n][DecidableEq n][Fintype m][DecidableEq m] (K:n→m→ℝ): ℝ := 1+∑ i,∑ j, K i j* ‖(Matrix.single i j 1:WRect n m)‖
-- remove X implicit
lemma settlem {n m:Type*}[Fintype n][DecidableEq n][Fintype m][DecidableEq m] (K:n→m→ℝ)(p:∀ i j,0≤K i j): 0<stakesize K ∧ ∀ (A:WRect n m)(x:ℝ),0≤x → (∀ i j, ‖A i j‖ ≤ K i j*x) → ‖A‖ ≤ stakesize K * x:=by
 have hf (i:n)(j:m):0 ≤ K i j* ‖(Matrix.single i j 1:WRect n m)‖:= mul_nonneg (p i j) (norm_nonneg _); unfold stakesize; constructor
 · exact add_pos_of_pos_of_nonneg zero_lt_one (sum_nonneg (fun i _=>sum_nonneg (fun j _=> hf i j)))
 intro A x hx h; have e:  (∑ i,∑ j, A i j • (Matrix.single i j 1: WRect n m))=A:= by simp_rw [Matrix.smul_single, smul_eq_mul,mul_one]; exact Matrix.sum_sum_single A
 nth_rw 1 [←e]; refine (norm_sum_le ..).trans ?_; rw [add_mul,one_mul,sum_mul]; apply le_trans _ (le_add_of_nonneg_left hx); refine sum_le_sum (fun i _=> ((norm_sum_le ..).trans ?_)); rw [sum_mul]; apply sum_le_sum; intro j _; rw [norm_smul,mul_right_comm]; exact mul_le_mul_of_nonneg_right (h i j) (norm_nonneg _)
lemma raise_sub {n:Type*}[Fintype n][DecidableEq n](D:Side)(i:Axis)(F G:Coast→Op n): raiser D i (F-G)=raiser D i F-raiser D i G:=by
 ext v a b; simp [levy,raiser,Finset.sum_apply,Matrix.sum_apply,sum_sub_distrib,mul_sub]
lemma raise_hold {n:Type*}[Fintype n][DecidableEq n]{R:ℝ}{F:Coast→Op n}(h:∀ i, ‖F i‖≤R)(D:Side)(i:Axis)(w:Coast): ‖raiser D i F w‖ ≤ R:=by
 rw [raiser]; simp only [Pi.smul_apply,Finset.sum_apply,norm_smul,norm_inv, Complex.norm_natCast,Function.comp];
 refine (mul_le_mul_of_nonneg_left ((norm_sum_le ..).trans (sum_le_sum (fun k (_:k∈ Finset.range D.val)=> h (raised D i k w)))) (by positivity)).trans_eq ?_; rw [Finset.sum_const,Finset.card_range,nsmul_eq_mul]; field_simp [Lat.nPos D]

variable (n p:ℕ)(G:Side)(g:8≤G.val)(e:n≥4)
local notation "V"=> plinth G n p e
local notation "Y"=> artisans G n p e
local notation "X"=>children G n p
local notation "M"=> utility
local notation "ρ"=> Real.exp (-(1/2))
local notation "W"=>screens n p e
def collage(w:Coast):Op (Fin p):= (X w)ᴴ*Y w
def solvent (w:Coast): Op (Fin p):= (↑(soap G (pier w))^2:ℂ) • 1 -- coerce before pow
private def tapeF(z:Torch)(t:roundC): Op (Fin p):= (nails n p t)ᴴ*( (1:Op SpinIdx) -zen (M (Ε z t))) * staves p t
lemma screens_coll (z:Torch)(t:roundC): collage n p G e (Ε z t)= (↑(soap G z)^2:ℂ) • (tapeF n p z t * screens n p e z):=by
 unfold collage tapeF; rw [children,artisans]; unfold plinth; simp only [here_p,here_l,Matrix.conjTranspose_smul,Matrix.smul_mul,Matrix.mul_smul,Matrix.mul_assoc]; simp only [sq,mul_smul,Complex.star_def,Complex.conj_ofReal]
lemma file_pay (i j:Fin p) : ∃ K:ℝ,0<K∧ ∀ x∈grounds, ∀ (D:Side)(t: roundC), ‖avg t D (fun t=>tapeF n p (road x) t i j) - (↑(φ⁻¹:ℝ):ℂ)* trove x true n p i j‖ ≤ K * ρ^D.val :=by -- will need uniform not per x, edit
 let a:ℕ:=n+i.val+j.val
 obtain ⟨K,hK,w⟩:= fares_all (- (a:ℤ)); refine ⟨K,hK,fun x hx D t=>?_⟩
 unfold tapeF; simp_rw [cofactor n p x _ hx]; have ht:= w D t x hx; rw [embark,printed,neg_neg] at ht; exact ht -- double neg within lambda? rw handles all? 
include e
private lemma height_bank : ∃ K:ℝ,0<K∧∀ x∈grounds,∀ (D:Side)(t:roundC), ‖(↑(D.val):ℂ)⁻¹ • (∑ s∈ range D.val, tapeF n p (road x) (t+s • tier D)) - ((↑(φ⁻¹:ℝ):ℂ) • trove x true n p)‖ ≤ K * ρ^D.val :=by
 choose Ks k e₁ using file_pay n p
 let y:= Ks
 obtain ⟨C,h⟩:=settlem y (fun i j=> (k i j).le); refine ⟨_,C, fun x w D t=>h _ _ (by positivity) (fun i j=>?_)⟩
 simp only [Matrix.sub_apply,Matrix.smul_apply,Matrix.sum_apply,smul_eq_mul]; exact e₁ i j _ w D t
-- moving symbolic only temporal
include g
lemma raises_time : ∃ K:ℝ,0<K ∧∀ (D:Side)(w:Coast), ‖raiser D (3:Axis) (collage n p G e) w-solvent p G w‖ ≤ K * ρ^D.val:=by
 obtain ⟨K,hK,e'⟩:= height_bank n p e; obtain ⟨b,h⟩:= isCompact_univ («X»:=Torch) |>.bddAbove_image ((continuous_pow 2).comp (soap_c G g)).continuousOn; obtain ⟨c,hc⟩:= isCompact_univ («X»:=Torch)|>.bddAbove_image ((screens_price n p e).norm.continuousOn); let R:=max 1 b; let S:=max 1 c; have hp:R>0:=zero_lt_one.trans_le (le_max_left ..); have hs:S>0:= zero_lt_one.trans_le (le_max_left ..)
 have hv(t:Torch):soap G t^2≤R:= (h (Set.mem_image_of_mem (fun x:Torch=> soap G x ^2) (Set.mem_univ t))).trans (le_max_right ..); have hw (t:Torch): ‖screens n p e t‖≤S:= (hc (Set.mem_image_of_mem (fun x:Torch=> ‖screens n p e x‖) (Set.mem_univ t))).trans (le_max_right ..)
 refine ⟨R*(K*S),by positivity,fun D w=>?_⟩
 let x:= pier w; let t:= lapse w; have e₂:Ε x t=w:=to_whole w; have h₀(s:ℕ): raised D (3:Axis) s w=Ε x (t+s •tier D):=by
    nth_rw 1 [←e₂]; funext i; cases i using Fin.lastCases with|last=> simp (config:={decide:=true}) [raised,Ε]| cast i=> simp (config:={decide:=true}) [raised,Ε,show (i.castSucc:Axis)≠3 from fun h₁=>Fin.castSucc_ne_last i h₁] -- tune
 let B:Op (Fin p):=(↑(D.val):ℂ)⁻¹ • (∑ s∈ range D.val, tapeF n p x (t+s • tier D)); let a:ℂ:=↑(soap G x)^2; let W':=screens n p e x;
 rw [show raiser D (3:Axis) (collage n p G e) w = a • (B * W') from ?_]; swap
 · unfold raiser a B W'; simp_rw [Pi.smul_apply,Finset.sum_apply,Function.comp,h₀,screens_coll,←Finset.smul_sum, Matrix.smul_mul, ships_add]; rw [smul_comm]
 change ‖a • _ - a • (1:Op (Fin p))‖≤_; rw [←smul_sub]; by_cases q:soap G x=0; · unfold a; rw [q]; simp only [Complex.ofReal_zero,zero_pow (by norm_num : (2:ℕ)≠0),zero_smul,norm_zero]; positivity
 obtain ⟨z,k,hx⟩:= soap_support G q; let A:= trove z true n p; let Z:=(↑(φ⁻¹:ℝ):ℂ) • A; have H₀: Z*W'=1:=by unfold Z W'; rw [hx,screens_r _ _ e z k,Matrix.smul_mul,Matrix.mul_smul,smul_smul]; have ht:= fit z true n p e k; rw [Matrix.mul_nonsing_inv A (A.isUnit_iff_isUnit_det.mp ht),←Complex.ofReal_mul,inv_mul_cancel₀ piRank.ne']; simp
 have ht : ‖B-Z‖ ≤ K * ρ^D.val:=by unfold B; rw [hx]; exact e' z k D t
 rw [←H₀,← Matrix.sub_mul,norm_smul]; refine mul_le_mul ?_ ((Matrix.l2_opNorm_mul ..).trans (mul_le_mul ht (hw _) (norm_nonneg _) (by positivity))) (norm_nonneg _) hp.le |>.trans_eq ?_
 · unfold a; rw [← Complex.ofReal_pow, Complex.norm_of_nonneg (by positivity)]; exact hv x
 ring
end YM.CF.Crest.Airy
open YM.CF.Crest.Airy
#print axioms raises_time
#print axioms raise_hold
