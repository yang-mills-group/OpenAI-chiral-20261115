import YM.SU5.FiniteGaugeData.Crest.Alps

/-! # Parallel flyers: a frequency box used with the SAME `Crest` normalization.
Sharpening the signal to nonzero excited state needs temporal Hankel arguments, after Male,
not one subtraction on a scalar. This file analytic, no new law assumptions. Units radians. -/
set_option autoImplicit false
set_option maxHeartbeats 350000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Crest.Airy
open Function Filter Metric NormedSpace Lattice Laurent Bloch Next.Free MeasureTheory
open Ember Jill Fir Shore Real
open scoped Topology BigOperators Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace
local notation "I"=>Complex.I
abbrev Facet3 := Fin 3 → ℝ
abbrev FaceL:= Fin 3→ℤ
abbrev Ε {V:Type*} (x:Fin 3→V)(y:V) : Axis → V:= Fin.snoc x y -- Greek large
@[simp] lemma node₂ {V:Type*}(x:Fin 3→V)(y:V) : Ε x y 2=x 2:= Fin.snoc_castSucc _ _ (2:Fin 3)
@[simp] lemma node₃ {V:Type*}(x:Fin 3→V)(y:V) : Ε x y 3=y := Fin.snoc_last _ _
@[simp] lemma nodeV {V:Type*}(x:Fin 3→V)(y:V) (i:Fin 3) : Ε x y i.castSucc=x i:= Fin.snoc_castSucc _ _ _
def ridge : FaceL × ℤ ≃ Cover where
 toFun v:= Ε v.1 v.2
 invFun v:= (fun i=> v i.castSucc,v 3)
 left_inv v:= Prod.ext (funext (nodeV v.1 v.2)) (node₃ v.1 v.2)
 right_inv v:=Fin.snoc_init_self _ -- tune
local notation "φ" => 2*π
abbrev turn (x:ℝ)(i:ℤ):ℝ:= x+ φ*i
def tempoL (x:Facet3)(v:FaceL):Facet3:= fun i=>turn (x i) (v i)
def tempoE (x:Facet3):= sqrt (∑ i:Fin 3,(x i)^2)
local notation "V" x:max l:max => tempoL x l
local notation "E" x:max => tempoE x
variable (x:Facet3)(v:FaceL)
lemma picked {V':Type*}[Add V'](u v:Fin 3→ V')(a b:V') : (Ε u a)+(Ε v b)= Ε (u+v) (a+b):= by ext i; cases i using Fin.lastCases <;> simp [Ε]
lemma ridges (w:ℝ)(i:ℤ) : Ε x w+stem (ridge (v,i)) = Ε (V x v) (turn w i):=by
 funext a; cases a using Fin.lastCases
 · simp [Ε,ridge,turn,stem]
 · simp [Ε,ridge,stem,tempoL,turn]
def sol (x:Facet3):ℝ:= ∏ i:Fin 3,sinc ((x i)/2)
lemma magnitude (w:ℝ) : (E x)^2+w^2=radius (Ε x w):= by
 rw [tempoE,sq_sqrt (Finset.sum_nonneg fun i _=>sq_nonneg _)]; unfold radius; change _=∑ i:Fin (3+1),(Ε x w i)^2; rw [Fin.sum_univ_castSucc (fun i:Fin (3+1)=>Ε x w i ^ 2)]; simp [Ε]
lemma weave_tail (w:ℝ): weave (Ε x w)= (sol x:ℂ)*skirt w:= by change (∏ i:Fin (3+1),skirt (Ε x w i))=_; rw [Fin.prod_univ_castSucc]; simp [Ε,sol,skirt, Complex.ofReal_prod]
lemma nonvoid {x:Facet3}{i:Fin 3}(p:x i≠0) : 0<E x := by
 apply sqrt_pos.mpr; exact lt_of_lt_of_le (sq_pos_of_ne_zero p) (Finset.single_le_sum (f:=fun i:Fin 3=>x i^2) (fun i _=>sq_nonneg _) (Finset.mem_univ _))
-- fixed band box any [*, π] positive. choose Ω = [1,2]
def grounds:= Set.pi (Set.univ : Set (Fin 3)) (fun _=> Set.Icc (1:ℝ) 2)
variable {x} (c:x∈grounds)
include c
lemma boundsG (i:Fin 3): 1 ≤ x i∧ x i≤2:= c i (Set.mem_univ i)
lemma banded (w:ℝ)(t:w∈ Set.Icc (-π) π): Bound π (Ε x w) := by
 apply (pi_norm_le_iff_of_nonneg pi_pos.le).mpr; intro i; cases i using Fin.lastCases with
 | last => simpa [Ε,abs_le] using t -- simp real norm
 | cast i=> -- tune
    rw [nodeV]; have h:= boundsG c i; rw [Real.norm_eq_abs,abs_of_pos (by linarith [h.1])]; exact h.2.trans (by linarith only [pi_gt_three]) -- syntax
lemma pureV (w:ℝ) : Ε x w ≠ (0:Bin):=fun h=>by
 have hk:=congrFun h 2; simp only [node₂,Pi.zero_apply] at hk; linarith [(boundsG c 2).1]
omit c in
private lemma abs_high {w:ℝ}(h:1≤w∧w≤2)(i:ℤ): 1 ≤ |turn w i|:=by
 have ht:= Real.pi_gt_three; obtain ⟨hx,hv⟩:=h
 by_cases p:0 ≤ i; · unfold turn; exact le_trans (by linarith only [hx,mul_nonneg (show 0 ≤ 2*π by positivity) (show 0≤(i:ℝ) by exact_mod_cast p)]) (le_abs_self _) -- remove positive syntax
 unfold turn; push Not at p; apply le_trans _ (neg_le_abs _); have he : (i:ℝ) ≤ -1:= by exact_mod_cast (show i ≤ -1 by omega)
 nlinarith [mul_le_mul_of_nonneg_left he Real.pi_pos.le]
lemma height (i:Fin 3): 1 ≤ |(V x v) i|:= abs_high (boundsG c i) (v i) -- binder v maybe auto included? adjust
lemma altitude (i:Fin 3): (V x v) i≠0:=by intro q; have h:= height v c i; simp [q] at h; linarith
lemma backend : 1≤ E (V x v):=by
 let z:=V x v
 have hp:(1:ℝ)≤ (z 0)^2:=by nlinarith [height v c 0,sq_abs (z 0)]; -- maybe local unfold
 apply le_trans _ (Real.sqrt_le_sqrt (hp.trans (Finset.single_le_sum (f:=fun i:Fin 3=> z i ^ 2) (fun i _=>sq_nonneg _) (Finset.mem_univ 0))))
 rw [Real.sqrt_one]
omit c in
private lemma for_period(w:ℝ)(h:w∈ Set.Icc 1 2)(i:ℤ): Real.sinc (turn w i /2) ≠0:=by
 unfold turn; by_cases p:w+φ*i=0; · simp only [p,zero_div,Real.sinc_zero]; norm_num
 rw [Real.sinc_of_ne_zero (div_ne_zero p (by norm_num)),show (w+φ*i)/2=w/2+(i:ℝ)*π by ring,sin_add_int_mul_pi]
 apply div_ne_zero (mul_ne_zero (zpow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)) (sin_pos_of_pos_of_lt_pi (by linarith [h.1]) (by linarith [h.2,Real.pi_gt_three])).ne') (?_); intro t; apply p; linarith [t]
lemma roaring : sol (V x v)≠0:= Finset.prod_ne_zero_iff.mpr fun i _=> for_period (x i) (boundsG c _) (v i)
lemma handy {i j:Fin 3}(h:i≠j) : |(V x v) i|< E (V x v):=by
 let x':= V x v; have he: insert i ({j}:Finset (Fin 3)) ⊆ Finset.univ:= Finset.subset_univ _
 have hp:= Finset.sum_le_sum_of_subset_of_nonneg (f:=fun i:Fin 3=> x' i^2) he (fun i _ _=> sq_nonneg _)
 simp only [Finset.sum_insert (mt Finset.mem_singleton.mp h), Finset.sum_singleton] at hp
 have ht: |x' i|^2 < ∑ i:Fin 3, x' i^2 := by rw [sq_abs]; linarith [(show 0 < x' j ^ 2 from sq_pos_of_ne_zero (altitude v c j))]
 exact Real.lt_sqrt_of_sq_lt ht
omit c
end YM.CF.Crest.Airy
open YM.CF.Crest.Airy
#print axioms height
#print axioms roaring
#print axioms handy
