import YM.CF.BProof.Dream.Whirl
import Mathlib.LinearAlgebra.Matrix.Adjugate

/-! Two-by-two subblocks. Eigensums for relative center twists. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Dream
open Matrix Complex Function
open scoped Matrix Kronecker ContDiff Topology BigOperators Matrix.Norms.L2Operator
local notation "π" => Real.pi
attribute [local instance] opCStarAlgebra
abbrev Duo := Op (Fin 2)
lemma rose_plus (a:ℝ): rose a+rose (-a)=2*↑(Real.cos a):=by rw [rose_spokes,rose_spokes,Real.cos_neg,Real.sin_neg,Complex.ofReal_neg]; ring
lemma rootsD (x y u v : ℂ)(h:x+y=u+v)(e:x*y=u*v): x=u∧y=v ∨ x=v∧y=u:=by
 have he : (x-u)*(x-v)=0:=by linear_combination x*h-e -- tune sign
 rcases eq_zero_or_eq_zero_of_mul_eq_zero he with he|he
 · rw [sub_eq_zero] at he; subst u; exact Or.inl ⟨rfl,add_left_cancel h⟩
 rw [sub_eq_zero] at he; subst v; exact Or.inr ⟨rfl,add_left_cancel (h.trans (add_comm ..))⟩
lemma spectral2 (W:Duo)(h:W∈unitary _)(t:W.det=1): ∃ (U:UNI (Fin 2))(d:Fin 2→ℂ), W=dial U d:=by
 let V:=W.adjugate; have hv:W*V=1:=by rw [show W*V=_ from Matrix.mul_adjugate W,t,one_smul]
 have he:V=star W:=by rw [←mul_one (star W),←hv,←mul_assoc, show star W*W=1 from h.1,one_mul]
 let a:=W.trace
 have hw:W+star W=a • 1:=by rw [←he,show V=_ from Matrix.adjugate_fin_two W]; ext i j; fin_cases i <;> fin_cases j <;> simp [a,Matrix.trace,Fin.sum_univ_succ] <;> ring -- tune
 let Z:Duo:=I • (W-star W); have hz:IsSelfAdjoint Z:=by rw [isSelfAdjoint_iff]; unfold Z; rw [star_smul,star_sub,star_star,Complex.star_def,Complex.conj_I,neg_smul,← smul_neg I, neg_sub]
 obtain ⟨U,d,H⟩:= spectral_exists _ hz
 let b(i:Fin 2):ℂ:=d i; change Z=dial U b at H
 let D:=fun (k:ℂ)=> k • (1:Fin 2→ℂ)
 refine ⟨U,(1/2:ℂ) • (D a+(-I) • b),?_⟩; rw [←dial_smul,←dial_add,←dial_smul U b,show dial U (D a)=a • (1:Duo) by unfold D; rw [←dial_smul,dial_one],←H]; unfold Z; rw [smul_smul,neg_mul,Complex.I_mul_I,neg_neg,one_smul, ←hw]; module -- tune
lemma twists2 (W:Duo)(h: W∈unitary _)(e:W.det=1)(a θ:ℝ)(t:W.trace=2*↑(Real.cos a))(p q:ℝ)
 (hp:MainT p)(hq:MainT q)(u:rose p=rose (-θ+a))(v:rose q=rose (-θ+(-a))): Whirl (rose (-θ) • W) (p+q):=by
 obtain ⟨U,d,hd⟩:=spectral2 _ h e; rw [←rose_plus a,hd,dialT,Fin.sum_univ_two] at t; rw [hd, dial_det,Fin.prod_univ_two,← show rose a*rose (-a)=1 from (by rw [← rose_add]; simp)] at e
 rw [hd,dial_smul, rose_add] at * -- only if tune
 have hu := rootsD _ _ _ _ t e; rcases hu with ⟨hx,hy⟩|⟨hx,hy⟩
 · refine ⟨U,![p,q],congrArg _ ?_,fun i=>?_,?_⟩; ext1 i; fin_cases i <;> simp [hx,hy,u,v]; fin_cases i <;> simpa; simp [Fin.sum_univ_two]
 refine ⟨U,![q,p],congrArg _ ?_,fun i=>?_,?_⟩; ext1 i; fin_cases i <;> simp [hx,hy,u,v]; fin_cases i <;> simpa; simp [Fin.sum_univ_two,add_comm]

def flect (t:ℝ):Duo:= !![(↑(Real.cos t):ℂ), ↑(Real.sin t); ↑(Real.sin t), -(↑(Real.cos t):ℂ)]
lemma flect_self (t:ℝ) : star (flect t)=flect t:=by ext i j; fin_cases i <;> fin_cases j <;> simp [flect,-ofReal_cos,-ofReal_sin]
lemma flect_trans (t:ℝ) : (flect t)ᵀ=flect t:=by ext i j; fin_cases i <;> fin_cases j <;> simp [flect]
lemma bandlaw(t:ℝ) : (↑(Real.cos t):ℂ)^2+(↑(Real.sin t):ℂ)^2=1:=by exact_mod_cast Real.cos_sq_add_sin_sq t
lemma flect_det (t:ℝ): (flect t).det= -1:=by rw [det_fin_two]; unfold flect; simp only [Matrix.of_apply, Matrix.cons_val_zero,Matrix.cons_val_one]; linear_combination -(bandlaw t)
lemma flect_unit (t:ℝ) : flect t∈unitary Duo:=by
 apply Matrix.mem_unitaryGroup_iff.mpr; rw [flect_self]; ext i j; fin_cases i <;> fin_cases j <;> simp [flect,Fin.sum_univ_two,Matrix.mul_apply, -ofReal_cos, -ofReal_sin] <;> (first | linear_combination bandlaw t | ring)

-- W' scaled relative
private abbrev ltT (θ:ℝ):= ![rose (-2*θ),rose θ]
def dress (θ:ℝ):= Matrix.diagonal (ltT θ)
def doubleU (θ t:ℝ):=dress θ*flect t*dress θ * flect t
lemma diagUnit {n:Type*}[Fintype n][DecidableEq n](d:n→ℂ)(h:∀ i,d i ∈unitary ℂ): diagonal d∈ unitary (Op n):=by
 apply Matrix.mem_unitaryGroup_iff.mpr; rw [Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose]; ext i j; rw [Matrix.diagonal_mul]; by_cases H:i=j; subst j; rw [diagonal_apply_eq,one_apply_eq]; exact (h i).2; simp [H]
lemma scalar_unitary {n:Type*}[DecidableEq n][Fintype n]{U:Op n}{s:ℂ}(h:U∈unitary _)(x:s∈ unitary _): s • U∈ unitary _:=by apply Matrix.mem_unitaryGroup_iff.mpr; rw [star_smul,Algebra.smul_mul_assoc,Algebra.mul_smul_comm,smul_smul,x.2,one_smul,h.2] -- tune
lemma dressU (θ:ℝ) : dress θ∈unitary _:=diagUnit _ (fun i=> by fin_cases i <;> exact roseU _)
lemma dressDet (θ:ℝ): (dress θ).det=rose (-θ):=by rw [dress,Matrix.det_diagonal,Fin.prod_univ_two]; simp only [ltT,Matrix.cons_val_zero,Matrix.cons_val_one]; rw [←rose_add]; congr 1; ring
lemma subUnit (θ t:ℝ) : rose θ • doubleU θ t∈unitary _:=scalar_unitary (((unitary Duo).mul_mem ((unitary _).mul_mem ((unitary _).mul_mem (dressU θ) (flect_unit t)) (dressU θ)) (flect_unit t))) (roseU _)
lemma subDet (θ t:ℝ) : (rose θ • doubleU θ t).det=1:=by simp only [Matrix.det_smul,Fintype.card_fin,doubleU,Matrix.det_mul, dressDet, flect_det,rose_minus]; field_simp [rose_ne]
lemma switchT (θ:ℝ) : doubleU θ (π/2)=rose (-θ) • (1:Duo):=by
 have ht:rose (-(2*θ))*rose θ=rose (-θ):=by rw [← rose_add]; congr 1; ring
 ext i j; fin_cases i <;> fin_cases j <;> simp [doubleU,flect,dress,ltT,Matrix.mul_apply,Fin.sum_univ_two,ht] <;> rw [mul_comm,ht] -- tune may simp cos only real casts?
lemma twistval(θ:ℝ) : (rose θ • doubleU θ (π/4)).trace= 1+ ↑(Real.cos (3*θ)):=by
 let c:ℂ := ↑(Real.cos (π/4)); have hp : c^2=1/2:=by dsimp only [c]; rw [← ofReal_pow,show Real.cos (π/4)^2=(1/2:ℝ) from (by rw [Real.cos_pi_div_four]; nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)])]; norm_num
 have hq : Real.sin (π/4)=Real.cos (π/4):=by rw [Real.cos_pi_div_four,Real.sin_pi_div_four]
 let a:= rose θ; let b:=rose (-2 * θ)
 have he:a*b^2= rose (-(3*θ)):=by dsimp only [a,b]; rw [pow_two,← rose_add,← rose_add]; congr 1; ring
 have hv:a^2*b=1:=by dsimp only [a,b]; rw [pow_two,← rose_add,← rose_add,show θ+θ+ -2*θ=0 from by ring, rose_zero]
 have hk:a^3= rose (3*θ):=by dsimp only [a]; rw [pow_succ (rose θ) 2,pow_two,←rose_add,←rose_add]; congr 1; ring
 unfold doubleU; rw [Matrix.trace_smul]; unfold dress flect; simp only [Matrix.trace,Fin.sum_univ_two,ltT,Matrix.diag_apply, Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.of_apply,Matrix.mul_apply, Matrix.diagonal_apply,hq, smul_eq_mul,if_neg (show (1:Fin 2)≠0 by decide),if_neg (show (0:Fin 2)≠1 by decide),↓reduceIte]
 -- express in vars a b c
 let A:=rose (3*θ); let B:=rose (-(3*θ)); have hX : A+B=2*↑(Real.cos (3*θ)):=rose_plus _
 -- ring equivalence
 calc
   _ = (a*b^2 + a^3+2*(a^2*b))*c^2:= by dsimp only [a,b,c]; ring_nf <;> first | rfl | (simp only [if_true] <;> ring)
   _ = _ := by rw [he,hv,hk,hp,add_comm (rose (-(3*θ))) (rose (3*θ)), hX]; ring
lemma half(θ a p q:ℝ)(e:1+Real.cos (3*θ)=2*Real.cos a)(h:MainT p)(t:MainT q)(u:rose p=rose (-θ+a))(v:rose q=rose (-θ+(-a))): Whirl (doubleU θ (π/4)) (p+q):=by
 have he:= twists2 _ (subUnit θ (π/4)) (subDet θ (π/4)) a θ (Eq.trans (twistval θ) (by exact_mod_cast e)) p q h t u v; rw [smul_smul, ←rose_add, neg_add_cancel,rose_zero,one_smul] at he; exact he
end YM.CF.BProof.Dream
