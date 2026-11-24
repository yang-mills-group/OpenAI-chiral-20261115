import YM.CF.BProof.Dream.Charm
/-! Move through the stabilizer in congruences. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Dream
open Matrix SU Finset Function Metric Complex Extension.Mar RCLike
open scoped Topology BigOperators Matrix Matrix.Norms.L2Operator Kronecker ContDiff ComplexConjugate
attribute [local instance] opCStarAlgebra
variable {n m : Type*}[Fintype n][DecidableEq n]
lemma starU {V:Op n}(h:V∈unitary _): star V ∈ unitary _:=by constructor <;> rw [star_star] <;> first | exact h.1 | exact h.2
def mold (V B:Op n):= V*B*Vᵀ
lemma moldT {V B:Op n} (h:Bᵀ=B): (mold V B)ᵀ=mold V B:=by rw [mold,transpose_mul,transpose_mul,h,transpose_transpose,mul_assoc]
lemma layers (V W B:Op n): mold (V*W) B=mold V (mold W B):=by simp [mold,transpose_mul,mul_assoc]
@[simp] lemma mold_one (B:Op n): mold 1 B=B:=by simp [mold]
lemma kingOne: inK (1:Op n) := ⟨(unitary _).one_mem,det_one⟩
lemma kingMul {V W:Op n}(h:inK V)(w:inK W): inK (V*W):=⟨(unitary _).mul_mem h.1 w.1,by rw [det_mul,h.2,w.2,mul_one]⟩
lemma kingTr {V:Op n}(h:inK V) : inK Vᵀ := ⟨Matrix.transpose_mem_unitaryGroup_iff.mpr h.1,(det_transpose ..).trans h.2⟩
lemma moldK {V B:Op n}(h:inK V)(p:inK B): inK (mold V B) := kingMul (kingMul h p) (kingTr h)
lemma kingStar{V:Op n}(h:inK V) : inK (star V):= ⟨starU h.1,by rw [Matrix.star_eq_conjTranspose,Matrix.det_conjTranspose,h.2,star_one]⟩
lemma twistKing {V:UNI n}{A:Op n}(h:inK A): inK (twist V A):=by
 rw [twist_formula]; refine ⟨(unitary _).mul_mem ((unitary _).mul_mem V.property h.1) (starU V.property),?_⟩; rw [det_mul,det_mul,h.2,mul_one, ← det_mul,V.property.2,det_one]

abbrev Tile (n:Type*) := Matrix n n ℝ
def fundC (U:Tile n): Op n:= U.map ((↑): ℝ→ℂ)
@[simp] lemma fundC_one : fundC (1:Tile n)=1:=by ext i j; by_cases h:i=j ; subst j; simp [fundC]; simp [h,fundC]
lemma fundC_mul (U V:Tile n): fundC (U*V)=fundC U*fundC V:=by ext; simp [mul_apply,fundC]
lemma fundC_star (U:Tile n): fundC (star U)=star (fundC U):=by ext; simp [fundC]
lemma fundC_det (U:Tile n): (fundC U).det=(U.det:ℂ):= (RingHom.map_det Complex.ofRealHom U).symm
lemma fundC_inj : Function.Injective (@fundC n):=by intro a b h; ext i j; exact Complex.ofReal_inj.mp (Matrix.ext_iff.mpr h i j)
lemma fundC_K (U:Tile n): inK (fundC U) ↔ inK U:=by
 constructor
 · intro h; refine ⟨⟨fundC_inj (by rw [fundC_mul,fundC_star,fundC_one]; exact h.1.1),fundC_inj (by rw [fundC_mul,fundC_star,fundC_one]; exact h.1.2)⟩,Complex.ofReal_inj.mp ?_⟩; rw [← fundC_det,h.2,Complex.ofReal_one]
 intro h; refine ⟨⟨?_,?_⟩,?_⟩; rw [←fundC_star, ←fundC_mul,h.1.1,fundC_one]; rw [←fundC_star, ←fundC_mul,h.1.2,fundC_one]; rw [fundC_det,h.2,Complex.ofReal_one]
lemma fundC_real {U:Op n}(h:U ∈ unitary _): mold U 1=1 ↔ ∃ A: Tile n, U=fundC A:=by
 constructor
 · intro e; rw [mold,mul_one] at e; have he:Uᵀ=star U:=by rw [←mul_one (star U),←e,←mul_assoc,h.1, one_mul]
   refine ⟨U.map Complex.re,?_⟩; ext i j; have ht: U i j=star (U i j):= Matrix.ext_iff.mpr he j i; change U i j=((U i j).re:ℂ); exact (Complex.conj_eq_iff_re.mp ht.symm).symm -- tune
 rintro ⟨A,rfl⟩; rw [mold,mul_one,show (fundC A)ᵀ=star (fundC A) from ?_, h.2]; ext; simp [fundC]
lemma smootherOne {V:Op n}[Nonempty n](h:inK V) (u:mold V 1=1): ∃ S:ℝ→ Op n, ContDiff ℝ ∞ S ∧ S 0=V∧ S 1=1 ∧ ∀ t,inK (S t)∧ mold (S t) 1=1:=by
 obtain ⟨U,rfl⟩:=(fundC_real h.1).1 u; have he:inK (1:Tile n):= ⟨(unitary _).one_mem,det_one⟩; obtain ⟨G,g,v,w,P⟩:= jumpstart U 1 ((fundC_K _).1 h) he
 refine ⟨fundC ∘ G,smoothM _ (fun i j=> Complex.ofRealCLM.contDiff.comp (g i j)),show fundC (G 0)=_ by rw [v],show fundC (G 1)=1 by rw [w,fundC_one],fun t=>?_⟩; exact ⟨(fundC_K _).2 (P t), (fundC_real ((fundC_K _).2 (P t)).1).2 ⟨_,rfl⟩⟩
lemma slide_mold (U: UNI n)(V B:Op n) : mold U.val (mold V B)= mold (twist U V) (mold U.val B):=by rw [twist_formula,← layers,←layers,mul_assoc,show star U.val*U.val=1 from U.property.1,mul_one]
lemma smoother [Nonempty n](U:UNI n){A: Op n}(h:inK A)(p:mold A (mold U.val 1)=mold U.val 1): ∃ S:ℝ→ Op n, ContDiff ℝ ∞ S ∧ S 0=A∧ S 1=1 ∧ ∀ t,inK (S t) ∧ mold (S t) (mold U.val 1)= mold U.val 1:=by
 let Y:=twist (star U) A; have hy: twist U Y=A:=by unfold Y; nth_rw 1 [←star_star U]; exact twist_inv ..
 have he:= slide_mold U Y 1; rw [hy,p] at he; have hv:Injective (mold U.val):= HasLeftInverse.injective ⟨mold (star U.val),fun x=> by rw [←layers,U.property.1,mold_one]⟩
 obtain ⟨G,g,hG,eG,W⟩:= smootherOne (n:=n) (V:=Y) (twistKing h) (hv he) -- tune
 refine ⟨twist U ∘ G,?_,show twist U (G 0)=A from hG ▸ hy,show twist U (G 1)=1 from (by rw [eG,map_one]),fun t=>⟨twistKing (W t).1,?_⟩⟩ -- trans equality? hG direction
 · have he : twist U ∘ G=fun t=> U.val*G t*star U.val:=funext fun i=> twist_formula ..; rw [he]; exact (contDiff_const.mul g).mul contDiff_const
 rw [Function.comp_apply,←slide_mold,(W t).2]
-- UUᵀ factorization required only on real B field.
lemma flavourFactor {B: Op n} (h:Bᵀ=B)(p:star B=B)(u:B∈unitary _) : ∃ U:UNI n,mold U.val 1=B:=by
 let P: Op n:= (1/2:ℂ) • (1+B); let Q:=1-P
 have he:B*B=1:=by nth_rw 1 [← p]; exact u.1
 have hh:P*P=P:=by unfold P; rw [Algebra.smul_mul_assoc,Algebra.mul_smul_comm,add_mul,one_mul,mul_add,mul_one,he]; module
 have hp:P*Q=0:=by unfold Q; rw [mul_sub,mul_one,hh,sub_self]
 have hi:Q*P=0:=by unfold Q; rw [sub_mul,one_mul,hh,sub_self]
 have hk:Q*Q=Q:=by rw [show Q*Q=(1-P)*Q from rfl,sub_mul,one_mul,hp,sub_zero]
 let T:=P+Complex.I • Q; have hq:Tᵀ=T:=by dsimp only [T,Q,P]; simp only [transpose_add,transpose_smul, transpose_sub,transpose_one,h] -- tune
 have hw:star T=P+(-Complex.I) • Q:= by unfold T Q P; simp only [star_add,star_sub,star_smul,Complex.star_def,star_one,map_div₀,map_one,map_ofNat,Complex.conj_I,p] -- simp p folded star
 have hb(a b:ℂ): (P+a • Q)*(P+b • Q)=P+(a*b) • Q:=by simp only [add_mul,mul_add,hh, Algebra.mul_smul_comm,Algebra.smul_mul_assoc,hi,hp,hk,smul_zero,add_zero,zero_add,smul_smul]; rw [mul_comm a] -- tune
 have ht:T∈unitary (Op n):=by
   apply Matrix.mem_unitaryGroup_iff.mpr; rw [hw, show T=P+Complex.I • Q from rfl,hb,mul_neg,Complex.I_mul_I,neg_neg]; simp [Q]
 refine ⟨⟨T,ht⟩,?_⟩; change T*1*Tᵀ=B; rw [mul_one,hq]; unfold T; rw [hb,Complex.I_mul_I]; unfold Q P; module
end YM.CF.BProof.Dream
