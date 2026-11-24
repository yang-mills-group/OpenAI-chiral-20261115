import YM.CF.Thera.Lawn
set_option autoImplicit false
noncomputable section
namespace YM.CF.Thera
open Filter Function MeasureTheory Gauge Matrix Fock SU Finset NormedSpace
open scoped Topology BigOperators Matrix.Norms.Frobenius InnerProductSpace
abbrev F₀:= Fin SU.group.repDim
variable (a b c i j:F₀)(z t:ℂ)
def curlA : V := Matrix.single a b z-Matrix.single b a (star z)
def hut : V := Matrix.diagonal (fun i=> if i=a then 4*Complex.I/5 else (-Complex.I)/5)
def bracket(U V':V):= U*V'-V'*U
lemma curl_b: star (curlA a b z)= -curlA a b z:=by
 ext i j; simp only [curlA,Matrix.neg_apply,Matrix.star_apply,Matrix.sub_apply,Matrix.single_apply]; simp_rw [ite_and]; split_ifs <;> simp
lemma curl_v(k:a≠b): curlA a b z∈ SU.group.lie:=by rw [league]; constructor; exact curl_b ..; simp only [curlA,trace_sub]; simp [k,Ne.symm] -- tune
lemma hutL: hut a∈ SU.group.lie:=by
 rw [league]; constructor
 · ext i j; rw [Matrix.star_apply]; unfold hut; simp only [Matrix.diagonal_apply,Matrix.neg_apply]; by_cases k:i=j <;> simp [k,Ne.symm] <;> split <;> simp_all <;> norm_num [map_ofNat] <;> ring
 unfold hut; rw [Matrix.trace_diagonal]; rw [sum_ite, show univ.filter (·=a)={a} by ext; simp, show univ.filter (fun j => ¬ j=a)=univ.erase a by ext; simp]; norm_num [Gauge.repDim,SU.group,card_erase_of_mem]; ring -- tune
lemma hut_b(a i j:F₀)(W:V): bracket (hut a) W i j = if i=a then if j=a then 0 else Complex.I * W i j else if j=a then -Complex.I*W i j else 0:=by
 by_cases h:i=a<;>by_cases p:j=a<;> simp [bracket,hut, h,p] <;> ring
lemma curl_p(k:a≠b) {W:V}(p:star W= -W): bracket (hut a) (bracket (hut b) W)=curlA a b (W a b):=by
 have hz:∀ i j:F₀, star (W i j)= -W j i:= fun i j=> Matrix.ext_iff.mpr p j i
 ext i j; by_cases h:i=a <;> by_cases l:i=b <;> by_cases g:j=a <;>by_cases e:j=b <;> simp_all [hut_b,curlA, Matrix.single_apply,Ne.symm,mul_comm,mul_left_comm,← mul_assoc] -- tune
lemma curl_x(k:a≠b): bracket (hut a) (curlA a b z)=curlA a b (Complex.I*z):=by
 ext i j; rw [hut_b]; by_cases h:i=a <;> by_cases l:i=b <;> by_cases g:j=a <;>by_cases e:j=b <;> simp_all [curlA, Matrix.single_apply,Ne.symm] <;> ring
lemma curl_n(k:a≠b):curlA b a z=curlA a b (-star z):=by
 ext i j; by_cases h:i=a <;> by_cases l:i=b <;> by_cases g:j=a <;>by_cases e:j=b <;> simp_all [curlA, Matrix.single_apply, Ne.symm]
lemma curl_s(x:ℝ):curlA a b (x•z)=x •curlA a b z:=by
 ext i j; unfold curlA; simp only [Matrix.sub_apply,Matrix.smul_apply, star_smul,star_trivial, Matrix.single_apply]; split_ifs <;> simp <;> ring
lemma curl_u:curlA a b (z+t)=curlA a b z+curlA a b t:=by
 ext i j; unfold curlA; simp only [Matrix.add_apply,Matrix.sub_apply,star_add,Matrix.single_apply]; split_ifs <;> abel
lemma puppet(k:a≠b)(h:b≠c)(l:a≠c): bracket (curlA a b z) (curlA b c t)=curlA a c (z*t):=by
 unfold bracket curlA; simp only [sub_mul,mul_sub] -- tune
 simp [k,h,l,Ne.symm] ; rw [mul_comm ((starRingEnd ℂ) t)] -- tune
lemma quartD(k:a≠b):bracket (curlA a b 1) (curlA a b Complex.I)= (2:ℝ) • (hut a-hut b):=by
 unfold bracket curlA hut; simp only [star_one,sub_mul,mul_sub]
 ext i j; by_cases h:i=a <;>by_cases p:i=b <;> by_cases H:i=j<;> simp_all [Matrix.single_apply,Matrix.diagonal_apply,Ne.symm]<;>ring -- tune
end YM.CF.Thera
