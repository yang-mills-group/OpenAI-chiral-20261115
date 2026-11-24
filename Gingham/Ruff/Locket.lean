import Gingham.Ruff.Lark
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Gingham.Ruff
open Function NormedSpace Finset Fock Scree Pastry
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
open Lattice Wilson Laurent Cube SU Lat Spire Scroll Peaks Drapes Rush Precision Tulip Jet
    Tap Laic Dial Paige Vault Pec Skye Branch
variable {N:Side}
open Nacre

abbrev owl (N:Side)(d:Shape)(U:UNI SpinIdx):UNI (Single N):=
 (prepU d U inert N)⁻¹

lemma owl_tag (d:Shape)(U:UNI SpinIdx)(g:Seat N→E):
    tradew N g * owl N d U = owl N d U * tradew N (g∘d.anon N):=by
  rw [owl]
  apply mul_left_cancel (a:=prepU d U inert N)
  rw [←mul_assoc,envoy,mul_assoc,mul_inv_cancel,mul_one,←mul_assoc,mul_inv_cancel,one_mul]


lemma owl_nonzero (d:Shape)(U:UNI SpinIdx){i j:Single N}
    (p:(owl N d U).val i j≠0):
    cabin i=d.mills N (cabin j):=
  (prep_nonzero d false U (fun e=>p (show star ((prepU d U (xtra false) N).val j i)=0 by rw [e,star_zero]))).symm

variable {e:ℝ}{S:Seal (Seat N)} {c:Toll (Single N)} {A:Fob N e}
def roe (d:Shape)(U:UNI SpinIdx)(k:Toll (Single N))(i j:Single N):=
  let V:=(owl N d U).val
  ∑ p,∑ q, ‖V i p*star (V j q)‖ * k p q
def cope (d:Shape)(U:UNI SpinIdx)(f:Fob N e):Fob N e :=
 fun x=>twist (owl N d U) (f (aviator d x))


lemma cope_eq (d:Shape)(U:UNI SpinIdx)(f:Fob N e)(i j):
    (fun x=>cope d U f x i j)=
     fun x=> ∑ p,∑ q, (owl N d U).val i p*star ((owl N d U).val j q)* f (aviator d x) p q:=by
  funext x; unfold cope
  rw [twist_formula,mul_assoc]
  simp only [mul_assoc,Matrix.mul_apply, mul_sum]
  refine sum_congr rfl fun p _=>sum_congr rfl fun q _=>?_
  rw [show star (owl N d U).val q j= star ((owl N d U).val j q) from rfl,
      mul_comm (f (aviator d x) p q)] -- fix

lemma ticket_inter (s:Jubilee e S c A)(g:Seat N→E)(x):
 A ((forum N e).drive g x)=twist (tradew N g) (A x):=by rw [twist_formula]; exact Inter.frame s.frame g x

lemma see_coif (d:Shape)(U:UNI SpinIdx)(s:Jubilee e S c A)(g:Seat N→E)(x):
    cope d U A ((forum N e).drive g x)=twist (tradew N g) (cope d U A x):=by
  unfold cope
  rw [show aviator d ((forum N e).drive g x)= (forum N e).drive (g∘d.anon N) (aviator d x) from Subtype.ext (perchG _ _ _),
    ticket_inter s,←twin,←twin,owl_tag]


lemma eyes (d:Shape)(U:UNI SpinIdx)(s:Jubilee e S c A) :
    Jubilee e (sheet d S) (roe d U c) (cope d U A):=by
  let V:=(owl N d U).val
  refine ⟨⟨fun g x=>?_,fun i j=>?_⟩,fun i j=>?_⟩
  · rw [see_coif d U s g x,twist_formula,mul_assoc,
        show (star (tradew N g).val*((bail N e).run g).val)=1 from (tradew N g).property.1,mul_one]; rfl
  · rw [cope_eq]
    unfold roe;dsimp only
    apply Expo.sumK
    intro p _
    apply Expo.sumK
    intro q _
    by_cases t:V i p*star (V j q)=0
    · simp only [show (owl N d U).val i p*star ((owl N d U).val j q)=0 from t,norm_zero,zero_mul]
      exact nothing ..
    have jv:V j q≠0:=fun z=> t (by rw [z,star_zero,mul_zero])
    exact (migrate d (s.expo p q) i j (owl_nonzero d U (left_ne_zero_of_mul t))
         (owl_nonzero d U jv)).discount _


  · rw [cope_eq]
    let L:=badge (Coif N e)
    
    intro S k γ n
    simp only [Function.comp_def]
    refine .fun_sum fun p _=> .fun_sum fun q _=> ?_
    exact (aviates d (s.fuel p q) S k γ n).const_mul _ 

def tableland:ℝ:= Fintype.card SpinIdx * (Fintype.card Slot:ℝ)
lemma tablelife: 1 ≤ tableland:=by
  have a:= Fintype.card_pos (α:=SpinIdx)
  have b:= Fintype.card_pos (α:=Slot)
  exact one_le_mul_of_one_le_of_one_le (by exact_mod_cast a) (by exact_mod_cast b) -- a: 0<
lemma faceted (d:Shape)(U:UNI SpinIdx)(p:Single N):
 ∑ i:Single N, ‖(owl N d U).val i p‖ ≤ tableland:=by
  let V:=owl N d U
  have e(i:Single N): ‖V.val i p‖≤ if cabin i=d.mills _ (cabin p) then (1:ℝ) else 0:=by
    by_cases t:V.val i p=0
    · rw [t,norm_zero];split<;>norm_num
    rw [if_pos (owl_nonzero d U t)]
    exact (norm_entry ..).trans_eq (CStarRing.norm_of_mem_unitary V.property)
  apply le_trans (sum_le_sum fun i _=>e i)
  change ∑ i: (Site N ×SpinIdx)×Slot, (if i.1.1 = d.mills _ (cabin p) then (1:ℝ) else 0) ≤ tableland
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
  rw [sum_eq_single_of_mem (d.mills N (cabin p)) (mem_univ _) (fun i _ h=>by simp [h])]
  simp [tableland]



lemma carven (d:Shape)(U:UNI SpinIdx)(p q:Single N):
    ∑ i:Single N,∑ j:Single N,
      ‖(owl N d U).val i p * star ((owl N d U).val j q)‖ ≤ tableland^2:=by
   simp_rw [norm_mul,norm_star,←mul_sum,←sum_mul,sq]
   exact mul_le_mul (faceted d U _) (faceted d U _) (by positivity)
    (zero_le_one.trans tablelife)

