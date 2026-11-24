import GaugeFieldConstruction.Adytum
import GaugeFieldConstruction.Argyll
set_option autoImplicit false
set_option quotPrecheck false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 340000
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Scree.Ing
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree
open Skye Scree Vow Hake Jet Fock
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open Cube Lat Tulip Peaks
attribute [local instance] opCStarAlgebra
open Rush Scroll Paige Vault Phase Acorn Spire
open scoped YM.CF.Mew
open BasisI Roots GJ Mew
section
variable {I J M:Type}[LinearOrder I][Fintype I][NormedCommRing M][NormedAlgebra ℂ M][CompleteSpace M]
variable (σ:I→J)
private lemma duo0 (p:I)(a b:Key I→M)(h:River a)(k:River b)(x:∀ z:Key I,z p=0→ a z=0)(y:∀ z:Key I,z p=0→b z=0):Kin σ (a*b) 0:=by
 have P:=h.mul_T k; refine ⟨P,zeroR _,?_⟩; intro s t
 have H:a∘dune p=0:=funext fun i=>x _ (update_self ..); have K:b∘dune p=0:=funext fun i=>y _ (update_self ..)
 by_cases e:p∈ s
 · obtain ⟨l,Q,u⟩:=List.append_of_mem e; let L:=l++Q; have f:s.Perm (p::L):=u ▸ List.perm_middle
   rw [(show tipI (a*b) s=tipI (a*b) (p::L) from move_ζ f P roots), tip_mul h k,H,K,mul_zero,zero_mul]; change tipI (fun _=> 0) _+tipI (fun _=>0) _=tipI (fun _=>0) _; simp only [tip_0,add_zero]
 rw [←tip_V (f:=a*b) p s e,show (a*b)∘dune p=0 from funext (fun i=>by change a (dune p i)*_=0; rw[x _ (update_self ..),zero_mul])]
variable {σ}
lemma loft_add {E:Type}[NormedAddCommGroup E][NormedSpace ℂ E][CompleteSpace E]{f g h k: Key I→ E} (p:Kin σ f g)(q:Kin σ h k): Kin σ (f+h) (g+k):=by
 refine ⟨dub_V p.1 q.1, dub_V p.2 q.2,fun t h=>?_⟩; exact (tip_A p.1 q.1 t).trans ((congrArg₂ (·+·) (p.3 t h) (q.3 t h)).trans (tip_A p.2 q.2 t).symm)
lemma loft_bank {E α:Type}[NormedAddCommGroup E][NormedSpace ℂ E][CompleteSpace E] {S:Finset α} (f g:α→ Key I→E)(p:∀ a∈S, Kin σ (f a) (g a)):Kin σ (fun z=>∑ a∈S,f a z) (fun z=>∑ a∈S,g a z):=by
 induction S using Finset.induction with
 | empty=> simp only [sum_empty]; exact Kin.refl _ (zeroR _)
 | insert a S h ih=> simp_rw [sum_insert h]; exact loft_add (p a (mem_insert_self ..)) (ih (fun x k=>p x (mem_insert_of_mem k)))
variable (σ)
private def card1 {α:Type}(S:Finset α)(f g:α→ M):=∑ a∈ S,((∏ x∈ S.erase a,f x)*g a)
private lemma kin_prodz {α:Type}(i:I) (f g:α→ Key I→M)(S:Finset α)(p:∀ a∈S,River (f a))(q:∀ a∈S,River (g a))(t:∀ a∈S,∀ z:Key I,z i=0→ g a z=0): Kin σ (fun z=>∏ x∈S,(f x z+g x z)) (fun z=> (∏ x∈S,f x z)+card1 S (fun i=>f i z) (fun i=>g i z)):=by
 induction S using Finset.induction with
 | empty=> simp only [card1,sum_empty,prod_empty,add_zero]; exact Kin.refl _ (zeroR _)
 | insert a S h ih=>
    have pf(x)(u:x∈S):River (f x):= p x (mem_insert_of_mem u); have qf(x)(u:x∈S):River (g x):=q x (mem_insert_of_mem u)
    have g0(x)(u:x∈S)(z:Key I)(w:z i=0):g x z=0:= t x (mem_insert_of_mem u) z w
    let L(z:Key I):= ∏ x∈S, f x z; let R(z:Key I):= card1 S (fun i=>f i z) (fun i=>g i z)
    have he(K:Finset α)(r:K ⊆ S):River fun z=>∏ x∈K,f x z:=by
       induction K using Finset.induction with
       | empty=> simp only [prod_empty]; exact zeroR _
       | insert x A t ih=> simp_rw[prod_insert t]; exact (pf _ (r (mem_insert_self ..))).mul_T (ih ((subset_insert ..).trans r))
    have hp:River L:= he _ (subset_refl _)
    have hv:River R:= (tip_bank S (fun x z=> (∏ i∈ S.erase x,f i z)*g x z) (fun x h=> (he _ (erase_subset ..)).mul_T (qf x h))).1
    have hr(z:Key I)(w:z i=0):R z=0:=sum_eq_zero fun j p=>by dsimp only; rw[g0 j p z w,mul_zero]
    have y:=p _ (mem_insert_self a S); have b:=q _ (mem_insert_self a S); let U:=fun z:Key I=>∏ x∈ S,(f x z+g x z)
    have Q:Kin σ ((f a+g a)*U) ((f a+g a)*(L+R)):= Kin.mulT (Kin.refl _ (dub_V y b)) (ih pf qf g0)
    simp_rw[prod_insert h]
    have hk: Kin σ (f a*L + f a*R + g a*L + g a*R) (f a*L + f a*R + g a*L+0):= loft_add (Kin.refl σ (dub_V (dub_V (y.mul_T hp) (y.mul_T hv)) (b.mul_T hp))) (duo0 σ i _ _ b hv (t _ (mem_insert_self ..)) hr)
    apply Q.trans; rw [add_mul,mul_add,mul_add,← add_assoc]
    refine hk.trans ?_
    suffices H:(f a*L + f a*R + g a*L + 0)=(fun z=> f a z*(∏ x∈S,f x z) + card1 (insert a S) (fun i=>f i z) (fun i=> g i z)) from H ▸ Kin.refl σ hk.rightC
    funext z; simp only [Pi.zero_apply,add_zero,Pi.add_apply,Pi.mul_apply]; unfold card1; change _ + f a _* (∑ i∈S,_) +_ = _; rw [sum_insert h,mul_sum, erase_insert h]; let X:=fun i=> g i z
    change f a z * L z + _ + g a z * L z=f a z*L z + ((∏ i∈S, f i z)*g a z + _)
    rw [show (∏ i∈ S,f i z)*g a z=g a z*L z from mul_comm ..,add_comm (g a z*L z) _,← add_assoc]
    congr 2; apply sum_congr rfl; intro j p; rw [erase_insert_of_ne (fun (e:a=j)=> h (e ▸ p)), prod_insert (fun t=>h (mem_of_mem_erase t)),mul_assoc]
variable {n:Side}(Ω:Support (More n))
omit [CompleteSpace M] in
private lemma card_jet (f g:Force n→ M): sparkJet Ω f g=∑ x:Finset (Force n) with PriceI id Ω x, card1 x f g:=by
 let Q(t:ℂ):=f+t • g
 have v: HasDerivAt Q g (0:ℂ):=by
    have e:HasDerivAt Q (0+(1:ℂ) • g) 0:=(hasDerivAt_const (0:ℂ) f).add ((hasDerivAt_id' (0:ℂ)).smul_const g)
    rwa[one_smul,zero_add] at e
 have hx: HasDerivAt (hum Ω id ∘ Q) (sparkJet Ω f g) 0:=by
    rw [show sparkJet Ω f g=fderiv ℂ (hum Ω id) (Q 0) g by unfold Q; simp[sparkJet]]; exact ((smooth_Hum Ω _).hasFDerivAt).comp_hasDerivAt _ v
 apply hx.unique; refine HasDerivAt.fun_sum (fun i _=>?_) -- may need Q
 have h(i:Force n): HasDerivAt (fun t:ℂ=>Q t i) (g i) 0:=by
    have hp:= (ContinuousLinearMap.hasFDerivAt (𝕜:=ℂ) (ContinuousLinearMap.proj (R:=ℂ) (φ:=fun _:Force n=>M) i)).comp_hasDerivAt 0 v; exact hp
 have pA:Q 0=f:=by simp[Q]
 have u:=HasDerivAt.fun_finsetProd (u:=i) (fun i _=>h i) -- inspect
 apply u.congr_deriv; rw[pA]; unfold card1; simp only [smul_eq_mul]; congr!
-- raw infinitesimal insertion
variable (f g:Force n→ Key I→ M)(i:I)(hf:∀ i,River (f i))(hg:∀ i,River (g i))(t:∀ j,∀ x:Key I,x i=0→ g j x=0)
include hf hg t
lemma turn_hum : Kin σ (fun z=>hum Ω id (fun i=>f i z+g i z)) (fun z=>hum Ω id (fun i=>f i z)+sparkJet Ω (fun i=>f i z) (fun i=>g i z)):=by
 simp_rw [hum,card_jet,←sum_add_distrib]; exact loft_bank _ _ (fun S _=> kin_prodz σ i f g S (fun i _=>hf i) (fun i _=>hg i) (fun i _=>t i))
lemma tilt_K (A B: Key I→ M)(ha:River A)(hb:River B)(p:∀ x:Key I,x i=0→ B x=0): Kin σ (fun z=> exp (A z+B z)*hum Ω id (fun i=>f i z+g i z)) (fun z=> exp (A z)* hum Ω id (fun i=>f i z)+exp (A z)*(B z * hum Ω id (fun i=>f i z)+sparkJet Ω (fun i=>f i z) (fun i=>g i z))):=by
 let F(z):=hum Ω id (fun i=>f i z); let H(z):=sparkJet Ω (fun i=>f i z) (fun i=>g i z); let V:=turn_hum σ Ω f g i hf hg t
 have hp:River F:=by
    let S:Key I→M:=0
    have e:=turn_hum σ Ω f (fun _=>S) i hf (fun _=>zeroR _) (fun _ _ _=>rfl)
    simpa [F,H,S] using e.1
 have hQ:River H:= by
    have h:River (F+H):=V.2
    have p:River ((F+H)+(-1:ℂ) • F):= dub_V h (hp.scale _)
    rw[neg_one_smul ℂ F,add_comm F H,add_neg_cancel_right] at p; exact p
 have hx:=duo0 σ i B H hb hQ p (fun z h=>by unfold H; rw[show (fun i'=>g i' z)=0 from funext fun k=> t k z h,map_zero])
 let e:=NormedSpace.exp ∘ A; let U:Key I→M:=1
 have v:River e:=ha.exp_V; have he:Kin σ (((U+B)) * (fun z=>hum Ω id (fun i=> f i z+g i z))) ((U+B)*(F+H)):= Kin.mulT (Kin.refl _ (dub_V (zeroR _) hb)) V
 letI: NormedAlgebra ℚ M := NormedAlgebra.restrictScalars ℚ ℂ M
 simp_rw[exp_add]; let b:Kin σ _ _:= Kin.mulT (sprigE σ i hb p) V; have W:Kin σ _ _:=Kin.mulT (Kin.refl _ v) b
 -- ring rearrange
 change Kin σ (fun z=>e z*(exp (B z))*_) (fun z=>e z*F z+e z*(B z* F z+ H z))
 simp_rw[mul_assoc,←mul_add]
 apply W.trans
 apply Kin.mulT (Kin.refl _ v)
 have Hx: Kin σ ((F+(B*F+H))+(B*H)) ((F+(B*F+H))+0):=loft_add (Kin.refl _ (dub_V hp (dub_V (hb.mul_T hp) hQ))) hx
 rw [add_zero] at Hx
 rw [show (F+(B*F+H))+(B*H)=(U+B)*(F+H) from (by unfold U; ring)] at Hx; exact Hx
end
#print axioms tilt_K
end YM.CF.Scree.Ing
end
