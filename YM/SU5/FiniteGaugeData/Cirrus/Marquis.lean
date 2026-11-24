import YM.SU5.FiniteGaugeData.Cirrus.Epitom
import YM.SU5.FiniteGaugeData.Maypole.Folio
set_option autoImplicit false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy.Seld.Poin.Cirrus
open Complex Filter Function Set MeasureTheory MeasureTheory.Measure Boundary OS OS.Semigroup Probe Maison
open scoped Topology NNReal InnerProductSpace
variable {H:Hilbert}(S: OS.Semigroup H timeAxis)
variable (Ω:Bench S)(hΩ:∀ p:E4,M S p Ω.val=Ω.val)(o:‖Ω.val‖=1)
variable {ι:Type}(G:Canopy H ι)(J K:Set ι)
local notation "a"=>timeAxis
open Submodule
variable {n:ℕ}(w:Points n)(g:Fin n→ G.Chip)
abbrev Chief (L:List (Fin n)): H.Op:= Film (fun i=>coreSp S (w i) (G.senses g i)) (rho S (G.credit g) (clockV a w)) L
local notation "B"=> Chief S G w g
local notation "C"=> G.Sr S Ω w g
local notation "Y"=> Height S Ω G
local notation "F"=> tower G
local instance : CompleteSpace (Height S Ω G J):= isClosed_closure.completeSpace_coe
local notation "H₁"=>  Canopy.Hatch (tower G J) S Ω
open Vp.Folio
lemma stayH(X:H.Op)(p:Commute X ((F J).Hatch S Ω))(y:H)(h:y∈Height S Ω G J): X y∈ Height S Ω G J:=by
 refine starProjection_eq_self_iff.mp ?_; change (H₁ * X) y=X y; rw [← DFunLike.congr_fun (show X*H₁=H₁*X from p) y] -- comp cast
 change X (H₁ y)= _; rw [show H₁ y=y from starProjection_eq_self_iff.mpr h]
include hΩ
lemma gapH (u:ℝ)(k:ℕ)(p:0<u) : Commute (leanX S u k) ((F J).Hatch S Ω):=by
 ext1 x; apply cache_I S k; let y:= Cache S k; let z:= leanX S u k; let P:= (F J).Hatch S Ω; let T:= y*(z*P); apply DFunLike.congr_fun (show y*(z*P)=y*(P*z) from ?_) x; rw [← mul_assoc, ← mul_assoc, show y*z=S.E u.toNNReal from heat_κ S u p, show y*P=P*y from ((F J).r_cap S Ω hΩ).pow_left k,mul_assoc, show y*z=S.E u.toNNReal from heat_κ S u p]; exact (F J).heat_P S Ω hΩ _
lemma stainH (x:E4)(t:G.Chip)(p:t.1∈J): Commute (coreSp S x (G.dep t)) ((F J).Hatch S Ω):= ((Canopy.stock (F J) S Ω hΩ ..).mul_left (Canopy.symphonyP (F J) S Ω hΩ (mDown G J t p))).mul_left (Canopy.stock (F J) S Ω hΩ ..)
lemma chop (L:List (Fin n))(p:ProofOrder w a L)(h:∀ i∈L,(g i).1∈ J) : Commute (Chief S G w g L) ((F J).Hatch S Ω):=by
 induction L with
 | nil=> exact Commute.one_left _
 | cons i L ih=>
    obtain ⟨q,r⟩:= List.pairwise_cons.mp p; have ht:= ih r (fun i k=> h _ (List.mem_cons_of_mem _ k)); refine (stainH S Ω hΩ G J _ _ (h i List.mem_cons_self)).mul_left ((show Commute (clip (rho S (G.credit g) (clockV a w)) i L) (H₁) from ?_).mul_left ht); cases L with
    | nil=> exact Commute.one_left _
    | cons j L=> exact gapH S Ω hΩ G J _ _ (sub_pos.mpr (q j List.mem_cons_self))
-- contiguous concatenating
variable (L R:List (Fin n)) (P:Pale S Ω G J K)
include P o
lemma stately (p:ProofOrder w a (L++R))(q:∀ i∈ L,(g i).fst∈ J)(r:∀ i∈ R,(g i).fst∈ K): C (L++R)= C L * C R := by
 change inner ℂ Ω.val (B _ Ω.val)=inner ℂ Ω.val (B _ Ω.val)*inner ℂ Ω.val (B _ Ω.val)
 have ht: inner ℂ Ω.val (B [] Ω.val)=1:=by change inner ℂ Ω.val Ω.val=1; rw [inner_self_eq_norm_sq_to_K,o]; simp
 cases L using List.reverseRecOn with
 | nil=> rw [ht,one_mul,List.nil_append]
 | append_singleton L i=> cases R with
    | nil=> rw [ht,mul_one,List.append_nil]
    | cons j R=>
       obtain ⟨v,k,z⟩:= List.pairwise_append.mp p; let T:=B (L++[i]); let A:= B (j::R); let X:=rho S (G.credit g) (clockV a w) i j; let u(k):=clockV a w k; have he:0<u j-u i:= sub_pos.mpr (z i (by simp) j List.mem_cons_self); have HP: X Ω.val=Ω.val:= earnO S Ω.val hΩ _ he; have hz:IsSelfAdjoint X:= warm_a S _ he
       let y:= (star T) Ω.val; have hy: y∈Y J := by
          apply stayH S Ω G J _ _ _ (Canopy.OmegaP (F J) S Ω)
          let W:=H₁; rw [show H₁ = star (W) from ((F J).hatch_adj S Ω).symm]; have hz:= congrArg star ((chop S Ω hΩ G J w g _ v q).symm.eq); simp only [star_mul] at hz; exact hz
       let h:=P y hy (X (A Ω.val)) (stayH S Ω G K _ (gapH S Ω hΩ G K _ _ he) _ (stayH S Ω G K _ (chop S Ω hΩ G K w g _ k r) _ (Canopy.OmegaP (F K) S Ω))) -- ims
       rw [show B ((L++[i])++(j::R))=T*X*A from joiningF ..]; change inner ℂ Ω.val (T (X (A Ω.val)))= _
       rw [← ContinuousLinearMap.adjoint_inner_left T]; apply (sub_eq_zero.mp h).trans; unfold y; change inner ℂ (T.adjoint Ω.val) _ * inner ℂ Ω.val (X (A Ω.val))=_; rw [ ContinuousLinearMap.adjoint_inner_left T, ← ContinuousLinearMap.adjoint_inner_left X, show X.adjoint=X from hz,HP]
#print axioms stainH
#print axioms stately
end YM.CF.Buffered.Afterglow.Hierarchy.Seld.Poin.Cirrus
