import GaugeFieldConstruction.Fangs
set_option autoImplicit false
set_option maxHeartbeats 40000
noncomputable section
namespace YM.Frugal
open Function Finset
open scoped Classical BigOperators Topology
variable {E:Type}[NormedAddCommGroup E][NormedSpace ℂ E][FiniteDimensional ℂ E](Λ:ℕ→E→ₗ[ℂ]E)(J: ∀ {i j:ℕ}, i≤j→∀ x:E, Λ i (Λ j x)=Λ i x)(V: ∀ {i j:ℕ}, i≤j →∀ x:E,Λ j (Λ i x)=Λ i x)
-- buy 8≥ before Patch. invariant frames optional.Canonical deriv Works.
private lemma pay_norm {I:Type}[Fintype I](g:I→E)(p:Injective (scalB g)) :∃ c:ℝ,0≤c∧∀ z:FrameK I,LoomK z ≤ c*‖Woof z g‖:=by
 let W:=scalB g; let R:=LinearMap.range W; let S:=LinearEquiv.ofInjective W p
 let K : R→L[ℂ]FrameK I:= S.symm.toLinearMap.toContinuousLinearMap
 refine ⟨(Fintype.card I:ℝ)*‖K‖,by positivity,fun z=>?_⟩
 have he:‖z‖≤ ‖K‖*‖Woof z g‖:= (show ‖z‖≤ ‖K‖*‖S z‖ from by have hh:=K.le_opNorm (S z); rw [show K (S z)=z from S.symm_apply_apply z] at hh; exact hh) -- tune syntax
 unfold LoomK; rw [mul_assoc]; conv_rhs=> rw [←nsmul_eq_mul];
 apply le_trans (sum_le_sum (g:=fun _=> _*_) (fun i (_:i∈ univ)=> (norm_le_pi_norm z i).trans he)); rw [sum_const,card_univ] -- tune
lemma Planaris.monoB {I:Type}[Fintype I]{g:I→ℕ}{k:ℕ}{b:I→E}{c s:ℝ}(p:Planaris g Λ k b c)(q:c ≤ s):Planaris g Λ k b s:=⟨p.ray,fun i=> (p.bounded i).trans q,p.coframe,p.saturated,fun i=> (p.brake i).trans (mul_le_mul_of_nonneg_right q (norm_nonneg _))⟩
private lemma model_b {I:Type}[Fintype I](b:I→E)(g:I→ℕ)(k:ℕ)(h:Injective (scalB b))(Y:∀ i,g i≤k)(C:∀ i j,Λ j (b i)= if g i ≤j then b i else 0)(B:∀ x:E,Λ k x=x →∃ w:FrameK I, x=Woof w b):∃ c:ℝ,8≤c∧Planaris g Λ k b c:=by
 obtain ⟨D,y,A⟩:=pay_norm b h; let K:=∑ i:I, ‖b i‖; have hx:0≤K:= sum_nonneg fun i _=>norm_nonneg _
 refine ⟨D+K+8,le_add_of_nonneg_left (add_nonneg y hx),Y,fun i=>?_,B,C,fun i=>(A i).trans ?_⟩
 · exact le_trans (b:=K) (single_le_sum (fun _ _=>norm_nonneg _) (mem_univ i)) (by linarith only [y])
 exact mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
private lemma Mold (S:Submodule ℂ E) : ∃ (I:Type) (p:Fintype I), letI:=p; ∃ b:I→E,Injective (scalB b)∧ (∀ i,b i∈S)∧∀ x∈S,∃ w:FrameK I,x=Woof w b:=by
 let b:= Module.Free.chooseBasis ℂ S; let X:=Module.Free.ChooseBasisIndex ℂ S; let e:= S.subtype
 let T (i:X):E:= e (b i); let H:FrameK X→ₗ[ℂ] S:= b.equivFun.symm.toLinearMap
 have hh(i:FrameK X):e (H i)= Woof i T:=by change e (b.equivFun.symm i)= _; rw [b.equivFun_symm_apply,map_sum]; exact sum_congr rfl fun j _=>map_smul ..
 refine ⟨X,inferInstance,T,?_,fun i=>(b i).property,fun i v=>?_⟩
 · intro x y p; exact b.equivFun.symm.injective (S.subtype_injective ((hh x).trans (p.trans (hh y).symm)))
 let Y:S:=⟨i,v⟩; obtain ⟨w,vw⟩:=b.equivFun.symm.surjective Y; exact ⟨w,(show i=e (H w) from (congrArg e vw).symm).trans (hh w)⟩
include V J
lemma Planaris.supply (n:ℕ) : ∃ (I:Type) (p:Fintype I), letI:=p; ∃ g b τ,8 ≤ τ∧Planaris (I:=I) g Λ n b τ:=by
 let S(i):Submodule ℂ E:=LinearMap.ker (Λ i-LinearMap.id)
 have he(i:ℕ)(x:E):x∈ S i ↔ Λ i x=x:=by change _; rw [show S i=_ from rfl,LinearMap.mem_ker]; exact sub_eq_zero -- tune
 induction n with
 | zero=>
    obtain ⟨I,h,b,p0,F,Y⟩:= Mold (S 0); letI:=h; refine ⟨I,h,(fun _=>0),b, model_b Λ b (fun _=>0) 0 p0 (fun i=> le_rfl) (fun i j=>?_) (fun x v=>Y x ((he _ _).mpr v))⟩
    change Λ j (b i)=if 0 ≤j then b i else 0; rw [if_pos (by omega)]; rw [←show Λ 0 (b i)= b i from (he _ _).mp (F i)]; exact V (by omega) _
 | succ n ih=>
    obtain ⟨I,h,l,b,t,y,p⟩:= ih; letI:= h; let R:=S (n+1) ⊓ LinearMap.ker (Λ n)
    obtain ⟨K,q,c,z,u,C⟩:= Mold R; letI:=q
    let T:= I⊕K; let x:= Sum.elim b c; let v:=Sum.elim l (fun _=>n+1:K→ _) -- tune syntax
    have hb(i:I): Λ n (b i)=b i:=by rw [p.saturated,if_pos (p.ray _)]
    have hk(i:K): Λ (n+1) (c i)=c i:= (he _ _).mp ((u i).1)
    have hd(i:K): Λ n (c i)=0:=(u i).2
    let W:=scalB x
    have hx(z:T→ℂ):W z= Woof (z ∘ Sum.inl) b + Woof (z ∘ Sum.inr) c:=Fintype.sum_sum_type ..
    have hp(z:T→ℂ):Λ n (W z)=Woof (z ∘ Sum.inl) b:=by
       rw [hx]; unfold Woof; simp only [map_add,map_sum,map_smul,hb, hd,smul_zero,sum_const_zero,add_zero]
    refine ⟨T,inferInstance,v,x,model_b Λ x v _ (LinearMap.ker_eq_bot.mp ?_) ?_ ?_ ?_⟩
    · rw [LinearMap.ker_eq_bot']; intro f g; have HE: Woof (f ∘ Sum.inl) b=0:=by rw [←hp]; change W f=0 at g; rw [g,map_zero]
      have hv:LoomK (f ∘ Sum.inl)≤0:=by have hv:=p.brake (f ∘ Sum.inl); rw [HE,norm_zero,mul_zero] at hv; exact hv
      have he0:f∘ Sum.inr=0:=z (by change Woof (f ∘ Sum.inr) c= _; rw [map_zero]; change W f=0 at g; rw [hx,HE,zero_add] at g; exact g)
      funext i; cases i with|inl i=>exact norm_le_zero_iff.mp ((single_k (f ∘ Sum.inl) i).trans hv)|inr i=>exact congrFun he0 i
    · intro i; cases i with|inl j=> exact (p.ray j).trans (by change n ≤ n+1; omega)|inr i=>exact le_rfl
    · rintro (i|j) k; · exact p.saturated i k
      change Λ k (c j)= if n+1 ≤ k then c j else 0; split_ifs with t
      · nth_rw 1 [←hk j]; rw [V t,hk]
      have t: k ≤ n:=by omega
      rw [←J t,hd,map_zero]
    · intro z y; let L:=Λ n z; let G:=z-L; have H : G∈R:=by
         refine ⟨(he _ _).mpr ?_,?_⟩; unfold G L; rw [map_sub,y,V (by omega)]
         change Λ n G=0; unfold G L; rw [map_sub,J le_rfl,sub_self]
      obtain ⟨l,y⟩:=p.coframe L (J le_rfl _); obtain ⟨g,v⟩:=C G H
      let X:=Sum.elim l g; have a:X ∘ Sum.inr=g:=rfl -- fun eta?
      have b:X ∘ Sum.inl=l:=rfl
      refine ⟨X,?_⟩; change z=W X; rw [hx,a,b,←y,←v]; unfold G; abel
end YM.Frugal
noncomputable section
namespace YM.CF.Oath
open TableF.Lenten.Layout YM.Frugal
lemma PCexists (g:ℕ) :∃ (I:Type) (p:Fintype I), letI:=p; ∃ b l τ,8 ≤τ ∧ Planaris (I:=I) l ΓProj g b τ:=by
 obtain ⟨I,p,l,b,τ,v,h⟩:=Planaris.supply ΓProj (@fun i j p x=> MStore x p) (@fun i j p x=> MGate p x) g
 exact ⟨I,p,b,l,τ,v,h⟩
end YM.CF.Oath
end
end
