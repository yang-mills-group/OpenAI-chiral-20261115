import YM.SU5.SatinWard.Resolution.Collier
/-! # The Wave must commute with even these complex tests once it meets the real tests -/
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 4000
noncomputable section
namespace YM.CF.Mezzo
open Function NormedSpace Lattice Finset Cube Lat Fock Tulip Peaks Drapes SU Ember
open Rush Scroll Paige Spire Fir Bloch Next.Free Dial ExTwo
open scoped Topology Matrix MatrixOrder Kronecker Classical BigOperators InnerProductSpace Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
local notation "▪"=> Op Slot
local notation "𝕂"=> Op (Fin 5)
local notation "I"=> Fin 3
abbrev TuneM:=Op (Fin 3)
local notation "M"=>TuneM
local notation "𝕌"=> UNI I
lemma coeffInj {A B C D:M}(t:sonnet A B=sonnet C D): A=C ∧ B=D:=by
 refine ⟨?_,?_⟩; exact (coeffJoint A B).1.symm.trans ((congrArg (passage · ac ac) t).trans (coeffJoint C D).1); exact (coeffJoint A B).2.symm.trans ((congrArg (passage · ab ab) t).trans (coeffJoint C D).2)
noncomputable def vote: 𝕌 × 𝕌→* UNI Slot:=
 { toFun:=fun x=> ⟨sonnet x.1.val x.2.val,by
                     have he(g:𝕌): g.val*star g.val=1:=g.property.2
                     exact Matrix.mem_unitaryGroup_iff.mpr (by rw [←coeffStar,←coeffMul, he, he, initial_jet])⟩
   map_one':=Subtype.ext initial_jet
   map_mul':=fun x y=> Subtype.ext (coeffMul ..) }
lemma registrar_vote (x:𝕌 × 𝕌): Registrar (vote x):= fun _=> still_U.mpr (firmSuite _ _ _).symm
lemma cred_vote (x y:𝕌 × 𝕌):Concert (vote (x*y*x⁻¹*y⁻¹)):= by rw [map_mul,map_mul,map_mul,map_inv,map_inv]; exact Concert.trade _ _ (registrar_vote x) (registrar_vote y)
lemma rotate_vote (v:𝕌 × 𝕌)(A B:M): twist (vote v) (sonnet A B)=sonnet (twist v.1 A) (twist v.2 B):=by
 rw [twist_formula, twist_formula,twist_formula]; change sonnet v.1.val v.2.val*_*star (sonnet v.1.val v.2.val)=_; rw [←coeffStar,←coeffMul,←coeffMul]
lemma vote_cc (A B:𝕌)(h:cc A.val=A.val)(p:cc B.val=B.val): cc (vote (A,B)).val=(vote (A,B)).val:= by
 change cc (sonnet _ _)=_; rw [←coeffCC,h,p]; rfl
section
variable {i:Type}[DecidableEq i][Fintype i]
lemma stencilL (g:Equiv.Perm i)(d:i→ℂ)(x y:i): (hair g*Matrix.diagonal d) x y= if g x=y then d y else 0:=by rw [Matrix.mul_diagonal,hair_at]; split<;>simp
lemma stencilR (g:Equiv.Perm i)(d:i→ℂ)(x y:i): (Matrix.diagonal d*hair g) x y= if g x=y then d x else 0:=by rw [Matrix.diagonal_mul,hair_at]; split<;>simp
lemma twirlMove (g:Equiv.Perm i)(d:i→ℂ): twist (hairU g) (Matrix.diagonal d)=Matrix.diagonal (d ∘ g):=by apply Mir.twist_comm _ _ _; change hair g*_= Matrix.diagonal (d ∘ g)*hair g; ext x y; rw [stencilL,stencilR]; split; rename_i t; rw [←t]; rfl; rfl
end
abbrev attuned(a:𝕌):=vote (a,a)
lemma concert_a (A B:𝕌):Concert (attuned (A*B*A⁻¹*B⁻¹)):= cred_vote (A,A) (B,B)
lemma pealU_star(i:I) : star (pealU i).val=(pealU i).val:=by ext a b; change star (Matrix.diagonal _) a b= Matrix.diagonal _ a b; by_cases h:a=b; subst b; simp [blastSign,tideU]; simp [h,Ne.symm h]
lemma pealU_cc(i:I): cc (pealU i).val=(pealU i).val:=by ext a b; change cc (Matrix.diagonal _) a b=Matrix.diagonal _ a b; by_cases h:a=b<;>simp [h,tideU,blastSign]
lemma partner(a b:I) :Concert (attuned (pealU a*pealU b)):=by
 let T:=hairU (Equiv.swap a b); have he: twist T (pealU b).val=(pealU a).val:=by
    unfold T; rw [show (pealU b).val=Matrix.diagonal _ from (rfl: _=(Matrix.diagonal (blastSign b))), twirlMove]; apply congrArg (Matrix.diagonal (n:=I)); funext i; by_cases h:i=a; · simp [h,blastSign]
    have ht:Equiv.swap a b i≠ b:= fun hx=>h ((Equiv.swap a b).injective (hx.trans (Equiv.swap_apply_left a b).symm)); simp [blastSign,h,Ne.symm h,ht,Ne.symm ht]
 have hz:T*pealU b*T⁻¹* (pealU b)⁻¹=pealU a*pealU b:=by
    apply Subtype.ext; change (T.val*_*star T.val)* star (pealU b).val=(pealU a).val*_ ; rw [←twist_formula,he,pealU_star]
 exact hz ▸ concert_a T (pealU b)
-- cyclic from two swaps: any ordered different gets a τ cycling i→j→k→i with even two-transposition. As commutator of two transposes.
abbrev shiftU (a b:I):𝕌:= hairU (Equiv.swap a b)
abbrev progressV(a b c:I):𝕌:= shiftU b c * shiftU a b * (shiftU b c)⁻¹ * (shiftU a b)⁻¹
lemma shiftX (a b:I):star (shiftU a b).val=(shiftU a b).val:=by
 change star (hair _)=hair _; rw [hair_t]; simp
lemma progress_view(a b c:I):let P:= (Equiv.swap b c).trans (Equiv.swap a b); (progressV a b c).val=hair (P.trans P):=by
 intro P; change (shiftU b c).val*(shiftU a b).val*star (shiftU b c).val*star (shiftU a b).val= _; rw [shiftX, shiftX]; change hair _ * hair _ * hair _ * hair _= _; rw [mul_assoc (hair _ * hair _), hair_mul,hair_mul]
lemma fiscal(X:▪)(h:∀ i:E,Commute (matter i).val X)(t:∀ g:UNI Slot,Concert g→cc g.val=g.val→ twist g X=X): ∃ a b:ℂ,X=sonnet (a • 1) (b • 1):=by
 let M':=passage X ac ac; let N':=passage X ab ab; let K:=sonnet M' N'; have hz:X=K:= collaborations X h
 have he (g:𝕌)(u:Concert (attuned g))(v:cc g.val=g.val): twist g M'=M'∧twist g N'=N':=by
    obtain p:= t (vote (g,g)) u (vote_cc _ _ v v); rw [hz,show K=sonnet _ _ from (rfl:K=sonnet M' N'),rotate_vote] at p; exact coeffInj p
 have hm(Z:M)(p:∀ g:𝕌,Concert (attuned g)→cc g.val=g.val→twist g Z=Z): ∃ a:ℂ,Z=a • (1:M):=by
    let d(x:I):= Z x x; have hk:Z=Matrix.diagonal d:=by
      ext i j; by_cases y:i=j; subst j; rw [Matrix.diagonal_apply_eq]
      rw [Matrix.diagonal_apply_ne _ y]; obtain ⟨k,hi,hj⟩:=(show ∀ i j:I,∃ k:I,k≠i ∧ k≠j from by decide) i j; let C:= pealU i*pealU k; have hy:cc C.val=C.val:=by unfold C; simp only [Submonoid.coe_mul,cc_mul,pealU_cc]
      obtain hT:=(still_U.mp (p C (partner ..) hy)).eq; unfold C at hT; change (Matrix.diagonal _*Matrix.diagonal _)*_= Z*(Matrix.diagonal _*Matrix.diagonal _) at hT; rw [Matrix.diagonal_mul_diagonal] at hT; let W:= Z i j; have hB:= Matrix.ext_iff.mpr hT i j; rw [Matrix.diagonal_mul,Matrix.mul_diagonal] at hB
      have hv:- W=W:=by simpa [W,blastSign,peal,y,Ne.symm y,hi,hj] using hB
      apply add_self_eq_zero.mp; exact neg_eq_iff_add_eq_zero.mp hv -- names
    refine ⟨d 0,?_⟩; have hd(j:I): d j=d 0:=by
      by_cases hx:j=0; rw[hx]
      obtain ⟨k,hi,hj⟩:=(show ∀ i j:I,∃ k:I,k≠i ∧ k≠j from by decide) 0 j
      let B:=progressV 0 j k; let S:= (Equiv.swap j k).trans (Equiv.swap 0 j); let Q:= S.trans S; have hb:B.val=hair Q:= progress_view ..
      have hy:= (still_U.mp (p B (concert_a ..) (show cc B.val=B.val by rw [hb,hairU_cc]))).eq; rw [hk,hb] at hy
      have hq: Q j=0:=by unfold Q S; simp [Equiv.swap_apply_of_ne_of_ne hi hj] -- direction maybe other
      have ht:=Matrix.ext_iff.mpr hy j 0; rw [stencilL,stencilR,hq,if_pos rfl] at ht; exact ht.symm
    rw [hk,show d=(fun _ : I=>d 0) from funext hd]; ext i j; by_cases h:i=j<;> simp [h]
 obtain ⟨a,g⟩:= hm M' (fun g u v=> (he g u v).1); obtain ⟨b,u⟩:=hm N' (fun g u v=> (he g u v).2); exact ⟨a,b,hz.trans (congrArg₂ sonnet g u)⟩

theorem coatWave(X:▪)(h:∀ i:E,Commute (matter i).val X)(t:∀ g:UNI Slot, Concert g→cc g.val=g.val → twist g X=X) (g:UNI Slot)(k:Registrar g): twist g X=X:=by
 obtain ⟨a,b,e⟩:= fiscal _ h t
 have he:g.val=sonnet _ _:= collaborations g.val (fun i=> (still_U.mp (k i)).symm); apply Mir.twist_comm; rw [e,he,←coeffMul,←coeffMul]
 congr 1 <;> (simp only [Algebra.mul_smul_comm, Algebra.smul_mul_assoc, mul_one,one_mul])
end YM.CF.Mezzo
