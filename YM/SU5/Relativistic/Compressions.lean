import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.MeasureTheory.Integral.Gamma
/-! # Unit Jacobian for changing scheduling of pinned coords at KK. Integer pin lattice but kernel real not required rational equations. -/
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 600000
noncomputable section
namespace YM.CF.Papyrus.MinorPins
open Function Finset Filter Matrix
open scoped BigOperators
variable {J K L : Type}[DecidableEq J][Fintype J][DecidableEq K][Fintype K][DecidableEq L][Fintype L]
variable {P : Submodule ℝ (J→ℝ)}{c d :Finset J}

-- reserve pins on outside clock. Int-lift property.
def hide (c:Finset J){R:Type} (x:J→R):↥(cᶜ)→ R := fun i=>x i

def InLattice {R:Type} (x:R→ℝ) := ∀ i,∃ j:ℤ,x i=j
structure Grates (c:Finset J)(P:Submodule ℝ (J→ℝ)):Prop where
 fade (x:J→ℝ)(h:x∈P)(t:hide c x=0): x=0
 stay (f:↥(cᶜ)→ℝ):∃ x∈P, hide c x=f
 pays (f:↥(cᶜ)→ℝ)(p:InLattice f):∃ (x:J→ℝ),x∈P ∧ InLattice x ∧ hide c x=f

variable (p:Grates c P)
namespace Grates
include p
private def lost (f:J→ℝ) : J→ℝ:= (p.stay (hide c f)).choose
private lemma slip (f:J→ℝ): lost p f∈P:= (p.stay _).choose_spec.1
private lemma bake (f:J→ℝ): hide c (lost p f)=hide c f:= (p.stay _).choose_spec.2
lemma unique {f g:J→ℝ}(h:f∈P)(t:g∈P)(u:hide c f=hide c g):f=g:= sub_eq_zero.mp (p.fade _ (P.sub_mem h t) (sub_eq_zero.mpr u))
def bright : (J→ℝ) →ₗ[ℝ] (J→ℝ) where
 toFun := lost p
 map_add' f g:= unique p (slip ..) (P.add_mem (slip ..) (slip ..)) (by rw [bake p]; change hide c f+ hide c g= hide c (lost p f)+hide c (lost p g); rw [bake,bake]) -- inference?
 map_smul' t f:= unique p (slip ..) (P.smul_mem t (slip ..)) (by rw [bake p]; change t • hide c f=t • hide c (lost p f); rw [bake])
lemma inBright (f:J→ℝ) : p.bright f∈P := slip p f
lemma dull (f:J→ℝ) : hide c (p.bright f)=hide c f:= bake p f
lemma price (f:J→ℝ)(h:InLattice f):InLattice (p.bright f):=by
 obtain ⟨x,t,u,v⟩:= p.pays (hide c f) fun i=>h i
 rw [p.unique (p.inBright _) t ((p.dull f).trans v.symm)]; exact u
end Grates
variable {e:K ↪ J}
def smear (e:K ↪ J):Matrix J K ℝ:= (1:Matrix J J ℝ).submatrix id e
lemma smear_t {e:K ↪ J} (v:K→ℝ)(i:K): (smear e *ᵥ v) (e i)=v i:=by
 unfold smear mulVec dotProduct; rw [sum_eq_single i]
 · change (1:Matrix J J ℝ) (e i) (e i) * _=_; rw [one_apply_eq,one_mul] -- tune
 · intro j u t; change (1:Matrix J J ℝ) (e i) (e j) * _=_; rw [one_apply_ne (fun x=> t (e.injective x.symm)),zero_mul]
 exact fun t => False.elim (t (mem_univ _))
lemma smear_f {e:K ↪ J} (v:K→ℝ) (i:J) (x:i∉Set.range e): (smear e *ᵥ v) i=0:= sum_eq_zero fun j _=>by change (1:Matrix J J ℝ) i (e j) * _=_; rw [one_apply_ne (fun i' => x ⟨j,i'.symm⟩),zero_mul]

lemma smeared (Q:Matrix J J ℝ) (e:K ↪ J) : (smear e)ᵀ * Q *smear e=Q.submatrix e e:=by
 ext i j; rw [Matrix.mul_apply,sum_eq_single (e j)]; swap
 · intro k u t; change _*(1:Matrix J J ℝ) k (e j)=_; rw [one_apply_ne t,mul_zero]
 swap; · exact fun t => False.elim (t (mem_univ _))
 rw [show smear e (e j) j=1 from one_apply_eq _,mul_one,Matrix.mul_apply,sum_eq_single (e i)]
 · rw [show (smear e)ᵀ i (e i)=1 from one_apply_eq _,one_mul]; rfl
 · intro k u t; change (1:Matrix J J ℝ) k (e i)*_= _; rw [one_apply_ne t,zero_mul]
 exact fun t => False.elim (t (mem_univ _))

namespace Grates
variable {g:L ↪ J}{A: Grates c P}{B:Grates d P}
lemma pin_card (B: Grates d P) : dᶜ.card= Module.finrank ℝ P:= by
 let F:= LinearMap.pi fun i:↥(dᶜ)=> (LinearMap.proj (R:=ℝ) i.val).comp P.subtype
 have he: Bijective F:=⟨fun x y t=> by apply Subtype.ext; exact B.unique x.property y.property t, by intro i; obtain ⟨v,t,u⟩:= B.stay i; exact ⟨⟨v,t⟩,u⟩⟩
 have h:= (LinearEquiv.ofBijective F he).symm.finrank_eq; simpa [Finset.card_compl] using h
-- core equival using arbitrary injections e,g basis.
private def Δ (e:K ↪ J)(g:L ↪ J)(A : Grates c P):Matrix K L ℝ:=LinearMap.toMatrix' ((LinearMap.pi (fun i:K=>LinearMap.proj (R:=ℝ) (e i))).comp ((LinearMap.id-(Grates.bright A)).comp (smear g).mulVecLin))
private lemma fare (p:Grates c P)(h:Set.range e=(c:Set J))(w:L→ℝ): smear e *ᵥ (Δ e g p *ᵥ w)= ((smear g)*ᵥ w)-p.bright ((smear g)*ᵥ w):=by
 funext i; by_cases H:i∈ Set.range e
 · obtain ⟨u,rfl⟩:= H; rw [smear_t]; unfold Δ; rw [LinearMap.toMatrix'_mulVec]; rfl
 rw [smear_f _ i H]; let v:↥(cᶜ):=⟨i,mem_compl.mpr fun x=>H (h.symm ▸ x)⟩; apply Eq.symm; exact sub_eq_zero.mpr (congrFun (p.dull ((smear g)*ᵥ w)) v).symm
private lemma fair (p:Grates c P)(b:Grates d P)(h:Set.range e=(c:Set J))(v:Set.range g=(d:Set J)): Δ e g p * Δ g e b=1:= by
 let T:=Δ e g p; let W:=Δ g e b
 apply Matrix.mulVec_injective -- likely wrong lemma
 funext x; rw [← Matrix.mulVec_mulVec, Matrix.one_mulVec]
 have hp:= fare (e:=e) (g:=g) p h (W *ᵥ x); have he:=fare b v (g:=e) x; change (smear g)*ᵥ (W*ᵥ x)= _ at he
 rw [he,map_sub, p.unique (p.inBright _) (b.inBright _) (p.dull _), show p.bright (smear e *ᵥ x)=0 from ?_,zero_sub,sub_neg_eq_add,sub_add_cancel] at hp; swap
 · apply p.fade _ (p.inBright _); rw [p.dull]; exact funext fun i=>smear_f (e:=e) x i.val (by rw [h]; exact mem_compl.mp i.property)
 funext i; exact Eq.trans (smear_t _ _).symm ( (congrFun hp (e i)).trans (smear_t _ _)) -- tune
private lemma projects (p:Grates c P) : ∃ x:Matrix K L ℤ,(x.map Int.cast)= Δ e g p:=by
 let F:= Δ e g p
 have h(i:K)(j:L): ∃ z:ℤ,F i j=(z:ℝ):=by
    let f:= (smear g) *ᵥ (Pi.single j 1);
    have he : InLattice f:=by
      intro i; by_cases t:i∈Set.range g
      · obtain ⟨u,rfl⟩:=t; unfold f; rw [smear_t]; by_cases p:u=j; subst p; exact ⟨1,by simp⟩; exact ⟨0,by simp [p]⟩
      exact ⟨0,(smear_f _ _ t).trans (Int.cast_zero.symm)⟩
    obtain ⟨y,u⟩:=he (e i); obtain ⟨z,v⟩:=p.price f he (e i); refine ⟨y-z,?_⟩
    have hx:F i j=(F*ᵥ Pi.single j 1) i:=by simp -- test
    rw [hx,show (F *ᵥ Pi.single j 1) i= _ from (show (F *ᵥ Pi.single j 1) i=f (e i)-p.bright f (e i) from (by unfold F Δ; rw [LinearMap.toMatrix'_mulVec]; rfl)),u,v, Int.cast_sub]
 choose x hx using h; exact ⟨Matrix.of x,Matrix.ext fun i j=> (hx i j).symm⟩

-- rewrite grams: Q kills kernel both. for same cardinal reindexed.
lemma exchange (p : Grates c P)(b:Grates d P){Q:Matrix J J ℝ}(h0:Q.transpose=Q)(t:P≤LinearMap.ker Q.mulVecLin)(e g : K ↪ J)(h:Set.range e=(c:Set J))(v:Set.range g=(d:Set J)): (Q.submatrix e e).det=(Q.submatrix g g).det:=by
 let T:= Δ e g p; let x:= Δ g e b; obtain ⟨X,hX⟩:=projects (e:=e) (g:=g) p; obtain ⟨Y,hY⟩:=projects (e:=g) (g:=e) b
 change X.map Int.cast=T at hX; change Y.map Int.cast=x at hY
 have he:T*x=1:= fair p b h v
 have hu: T.det*T.det=1:=by
    have hf: ((X.det:ℤ):ℝ)=T.det:= by rw [←hX]; exact (Int.castRingHom ℝ).map_det X -- tune map order
    have hg: ((Y.det:ℤ):ℝ)=x.det:=by rw [←hY]; exact (Int.castRingHom ℝ).map_det Y
    have hm: X.det*Y.det=1:=by
      have hh: (((X.det*Y.det:ℤ):ℤ):ℝ)=1:=by rw [Int.cast_mul,hf,hg,←Matrix.det_mul, he]; simp
      exact_mod_cast hh
    rw [←hf]; rcases Int.isUnit_iff.mp (IsUnit.of_mul_eq_one Y.det hm) with w|w <;> rw [w] <;> norm_num
 have hx:Q * ((smear e)*T)= Q * (smear g):=by
    apply Matrix.mulVec_injective; funext w; simp only [←mulVec_mulVec]; rw [show (smear e) *ᵥ (T*ᵥ w)= _ from (show (smear e) *ᵥ (T*ᵥ w)= _ from fare p h w),mulVec_sub]; rw [show Q *ᵥ _= _ from (show Q*ᵥ p.bright _=0 from t (p.inBright (smear g *ᵥ w))),sub_zero] -- tune
 let A:= smear e*T; let B:=smear g
 have hy :(Q*A)ᵀ=(Q*B)ᵀ:=congrArg _ hx
 rw [Matrix.transpose_mul Q A,Matrix.transpose_mul Q B,h0] at hy
 have hQ:T.transpose*(Q.submatrix e e)*T=(Q.submatrix g g):= by
    rw [←smeared,← smeared]; calc
       _ = Aᵀ * Q*A:= by unfold A; simp only [Matrix.transpose_mul,Matrix.mul_assoc]
       _ = Aᵀ * (Q*B):= by rw [Matrix.mul_assoc,show Q*A= Q*B from hx] -- syntactic tune
       _ = Bᵀ *Q * B:=by rw [←Matrix.mul_assoc,hy]
 rw [←hQ,Matrix.det_mul,Matrix.det_mul,det_transpose,mul_right_comm,hu,one_mul]
lemma invariance {Q:Matrix J J ℝ}(A: Grates c P)(B:Grates d P)(h:Set.range e=(c:Set J))(v:Set.range g=(d:Set J))(p:Q.transpose=Q)(t:P≤LinearMap.ker Q.mulVecLin): (Q.submatrix e e).det=(Q.submatrix g g).det:=by
 have hc:c.card=Fintype.card K := by
    rw [← Finset.card_univ (α:=K),←card_image_of_injective (Finset.univ:Finset K) e.injective]
    rw [show univ.image e=c from by ext i; simp [← Finset.mem_coe,←h,Set.mem_range]] -- tune
 have hd:d.card=Fintype.card L := by
    rw [← Finset.card_univ (α:=L),←card_image_of_injective (Finset.univ:Finset L) g.injective]; rw [show univ.image g=d from by ext i; simp [← Finset.mem_coe,←v,Set.mem_range]]
 let f:= Fintype.equivOfCardEq (α:=K) (β:=L) (by have h:= A.pin_card; have t:=B.pin_card; have v:= Finset.card_compl_add_card c; have W:= Finset.card_compl_add_card d; omega)
 let k:= f.toEmbedding.trans g
 have hp:Set.range k= (d:Set J):= by rw [←v]; ext i; refine ⟨?_,?_⟩; rintro ⟨x,rfl⟩; exact ⟨f x,rfl⟩; rintro ⟨x,rfl⟩; obtain ⟨x,rfl⟩:= f.surjective x; exact ⟨x,rfl⟩
 exact (exchange A B p t e k h hp).trans (show _=_ from Matrix.det_submatrix_equiv_self f (Q.submatrix g g))
end Grates
end YM.CF.Papyrus.MinorPins
#print axioms YM.CF.Papyrus.MinorPins.Grates.invariance
