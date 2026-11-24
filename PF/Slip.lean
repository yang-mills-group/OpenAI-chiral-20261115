import PF.Third
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option synthInstance.maxSize 28000
set_option maxRecDepth 2000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance Lamour.Bridge.Celeste Designs Twah Prototype
open Lamour.Bridge.Celeste.Morn
open Spine
open CF.Velvet CF.Pannier.Chancel
open QuadClock
open Aria Casting MacroGrid Preparation.Yoke Yoke.Travel
open SatinNucleus Six DoseTravel Set
namespace PureForce.WickLabels
open Hake Hive Sault Pastry Set
variable {N:Type}[LinearOrder N][Fintype N]
local notation "d"=>Oboe N
private abbrev matT (P:Op N)(i:d):Op N:= if i.1 then P else 1-P
-- right vanishing piece
private abbrev partR (P:Op N) (i:d):FC N:= let x:=acts (matT P i) (basisKet i.2); if i.1 then create x else Fock.remove x

def ink (P:Op N)(i j:d):ℂ:= if i.1=j.1 then 0 else if i.1 then P j.2 i.2 else (1-P) i.2 j.2
lemma actor (P:Op N)(T:IsStarProjection P)(v:Wave N)(p:Fock.Sea P v)(i:d) : acts (partR P i) v=0 ∧ acts (star (Hake.bell i-partR P i)) v=0:=by
 rcases i with ⟨b,i⟩
 let j: N→ Ket N:= basisKet; let f:=acts P (j i); let e:=acts (1-P) (j i)
 have h1: acts P f=f:=by unfold f; rw [←act_mul,T.isIdempotentElem.eq]
 have h2: acts P e=0:= by unfold e; rw [←act_mul,mul_sub,mul_one,T.isIdempotentElem.eq,sub_self,act_zero]
 have ht:=tarp T p.1 h1; have hv:=tars T p.1 h2
 have he: e+f=j i:=by unfold e f; rw [←act_add,sub_add_cancel,act_one]
 cases b
 · refine ⟨hv,?_⟩; change acts (star (takeF i-Fock.remove e)) v=0; rw [←remove_take i, remove, remove, star_sub,star_star,star_star]; change acts (create (j i)-create e) v=0; rw [←he,map_add,add_sub_cancel_left]; exact ht
 refine ⟨ht,?_⟩; change acts (star (put i-create f)) v=0; rw [←create_put i]; change acts (star (create (j i)-create f)) v=0; rw [←he,map_add,add_sub_cancel_right]; exact hv
lemma pair (P:Op N)(T:IsStarProjection P)(i k:d):antiB (partR P i) (Hake.bell k)=ink P i k • 1:=by
 cases i with | mk b i=> cases k with | mk g k=>
  let x:=acts P (basisKet i); let y:= acts (1-P) (basisKet i)
  have he: star (1-P)=1-P:=by rw [star_sub,star_one,T.isSelfAdjoint]
  cases b <;> cases g
  · simp only [partR, Hake.bell, matT, Bool.false_eq_true,↓reduceIte,ink,zero_smul]; rw [←remove_take]; unfold antiB Fock.remove; rw [← star_mul, ←star_mul,← star_add, car_create,star_zero]
  · change antiB (Fock.remove y) (put k)= (1-P) i k • 1; rw [←create_put]; unfold antiB; rw [car]; apply congrArg (· • (1:FC N)); unfold y; nth_rw 1 [←he]; rw [act_inner, basis_inner,basis_act]
  · change antiB (create x) (takeF k)=P k i • 1; rw [←remove_take k]; unfold antiB; rw [add_comm,car,basis_inner, show x.ofLp k=P k i from basis_act ..]
  change antiB (create x) (put k)=(0:ℂ) • (1:FC N); rw [zero_smul,←create_put]; exact car_create ..
private lemma innerL (v:Wave N){I:Type*}(l:List I)(F:I→Wave N):⟪v,(l.map F).sum⟫_ℂ=(l.map (fun i=> ⟪v,F i⟫_ℂ)).sum:=by induction l with|nil=>simp|cons a b ih=>simp [ih]

def E (P:Op N)(q:Wave N)(l:List d):ℂ:=inner ℂ q (Fock.chime Hake.bell q l)
lemma cashE (P:Op N)(T:IsStarProjection P)(q:Wave N)(h:Fock.Sea P q)(i:d)(l:List d) :
    E P q (i::l)=((picks l).map fun p:Bout d=> (Fock.cval p.neg * ink P i p.front)*E P q p.back).sum :=by
 rw [E,Fock.charm]; let w:=Fock.chime Hake.bell q l; let a:=partR P i; let u:= Hake.bell i
 have hz:⟪q,acts (u-a) w⟫_ℂ=0:=by rw [←act_inner,show acts (star (u-a)) _=0 from (actor P T q h i).2,inner_zero_left]
 rw [act_sub,inner_sub_right] at hz
 rw [show inner ℂ q (acts (Hake.bell i) _)=inner ℂ q (acts a w) from sub_eq_zero.mp hz]
 rw [show acts a w= _ from plume Hake.bell (partR P) q (ink P) (fun i=>(actor P T q h i).1) (pair P T) i l, innerL]; unfold seatsC E; simp_rw [inner_smul_right]
-- scalar linked seat shells. all attached to one pad (Finset X), may enlarge with further components if needed.
open Branch Material
namespace Bill
variable {D X:Type}[TopologicalSpace D][Fintype X][DecidableEq X]
-- use Bit same H and N with fictitious i=j picked in Χ (can't guarantee has any Single at pad of Gram). easier separate.
variable {H:Host X N D}
structure Tag (H:Host X N D)(ν:D→ℝ)(pad S:Seal X)(f:D→ℂ)(C:ℝ): Prop where
 pos : 0 ≤ C
 price (x:D): ‖f x‖ ≤ C*ν x
 cont:Continuous f
 portal(x y:D):H.advert S x y→ f x=f y
 resource (_:C≠0): pad⊆S∧ Grove H.space S

def Cred (H:Host X N D)(ν:D→ℝ)(pad:Seal X)(a:ℝ)(f:D→ℂ)(B:ℝ):Prop:= ∃ (I:Type)(_ :Fintype I)(S:I→Seal X)(F:I→D→ℂ)(T:I→ℝ), (∀ i, Tag H ν pad (S i) (F i) (T i)) ∧ (∑ i,rent a (S i \ pad)*T i) ≤ B ∧ ∀ x,f x=∑ i,F i x

variable {ν ξ:D→ℝ} {pad S T: Seal X}{a c k:ℝ}{f g:D→ℂ}
lemma scalar0 (h:Grove H.space pad) : Cred H (fun _=>1) pad a 1 1:=by
 refine ⟨Unit,inferInstance,fun _=>pad,fun _=>1,fun _=>1,(fun i=> ⟨zero_le_one,fun _=>by simp,continuous_const,fun _ _ _=>rfl,fun _=> ⟨Finset.Subset.refl _,h⟩⟩),by simp [Branch.rent],by simp⟩
lemma dormant : Cred H ν pad a 0 0:=⟨Empty,inferInstance,fun x=>x.elim,fun x=>x.elim,fun x=>x.elim,(fun x=>x.elim),by simp,by simp⟩
namespace Cred
lemma nn (h:Cred H ν pad a f c): 0 ≤ c:=by obtain ⟨I,i,N,F,T,J,U,_⟩:=h; exact (sum_nonneg (f:=fun i=> rent a _ * T i) (fun i _=>mul_nonneg (rent_pos ..).le (J i).pos)).trans U
lemma up (h:Cred H ν pad a f c)(p:c≤ k): Cred H ν pad a f k :=by obtain ⟨I,q,N,T,A,w,m,p'⟩:=h; exact ⟨I,q,N,T,A,w,m.trans p,p'⟩
lemma pin (h:Tag H ν pad S f c): Cred H ν pad a f (rent a (S\ pad)*c):=by exact ⟨Unit,inferInstance,fun _=>S,fun _=>f,fun _=>c,(fun _=>h),by simp,by simp⟩
lemma plus (h:Cred H ν pad a f c)(p:Cred H ν pad a g k) : Cred H ν pad a (fun x=>f x + g x) (c+k) :=by
 obtain ⟨A,i,Y,M,C,z,e,hf⟩:=h; obtain ⟨B,j,W,T,F,t,q,hg⟩:=p
 refine ⟨A⊕B,inferInstance,Sum.elim Y W,Sum.elim M T,Sum.elim C F,?_,?_,?_⟩
 · intro i; cases i; apply z; apply t
 · simp only [Fintype.sum_sum_type,Sum.elim_inl,Sum.elim_inr]; exact add_le_add e q
 intro x; rw [Fintype.sum_sum_type]; exact congrArg₂ (·+·) (hf _) (hg _)
lemma mult (h:Cred H ν pad a f c)(p:Cred H ξ pad a g k)(v:pad.Nonempty)(e:0 ≤ a): Cred H (ν*ξ) pad a (fun x=> f x*g x) (c*k):=by
 obtain ⟨A,i,Y,M,C,z,h₁,hf⟩:=h; have hp:=p.nn; obtain ⟨B,j,W,T,F,t,h₂,hg⟩:=p
 let S(i:A × B):=Y i.1 ∪ W i.2
 refine ⟨A×B,inferInstance,S,fun i x=>M i.1 x*T i.2 x,fun i=>C i.1*F i.2,?_,?_,?_⟩
 · rintro ⟨i,j⟩; let b:=z i; let h:=t j; refine ⟨mul_nonneg b.pos h.pos,fun x=>?_,b.cont.mul h.cont,fun x y V=> congrArg₂ (·*·) (b.portal _ _ (H.relay subset_union_left V)) (h.portal _ _ (H.relay subset_union_right V)), fun hx=>?_⟩
   · rw [norm_mul]; exact (mul_le_mul (b.price _) (h.price x) (norm_nonneg _) ((norm_nonneg _).trans (b.price _))).trans_eq (by simp only [Pi.mul_apply]; ring)
   have ⟨hi,hp⟩:=b.resource (left_ne_zero_of_mul hx); have ⟨hl,hg⟩:=h.resource (right_ne_zero_of_mul hx); obtain ⟨u,w⟩:=v; exact ⟨hi.trans subset_union_left,hp.unite hg (hi w) (hl w)⟩
 · refine le_trans ?_ (mul_le_mul h₁ h₂ (sum_nonneg (fun j _=>mul_nonneg (rent_pos ..).le (t _).pos)) (Cred.nn (f:=f) (show Cred H ν pad a f c from ⟨A,i,Y,M,C,z,h₁,hf⟩)))
   rw [Fintype.sum_prod_type,sum_mul]; simp_rw [mul_sum]; apply sum_le_sum; intro k _; apply sum_le_sum; intro j _
   -- look sum_mul order reversal ?
   unfold S; dsimp only; rw [Finset.union_sdiff_distrib]; apply le_trans (mul_le_mul_of_nonneg_right (rent_join (_\pad) (_\pad) e) (mul_nonneg (z k).pos (t j).pos)) (Eq.le ?_); ring
 intro x; change f x*g x= _; rw [hf,hg,Fintype.sum_prod_type,sum_mul]; simp_rw [mul_sum] -- tune sum order
lemma lists {I:Type*}(l:List I)(F:I→ D→ℂ)(T:I→ℝ)(h:∀ i∈l,Cred H ν pad a (F i) (T i)):Cred H ν pad a (fun x=> (l.map (fun i=>F i x)).sum) ((l.map T).sum):=by
 induction l with|nil=> exact dormant|cons i L p=> simp only [List.map_cons,List.sum_cons]; exact (h i List.mem_cons_self).plus (p (fun i q=>h i (List.mem_cons_of_mem _ q)))
lemma weighted (h:Cred H ν pad a f c)(z:ℂ)(p:‖z‖=1): Cred H ν pad a (fun x=>z*f x) c:=by
 obtain ⟨I,i,S,M,C,g,h,U⟩:=h; refine ⟨I,i,S,fun j x=> z*M j x,C,fun j=>{g j with cont:=continuous_const.mul (g j).cont,portal:=fun x y d'=>congrArg _ ((g j).portal x y d'),price:=?_},h,?_⟩
 · intro x; rw [norm_mul,p,one_mul]; exact (g j).price _
 intro x; change z*f x= _; rw [U,mul_sum]
end Cred

-- Shot element to billing on a given Pad containing i,j. cost global row price, not just single element. relabel Y ⊔ Pad
namespace Materialize
lemma entries {P:D→Op N}(h: Shot H (fun _=>1) ∅ a k P)(t:0≤a)(pad: Seal X)(b:Grove H.space pad):
    ∃ Q:N→N→ℝ,(∀ i j,0≤Q i j) ∧ (∀ i,∑ j,Q i j≤k) ∧ (∀ j,∑ i,Q i j≤k) ∧
    ∀ i j:N,H.port i∈pad→ Cred H (fun _=>1) pad a (fun x=> P x i j) (Q i j):=by
 obtain ⟨Y,L,G,T,U⟩:=h; have hs(S i j):0≤ L S i j:= ((G S).block i j).pos
 refine ⟨saleM a L,sale_nn hs a,T.rows,T.cols,fun i j l=> ⟨Seal X,inferInstance, fun s=>s∪ pad, fun s x=>Y s x i j,fun s=>L s i j,?_,?_,?_⟩⟩
 · intro S; let h:=(G S).block i j; exact ⟨h.pos,h.load,h.listens,fun x y p=> h.inputs _ _ (H.relay subset_union_left p),fun v=> ⟨subset_union_right,(h.stake v).2.1.unite b (h.stake v).2.2.1 l⟩⟩
 · unfold saleM; refine sum_le_sum ?_; intro S _; dsimp only; rw [Finset.union_sdiff_distrib, Finset.sdiff_self, Finset.union_empty]; unfold Branch.rent; gcongr; apply hs; exact Finset.sdiff_subset
 intro x; change P x i j= _; rw [U,Matrix.sum_apply]
-- contraction fees using rows flip. No need other endpoint in Pad? need first of matrix entry not sender in ink with sign true, so require both.
lemma options {P:D→Op N}(h: Shot H (fun _=>1) ∅ a k P)(t:0≤a)(pad:Seal X)(w:Grove H.space pad) :
    ∃ c:d→ d→ℝ,(∀ i j,0≤c i j)∧(∀ i,∑ j:d,c i j≤Real.exp a+k) ∧
    ∀ i j:d,H.port i.2∈pad→H.port j.2∈ pad→ Cred H (fun _=>1) pad a (fun x=>ink (P x) i j) (c i j):=by
 let K:=Real.exp a+k; have hv:= h.cost_pos
 obtain ⟨c,h₁,h₂,h₃,t₁⟩:= entries h t pad w; obtain ⟨f,e₁,e₂,e₃,t₂⟩:=entries (Shot.one.sub h) t pad w
 let R(i j:d):ℝ:=if i.1=j.1 then 0 else if i.1 then c j.2 i.2 else f i.2 j.2
 refine ⟨R,fun i j=>?_,fun i=>?_,fun i j he hr=>?_⟩
 · unfold R; split; rfl; split; apply h₁; apply e₁
 · rw [Fintype.sum_prod_type,Fintype.sum_bool]; obtain ⟨g,i⟩:=i; cases g
   · simpa only [R, Bool.false_eq_true, ↓reduceIte,sum_const_zero, add_zero,zero_add] using e₂ i
   simpa only [R,Bool.true_eq_false,↓reduceIte,sum_const_zero,add_zero,zero_add] using (h₃ i).trans (le_add_of_nonneg_left (Real.exp_pos _).le)
 unfold ink R; by_cases hp:i.1=j.1
 · simp only [hp,↓reduceIte]; exact dormant
 simp only [hp,↓reduceIte]; split_ifs with hr; exact t₁ _ _ ‹_›; exact t₂ i.2 j.2 he
end Materialize
-- Sum picks each index once (since reduced to Nodup list in no_clash)
private lemma chooseBack (L:List d)(b:Bout d)(p:b∈picks L): b.front∈L ∧ b.back.Sublist L :=by
 induction L generalizing b with
 | nil=>simp [picks] at p
 | cons i k ih =>
    rcases List.mem_cons.mp p with h|h; subst b; exact ⟨List.mem_cons_self,List.sublist_cons_self i k⟩
    obtain ⟨B,lH,rfl⟩:=List.mem_map.mp h; obtain ⟨hp,hq⟩:=ih B lH; exact ⟨List.mem_cons_of_mem _ hp,hq.cons_cons _⟩
private lemma chooseFront (L:List d): (picks L).map Bout.front=L:=by
 induction L with|nil=>rfl|cons i L ih=> simpa [picks,Function.comp_def,beside] using ih
variable {P:D→Op N}{v:D→Wave N}
private lemma tilled (p:∀ x,IsStarProjection (P x))(t:∀ x,Fock.Sea (P x) (v x))(B:Shot H (fun _=>1) ∅ a k P)(e:0≤a)(q:Grove H.space pad)(u:pad.Nonempty)(r:ℕ):∀ l:List d,l.length≤r→ l.Nodup→ (∀ i∈l,H.port i.2∈pad) → Cred H (fun _=>1) pad a (fun x=> E (P x) (v x) l) ((Real.exp a+k)^l.length):=by
 let G:=Real.exp a+k; have hg:1≤G:= (Real.one_le_exp e).trans (le_add_of_nonneg_right B.cost_pos)
 induction r with
 | zero=> intro l f _ _; rw [List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero f)]; convert scalar0 q using 1; funext x; unfold E; rw [emptyChime,inner_self_eq_norm_sq_to_K,(t x).2]; simp; simp
 | succ n ih=>
   rintro (_ | ⟨i,l⟩)
   · intro _ _ _; convert scalar0 q using 1; funext x; unfold E; rw [emptyChime,inner_self_eq_norm_sq_to_K,(t x).2]; simp; simp
   intro hl hv bt; have hv:= (List.nodup_cons.mp hv).2; have hl':l.length ≤ n:=Nat.le_of_succ_le_succ hl
   obtain ⟨c,cp,cx,cc⟩:= Materialize.options B e pad q
   let F (j:Bout d)(x:D):ℂ:=(Fock.cval j.neg * ink (P x) i j.front)* E (P x) (v x) j.back
   let M (j:Bout d):=c i j.front * G^l.length
   have hf j (hk:j∈ picks l): Cred H (fun _=>1) pad a (F j) (M j):=by
       obtain ⟨hR,hN⟩:=chooseBack l j hk
       have hE:= ih _ (hN.length_le.trans hl') (hN.nodup hv) (fun a x=>bt a (List.mem_cons_of_mem _ (hN.subset x)))
       let V:= (fun x=> Fock.cval j.neg * ink (P x) i j.front)
       have hp:= (cc i j.front (bt _ List.mem_cons_self) (bt _ (List.mem_cons_of_mem i hR))).weighted (Fock.cval j.neg) (by unfold Fock.cval; split <;> simp)
       convert (hp.mult hE u e).up (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hg hN.length_le) (cp ..)) using 1; ext; simp
   have hy: (fun x=> E (P x) (v x) (i::l)) = fun x=> ((picks l).map (fun j=> F j x)).sum :=funext fun x=> cashE _ (p x) _ (t x) i l
   rw [hy]; apply (Cred.lists (picks l) F M hf).up
   unfold M; change (((picks l).map (fun j=> c i (Bout.front j)*_)).sum) ≤ G^(l.length+1)
   rw [show (fun j:Bout d=> c i (Bout.front j)*G^l.length)=(fun a:d=>c i a*G^l.length) ∘ Bout.front from rfl,←List.map_map,chooseFront,Stilo.deed _ _ hv,←Finset.sum_mul,pow_succ']; apply mul_le_mul_of_nonneg_right _ (by positivity)
   exact (sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun j _ _=>cp _ _)).trans (cx i)
lemma supplied (p:∀ x,IsStarProjection (P x))(t:∀ x,Fock.Sea (P x) (v x))(B:Shot H (fun _=>1) ∅ a k P)(e:0≤a)(q:Grove H.space pad)(u:pad.Nonempty)(l:List d)(b:∀ i∈l,H.port i.2∈pad) : Cred H (fun _=>1) pad a (fun x=> E (P x) (v x) l) ((Real.exp a+k)^l.length):=by
 let G:=Real.exp a+k; have ht:1 ≤ G:=(Real.one_le_exp e).trans (le_add_of_nonneg_right B.cost_pos)
 rcases Hake.no_clash Hake.bell l Hake.revive with h|⟨T,c,g,z,f,h⟩
 · convert Cred.up (dormant (a:=a) (H:=H) (ν:=fun _=>1) (pad:=pad)) (show 0≤G^l.length by positivity) using 1; funext x; unfold E Fock.chime; rw [h,act_zero,inner_zero_right]; rfl -- act_zero namespace
 convert Cred.up ((tilled p t B e q u T.length T le_rfl g (fun i v=>b i (c.subset v))).weighted z f) (show G^T.length ≤ G^l.length from pow_le_pow_right₀ ht c.length_le) using 1; funext x; unfold E Fock.chime; rw [h,act_smul,inner_smul_right]
end Bill
end PureForce.WickLabels
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
