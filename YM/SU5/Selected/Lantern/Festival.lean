import YM.SU5.Selected.Lantern.Pops
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 450000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Pannier.Chancel.Lantern
open Function Filter NormedSpace Metric Lattice Wilson Laurent Finset Cube SU Fock Lat Spire Scroll MeasureTheory ProbabilityTheory Peaks Drapes Rush Tulip Dial Pastry
open Buffered Branch Tenant Skye RG
open Crest.Airy
open Reed (Fine)
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] opCStarAlgebra
local notation "I"=>Complex.I
open Damask
section wire
variable {I':Type*}[LinearOrder I'][Fintype I']
  {F Φ:Wave I'}{G A:FC I'}{Q:FC I' → Prop}{ε d w :ℝ}
lemma paper (u:Blend Q w A)(p:∀ Z, Q Z→ Yep ε (acts (star (Z*G)) F) Φ d)(h:0≤ε)(v:0≤d) : Yep ε (acts (star (A*G)) F) Φ (d*w):=by
 induction u with
 | item A q=> rw [mul_one]; exact p _ q
 | zero=>simp [Yep]
 | extendsTo _ q ih=> exact ih.weigh (mul_le_mul_of_nonneg_left q v) h
 | join _ _ a b=> intro i; rw [add_mul,star_add,act_add,inner_add_left]; rw [mul_add,add_mul]; apply (norm_add_le ..).trans; exact add_le_add (a i) (b i)
 | smul _ c ih=> intro i; rw [Algebra.smul_mul_assoc,star_smul,act_smul,inner_smul_left,norm_mul]; exact (mul_le_mul_of_nonneg_left (ih i) (norm_nonneg _)).trans_eq (by simp; ring)
private lemma weaveFo {k:ℕ}{X Y : Type*}(L:List X)(u:L.Nodup) (w:X→FC I')(P:X×Y→ FC I')(S:X→ List Y)(p:∀ i,w i=fo (fun j=>P (i,j)) (S i))(h:∀ i,(S i).Nodup)(d:∀ i,k ≤ (S i).length):
    ∃ F:List (X×Y), F.Nodup ∧ L.length*k≤F.length ∧ fo w L=fo P F:=by
 let f(i):= (S i).map (fun j=>(i,j)); let g(L:List X):= L.flatMap f
 have he:L.Pairwise (List.Disjoint on f):=by
    apply u.imp; intro a b h x y z; obtain ⟨t,u,rfl⟩:=List.mem_map.mp y; obtain ⟨j,v,hz⟩:=List.mem_map.mp z; exact h (Prod.mk.inj hz).1.symm
 refine ⟨g L,List.nodup_flatMap.2 ⟨fun i _ => (h i).map (fun a b h=> (Prod.mk.inj h).2),he⟩,?_⟩
 clear he u; induction L with
 |nil=> simp [fo,g]
 |cons i L h=>
    constructor; · change _ ≤ (f i ++ g L).length; rw [List.length_append,List.length_cons,add_comm L.length,Nat.add_mul,one_mul]; apply add_le_add _ h.1; unfold f; rw [List.length_map]; exact d i
    change w i * fo w L= fo P (f i ++g L); rw [h.2,p]; unfold fo f; rw [List.map_append,List.prod_append,List.map_map]; rfl -- tune
private lemma constBill {X:Type*}(L:List X)(u:ℝ)(r:ℕ): (L.map (fun _=> u^r)).prod=u^(L.length*r):=by induction L with | nil=> simp|cons a L h=> rw [List.map_cons,List.prod_cons,h,List.length_cons,add_comm L.length,Nat.add_mul,one_mul,pow_add]
end wire
variable {n:Side} {q:Type}[Fintype q][DecidableEq q] {L:List (Cab n)}
 {M:Tulip.Male}{j w t r:ℕ}{τ η ξ J R δ γ ε E:ℝ}
 {T:Finset (Seat n)} (C: Service M j w t τ η ξ J R δ q r L) {b:Bool}
 {U:Fields n}{A:FC (Single n)}{Φ Ψ: Wave (Single n)}
namespace Service
include C
lemma peels (h:Winter j δ n γ w ε) (p:0<E)(u:E≤1)(hc:E*(2*R+3)≤1)
    (tR:0<R)(z:0≤ξ)(g:0≤η)(v₁:η+(ξ+ε*R) ≤ 1/3)(v₂:ξ+ε*R+(R*2)*(η+(ξ+ε*R))≤ E^3)
    (hp:Guard U.2 δ)(ht:IsStarProjection (spar j M U.2))(P:Sea (spar j M U.2) Φ)(Q:Sea (cutM (Tset n)) Ψ)
    (clean:∀ a∈ L,a.feels U t τ) (v:∀ a∈L, Agrees a.broad U.1 U.2) (l:∀ a∈L,a.rev=b)
    (p':Fine (Tset n) (modesIn n T) false A)(v':Disjoint (Resort L) T) :
       Yep E⁻¹ (acts (star (guest L U*A)) Ψ) Φ (((J*(E*(2*R+3)))^(L.length*r)) *‖A‖):=by
 classical
 let Pr (a:Cab n): FC (Single n)→Prop:= Marquee U M j R η ξ b a.core q r
 have hx(a)(e:a∈L): Blend (Pr a) (J^r) (a.frame U):=by unfold Pr; nth_rw 1 [← l a e]; exact (C.guests _ e).pressed _ (clean _ e) (v _ e) hp
 let Exp(f: FC (Single n)):= ∃ V': Cab n→FC (Single n), (∀ i∈ L,Pr i (V' i)) ∧ f=fo V' L; have he:Blend Exp (J^(L.length*r)) (guest L U):=by rw [visits_C U L,← constBill L J]; exact Blend.prod L C.nodup hx
 let x:=E*(2*R+3); rw [show ((J*(E*(2*R+3)))^(L.length*r))*‖A‖= (x^(L.length*r) *‖A‖)* (J^(L.length*r)) by unfold x; rw [mul_pow]; ring]; have e:0<x:= by unfold x; positivity
 apply paper he _ (by positivity) (by positivity); rintro F ⟨V,H,rfl⟩
 let Act:={i:Cab n//i∈L}
 haveI:Fintype Act:= by unfold Act; infer_instance -- inst from list.Attach? no
 -- expo choose one XZ L and tape length >= r
 have hh(i:Act): Pr i.val (V i.val):= H i.val i.property
 choose X Z L' e' e₀ a₀ hF using (fun i:Act=>hh i)
 obtain ⟨F,hZ⟩:=resupply M b h hp Z (fun i:Act=>i.val.broad) (fun i=>i.val.core) (fun i=>(C.guests _ i.property).enroll) (fun i=>(C.guests _ i.property).fence) (fun i j h=> C.apart i.property j.property (mt Subtype.ext h)) X T A (fun i=>(e' i).hang) (fun i=>(e' i).vine) (fun i=>v'.mono_left (broad_dine i.property)) ht (fun i=>(e' i).pitch) (fun i=>(e' i).lies) (fun i=>(e' i).stem) (fun i=>(e' i).ace) (fun i=>(e' i).need) p' tR z g v₁ v₂
 -- tape shuffle; product from attachments
 let f (i: Act × q):= handy b (Tset n) (col (X i.1) i.2) (col (Z i.1) i.2)
 obtain ⟨u',l,eT,t'⟩:=weaveFo L.attach C.nodup.attach (fun i:Act=> V i.val) f L' hF a₀ e₀
 rw [List.length_attach] at eT; change Yep _ (acts (star (fo V L*A)) _) _ _
 rw [show fo V L=fo f u' from ?_]; exact (forded hZ ht P Q p u (by positivity) u' l).weigh (mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one e.le hc eT) (norm_nonneg _)) (by positivity)
 rw [← t']; unfold fo; have ht : L.attach.map (V ∘ Subtype.val)=L.map V:=by rw [← List.map_map,List.attach_map_subtype_val]
 exact congrArg List.prod ht.symm -- scope
end Service
end YM.CF.Pannier.Chancel.Lantern
open YM.CF.Pannier.Chancel.Lantern
#print axioms Service.peels
