import YM.SU5.Selected.Attic.Tally
import YM.SU5.Selected.Lantern.Count
/-! # combine local product goods and copies with **tilted MateK**. Need total debris cost paid
separately after. No estimate on sector count in full Fock. -/
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Pannier.Chancel
open Function Filter NormedSpace Metric Lattice Cube SU Fock Lat Spire Scroll MeasureTheory ProbabilityTheory Peaks Drapes Rush Tulip Skye Pastry
open Damask Dais.Parity
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] opCStarAlgebra
variable {n ι : Type*}[LinearOrder n][Fintype n][Nonempty n]
namespace Attic
variable {X Y Y' A A':ι→FC n}{b:Bool}{r E:ℝ}{M W:Wave n}{G:FC n}
local notation "ℸ" => fun i:ι=> together (X i) (Y' i)
local notation "ℓ" => fun i:ι=> together (X i) (Y i)
def tiltLoan (M:Wave n)(P:Op n)(s:ℝ):ℝ:=‖driftW (cards P s) M‖
def southern (E t r:ℝ):ℝ:= E*(r+3)*t⁻¹^2
variable {P:Op n}{t:ℝ}(pV:IsStarProjection P)(pW:Sea P W)(e:0<E)(u:E≤1)(c:0<r)(a:0<t)(t':t≤1){k:ℕ}(g:Riser k G)
local notation "B"=> E*(r+2)
local notation "Cρ"=> E*(r+3)
local notation "K"=> tiltLoan M P t
local notation "A₀" R:max=> ‖driftW (cards P t) M‖ * t⁻¹^ R
include pV pW e c u a t' g
lemma policy (f:Folder X Y Y' A A' b r E M W G)(L:List ι)(d:L.Nodup) : Yep (E⁻¹*t⁻¹) (acts (star (fo (ℸ) L*G)) M) W ((southern E t r)^L.length * t⁻¹^ k *‖G‖* K):=by
 intro l; rw [act_inner]; let U:=acts (fo Damask.use l) W; have hv: ‖U‖≤1:= token_limit l pW.2; let z:=l.length; let p:=k+2*L.length+z; have ht: Access P (0+l.length) U:= add_comm l.length 0 ▸ token_spend l P W 0 (access_unit pW)
 have he:= f.tenderQ pV a t' g e c u L [] U (0+l.length) (pause_token A (fun i=> ⟨_,f.pitch i⟩) (startPause A f.standing) l) (by simpa using d) (wd:=show k+2*( ([]:List ι).length+L.length)+(0+l.length)≤ p from le_of_eq (by simp [p,z])) ht
 simp only [fo,List.map_nil,List.prod_nil,one_mul,List.length_nil,pow_zero,zero_add] at he
 change _≤ _*(E⁻¹*t⁻¹)^l.length; apply he.trans
 change Cρ^L.length*(‖G‖*(‖U‖*E⁻¹^l.length))*(A₀ p) ≤ _; apply (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hv (by positivity)) (norm_nonneg _)) (by positivity)) (by positivity)).trans_eq; unfold southern tiltLoan p z; rw [pow_add,pow_add t⁻¹,pow_mul]; simp_rw [mul_pow]; ring -- tune
omit g pV e c u pW t' a
open Crest.Airy Buffered
lemma ford_wealth {R:ℝ}{S T: Finset n}{X Y Z:ι→ Ket n}(h: Sheet S T P G b X Y Z R E)(p:IsStarProjection P)(w: Sea P W)(m:Sea (cutM S) M)(e:0<E)(u:E≤1)(a:0<t)(t':t≤1)(j:0<R)(g:Riser k G)(l:List ι)(d:l.Nodup): Yep (E⁻¹*t⁻¹) (acts (star (fo (fun i=>handy b S (X i) (Z i)) l*G)) M) W ((southern E t R)^l.length * t⁻¹^ k *‖G‖*K):= policy p w e u j a t' g (lodging h p w m e u) l d
#check @ford_wealth

section wires
variable {I':Type*}[LinearOrder I'][Fintype I']
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
end wires
open Function Filter NormedSpace Metric Lattice Wilson Laurent Finset Cube SU Fock Lat Spire Scroll MeasureTheory ProbabilityTheory Peaks Drapes Rush Tulip Dial Pastry
open Buffered Branch Tenant Skye RG
open Reed (Fine)
open Lantern
variable {n:Side} {q:Type}[Fintype q][DecidableEq q] {L:List (Cab n)}
 {M:Tulip.Male}{j w t r:ℕ}{τ η ξ J R δ γ ε E:ℝ}
 {T:Finset (Seat n)} (C: Lantern.Service M j w t τ η ξ J R δ q r L) {b:Bool}
 {U:Fields n}{A:FC (Single n)}{Φ Ψ: Wave (Single n)}

include C
lemma grains (h:Winter j δ n γ w ε) (p:0<E)(u:E≤1){δ':ℝ}(py:0<δ')(vT:δ'≤1)(hc:southern E δ' (2*R)≤1)
    (tR:0<R)(z:0≤ξ)(g:0≤η)(v₁:η+(ξ+ε*R) ≤ 1/3)(v₂:ξ+ε*R+(R*2)*(η+(ξ+ε*R))≤ E^3)
    (hp:Guard U.2 δ)(ht:IsStarProjection (spar j M U.2))(P:Sea (spar j M U.2) Φ)(Q:Sea (cutM (Tset n)) Ψ)
    (clean:∀ a∈ L,a.feels U t τ) (v:∀ a∈L, Agrees a.broad U.1 U.2) (l:∀ a∈L,a.rev=b)
    {d:ℕ}(xy:Riser d A)(p':Fine (Tset n) (modesIn n T) false A)(v':Disjoint (Resort L) T) :
       Yep (E⁻¹ * δ'⁻¹) (acts (star (guest L U*A)) Ψ) Φ (((J*southern E δ' (2*R))^(L.length*r)) * δ'⁻¹^d* ‖A‖ * tiltLoan Ψ (spar j M U.2) δ'):=by
 classical
 let Pr (a:Cab n): FC (Single n)→Prop:= Marquee U M j R η ξ b a.core q r
 have hx(a)(e:a∈L): Blend (Pr a) (J^r) (a.frame U):=by unfold Pr; nth_rw 1 [← l a e]; exact (C.guests _ e).pressed _ (clean _ e) (v _ e) hp
 let Exp(f: FC (Single n)):= ∃ V': Cab n→FC (Single n), (∀ i∈ L,Pr i (V' i)) ∧ f=fo V' L; have he:Blend Exp (J^(L.length*r)) (guest L U):=by rw [visits_C U L,← constBill L J]; exact Blend.prod L C.nodup hx
 let x:=southern E δ' (2*R); rw [show ((J*southern E δ' (2*R))^(L.length*r))* δ'⁻¹^d*‖A‖ * tiltLoan Ψ (spar j M U.2) δ'= (x^(L.length*r) * δ'⁻¹^d* ‖A‖ * tiltLoan Ψ (spar j M U.2) δ')* (J^(L.length*r)) by unfold x; rw [mul_pow]; ring]; have e:0<x:= by unfold x southern; positivity
 apply paper he _ (by positivity) (by unfold tiltLoan; positivity); rintro F ⟨V,H,rfl⟩
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
 rw [show fo V L=fo f u' from ?_]; exact (ford_wealth hZ ht P Q p u py vT (by positivity) xy u' l).weigh (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one e.le hc eT) (by positivity)) (norm_nonneg _)) (show 0≤tiltLoan Ψ _ δ' from norm_nonneg _)) (by positivity)
 rw [← t']; unfold fo; have ht : L.attach.map (V ∘ Subtype.val)=L.map V:=by rw [← List.map_map,List.attach_map_subtype_val]
 exact congrArg List.prod ht.symm -- scope
end Attic
end YM.CF.Pannier.Chancel
open YM.CF.Pannier.Chancel.Attic
#print axioms grains
#print axioms policy
