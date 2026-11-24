import YM.SU5.Selected.Attic.Bon
import YM.SU5.Selected.Lantern.Scatter
import YM.SU5.Selected.Lantern.Particle
/-! # Copy degree. Geometric budget uses F(actual) not horizon. -/
set_option autoImplicit false
set_option maxHeartbeats 450000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Pannier.Chancel.Attic
open Function Filter NormedSpace Metric Lattice Wilson Laurent Finset Cube SU Fock Lat Spire Scroll MeasureTheory ProbabilityTheory Peaks Drapes Rush Tulip Dial Pastry
open Buffered Branch Tenant Skye RG
open Crest.Airy Lantern
open Reed (Fine)
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] opCStarAlgebra
open Dais.Parity
variable {I t:Type*} [LinearOrder I][Fintype I][Nonempty I]
-- use standard grade generated
inductive Plump : ∀ (_:ℕ)(_ : FC I), Prop where
 | one(n:ℕ): Plump n (1:FC I)
 | letter (b:Bool)(x:Ket I): Plump 1 (creed b x)
 | growth {n m:ℕ}{A: FC I} (p:Plump n A): n ≤ m → Plump m A
 | add {n:ℕ}{X Y: FC I}: Plump n X→ Plump n Y→ Plump n (X+Y)
 | sub {n:ℕ}{X Y: FC I}: Plump n X→ Plump n Y→ Plump n (X-Y)
 | scale {n:ℕ}{X:FC I}: Plump n X→∀ c:ℂ, Plump n (c • X)
 | mul {m n:ℕ}{X Y:FC I}: Plump n X→ Plump m Y→ Plump (n+m) (X*Y)
namespace Plump
variable {n:ℕ}{X:FC I}(p:Plump n X)
include p
theorem mount : Riser n X:=by
 induction p with|one=>exact Riser.one|letter=>exact Riser.letter ⟨_,_,rfl⟩|growth _ p v=>exact v.mono p|add _ _ p q=> exact p.add q|sub _ _ p q=> exact p.sub q|scale _ p q=> exact q.scale p|mul _ _ p q=> exact p.mul q
lemma rise (V:UNI I): Plump n (theta V X):=by
 induction p with
 | one n=> rw [theta_one]; exact .one n
 | letter b x => cases b; rw [show creed false x=create x from rfl,theta_upV]; exact (Plump.letter true (acts V.val x)).scale _; rw [show creed true x=remove x from rfl,theta_downV]; exact (Plump.letter false (acts V.val x)).scale _
 | growth p q r=>exact r.growth q
 | add _ _ v t=> rw [theta_add]; exact v.add t
 | sub _ _ v t=> rw [theta_sub]; exact v.sub t
 | scale _ c h=> rw [theta_smul]; exact h.scale _
 | mul _ _ h q=> rw [theta_mul]; exact h.mul q
omit p in
lemma cancel : Plump n (0:FC I):=by simpa using (Plump.one (I:=I) n).sub (.one _)
lemma negP: Plump n (-X):=by rw [← neg_one_smul ℂ]; exact p.scale _
omit p
lemma sum [DecidableEq t](f:t→FC I)(S:Finset t)(h:∀ i, Plump n (f i)): Plump n (∑ i∈S,f i):=by induction S using Finset.induction with| empty=> rw [sum_empty]; exact Plump.cancel| insert a L p q=> rw [sum_insert p]; exact (h _).add q
lemma prodV (f:t→FC I)(L:List t)(h:∀ i∈ L, Plump n (f i)): Plump (n*L.length) (L.map f).prod:=by induction L with| nil=> exact Plump.one _|cons x L ih=> rw [List.map_cons,List.prod_cons,List.length_cons,Nat.mul_add,mul_one,add_comm]; exact (h x List.mem_cons_self).mul (ih (fun i v=>h i (List.mem_cons_of_mem _ v)))
end Plump
variable {N m:Side}{M:Tulip.Male}{ν:Mark N→ℂ}{K:Calibration}
 {q:Type}[Fintype q][DecidableEq q]{j w t k s y B:ℕ}{τ η ξ J R δ:ℝ}{L: List (Cab N)}
def Huts(n:ℕ)(L:List (Cab N)):Prop:= ∀ i∈L,∀ z:Fields N, Plump n (i.frame z)
lemma huts_price (p:Huts y L)(z:Fields N): Riser (y*L.length) (guest L z):= by rw [visits_C]; exact (Plump.prodV _ L (fun i l=> p i l z)).mount
lemma Huts.append {L':List (Cab N)}(p:Huts y L)(q:Huts y L') : Huts y (L++L'):= fun i h z=> (List.mem_append.mp h).elim (fun a=>p _ a z) (fun a=>q _ a z)
lemma huts_mirror (p:Huts y L) (i:Axis)(s:ℤ): Huts y (L.map (fun x=>x.shadow i s)):=by intro A h z; obtain ⟨x,v,rfl⟩:= List.mem_map.mp h; exact (p x v (reflFields i s z)).rise _

-- after Lantern/Scatter. add degree control.
section roads
variable {n:Side}{ν:Mark n→ℂ}{l:ℕ}
open Buffered.Afterglow Journey Lantern.Roads
variable (h: Twosome K n ν) (hs:safeReflect M j δ n)
local notation "Act"=>Service M j w t τ η ξ J R δ q k
include h hs
lemma stand (g:n=K.c m) (A:List (Cab n)) (i:Axis)
    (f:Act A)(a:Huts y A) (q:cows i (Resort A) B)(v:2^l*(B+addgap K)≤ n.val) :
    ∃ V:List (Cab n),Act V ∧ Huts y V∧ V.length=2^l*A.length ∧ ‖ν (guest A)‖^(2^l)≤ ‖ν (guest V)‖ ∧ ∀ a,a≠i → ∀ s,cows a (Resort A) s → cows a (Resort V) s := by
 induction l generalizing B A with
 | zero=> exact ⟨A,f,a,by simp,by simp,fun a _ s u=>u⟩
 | succ l ih=>
    have ht:B+addgap K ≤ n.val:= v.trans' (Nat.le_mul_of_pos_left _ (pow_pos two_pos _)); obtain ⟨z,p,u,e⟩:=topLong (i:=i) g _ q ht; let s:= Heat.gaugeShift K.B z
    let U:= A.map fun a=> a.shadow i s; let W:= U++A; have h'': Resort W=hyphen i s (Resort A)∪ Resort A:=by unfold W U; rw [resort_duc,Service.back_wall]; -- fix rfl
    have hp:Resort A⊆ band n i s K.ℓ:=p
    have hx: Act W := (f.back i s hs).append f (by rw [Service.back_wall]; exact west K i s _ hp) -- wtf
    have hw:= h i z (guest A) (f.permit hp)
    obtain ⟨Y,aq,wF,b,r,g'⟩:= ih W hx ((huts_mirror a i s).append a) (B:=2*B+addgap K) (by rw [h'']; exact u) (by rw [pow_succ] at v; exact v.trans' (le_of_eq (by ring)))
    refine ⟨Y,aq,wF,?_,?_,fun a g t k=> g' a g t (h''.symm ▸ e a g t k)⟩
    · rw [b,pow_succ]; unfold W U; rw [List.length_append,List.length_map]; ring -- W/U let
    rw [pow_succ',pow_mul]; have he:reflMark i (Heat.gaugeShift K.B z) (guest A)*guest A=guest W:=by unfold W U; rw [guest_comb,Service.back_refl] -- let
    rw [he] at hw; exact (pow_le_pow_left₀ (by positivity) hw _).trans r
-- spill all axes
lemma scatter (g:n=K.c m)(v:2^l*(B+addgap K)≤ n.val)(S:Finset Axis) (A:List (Cab n))(f:Act A)(a:Huts y A)
    (p:∀ a∈S,cows a (Resort A) B) : ∃ U:List (Cab n), Act U ∧ Huts y U ∧ U.length=(2^l)^S.card*A.length ∧ ‖ν (guest A)‖^((2^l)^S.card) ≤ ‖ν (guest U)‖:=by
 induction S using Finset.induction_on generalizing A with
 | empty=> exact ⟨A,f,a,by simp,by simp⟩
 | @insert i S x ih=>
    obtain ⟨U,hU,Ue,au,b,vL⟩:= stand h hs g A i f a (p i (mem_insert_self ..)) v
    obtain ⟨Z,gX,wU,e,l'⟩:= ih U hU Ue (fun s v=> vL s (fun h=>x (h ▸ v)) _ (p s (mem_insert_of_mem v))) -- extras
    rw [card_insert_of_notMem x,pow_succ']; refine ⟨Z,gX,wU,?_,?_⟩
    · rw [e,au]; ring
    rw [pow_mul]; exact (pow_le_pow_left₀ (by positivity) b _).trans l'
include h hs
/-- One-datum general, including already-mirrored pair. late n lower bound. -/
theorem replicate (g:n=K.c m)(v:B+addgap K≤n.val)(F:List (Cab n))(f:Act F)(ha:Huts y F)
   (z:∀ i,cows i (Resort F) B) : ∃ U: List (Cab n), ∃ u:ℕ, Act U∧ Huts y U ∧ 0 < u ∧ U.length=u*F.length ∧ u≤(More n).val^4 ∧ (More n).val^4 ≤ u*(4*(B+addgap K))^4 ∧ ‖ν (guest F)‖^u ≤ ‖ν (guest U)‖:=by
 obtain ⟨k',a,l⟩:= goldilock (x:=n.val) (show 0<B+addgap K from Nat.add_pos_right _ addgap_pos) v
 obtain ⟨U,g',wt,e,y⟩:= scatter h hs g a univ F f ha (fun i _=> z i)
 rw [Finset.card_fin 4] at e y
 refine ⟨U,_,g',wt,by positivity,e,?_,?_,y⟩
 · change _ ≤ (n.val*2)^4; apply pow_le_pow_left'; have hq:= a.trans' (Nat.le_mul_of_pos_right (2^k') (Nat.add_pos_right _ (show 0 < addgap K from addgap_pos))); omega
 · rw [←mul_pow]; apply pow_le_pow_left'; change n.val*2 ≤_; apply le_trans (Nat.mul_le_mul_right 2 l); exact le_of_eq (by ring)
end roads
end YM.CF.Pannier.Chancel.Attic
open YM.CF.Pannier.Chancel.Attic
#print axioms replicate
#print axioms huts_price
