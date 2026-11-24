import Gingham.Ruff.Locket
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

lemma sheet_bij (d:Shape): Bijective (@sheet N d):= by
  rw [Fintype.bijective_iff_injective_and_card]
  exact ⟨Finset.image_injective d.anon_b.1,rfl⟩
def loon(N:Side)(d:Shape): Equiv.Perm (Seal (Seat N)) :=Equiv.ofBijective _ (sheet_bij d)

lemma reorderX {ι:Type*}[Fintype ι](f:ι→ι→ι→ι→ℝ):
    ∑ i,∑ j,∑ p,∑ q, f i j p q=∑ p,∑ q,∑ i,∑ j,f i j p q:=by
  have z(g:ι→ι→ι→ℝ):∑ i,∑ j,∑ k,g i j k=∑ j,∑ k,∑ i,g i j k:=by
     rw [sum_comm];exact sum_congr rfl fun _ _=>sum_comm
  have h(g:ι→ι→ι→ι→ℝ):∑ i,∑ j,∑ k,∑ l,g i j k l=∑ j,∑ k,∑ l,∑ i,g i j k l:=by
     rw [sum_comm];exact sum_congr rfl fun _ _=>z _
  rw [h f,h (fun j k l i=>f i j k l)]

lemma loomSale (d:Shape)(U: UNI SpinIdx)(M: Toll (Single N))(n:∀ i j, 0 ≤ M i j):
    ∑ i,∑ j, roe d U M i j ≤ tableland^2 * ∑ i,∑ j, M i j :=by
  unfold roe
  calc
    _ = ∑ p,∑ q,∑ i,∑ j, ‖(owl N d U).val i p * star ((owl N d U).val j q)‖ * M p q:=by
      -- use helper
      exact reorderX (fun i j p q=>‖(owl N d U).val i p * star ((owl N d U).val j q)‖ * M p q)
    _ ≤ _:=by
      simp_rw [mul_sum]
      refine sum_le_sum fun p _=>sum_le_sum fun q _=> ?_
      simp only [←sum_mul]
      exact mul_le_mul_of_nonneg_right (carven ..) (n p q)

lemma cans {I Y : Type*}[Fintype I][Fintype Y][DecidableEq Y][DecidableEq I] (k:ℝ)(c:Seal Y→ Toll I):
    savings k c = ∑ S,Branch.rent k S*∑ i,∑ j,c S i j:=by
  classical
  simp only [savings,saleM,mul_sum]
  symm; rw [sum_comm]; exact sum_congr rfl fun _ _=> sum_comm


variable {e:ℝ}{R:Seal (Seat N)→Prop}{A:Fob N e}{a c:ℝ}(d:Shape)(U: UNI SpinIdx)
abbrev Buttons (N:Side)(e:ℝ)(R:Seal (Seat N)→Prop):=
   Shells R (badge _) (bail N e) (bail N e)
def wig (H:Buttons N e R a c A):
 Buttons N e (R ∘ (loon N d).symm) a (tableland^2*c) (cope d U A):=by
  let E:=loon N d
  let f(S:Seal (Seat N)):= cope d U (H.mark (E.symm S))
  let M(S:Seal (Seat N)):= roe d U (H.cost (E.symm S))
  refine ⟨f,M,fun S=>?_,fun x=>?_,fun S i j g=>?_,?_⟩
  · have t:=show Jubilee e (E (E.symm S)) (M S) (f S) from eyes d U (H.pass _)
    rwa [E.apply_symm_apply] at t
  · unfold cope
    rw [H.sum,map_sum]
    exact Fintype.sum_equiv E _ (fun s=>f s x) fun i=>by dsimp only [f];rw [Equiv.symm_apply_apply]; rfl
  · obtain ⟨p,_,t⟩:=exists_ne_zero_of_sum_ne_zero g
    obtain ⟨q,_,v⟩:=exists_ne_zero_of_sum_ne_zero t
    exact H.good _ p q (right_ne_zero_of_mul v)


  apply le_trans _ (mul_le_mul_of_nonneg_left H.paid (sq_nonneg _))
  rw [cans,cans, ← Equiv.sum_comp E]
  rw [mul_sum]
  apply sum_le_sum;intro S _
  have b:Branch.rent a (E S) = Branch.rent a S:=by
    unfold Branch.rent
    rw [show (E S).card = S.card from Finset.card_image_of_injective _ d.anon_b.1]
  rw [b,mul_left_comm (tableland^2)] -- wrong occurrence
  apply mul_le_mul_of_nonneg_left _ (rent_pos ..).le
  rw [show M (E S)=roe d U (H.cost S) from by simp [M]]
  exact loomSale d U _ (H.pass S).nonn -- tune


lemma wig_light (H:Buttons N e R a c A)(m:ℕ):
    (wig d U H).light m=cope d U (H.light m):=by
  funext x
  let E:=loon N d
  rw [Shells.light,Shells.clipped]
  conv_rhs => rw [Shells.light,cope,Shells.clipped,map_sum]
  symm; refine Fintype.sum_equiv E _ _ fun S=>?_
  have s:(E S).card=S.card:=Finset.card_image_of_injective _ d.anon_b.1
  rw [s]; split
  · change _ = cope d U (H.mark (E.symm (E S))) x
    rw [Equiv.symm_apply_apply]; rfl
  rw [map_zero]

lemma wig_mark(H:Buttons N e R a c A)(S):
    (wig d U H).mark (sheet d S)= cope d U (H.mark S):=by
  let E:=loon N d
  show cope d U (H.mark (E.symm (E S)))= _
  rw [E.symm_apply_apply]


def lace (x:Coif N e):Coif N e:=⟨ice x.val,ice_o x.val _ x.property⟩
def pointe (A:Fob N e):Fob N e:=fun x=>star (A (lace x))

-- based on Drapes.Crown.impose
lemma ringlet {S:Seal (Seat N)}{M:Toll (Single N)}(q:Jubilee e S M A):
    Jubilee e S (fun i j=>M j i) (pointe A):=by
  let h: Continuous (@lace N e):=
     (Tulip.burnOut.comp continuous_subtype_val).subtype_mk _
  have u: Ticket (bail N e) (bail N e) S M (A ∘ lace):=by
    refine ⟨?_,?_⟩
    · intro i x
      unfold Function.comp
      rw [show lace ((forum N e).drive i x)=(forum N e).drive i (lace x) from Subtype.ext (icy_g ..)]
      exact q.frame ..
    intro i j
    have x:=q.expo i j
    refine ⟨x.positive,x.triggered,fun a=>x.bounded _,fun a b=> (x.variation (lace a) (lace b)).trans_eq ?_, x.connected.comp h⟩
    exact congrArg (fun d=> M i j*(d/|e|)) (ice_f ..)
  exact ⟨u.starT,
     fun i j=>realigns (q.fuel j i) lace fun _ e f h=>snowy e (fun z=>(f z).val) h⟩


def arabesque (H:Buttons N e R a c A):Buttons N e R a c (pointe A):=
  ⟨fun S=>pointe (H.mark S),fun S i j=>H.cost S j i,fun S=>ringlet (H.pass S),
    fun x=>by unfold pointe; rw [H.sum,star_sum],
    fun S i j=>H.good S j i,
    show (∑ i, ∑ j,saleM a H.cost j i)≤c from (sum_comm.trans_le H.paid)⟩

lemma arabesque_light (H:Buttons N e R a c A)(m:ℕ):
   (arabesque H).light m=pointe (H.light m):=by
  funext x
  rw [Shells.light,Shells.clipped,pointe,Shells.light,Shells.clipped,star_sum]
  refine sum_congr rfl fun S _=>?_
  by_cases t:S.card≤ m
  · rw [if_pos t,if_pos t]; rfl
  simp [t]

lemma wig_norm {M P:ℕ}{x:Seat N} (S:Seal (Seat N))
    (r:(faerie (Tenant.terr _) x M P ∘(loon N d).symm) S):
    faerie (Tenant.terr _) (d.anon N x) M P S:=by
   obtain ⟨u,rfl⟩:= (loon N d).surjective S
   simp only [Function.comp_apply,Equiv.symm_apply_apply] at r
   change faerie _ _ _ _ (sheet d u)
   intro y h
   obtain ⟨v,w,rfl⟩:=mem_image.mp h
   change separation (Lattice.affine _ _ _) (Lattice.affine _ _ _)≤ M+P*(sheet d u).card
   rw [Lattice.affine,Lattice.affine,separation_translate,separation_signed,sheet,Finset.card_image_of_injective _ d.anon_b.1]
   exact r v w

