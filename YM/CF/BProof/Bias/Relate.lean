import YM.CF.BProof.Bias.Reel
import YM.CF.BProof.Tape.Vase
/-! expose local-bias price on comparison cone Loft. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Bias
open Function Filter Fock Finset Branch Tenant Cube SU Tulip Lat Lattice Dial Spin Fig Align Stint Wick Hearth
open Fir Laurent Rush Bloch Next.Free BZ Real Tape
open scoped Topology BigOperators Matrix MatrixOrder InnerProductSpace Kronecker Matrix.Norms.L2Operator Hearth
attribute [local instance] opCStarAlgebra
variable {a b l r δ c v η g:ℝ}{j:ℕ}{N:Side}{P: Spin.Ready j a b l r}{F:Core j a b l r N} (H:Honor P F δ)
variable (x:Loft F δ c v η)
def LastC := Tape.roam x.val.2.val (false,false) 1
def BillLeg := offCut (piF x.val.1) (pair (LastC x))
structure Ivory (x:Loft F δ c v η)(R:Finset (Per N)):Prop where
  pure : Tape.carried x.val.1=1
  gap : x.val.1.val.2=rowsX Rᶜ
variable {R J U X:Finset (Per N)}(hx:Ivory x R)
include H hx
lemma realPI : piF x.val.1=Polar j F.M R:=by rw [piF,Tape.cutX, Tape.cutX,hx.pure,hx.gap,F.θtriv P H.1.minN]; rfl -- tune
lemma pureB : Free c j F.M R:=by
 have ht: Board (F.θ (carried x.val.1) 1) (cutX true x.val.1) (cutX false x.val.1) c:= x.val.1.property; rw [hx.pure,cutX,cutX,hx.gap,F.θtriv P H.1.minN] at ht; exact ht
lemma tailB (k:ℕ): Near ht k (tailPay P.hP k) (redP j F.M N):=by
 let b:=iron N P.hT δ; let v(U:Counter (More N) δ):=spar j F.M U.val; exact temporal_near b ⟨1,guard0 H.1.pos⟩ (A:=v) (P.mat N H.1.minN F.M δ H.1.shelter) k
lemma pureC : BillLeg x= Plus j F.M R (LastC x):=by rw [BillLeg,realPI H x hx]
-- budget
omit hx H -- syntax
lemma receipt (P: Spin.Ready j a b l r)(e:1≤v)(u:0<c)(δ:ℝ): ∃ p:Stint.Pay,∀ {N:Side}{F:Core j a b l r N}(H:Honor P F δ)(η:ℝ), let b:=Tape.kiln H.1 c v η; Earn p b.mark b.mark.reverseV BillLeg:=by
 obtain ⟨a,F⟩:= purchaseV e P δ c; obtain ⟨i,s,S⟩:= Wick.cash Spin.quota_p.le u a a a a; refine ⟨(s.mul a).mul (Stint.Pay.simple.add s),?_⟩; intro N D H η b; obtain ⟨hA,hT,hQ,hL,L⟩:= F H.1; have hz:= (S (H.1.beam c).cap hL (hQ true) (hQ false) hT (fun (i:InRoad D δ c)=>H.2 i.val.1) (fun i=>i.property)).2; have ht:= gate H.1 (A:=piF) hz v η; have he:Earn a b.mark b.mark.reverseV (fun x=> pair (LastC x)):=est (L η (false,false)) (⟨1,walk1⟩:Time); exact (ht.times he).times ((Earn.one b.mark.reverseV).minus ht.ccUp)
lemma last_sk : (pair (LastC x))ᵀ= -pair (LastC x):=(show Ride .. from x.property).pores 1 walk1|>.sym
variable {A B:Stamp}
lemma dots_pay{I:Type}[Fintype I][DecidableEq I][Nonempty I](Z:Op I)(x:I): (Z*star Z) x x= (‖acts (star Z) (basisKet x)‖^2 :ℂ) := by
    let v:=basisKet x; rw [← basis_act (Z*star Z),← basis_inner,act_mul]; rw [←act_inner]; exact inner_self_eq_norm_sq_to_K .. -- tune
lemma lackFace(i:Single N)(h:0≤g)(t:g≤ ‖acts (star (BillLeg x)) (basisKet i)‖) : Tape.bias x (badgeOf i) ≤ -(1/4) * g^2 := by
 let A:= Tape.offProfit x; let S:=BillLeg x; let T:= (iron N 0 0).st; apply le_trans (Tape.levy x (badgeOf i)).1; push_cast; apply mul_le_mul_of_nonpos_left _ (by norm_num); rw [peak_eq,Complex.re_sum]; apply le_trans ?_ (single_le_sum (f:=fun i=>(A i i).re) (fun j _ => diagonal_le _ _ (show 0 ≤ A from width_pos ..) j) (show i∈ board T {badgeOf i} from (by apply mem_filter.mpr; exact ⟨mem_univ _,mem_singleton_self _⟩))); change _≤((S*star S) i i).re; rw [dots_pay, ←Complex.ofReal_pow,Complex.ofReal_re]; exact pow_le_pow_left₀ h t _
lemma pure_vac (h:1≤j)(t:Call R J A A (LastC x))(s:Honor P F δ)(hx:Ivory x R):offCut (piF x.val.1) (pair (LastC x))=0:=by
 let B:=pureB s x hx; let C:=pair (LastC x); have ht:= opening t F.M h B; rw [sub_self,drum, pair_const, Matrix.kronecker_zero,mul_zero] at ht; rw [realPI s x hx]; exact shield (sub_eq_zero.mp ht) (show Board .. from B).PiHp -- tune use no Unit
end YM.CF.BProof.Bias
