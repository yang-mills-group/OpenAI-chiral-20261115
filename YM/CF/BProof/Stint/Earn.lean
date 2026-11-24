import YM.CF.Support.Hit

/-! ## Operator prices (B method)
Retain one common Stage on the support argument throughout products, series, and
parameter integrals. Use the FiniteGaugeData Branch.Support libraries (their power estimate uses
Range grouped into a bounded support price on micro balls, as in B-matrix). Constants
purchased here don't depend on Stage/matrix sizes. Use strongly covariant prices to
keep trace terms individually invariant for face cancellations. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Stint
open Function Filter Fock Finset Branch
open scoped Topology BigOperators Matrix MatrixOrder InnerProductSpace Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
structure Pay where
 rate : ℝ
 cash : ℝ
 charge : 0 < rate
 funding : 0 < cash
namespace Pay
def lodge (a b:Pay):Pay:=⟨min a.rate b.rate,max a.cash b.cash,lt_min a.charge b.charge,lt_max_of_lt_left a.funding⟩
def add (a b:Pay):Pay:=⟨min a.rate b.rate,a.cash+b.cash,lt_min a.charge b.charge,add_pos a.funding b.funding⟩
def mul (a b: Pay):Pay:=⟨min a.rate b.rate,2*(a.cash*b.cash),lt_min a.charge b.charge,mul_pos (by norm_num) (mul_pos a.funding b.funding)⟩
def wage (a : Pay)(v:ℝ):Pay:=⟨a.rate,max 1 (v*a.cash),a.charge,lt_max_of_lt_left zero_lt_one⟩
def simple : Pay:=⟨1,Real.exp 1,one_pos,Real.exp_pos _⟩
def wide (p q:Pay):Prop:=p.rate ≤ q.rate ∧ q.cash ≤ p.cash
theorem lodge_left (p q: Pay): (p.lodge q).wide p:=⟨min_le_left ..,le_max_left ..⟩
theorem lodge_right (p q: Pay): (p.lodge q).wide q:=⟨min_le_right ..,le_max_right ..⟩
theorem Wide {p q r:Pay}(h:p.wide q)(t:q.wide r): p.wide r:=⟨h.1.trans t.1,t.2.trans h.2⟩
end Pay

variable {I Y Z G:Type*}[Fintype Y][Fintype I][DecidableEq I][DecidableEq Y][TopologicalSpace Z] {b:Branch.Stage Y I Z G} {s t q: Branch.Tag b} {p r:Pay}{A B:Raw Z I}
def Earn (p:Pay)(s t:Branch.Tag b)(A:Raw Z I): Prop:=RootedK s t p.rate p.cash A
namespace Earn
lemma holds (h: Earn p s t A): RootedK s t p.rate p.cash A:=h
lemma change (h:Earn p s t A)(e:r.wide p): Earn r s t A:= (h.holds.drop e.1).books e.2
lemma plus (h:Earn p s t A)(k:Earn r s t B): Earn (p.add r) s t (fun x=>A x+B x):= (h.holds.drop (min_le_left ..)).plus (k.holds.drop (min_le_right ..))
lemma times (h:Earn p s t A)(k:Earn r t q B): Earn (p.mul r) s q (fun x=> A x * B x):=(h.holds.drop (min_le_left ..)).product (k.holds.drop (min_le_right ..)) (le_min p.charge.le r.charge.le)
lemma neg (h:Earn p s t A):Earn p s t (fun x=> -A x):= h.holds.minus
lemma minus (h: Earn p s t A)(k:Earn r s t B): Earn (p.add r) s t (fun x=>A x-B x):= by simp_rw [sub_eq_add_neg]; exact h.plus k.neg
lemma scalar (h:Earn p s t A){c:ℂ}{v:ℝ}(hv:‖c‖≤v):Earn (p.wage v) s t (fun x=> c • A x):=(h.holds.raise c).books ((mul_le_mul_of_nonneg_right hv p.funding.le).trans (le_max_right ..))
lemma wage (h:Earn p s t A){c v:ℝ}(hv:‖c‖≤v):Earn (p.wage v) s t (fun x=>c • A x):=by simpa only [Complex.coe_smul] using h.scalar (show ‖(c:ℂ)‖≤v by rwa [Complex.norm_real])
lemma adj (h:Earn p s t A):Earn p t s (fun x=>star (A x)):= h.holds.starUp
lemma ccUp (h:Earn p s t A):Earn p s.reverseV t.reverseV (fun x=>cc (A x)):= h.holds.ccUp
lemma one (s: Tag b):Earn .simple s s (fun _=>1):=RootedK.oneK ..
lemma free (p:Pay): Earn p s t (fun _=>0):=RootedK.free.books p.funding.le
lemma norm (h:Earn p s t A)(x): ‖A x‖≤p.cash:=h.holds.boundOp p.charge.le x
lemma cov (h:Earn p s t A): Inter s t A:= h.holds.tiesK
lemma cont (h:Earn p s t A): Continuous A:= by obtain ⟨F,C,e,t,W⟩:= h.holds; rw [show A= _ from funext W]; exact continuous_finsetSum _ (fun i _=>(e i).cont)
lemma restrict {D G':Type*}[TopologicalSpace D](h: Earn p s t A){k: Stage Y I D G'}{v w: Tag k}(ρ:D→Z)(hρ:Continuous ρ)(u:b.F=k.F)(g:b.home=k.home)(e:∀ S x y,b.eval S (ρ x) (ρ y)≤k.eval S x y)(hg:G'→G)(H:∀ a y, b.drive (hg a) (ρ y)=ρ (k.drive a y))(hv:s.run ∘ hg=v.run)(hw:t.run ∘ hg=w.run): Earn p v w (fun x=> A (ρ x)):= by
 obtain ⟨P,W,ht,w,Q⟩:=h.holds; refine ⟨fun S x=> P S (ρ x),W,fun S=>⟨?_,?_⟩,w,fun x=>Q _⟩
 swap
 · intro i j; let h: Expo b _ _ _ _ _:= (ht S).expo i j; refine ⟨h.positive,?_,fun x=>h.bounded _,fun x y=>(h.variation _ _).trans (mul_le_mul_of_nonneg_left (e _ _ _) h.positive),h.connected.comp hρ⟩; rw [←u,←g]; exact h.triggered
 intro a y; have hp:= (ht S).frame (hg a) (ρ y); rw [H,show s.run _= _ from congr_fun hv a,show t.run _= _ from congr_fun hw a] at hp; exact hp
end Earn
end YM.CF.BProof.Stint
