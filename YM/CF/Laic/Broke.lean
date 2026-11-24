import YM.CF.Kennel.Lan
import YM.Planned.STATIONARY_JET_PORT.Compose
import YM.Push.STATIONARY_UNIFORM.Continue
set_option autoImplicit false
noncomputable section
namespace YM.CF.Laic
open Function Filter Metric Lattice Wilson Laurent Precision Tree Finset Exterior Extra Bloch Lat Rush Cube Scroll SU Peaks Dial Fock Thera Nacre Branch Drapes Tulip Paige Spire Vault Font Kennel Planned.JetPort Push.Uniform
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
section Wire
variable {n:Side}{ι κ τ :Type}[Fintype ι]{k:ℕ}{l:ι→Site n}{β:τ→Site n}{u:κ→Site n}{F:Positions ι→ Matrix τ κ ℂ}{x:Positions ι}{a b c d:ℝ}
def matte (r:Bool):ℂ→L[ℝ]ℝ:= if r then Complex.reCLM else Complex.imCLM
def coinZ(r:Bool)(P:Matrix τ κ ℂ):=P.map (matte r)
def CableM (l:ι→Site n)(β:τ→Site n)(u:κ→Site n)(a:ℝ)(k:ℕ)(F:Positions ι→Matrix τ κ ℂ)(x:Positions ι)(c:ℝ):Prop:=∀ r:Bool,Cable l β u none a k (coinZ r ∘ F) x c
abbrev smooth(F:Positions ι→ Matrix τ κ ℂ)(x:Positions ι):Prop:=∀ i j,ContDiffAt ℝ ω (fun y=> F y i j) x
namespace CableM
lemma books(h: CableM l β u a k F x c)(p:c ≤ d): CableM l β u a k F x d:= fun r=>(h r).cost p
lemma mild(h:CableM l β u a k F x c)(p:b ≤ a)(g:0≤c): CableM l β u b k F x c :=fun r=>(h r).rate g p
end CableM
lemma inkJet(r:Bool)(h:smooth F x): bornMatrix (coinZ r ∘ F) x:=fun i j=>(matte r).contDiff.contDiffAt.comp x (h i j)
lemma chip {F B:Positions ι→ Matrix τ κ ℝ}(p:bornMatrix F x)(q: bornMatrix B x)(r:Cable l β u none a k F x c)(e:Cable l β u none a k B x d):Cable l β u none a k (fun x=>F x+B x) x (c+d):=by
 intro i j; simp only [Matrix.add_apply,thread_none,mul_one, add_mul]; simpa only [thread_none,mul_one] using Beacon.add (p i j) (q i j) (r i j) (e i j)
lemma minusCR {F:Positions ι→Matrix τ κ ℝ}(p:bornMatrix F x): bornMatrix (fun x=>-(F x)) x:= fun i j=>(p i j).neg
lemma inkP {G:Positions ι→ Matrix τ κ ℂ}(p:smooth F x)(g:smooth G x)(h: CableM l β u a k F x c)(v:CableM l β u a k G x d): CableM l β u a k (fun x=>F x+G x) x (c+d):=by
 intro r; rw [show coinZ r ∘ (fun x=>F x+G x) = _ from ?_]; apply chip (inkJet r p) (inkJet r g) (h r) (v r); funext x; apply Matrix.ext; intro i j; exact map_add (matte r) (F x i j) (G x i j)
lemma inkN(p:smooth F x)(h:CableM l β u a k F x c): CableM l β u a k (fun x=>-(F x)) x c:=by
 intro r; rw [show coinZ r ∘ (fun x=>-(F x))= (fun x=> -(coinZ r (F x))) from ?_]; exact (h r).neg (inkJet r p); funext x; apply Matrix.ext; intro i j; exact map_neg (matte r) (F x i j)
set_option maxHeartbeats 700000 in
lemma wire_mul [Fintype κ]{γ:Type}{V:γ→ Site n}{B:Positions ι→ Matrix κ γ ℂ}(p:smooth F x)(g:smooth B x)(h:CableM l β u a k F x c)(e:CableM l u V a k B x d)(s:0<a)(hc:0<c)(hd:0<d){Y:ℕ}(hv:Multiplicity u Y): CableM l β V (slip k a) k (fun x=> F x*B x) x (c*d*conductor k Y a +c*d*conductor k Y a):=by
 let U(t i x):=coinZ t (F x)*coinZ i (B x)
 have he t i : Cable l β V none (slip k a) k (U t i) x (c*d*conductor k Y a):= Cable.multiply (inkJet t p) (inkJet i g) (h t) (e i) s hc hd hv
 have ht t i: bornMatrix (U t i) x:= (inkJet t p).multiply (inkJet i g)
 intro r; cases r with
 | false=>
   rw [show (coinZ false ∘ fun x=> F x*B x)=(fun x=> U true false x + U false true x) from ?_]; exact chip (ht true false) (ht false true) (he true false) (he false true); funext x; apply Matrix.ext; intro i j; simp only [Function.comp_apply,coinZ,Matrix.map_apply]; change ((F x*B x) i j).im = _ -- syntax
   rw [Matrix.mul_apply,Complex.im_sum]; simp only [Complex.mul_im,sum_add_distrib]; change _=U true false x i j + U false true x i j; simp only [U, Matrix.mul_apply,coinZ,Matrix.map_apply]; simp [matte] -- tune -- check order
 | true=> rw [show (coinZ true ∘ fun x=>F x*B x)=(fun x=>U true true x+ -(U false false x)) from ?_]; exact chip (ht true true) (minusCR (ht false false)) (he true true) ((he false false).neg (ht false false)); funext x; apply Matrix.ext; intro i j; change (((F x)*(B x)) i j).re= _; rw [Matrix.mul_apply,Complex.re_sum]; simp only [Complex.mul_re,sum_sub_distrib]; change _ = U true true x i j + -(U false false x i j); simp only [U,Matrix.mul_apply,coinZ,Matrix.map_apply]; simp [matte,sub_eq_add_neg]
lemma pendant(h:smooth F x)(p:CableM l β u a k F x c)(i j): Beacon l a k (fun y=> F y i j) (β i) x ((2*c)* Push.Uniform.Decay a (β i) (u j)):=by
 have he(r:Bool)(g:ℕ)(q:Fin g→ι): matte r (Push.Uniform.entry (fun y=> F y i j) x q)=Push.Uniform.entry (fun y=>coinZ r (F y) i j) x q:=by
    unfold Push.Uniform.entry; rw [show (fun y=> coinZ r (F y) i j)= matte r ∘ (fun y=>F y i j) from rfl,(matte r).iteratedFDeriv_comp_left (h i j) le_top]; rfl
 intro g hg q; let f:=Push.Uniform.entry (fun y=> F y i j) x q; apply (show ‖f‖≤‖matte true f‖+‖matte false f‖ from Complex.norm_le_abs_re_add_abs_im _).trans; unfold f; rw [he,he]; apply (add_le_add (p true i j g hg q) (p false i j g hg q)).trans_eq; rw [thread_none]; ring
lemma ledger (f:smooth F x)(h:∀ i j,Beacon l a k (fun y=>F y i j) (β i) x (c*Push.Uniform.Decay a (β i) (u j))):CableM l β u a k F x c:=by
 intro r i j g p q; rw [thread_none,mul_one]; change ‖Push.Uniform.entry ((matte r) ∘ (fun y=>F y i j)) x q‖≤ _
 unfold Push.Uniform.entry; rw [(matte r).iteratedFDeriv_comp_left (f i j) le_top]; let Z:= Push.Uniform.entry (fun y=>F y i j) x q; refine le_trans (b:=‖Z‖) ?_ (h i j _ p _); change ‖matte r Z‖≤_; cases r; exact Complex.abs_im_le_norm _; exact Complex.abs_re_le_norm _
end Wire
end YM.CF.Laic
