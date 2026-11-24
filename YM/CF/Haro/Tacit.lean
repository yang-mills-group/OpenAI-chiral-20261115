import YM.CF.Haro.Fig
import YM.CF.Facet.Gust
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Haro
open Function Filter Metric Fir Lattice Laurent Next.Free Bloch Finset Lat Stationary Rush Cube Scroll SU Drapes Fir Peaks Dial Paige Brace Vault Fock Tulip Font Spire Nacre Ember Pec
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix Matrix.Norms.L2Operator Kronecker MatrixOrder Classical
attribute [local instance] opCStarAlgebra
open Tap Hake Urn Yaw Levier Proa Rill
open Branch Laic
open Skye Precision
open Jet Scree
variable {n:Side}
def liveB (S:Finset (Hub n)):Prop:=∀ g:Sweep n,S.image (moveHub g)=S
lemma pure_s(s:Sweep n): Injective (moveHub s):=by
 intro i j h; apply Subtype.ext; have ht:=congrArg Subtype.val h; refine Prod.ext ((boxA s).symm.injective (congr_arg Prod.fst ht)) ?_; exact Finset.map_injective (boxA s).symm.toEmbedding (congrArg Prod.snd ht)
abbrev Cred (F:Hub n→InkD n)(S:Finset (Hub n)):Prop:=∀ k:Sweep n,∀ U,JetS k.s k.charge (detX k.s) U →∀ x∈S,F (moveHub k x) 1= paintR k.charge (detX k.s) (prepU (castX k) U (xtra k.charge) n) (F x 1)
variable (F:Hub n→InkD n)(S:Finset (Hub n))(s:liveB S)(g:Cred F S)
include s g
lemma jus : AxisB (StackL F S):=by
 intro Q b U v; let k:= ray (N:=n) b Q; let V:=siteU Q b U n; let T:= (StackL F S)
 let U':= prepU (castX k) U (xtra k.charge) n
 have h: (prepU Q U (xtra b) n).val= Rush.fee (periods n Q.t-periods n (castX k).t) • U'.val:= utu n b U Q.s _ _ (wrap_lift _).symm
 let t:= detX k.s; let A(x:Hub n):= orbitPH (F x 1); have hp(i:Hub n)(h:i∈S): A (moveHub k i)=Thera.jazz t (sings k.charge U' (A i)):=by unfold A; rw [g _ _ v _ h,paral]
 have hh:sings b V=sings k.charge U':=by funext x; rw [singT,singT,twist_formula,twist_formula,show V.val=_ from h]; simp only [star_smul,Matrix.smul_mul, Matrix.mul_smul,smul_smul,fee_real,fee_one,one_smul]; rfl
 have he:= s k; change sings b V _=_; rw [hh,singT,StackL,win_sum,map_sum]; simp_rw [← singT]; conv_rhs=> rw [←he, sum_image (pure_s k).injOn]
 rw [show detX Q.s=t from rfl]
 let L(x):= sings k.charge U' (A x); change ∑ i ∈ S,L i = Thera.jazz t (∑ i∈ S,A (moveHub k i)); rw [sum_congr rfl hp]
 unfold L A; cases t <;>simp only [Thera.jazz,ite_true,ite_false,Bool.false_eq_true,star_sum,sum_neg_distrib,star_neg,star_star,neg_neg] -- tune
omit s g
variable {T Y:RG.BudgetPoint}{m:ℕ}
lemma Kred{h v:ℝ}(p:Scree.IncX (fun _=>True) F T h v): Cred F S:=by intro k U g x l; have ht:=p.face k trivial _ g x 1; rwa [Facet.glacial] at ht
include s g
lemma silver (P: Hub n→ℝ)(h v:ℝ)(p: ∀ x∈ S,PressB T x (F x) h (P x))(hp:0<h)(he:∑ i∈ S,P i≤ Fintype.card (Site n)*v):
 let A:=StackL F S; let W:=loft A; AxisP (heroP A) ∧ A=love n (Rush.cart n W) ∧ RailP T.power W ((4:ℝ)^T.power*((2:ℝ)^T.power*v/h^2)) ∧∀ i: Single n,rakeV A T.power i≤ (2:ℝ)^T.power*v/h^2:=by
 intro A W; have hx := jus F S s g
 have hl:= shadeH F S P p he hp; rw [show (2:ℝ)^T.power*(Fintype.card (Site n)*v)/h^2=Fintype.card (Site n)*((2:ℝ)^T.power*v/h^2) from (by ring)] at hl; let Z:=daff A hx _ hl; exact ⟨issue_p _ hx (mono_l F S P p), (gift _ hx).symm,tideP A _ _ Z,Z⟩
end YM.CF.Haro
