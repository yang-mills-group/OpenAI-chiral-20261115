import Bay.Arbor
import YM.CF.Ione.Rake
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 800000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Bay.C
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open Skye Scree Cadre Palot
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open Cube Lat Tulip Fock Rush Scroll Paige Vault Phase Acorn Spire
open Pastry Vow Rue
attribute [local instance] opCStarAlgebra
open Hake Jet Sault Stax Sour
attribute [local instance] Sour.loreM Sour.loreN
open Rill Branch Tenant Drapes Leaf



open Levier Urn Ione
open Peaks


/- row-monomial matrices. -/
section
variable {n : Type*} [Fintype n] [DecidableEq n]
def Rook (A:Op n):Prop:=∀ i j k,A i j ≠ 0 → A i k ≠ 0 → j=k
lemma one_rook : Rook (1:Op n):=by
 intro i j k u v; by_contra p
 have a:i=j:= by by_contra d; exact u (by simp [d])
 exact v (by simp [a,p])
lemma Rook.mult {A B:Op n}(a:Rook A)(b:Rook B): Rook (A*B):=by
 intro i j k u v
 simp only [Matrix.mul_apply] at u v
 have f : ∀ l, (∑ t,A i t * B t l)≠0 → ∃ t,A i t≠0 ∧ B t l≠0:=by
    intro l p; by_contra! d; exact p (Finset.sum_eq_zero fun i _=> (mul_eq_zero.mpr ((em (A _ i=0)).imp_right (d i))))
 obtain ⟨x,e,g⟩:=f j u; obtain ⟨y,h,r⟩:=f k v; cases a i x y e h; exact b x j k g r
lemma Rook.scal {A:Op n}(a:Rook A)(z:ℂ):Rook (z • A):=by
 intro i j k u v
 exact a i _ _ (fun h=>u (show z * A i j=0 by rw [h,mul_zero])) (fun h=>v (show z * A i k=0 by rw [h,mul_zero]))
lemma Rook.whi {U: UNI n}(a:Rook U.val):Rook (ccU U).val:=by
 intro i j k u v
 exact a i _ _ (fun h=>u (show star (U.val i j)=0 by rw [h,star_zero]))
    (fun h=>v (show star (U.val i k)=0 by rw [h,star_zero]))

lemma Rook.walk {U: UNI n}(a:Rook U.val) : ∃ f:Equiv.Perm n,
   ∀ i j, j≠f i → U.val j i=0:=by
 have m(i:n):∃ t,U.val t i≠0:=by
   have h: (star U.val*U.val) i i=1:=by rw [U.property.1]; simp
   by_contra! d; simp [Matrix.mul_apply,d] at h
 choose f p using m
 have I:Injective f:=by
   intro i j e; exact a (f i) i j (p i) (e.symm ▸ p j) -- subst at f i?
 have S:=Finite.surjective_of_injective I
 refine ⟨Equiv.ofBijective f ⟨I,S⟩,?_⟩
 intro i j d
 obtain ⟨k,rfl⟩:=S j
 by_contra v; exact d (congrArg f (a _ _ _ (p k) v))

lemma one_fase {U: UNI n}{i j:n}(z:∀ t,t≠i → U.val t j=0): ‖U.val i j‖=1:=by
 have e:(star U.val*U.val) j j=1:=by rw [U.property.1]; simp
 rw [Matrix.mul_apply,Finset.sum_eq_single i (fun t _ d=>by rw [z t d,mul_zero]) (by simp)] at e
 change star (U.val i j) * U.val i j = 1 at e -- specify
 have := congrArg norm e
 rw [norm_mul,norm_star,norm_one] at this
 nlinarith [norm_nonneg (U.val i j)]
lemma crowd {m:Type*}[Fintype m][DecidableEq m] (f:Equiv.Perm m)(v:m→Op n)
 (h:∀ i,Rook (v i)):Rook (jump f v):=by
  intro i j k u p; rw [jump_apply] at u p
  rw [Ne] at u p
  split_ifs at u with g; swap; · contradiction
  split_ifs at p with r; swap; · contradiction
  exact Prod.ext (g.symm.trans r) (h _ _ _ _ u p)


end

variable {n : Type*} [LinearOrder n] [Fintype n]
lemma throne {U:UNI n}{f:Equiv.Perm n}(g:∀ i j,j≠f i→ U.val j i=0)
 (i:Finset n) (j:Finset n) (e:j≠i.map f.toEmbedding) :
   (quantU U).val j i=0:=by
 have a(x:n):acts U.val (basisKet x)= U.val (f x) x • basisKet (f x):=by
   apply PiLp.ext; intro t; rw [basis_act,PiLp.smul_apply]
   by_cases k:t=f x
   · rw [k];simp
   rw [g _ _ k]; simp [k]
 have p(X:Finset n):∃ z:ℂ,wedge U.val X=z • basisKet (X.map f.toEmbedding):=by
   induction X using Finset.induction_on with
   | empty=>exact ⟨1,by simpa using wedge_empty U.val⟩
   | @insert i S k h=>
      obtain ⟨z,h⟩:=h
      let V:=S.map f.toEmbedding
      have t:f i∉V:=fun v=> k ((mem_map' _).mp v)
      rw [wedge_any _ _ _ k,h,a,map_smul,map_smul,create_put,act_smul,put_act,if_neg t,map_insert]
      simp only [smul_smul]
      exact ⟨_,rfl⟩
 change (wedge U.val i).ofLp j=0
 obtain ⟨z,h⟩:=p i; rw [h];simp [e]

lemma Rook.spiced {U:UNI n}(h:Rook U.val) (b:Bool):Rook (spice U b).val:=by
 have k (v:UNI n)(g:Rook v.val)(i:Bool):Rook (thread v i).val:=by cases i;exact g.whi;exact g
 cases b; exact crowd _ _ (k U h)
 exact crowd _ _ (k _ ((one_rook.scal Complex.I).mult h))
lemma Rook.inBody (a:Shape)(N:Side)(V:UNI SpinIdx)(q:Rook V.val)(b:Bool): Rook (siteU a b V N).val:=by
 have y:Rook (spinQ V (xtra b)).val:=by
    intro i j k h t
    change V.val _ _ * (1:Op SU.Slot) _ _ ≠0 at h t
    -- specify
    have ss:=mt mul_eq_zero.mpr h;have uu:=mt mul_eq_zero.mpr t
    push Not at ss uu
    refine Prod.ext (q _ _ _ ss.1 uu.1) ?_
    exact one_rook _ _ _ ss.2 uu.2
 have z:Rook (mealU a V (xtra b) N).val:= crowd _ _ (fun i=>y.scal _)
 intro i j k
 exact fun h t=> (helix N).injective (z _ _ _ h t)

set_option maxHeartbeats 1800000 in
lemma esp(i:Axis): Rook (gammaOp i):=by
 intro a b c
 fin_cases i <;> fin_cases a <;> fin_cases b <;> fin_cases c <;> simp [gammaOp]
lemma planetJ:Rook spinJ:=by
 intro a b c;fin_cases a <;> fin_cases b <;> fin_cases c <;> simp [spinJ]

def Glam (p:Bool)(s:Signed):Prop:= Rook (spinU p s).val
abbrev Velvet {N:Side}(s:Sweep N):=Glam s.charge s.s
lemma shine (s:Signed) (p:Bool)(U:UNI SpinIdx)(v:JetS s p (detX s) U)(h:Rook U.val):Glam p s:=by
 obtain ⟨z,b,_⟩:= kitsX p s _ _ (spinZ p s) v
 unfold Glam;rw [b];exact h.scal z
lemma Glam.flat (p:Bool):Glam p 1:=by
 cases p
 · exact shine 1 false 1 (by rw [det_i]; exact calmSX) (show Rook (1: UNI SpinIdx).val from one_rook)
 exact shine 1 true ⟨spinJ,spinJ_unitary⟩ (by rw [det_i]; exact cloneSX) planetJ
lemma Glam.axis (i:Axis):Glam false (Signed.mirror i):=by
 refine shine _ _ ⟨Mir.pin i,Mir.pin_U i⟩ (by rw [det_t]; exact mirrorX i) ?_
 have k:Rook grading:=by
    rw [grading_rule];exact (((esp _).mult (esp _)).mult (esp _)).mult (esp _)
 exact (esp i).mult k
lemma Glam.product {p q:Bool}{s t:Signed}(a:Glam p s)(b:Glam q t): Glam (p.xor q) (s*t):=by
 refine shine _ _ _ (shineU p ⟨s,0⟩ q _ _ t (spinZ p s) (spinZ q t)) ?_
 exact Rook.mult b (show Rook (whiten q (spinU p s)).val from by cases q; exact a;exact Rook.whi a)
-- Precise spin price on velvet Sweeps.
abbrev socks {N:Side}(s:Sweep N):=siteU (castX s) s.charge (spinU s.charge s.s) N
lemma rook_socks {N:Side}(s:Sweep N)(x:Velvet s): Rook (socks s).val:=Rook.inBody _ _ _ x _
