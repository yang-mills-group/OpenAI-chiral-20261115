import YM.SU5.FiniteGaugeData.Pannier.Filigree
import YM.CF.Matter.Mass
/-!
# Distinguishing the mixed readings

Restriction to the elected FiniteGaugeData hierarchy. Not using a Hilbert axiom about low energy. `Factorizes`
is a vacuum interpretation test in this *specific* sense only: the linear Euclidean functional
(on the joint algebra, extending to the supported even gauge-covariant/charged slices) does not
read as the product of its gauge and chiral-matter marginals even at this **one** level. Its marginal on
pure matter tomes here is not the value of a gauge-fixed Grassmann integral. `Factorizes` is meant for testing
a claim about the course/single E with the *given* gauge symmetry, observable assignments and laws.
Tests only the tomography clauses relevant to the claimed nonzero observable (inserted once), doesn't
require factorization all scales. Doesn't rule out factorization on different/additional variables, doesn't
assert Haag-algebra nonfactorization or Lorentz/separation properties of subinsertions inside this observable,
nor prove continuum S-matrix interaction.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 16000
noncomputable section
namespace YM.CF.Pannier.Chancel
open Function Filter NormedSpace Metric Lattice Wilson Laurent Finset Cube SU Fock Lat Spire Scroll MeasureTheory ProbabilityTheory Peaks Drapes Rush Tulip Dial Pastry
open Buffered Branch Tenant Skye Cliplet RG Brace
open Window (mem_Tset family)
open Py.Rate.Pannier
open Lifted
open Reed (Fine)
open Afterglow Afterglow.Tapestry
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] opCStarAlgebra
variable {K:Calibration}{k:ℕ}{b:Fin k→ Cover}{S:Finset Cover}{s:SU.Slot}{W:Window.Family}{L:List (Fin k)} {x y:Buffered.Family K}
private lemma quan(W:Window.Family) (a:SU.Slot)(p:family a=W): SU.charge a=if W.2 then 2 else 4:=by subst W; rcases a with ⟨v,b|b⟩<;> rfl
private def phaseZ (W: Window.Family):= SU.z^(if W.2 then 2 else 4:ℕ)
private lemma anti_self(W:Window.Family):phaseZ W≠1:=fun h=> by
 obtain p:= SU.z_prim.dvd_of_pow_eq_one _ h; split at p<;> omega -- tune
private lemma carat (W:Window.Family): ‖phaseZ W‖=1:=by unfold phaseZ; rw [norm_pow,SU.z_n]; simp
private lemma node_f {x y:Cover}(p:x ≠ y): nodeC x≠nodeC y:=fun e=>p (nsmul_right_injective two_ne_zero (add_right_cancel e))

variable (W K S b)
private def encomium (o:Cover)(x:Cover): SU.E:= if x=nodeC o then SU.central else 1
private def wraith (j:Fin k)(L:List (Fin k)):ℂ:= if j∈L then phaseZ W else 1
private lemma star_atom (y o:Cover)(i:SpinIdx)(b:SU.Slot) (e:family b=W)(z:nodeC y∈ S){n:Side}(g:Seat n→SU.E)(h:TraceGauge S (encomium o) g) : acts (tradew n g).val (basisC n y i b)= (if y=o then phaseZ W else 1) • basisC n y i b:=by
 rw [turn_basisC,h _ z]; unfold encomium; by_cases p:y=o
 · subst y; rw [if_pos rfl,SU.by_charge,if_pos rfl]; rw [sum_eq_single b]
   · rw [Matrix.diagonal_apply_eq,phaseZ,quan W b e]
   · intro a u t; rw [Matrix.diagonal_apply_ne _ t, zero_smul]
   simp
 simp [if_neg p,if_neg (node_f p),map_one,OneMemClass.coe_one,Matrix.one_apply]
variable {W S b}
lemma homageC (p:Injective b)(h:CRow K W b S L x)(a:Fin k)(d:L.Nodup) : Circular S (encomium (b a)) x (wraith W a L • x):=by
 induction h with
 | gave=> intro m u t v; simp only [wraith,List.not_mem_nil,↓reduceIte,one_smul]; exact Eq.symm (map_one _)
 | zip=> rw [smul_zero]; exact fun i v t q=> (map_zero _).symm
 | glaze z h ih=> rw [smul_comm]; exact (ih d).scale _ S z
 | fuse _ _ r R=> rw [smul_add]; exact (r d).add _ S (R d)
 | pair i j v f A B w x η u e t g l r=>
    rename_i Jν K₀ -- J Family, K list
    have hp:=(r (List.nodup_cons.mp d).2); intro m G h X; let T:=(twist (quantU (tradew _ G))); let q(i': Cover):= if i'=b a then phaseZ W else (1:ℂ)
    let P:= Fock.remove (basisC (K.c m) (b i) v B); let D:=create (basisC (K.c m) j f A);
    have hl: T P= star (q (b i)) • P:=by change twist _ (remove _) = _; rw [twist_remove,star_atom S W (b i) (b a) v B w t G h]; unfold remove; rw [map_smul,star_smul]
    have hD:T D=D:=by change twist _ (create _) = _; rw [twist_create,star_atom S W j (b a) f A x e G h,if_neg (g a),one_smul] -- `star_atom` binder
    change P*D* Jν m (simultaneous G X)= T (wraith W a (i::K₀) • (P*D*Jν m X)); rw [hp m G h X] -- scalar first
    change P*D*T (wraith W a K₀ • _)= T (wraith W a (i::K₀) • _); unfold T; rw [twist_scalar,twist_scalar,map_mul,map_mul]; change P*D*(_ • _)=wraith W a (i::K₀) • (T P*T D*_); rw [hl,hD,Algebra.smul_mul_assoc,Algebra.smul_mul_assoc,smul_smul, Algebra.mul_smul_comm];
    by_cases V:i=a; · subst i; have ht:a∉ K₀:= (List.nodup_cons.mp d).1; rw [wraith,if_neg ht,wraith,if_pos List.mem_cons_self,show q (b a)=phaseZ W from if_pos rfl,mul_comm (phaseZ W),scale_unit_self (carat _)]
    have hs:a∈ i::K₀ ↔ a∈ K₀:=by simp [Ne.symm V]
    rw [show q (b i)=(1:ℂ) from if_neg fun w=> V (p w),star_one,mul_one]; congr 1; unfold wraith; simp only [hs]

-- At this level and fixed caller support, restricted linear + gauge laws.
structure Scopes (K:Calibration)(S:Finset Cover)(E:Buffered.Family K→ℂ):Prop where
 unit : E 1 = 1
 plus_v (f g:Buffered.Family K)(p:InTest K true S false f)(q:InTest K true S false g): E (f+g)= E f+ E g
 scale (f:Buffered.Family K)(p: InTest K true S false f)(z:ℂ) : E (z • f)= z • E f
 gauge (T: Cover→SU.E)(f F:Buffered.Family K)(p:InTest K true S false f)(u:InTest K true S false F)(t:Circular S T f F): E f=E F
/-- If even chiral and gauge factors are read independently at this resolution,
in particular at all such fixed caller support probes, *in the gauge-covariant extension
charge symmetry*, then `Parcel` is an obligation. Not allowing comparisons where the state
is given only on gauge invariant and no pure charged reads licensed. This is a test
for a visible coupling footprint on the Euclidean data, may also detect correlations
from coherent gauge blocking operations. -/
def Parcel (W:Window.Family)(b:Fin k→ Cover)(S:Finset Cover)(E:Buffered.Family K→ℂ) := ∀ v:Buffered.Family K, v∈ Lode K W b S → ∀ f, Coeff false S f → E (scalar K f*v)= E (scalar K f)*E v
-- `K` explicit binder via command? check
namespace Scopes
variable {K} {E:Buffered.Family K→ℂ}(h: Scopes K S E)
include h
lemma nil_v :E 0=0:=by simpa using h.scale _ (.one) 0
lemma singletonLetter (p:Injective b)(g:CRow K W b S L x)(e:L ≠ [])(t:L.Nodup): E x=0:=by
 cases L with
 | nil=> contradiction
 | cons i l=>
    let z:= wraith W i (i::l); have pK:=homageC K p g i t; have ht:= h.gauge _ x (z • x) g.inTest.widen (.smul z g.inTest.widen) pK; rw [h.scale _ g.inTest.widen] at ht; have hv:z= phaseZ W:= if_pos List.mem_cons_self
    by_contra g; apply anti_self W; rw [←hv]; apply mul_right_cancel₀ g; rw [one_mul]; exact ht.symm
lemma footprint (p:Injective b)(w:x∈ Lode K W b S): E x=0:=by
 refine Submodule.span_induction (p:=fun x _=> E x=0) (fun x w=>?_) h.nil_v ?_ ?_ w
 · obtain ⟨l,g,t,u⟩:= w; exact h.singletonLetter p u g t
 · intro x y v w a b'; rw [h.plus_v x y (Lode_test (W:=W) (b:=b) (by exact v)|>.widen) (Lode_test (W:=W) (b:=b) (by exact w)|>.widen),a,b',add_zero] -- implicit b unresolved
 intro x y v t; rw [h.scale y (Lode_test (W:=W) (b:=b) (by exact v)|>.widen), t,smul_zero]
lemma detects (p:Injective b)(u: Parcel K W b S E)(w:x∈ Filigree K W b S): E x=0:=by
 refine Submodule.span_induction (p:=fun x _=> E x=0) (fun x w=>?_) h.nil_v ?_ ?_ w
 · obtain ⟨y,z,m,v,rfl⟩:= w; rw [u y m z v,h.footprint p m,mul_zero]
 · intro x y v w a b'; rw [h.plus_v x y (FilTest (W:=W) (b:=b) (by exact v)|>.widen) (FilTest (W:=W) (b:=b) (by exact w)|>.widen),a,b',add_zero]
 intro x y v t; rw [h.scale y (FilTest (W:=W) (b:=b) (by exact v)|>.widen), t,smul_zero]
end Scopes
end YM.CF.Pannier.Chancel
#print axioms YM.CF.Pannier.Chancel.Scopes.detects
