import YM.CF.Scion.Yoke
set_option linter.unusedSimpArgs false
set_option autoImplicit false
set_option synthInstance.maxSize 20000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Scion
open Function Filter Metric NormedSpace Finset Fock Lattice Wilson Laurent Lat Rush SU Drapes Fir Peaks Dial Paige Brace Vault Tulip Tenant Phase Broc Scroll Thera Branch Laic Cube Relation
open scoped Matrix.Norms.L2Operator Matrix Topology ContDiff MatrixOrder BigOperators InnerProductSpace Kronecker
attribute [local instance] opCStarAlgebra
open Scree Pastry Stilo Urn Palot Hake
variable {ι A n M: Type*}[LinearOrder n][Fintype n][LinearOrder M][Fintype M]

local notation "bay"=>Stilo.bay
lemma crossTerm {T S:Set (Twig n)}(W:Weave n M)(P Q:List (LeanV n))(U V:List (Oboe n))(p:Even Q.length)(g:Fit T (cue P U))(h:Fit S (cue Q V))(t:∀ i∈T,∀ j∈ S,W.pals i j=0∧W.pals j i=0): issue W (rollC put P*rollC put Q) (rollC bell U*rollC bell V)=issue W (rollC put P) (rollC bell U)*issue W (rollC put Q) (rollC bell V):=by
 rw [←Hake.lump,←Hake.lump]; simp_rw [ring_u,cue]; rw [List.map_append,List.map_append,←List.append_assoc]; apply cross_v W.seats W.pals; simpa; intro i p' j q'; exact And.symm (t j (g j (List.mem_append_right _ q')) i (h i (List.mem_append_left _ p'))); exact fun i u j v=> (t i (g i u) j (h j v)).1
variable {T S:Set (Twig n)} (W:Weave n M)(t:∀ i∈T,∀ j∈ S,W.pals i j=0∧W.pals j i=0)
variable {X Y: FC (LeanV n)}{U V: FC n}
include t
lemma crossY (a: Pitch put (lipV T) 0 X)(b:Pitch put (lipV S) 0 Y)(c:Pitch bell (lipF T) 0 U)(d:Pitch bell (lipF S) 0 V): issue W (X*Y) (U*V)=issue W X U * issue W Y V:=by
 induction a with
 | null=> simp
 | add _ _ h g=> simp [h,g,mul_add,add_mul]
 | stam z _ pX=> simp [pX]
 | term p r x=>
  induction b with
  | null=> simp
  | add _ _ h g=> simp [h,g,mul_add,add_mul]
  | stam z _ pX=> simp [pX]
  | term q k v=>
   induction c with
   | null=> simp
   | add _ _ h g=> simp [h,g,mul_add,add_mul]
   | stam z _ pX=> simp [pX]
   | term i κ w=>
    induction d with
    | null=> simp
    | add _ _ h g=> simp [h,g,mul_add,add_mul]
    | stam z _ pX=> simp [pX]
    | term j l y=>
     exact crossTerm W _ _ _ _ (Nat.even_iff.mpr k) (cueFit x w) (cueFit v y) t

-- incidence calculus. view objects honest fibre polynomials, no whole determinant post hoc.
variable {α:Type*}[SemilatticeSup α][OrderBot α][Fintype α][DecidableEq α]
variable {E:Type*}[Ring E][Module ℝ E][FiniteDimensional ℝ E]
omit t
set_option linter.unusedSimpArgs false
def reconL : (α→E)≃ₗ[ℝ](α→E):=by
 let H : (α→E)→ₗ[ℝ](α→E):={ toFun:=fun f i=> Stilo.view i f,map_add':=fun x y=>funext fun i=> view_add .., map_smul':=fun c x=>funext fun i=> by change view i (c • x)=c • view i x; unfold view; simp only [smul_sum]; rfl }
 have hi:Injective H:= fun _ _ p=> funext fun i=> proves fun j _=> congrFun p j
 exact LinearEquiv.ofBijective H ⟨hi,(LinearMap.injective_iff_surjective_of_finrank_eq_finrank rfl).mp hi⟩
lemma recon (W:α→E)(s:α):view s (reconL.symm W)= W s:=congrFun (reconL.apply_symm_apply W) s
lemma solve (W:α→E)(F: α→E)(h:∀ a,W a=view a F):reconL.symm W=F:= by rw [funext (fun i=> show W i = reconL F i from h i), reconL.symm_apply_apply]
end YM.CF.Scion
