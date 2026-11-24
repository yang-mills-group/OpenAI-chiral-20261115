import Gingham.Ruff.Diadem
import Gingham.Ruff.Placket
import Gingham.Ruff.Ruffle
import YM.CF.Tap.Gamin
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

abbrev Jabot (R:Seal (Seat N)→Prop)(a c:ℝ)(f:Chin N→Op (Single N))(e:ℝ):=
  Brooch R (badge _) (bail N e) (bail N e) a c (fun x=> f x.val)
abbrev Spotlit (x:Site N) := Jabot (fun S=>node x∈S)
abbrev WW (x:Site N) : Op (Single N):= strip (forum N 0) {node x}
abbrev cabin (i:Single N):= i.1.1 -- collision?
lemma node_inj: Injective (@Cube.node N):= by
  intro x y h; exact (assembly N).embed_injective (add_right_cancel h)

lemma WWj (x:Site N)(U:Op (Single N))(i j):
    (U*WW x) i j= if cabin j=x then U i j else 0:= by
  rw [strip_j]
  simp_rw [show (forum N _).home j=node (cabin j) from rfl,node_inj.eq_iff]

lemma WWi (x:Site N)(U:Op (Single N))(i j):
    (WW x*U) i j= if cabin i=x then U i j else 0:= by
  rw [strip_i]
  simp_rw [show (forum N _).home i=node (cabin i) from rfl,node_inj.eq_iff]
lemma WW_sum (N:Side): ∑ x:Site N, WW x = 1:=by
  ext i j; simp [Matrix.sum_apply,WW,stripe1,show (forum N 0).home i=node (cabin i) from rfl,node_inj.eq_iff,ite_and,Matrix.one_apply]
lemma WW_p (x:Site N): IsStarProjection (WW x) := cutM_idp _
lemma WW_A (x:Site N): Commute (tickA N) (WW x):=by
  unfold Commute SemiconjBy
  ext i j; rw [WWi,WWj]
  by_cases h:i=j
  · rw [h]
  have z:tickA N i j=0:=by
    change cutM _ ((helix N) i) ((helix N) j)=0
    rw [cutM,Matrix.diagonal_apply_ne _ ((helix N).injective.ne h)]
  rw [z]; simp

variable {a c d e:ℝ} {f g:Chin N→Op (Single N)} {R:Seal (Seat N)→Prop}

lemma starring (x: Site N) (h:Solo a c f e): Spotlit x a c (fun z=> f z * WW x) e :=
  ((Brooch.crowned h).streamj (node x)).shape (fun _ _ _ _ _ _=>And.left)
lemma feathers0 (x:Site N)(a e:ℝ): Spotlit x a (Real.exp a) (fun _=>WW x) e:=by
  simpa using starring x (f:=fun _=>1) (a:=a) (e:=e) (Crown.ident ..)

lemma kite (x:Site N)(ha:0≤a)(h:Spotlit x a c f e)(l:Solo a d g e): Spotlit x a (2*(c*d)) (fun y=> f y * g y) e :=
 h.product l ha (fun _ _=>mem_union_left _)
def breast (f:Chin N→Op (Single N))(x:Site N)(z:Chin N):= (f z - tickA N)*WW x
def wings (f g:Chin N→Op (Single N))(x:Site N)(z:Chin N):= 𝒪 (f z) (g z) (WW x)
lemma feathers1 (x:Site N)(h:Solo a c f e): Spotlit x a (c+wingRent Fir.Aop a) (breast f x) e:=
  starring x (h.sub (soil_tick ..))

def perch (c d:ℝ):=2*(c*d)
def dovecote (a c:ℝ):=
  let w:=Real.exp a
  let h:=w+perch (perch (w+c) c) c
  w+ (perch (perch h c) (perch c h) +
     perch (perch h (w+c)) (perch (w+c) h))

lemma feathers2 (x:Site N)(ha:0≤a)(h:Solo a c f e)(l:Solo a c g e):
    Spotlit x a (dovecote a c) (wings f g x) e:=by
  have ht: Solo (N:=N) a (Real.exp a) (fun _=>1) e := Crown.ident ..

  let w:=Real.exp a; let t:=perch (perch (w+c) c) c
  have z: Solo a (w+c) (fun y=>1-f y) e:= ht.sub h
  have p: Solo a t (fun y=> ℱ (f y) (g y)) e:= (z.product l ha).product h ha
  have q: Solo a (w+t) (fun y=> 𝒞 (f y) (g y)) e:= ht.plus p
  have r: Solo a (w+t) (fun y=> 𝒞' (f y) (g y)) e:= ht.sub p
  have B(i:ℝ)(D:Chin N→Op (Single N))(l:Solo a i D e): Spotlit x a
    (perch (perch (w+t) i) (perch i (w+t)))
    (fun y=> (𝒞 (f y) (g y) * D y * WW x) * (D y * 𝒞' (f y) (g y))) e:=
     kite x ha (starring x (q.product l ha)) (l.product r ha)

  unfold wings
  simp_rw [𝒪,sheaf,seam,mul_add,add_mul,←mul_assoc]
  have v:= (feathers0 x a e).sub ((B c f h).plus (B _ _ z))
  simp only [←mul_assoc] at v; exact v


-- hitch pieces (false leg pays with transpose of S*W)
lemma reflected_spur (x:Site N) (h:Solo a c f e):
    Spotlit x a (Real.exp a+c) (fun z=> -(WW x * (1-f z))) e:=by
  have b: Solo a (Real.exp a+c) (fun z=> 1-f z) e:= (Crown.ident ..).sub h
  exact (((Brooch.crowned b).streami (node x)).shape
     (R':=fun S=>node x∈S) (fun _ _ _ _ _ _=>And.left)).minus

