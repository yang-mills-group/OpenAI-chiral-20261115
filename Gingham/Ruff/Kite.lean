import Gingham.Ruff.Teal
import Gingham.Ruff.Purse
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


lemma iguana (x y:Site N) : separation (node x) (node y) = 2*separation x y:=by
  unfold node; rw [separation_translate]; exact Laic.emptio (assembly N) x y

def turncoat (z:Site N) := Lattice.route 0 (Lattice.lift z) 1
lemma turncoat_distance (z:Site N) : stop 0 (turncoat z) = z:=by
  rw [← AddMonoidHom.map_zero (Lattice.wrap N),←wrap_stop_cover,turncoat,Lattice.route_end,Lattice.wrap_lift]
lemma turncoat_size (z:Site N) : (turncoat z).length ≤ 4*pdist z := by
  exact Cube.route_size _ _ _ _ (fun i=>by rw [Pi.zero_apply,sub_zero]; exact Lattice.component_le z i)
-- exact .. notation after parameter?

variable {M M' : Type*} [AddCommGroup M] [AddCommGroup M']

def foremast (v:Site N→M)(p:Step)(a y:Site N)(i:Axis):M:=
  if i=p.dir then
    if p.neg then -(v (y-(a+p.vec))) else v (y-a)
  else 0

def sail (v: Site N→M) (i:Axis) (a y:Site N): Walk → M
| [] => 0
| p :: w => foremast v p a y i + sail v i (a+p.vec) y w

def voyage (v: Site N→Site N→M)(i:Axis)(y:Site N):=
  ∑ z: Site N, sail (v z) i 0 y (turncoat z)


lemma foremast_div (v:Site N→M)(p:Step)(a y:Site N):
    ∑ i, (foremast v p a y i - foremast v p a (y-Lattice.step i) i) =
      v (y-a)-v (y-(a+p.vec)):=by
  rw [sum_eq_single_of_mem p.dir (mem_univ _) (fun j _ h=>by simp [foremast,h])]
  obtain ⟨k, b | b⟩:=p
  · simp [foremast, Lattice.Step.vec,
      show y-Lattice.step k-a=y-(a+Lattice.step k) from (by abel)]
  simp only [foremast,Lattice.Step.vec, ↓reduceIte]
  rw [show y-Lattice.step k-(a+-Lattice.step k)=y-a from by abel]; abel

lemma sail_div (v:Site N→M)(w:Walk)(a y:Site N):
    ∑ i, (sail v i a y w - sail v i a (y-Lattice.step i) w) =
      v (y-a)-v (y-stop a w):=by
  induction w generalizing a with
  | nil => simp [sail,stop]
  | cons p w ih =>
    simp only [sail,stop, add_sub_add_comm,sum_add_distrib]
    rw [foremast_div,ih]; abel

lemma voyage_div (v:Site N→Site N→M)(y:Site N):
    ∑ i,(voyage v i y - voyage v i (y-Lattice.step i))=
     ∑ z,(v z y-v z (y-z)):=by
  simp_rw [voyage,←sum_sub_distrib]
  rw [sum_comm]; simp_rw [sail_div,turncoat_distance, sub_zero]


-- Generic add-hom map and translation
lemma foremast_map {H: Type*}[FunLike H M M'][AddMonoidHomClass H M M'](h:H)
    (c:Site N){v:Site N→M}{g:Site N→M'}
    (p:Step)(i:Axis)(a y:Site N)(k:∀ x,g (x+c)=h (v x)):
    foremast g p a (y+c) i = h (foremast v p a y i):=by
  unfold foremast; split
  · split
    · rw [add_sub_right_comm,k,map_neg]
    rw [add_sub_right_comm,k]
  rw [map_zero]


lemma sail_map {H: Type*}[FunLike H M M'][AddMonoidHomClass H M M'](h:H)(c:Site N)
  {v:Site N→M}{g:Site N→M'}(k:∀ x,g (x+c)=h (v x))(w: Walk)(i:Axis)(a y:Site N):
    sail g i a (y+c) w = h (sail v i a y w):=by
  induction w generalizing a with
  | nil => simp [sail]
  | cons p w ih => rw [sail,sail,map_add,ih,foremast_map h _ _ _ _ _ k]
lemma voyage_map {H: Type*}[FunLike H M M'][AddMonoidHomClass H M M'](h:H)(c:Site N)
    {v:Site N→Site N→M}{g:Site N→Site N→M'}(k:∀ z x, g z (x+c)=h (v z x))
    (i:Axis)(y:Site N): voyage g i (y+c)=h (voyage v i y):=by
  rw [voyage,voyage,map_sum]; exact sum_congr rfl fun z _=> sail_map _ _ (k z) ..

abbrev OP (N:Side) := Op (Single N)
variable (f g:Chin N→OP N)
def firstmate (z y:Site N)(p:Chin N):=
  WW (y+z)*wings f g y p
def sprit (i:Axis)(y:Site N)(p:Chin N):=
  voyage (fun z x=>firstmate f g z x p) i y


lemma sprit_div (y:Site N)(p:Chin N)(h:IsStarProjection (f p)):
    ∑ i,(sprit f g i y p - sprit f g i (y-Lattice.step i) p) = wings f g y p:=by
  unfold sprit
  rw [voyage_div,sum_sub_distrib]
  simp only [firstmate, sub_add_cancel, wings]
  have b:(∑ z:Site N, 𝒪 (f p) (g p) (WW (y-z)))=0:=by
    rw [𝒪_sum, Fintype.sum_equiv (Equiv.subLeft y) (fun z=> WW (y-z)) (@WW N) (fun _=>rfl),
      WW_sum,𝒪_one h]
  rw [←sum_mul, Fintype.sum_equiv (Equiv.addLeft y) (fun z=>WW (y+z)) (@WW N) (by intro; rfl),WW_sum,one_mul, ←mul_sum,b,mul_zero,sub_zero]
-- argument duplication fun!

