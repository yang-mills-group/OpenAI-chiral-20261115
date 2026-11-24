import YM.CF.Lattice.Frequencies
/-! Antiperiodic full matrix at trivial links. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Lat
open Lattice BZ WilsonFrame
open Finset
open scoped MatrixOrder Matrix.Norms.L2Operator Matrix Topology BigOperators Kronecker
attribute [local instance] opCStarAlgebra
variable {K n : Type*} [Group K] [Fintype n] [DecidableEq n]
variable (R : K →* UNI n) (N:Side)

/-- Unital algebra hom here for pi operations on symbols. -/
def fb : (Site N → Op SpinIdx) →ₐ[ℝ] Op (Tx N n) :=
  AlgHom.ofLinearMap (bandMap (N:=N) n) (bands_one n) (bands_mul n)
-- `n` implicit.

def fourImage (n : Type*) [Fintype n] [DecidableEq n] (N:Side) :
    (Site N → Op SpinIdx) →ₐ[ℝ] Op (Tx N n) :=
  (twist (spatialU N n)).toAlgEquiv.toAlgHom.comp (fb N)
lemma fourStar (A : Site N → Op SpinIdx) : fourImage n N (star A)=star (fourImage n N A) := by
  change twist _ (bands _ _) = star (twist _ (bands _ _)); rw [← map_star]
  unfold bands; simp only [jump_star,op_star_kron,Equiv.refl_symm,Equiv.refl_apply,star_one]; rfl

def emptyFrame := frame R (1:RLink N K) (anticut N)
def latticeAtoms (k : Site N) := atom (pm k)
lemma H0_four : (emptyFrame R N).H0=fourImage n N (fun k => (latticeAtoms N k).H0) := by
  let Q := fourImage n N; let E := emptyFrame R N; let W := latticeAtoms N
  have ht i : Q (fun k => (W k).T i)=E.T i := (twist_bands_shift R i).symm
  have hb i : Q (fun k => star ((W k).T i))=star (E.T i) := by
    rw [show Q (fun k => star _)=_ from fourStar N (fun k => (W k).T i),ht i]
  have hc i : Q (fun k => (W k).gamma i)=E.gamma i := (twist_bands_spin n _).symm
  have he (i) : Q (fun k => (W k).inc i)=E.inc i := by
    let F := fun k => (W k).lap i; let G := fun k => (W k).diff i
    let T := fun k => (W k).T i; let Y := fun k => star (T k)
    change Q (F+(fun k => (W k).gamma i)*G)=E.inc i
    rw [map_add,map_mul,hc]
    change Q (1-(1/2:ℝ) • (T+Y))+ _ * Q ((1/2:ℝ) • (T-Y))=_
    simp only [map_sub,map_smul,map_add,map_one,show Q T=E.T i from ht i,show Q Y=star _ from hb i]; rfl
  change -1+∑ i, E.inc i=Q (fun k => (W k).H0)
  rw [show (fun k => (W k).H0)=-1 + ∑ i, fun k => (W k).inc i by ext k : 1; simp [WilsonFrame.H0]]
  simp only [map_add,map_one,map_sum,map_neg, he]
lemma H_four : (emptyFrame R N).H=fourImage n N (fun k => (latticeAtoms N k).H) := by
  let Q := fourImage n N
  change _=Q ((fun k => (latticeAtoms N k).chir)*(fun k => (latticeAtoms N k).H0))
  rw [map_mul,show Q (fun k => (latticeAtoms N k).chir)=spin N n grading from (twist_bands_spin n _).symm, show Q (fun k => _)=_ from (H0_four R N).symm]; rfl

lemma plus_four : (emptyFrame R N).plus=fourImage n N (fun k => (latticeAtoms N k).plus) := by
  let Q := fourImage n N
  change _=Q ((1/2:ℝ) • (1+(fun k : Site N => grading)))
  rw [map_smul,map_add,map_one,show Q (fun k => _)=spin N n grading from (twist_bands_spin n _).symm]; rfl

variable [Nonempty n]
lemma emptyBand : Safe (emptyFrame R N).H := by
  apply band; intro x i j h; simp [square,travel]
set_option maxHeartbeats 600000 in
lemma project_four : projector (emptyFrame R N).H=fourImage n N (fun k => projector (latticeAtoms N k).H) := by
  let Q := fourImage n N; let A := fun k => (latticeAtoms N k).H
  let B := fun k => rsEval (A k)
  have hs : HasSum (fun i k => rsTerm (A k) i) B := by rw [Pi.hasSum]; exact fun i => rs_sum ((atom_safe (pm i)).good.trans_lt rho_lt)
  have hx : HasSum (rsTerm (Q A)) (Q B) := by
    convert hs.map Q Q.toLinearMap.continuous_of_finiteDimensional using 1
    ext1 i; change rsTerm (Q A) i=Q (fun k => rsTerm (A k) i)
    rw [show (fun k => rsTerm (A k) i)=SignScalar.c i • ((1 - (1/256:ℝ) • A^2)^i) by
      funext k; simp only [rsTerm,Pi.pow_apply,Pi.smul_apply,Pi.sub_apply, Pi.one_apply,slack]]
    rw [map_smul,map_pow,map_sub,map_one,map_smul,map_pow]; rfl
  have hA : Safe (Q A) := H_four R N ▸ emptyBand R N
  rw [H_four]
  change projector (Q A)=Q (fun k => projector (A k))
  rw [show (fun k=> projector (A k)) = ((1/2:ℝ) • (1+((1/16:ℝ) • A)*B)) by
    funext k; simp only [projector,polarity,B,Pi.smul_apply,Pi.one_apply,Pi.add_apply,Pi.mul_apply]]
  rw [projector,polarity, (rs_sum (hA.good.trans_lt rho_lt)).unique hx,map_smul,map_add,map_one,map_mul,map_smul]
lemma periodic_K :
    let W := emptyFrame R N
    ∃ J:Op (Tx N n),
    let P := projector W.H; let A := W.plus; let D := W.overlap*P
    D*J=A ∧ J*D=P := by
  intro W
  let K := latticeAtoms N; let A := fun k => (K k).plus; let P := fun k => projector (K k).H
  let Q := fourImage n N
  let B := fun k => (scale (pm k))⁻¹ • (P k * A k)
  have hk (k : Site N) := inverseMode (pm k) (pm_zone k) (pm_nonzero k)
  have hs : A*P*B=A := by
    funext k; change A k*P k * B k= _; rw [show A k*P k=(K k).overlap*P k from ((K k).overlap_action (atom_safe _)).symm]; exact (hk _).1
  have ht : B*(A*P)=P := by
    funext k; change _*(A k*P k)=_; rw [show A k*P k=(K k).overlap*P k from ((K k).overlap_action (atom_safe _)).symm]; exact (hk _).2
  refine ⟨Q B,?_⟩
  dsimp only; rw [W.overlap_action (emptyBand R N),show projector W.H=Q P from project_four ..,
    show W.plus=Q A from plus_four ..,← map_mul, ← map_mul, ← map_mul,hs,ht]; trivial
end YM.CF.Lat
