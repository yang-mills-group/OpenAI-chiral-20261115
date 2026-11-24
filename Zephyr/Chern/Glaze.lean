import Zephyr.Chern.Lint
set_option autoImplicit false
noncomputable section
namespace Zephyr.Chern

open YM YM.Lattice Filter Topology YM.CF YM.CF.Tulip YM.CF.Cube YM.CF.Lat YM.CF.Rush YM.Laurent
open scoped Matrix Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra


variable {N:Side}{F:Oil N}{a e r:ℝ}

lemma solo_inter (p:Solo a r F e) {U:Bkg (More N)}
    (h:profile U∈Openc _ e) (g:Site (More N) → SU.E):
    F (profile (gauge g U)) * (tradew N g).val=(tradew N g).val * F (profile U):=by
  obtain ⟨Y,C,b,_,k⟩:=p
  rw [profile_g]
  let x :↑(Openc (More N) e):=⟨profile U,h⟩
  let y:=(forum N e).drive g x
  change F y.val * _=_* F x.val
  dsimp only at k
  rw [k y,k x,Matrix.sum_mul,Matrix.mul_sum]
  exact Finset.sum_congr rfl (fun i _=> (b i).frame g x)

lemma tradew_diag (g:Site (More N)→ℝ) :
    (tradew N (arc∘g)).val =
     Matrix.diagonal (fun i=> Complex.exp (wgt i.2 * g (book i))) := by
  ext ⟨x,u⟩ ⟨y,v⟩
  unfold tradew
  dsimp only
  have h(t:ℝ) : (SU.matter (arc t)).val =
      Matrix.diagonal (fun i=>Complex.exp (wgt i*t)) :=
    congrArg Prod.fst (brand_arc t)
  rw [jump_apply]
  simp only [Equiv.refl_apply,Function.comp_apply,h]
  simp [Matrix.diagonal_apply,book,ite_and]

lemma glazed_pose (N:Side)(z:Cover)(t:ℝ):
    petals (glazed N z) t =
    gauge (arc ∘ (fun v=>riseA z v*t)) (petals (stream N) t):=by
  funext i
  rcases i with ⟨j,k⟩
  simp [Lattice.gauge,glazed,petals,sub_eq_add_neg,add_mul,arc_add,arc_neg]

lemma tap_glazed (p:Solo a r F e)
    (z y:Cover)(n:2*size y<N.val) (t:ℝ)
    (h:profile (petals (stream N) t)∈Openc _ e)
    (i j:IS):
    tap F (glazed N z) (-y) 0 i j t=
      Complex.exp ( (wgt i.2 * (2*flux y z : ℝ))*t)* tap F (stream N) (-y) 0 i j t := by
  have u:=solo_inter p h (arc ∘ fun v=>riseA z v*t)
  rw [tradew_diag, ← glazed_pose] at u
  have hk := congrArg (fun P:Op (Single N)=> P (tag N (-y) i) (tag N 0 j)) u
  rw [Matrix.mul_diagonal,Matrix.diagonal_mul,pwin,rise_one,zero_mul,Complex.ofReal_zero,
    mul_zero,Complex.exp_zero,mul_one,book] at hk
  have ht : (tag N (-y) i).1.1 = wrap N (-y):=rfl
  rw [ht,rise_charge z y n, Complex.ofReal_mul,←mul_assoc] at hk
  simp only [tap,lint];rw [hk,mul_left_comm];rfl

lemma tuft_glazed (p:Solo a r F e)(he:0<e)
    (z y:Cover)(n:2*size y<N.val) (i j:IS):
    tuft F (glazed N z) (-y) 0 i j =
      splice (ringlet (wgt i.2 * (2*flux y z:ℝ))) (tuft F (stream N) (-y) 0 i j) := by
  apply Bloom.bud_eq
    (f:=tap F (glazed N z) (-y) 0 i j)
  apply ((bloom_exp _).mul (tuft_bloom p he ..)).congr
  filter_upwards [petals_open he (stream N)] with t ht
  exact tap_glazed p z y n t ht i j
