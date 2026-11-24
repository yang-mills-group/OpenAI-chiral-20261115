import Zephyr.Chern.Bar
import Zephyr.Chern.Reach
set_option autoImplicit false
noncomputable section
namespace Zephyr.Chern

open YM YM.Lattice Filter Topology YM.CF YM.CF.Tulip YM.CF.Cube YM.CF.Scroll YM.CF.Fir YM.CF.Rush YM.Laurent


open scoped Kronecker

variable {s:ℕ}{N:Side}

def peg (N:Side)(x z:Cover): ℂ := if wrap N z=wrap N x then
  flag N (-x)*flag N 0 * wind (wrap N (-x)) z
  else 0

lemma peg_le (N:Side)(x z:Cover) : ‖peg N x z‖≤1 := by
  unfold peg
  split
  · rw [norm_mul,norm_mul,flag_norm,flag_norm,wind,fee_norm,mul_one,mul_one]
  simp

lemma peg_at (N:Side)(x:Cover) : peg N x x=1:=by
  rw [peg,if_pos rfl]
  have h:wind (wrap N (-x)) x=(drag x).payA (wrap N (-x)):=by
    simp [wind,Shape.payA,Shape.rent,drag_flee]
  rw [h,mul_right_comm,drag_flag,neg_add_cancel,flag_sq]

lemma peg_cart (x:Cover)(f:Cover→Op SpinIdx)(i j:IS):
    lint (cart N f ⊗ₖ (1:Op SU.Slot)) (-x) 0 i j =
    ∑' z, peg N x z * (f z ⊗ₖ (1:Op SU.Slot)) i j := by
  rcases i with ⟨i,l⟩; rcases j with ⟨j,k⟩
  rw [lint,tag,tag,Matrix.kronecker_apply,cart,Matrix.of_apply,←tsum_mul_right,←tsum_mul_left]
  apply tsum_congr;intro z
  rw [Matrix.kronecker_apply,wagon,jump_apply]
  dsimp only
  have e: Equiv.addRight (wrap N z) (wrap N (-x))=wrap N 0 ↔ wrap N z=wrap N x:=by
    change wrap N (-x)+wrap N z=wrap N 0 ↔_
    rw [map_neg,map_zero, add_comm,←sub_eq_add_neg,sub_eq_zero]
  rw [peg]
  by_cases b:wrap N z=wrap N x
  · rw [if_pos b,if_pos (e.mpr b)]
    rw [Matrix.smul_apply,smul_eq_mul];ring
  rw [if_neg b, if_neg (mt e.mp b)]; simp

lemma Looming.flat {r} (h:Looming s r)(hs:1≤s)(m:Male)
    (x:Cover)(i j:IS) :
    tuft (funde s m N) (stream N) (-x) 0 i j 0 =
    ∑' z, peg N x z * seam z (snow SU.Slot (r m)) i j:=by
  change lint (funde s m N (profile _)) _ _ _ _=_
  rw [petal_idle,profile_trivial,funde_flat _ hs,peg_cart]
  simp_rw [h.seam_snow hs]

variable {κ:Type*}{L:Filter κ} [L.NeBot]{X:Cross s L} {p:Stack}

lemma Cross.Relax.shade (h:X.Relax p)
    {r:Male→Streams} (q:Looming s r)
    {u:Streams}(a:∀ k,Arrives L (fun i=>r (X.M i) k) (u k)) :
    p 0=snow SU.Slot u:=by
  apply seam_ext;intro x
  apply Matrix.ext;intro i j
  have h₁:=h x i j 0
  let f n z:=peg (X.N n) x z * seam z (snow SU.Slot (r (X.M n))) i j
  have aa:= arrives_snow a i j
  have h₂:Tendsto (fun n=>∑' z, f n z) L
      (𝓝 (∑' z, if z=x then seam x (snow SU.Slot u) i j else 0)):=by
    obtain ⟨b,hb,t⟩:=aa.swift
    apply tendsto_tsum_of_dominated_convergence hb.abs
    · intro z
      by_cases v:z=x
      · subst z
        simp only [f,if_true,peg_at,one_mul]
        exact aa.co x
      simp only [if_neg v]
      apply tendsto_const_nhds.congr'
      filter_upwards [X.apply_lift x, X.apply_lift z] with n e d
      have hne:wrap (X.N n) z≠wrap (X.N n) x:=
        fun y=> v <| d.symm.trans ((congrArg lift y).trans e)
      simp [f,peg,hne]
    filter_upwards [t] with n pn z
    rw [show f n z=peg (X.N n) x z * _ from rfl, norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (peg_le ..)).trans (pn z)
  have g: ∀ n,X.test x i j 0 n=∑' z, f n z:=fun n=>q.flat X.yes ..
  rw [funext g] at h₁
  simp only [tsum_ite_eq] at h₂
  exact tendsto_nhds_unique h₁ h₂
