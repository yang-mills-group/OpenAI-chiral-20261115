import Zephyr.Chern.Lint
set_option autoImplicit false
noncomputable section
namespace Zephyr.Chern

open YM YM.Lattice Filter Topology YM.CF YM.CF.Tulip YM.CF.Cube YM.CF.Lat YM.CF.Rush YM.Laurent


variable {N:Side}

def hole (y:Site N):Cover := lift (-y)
lemma rep_hole (y:Site N) : wrap N (-(hole y)) = y:=by
  simp [hole]
lemma lattice_sum (N:Side)(f:Cover→ℂ):
    (∑' z, if lift (wrap N z)=z then f z else 0)=∑ y:Site N, f (hole y):=by
  let s := (Finset.univ: Finset (Site N)).image hole
  have h:Function.LeftInverse (fun z=>wrap N (-z)) hole:=rep_hole
  classical
  rw [tsum_eq_sum (s:=s),Finset.sum_image h.injective.injOn]
  · simp [hole]
  intro x g
  rw [if_neg]
  intro i
  apply g
  refine Finset.mem_image.mpr ⟨- wrap N x,Finset.mem_univ _,?_⟩
  simpa only [hole,neg_neg]

lemma lint_mul (P Q:Op (Single N)) (x y:Cover) (i j:IS):
    lint (P*Q) x y i j =
    ∑ w:Site N, ∑ l:IS, lint P x (-(hole w)) i l * lint Q (-(hole w)) y l j:=by
  rw [lint,Matrix.mul_apply, Finset.mul_sum,
    ← (helix N).symm.sum_comp,Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun w _=>Finset.sum_congr rfl fun l _=>?_
  have he:tag N (-(hole w)) l=(helix N).symm (w,l):=by rw [tag,rep_hole];rfl
  simp only [lint,he]
  conv_lhs => rw [←one_mul (_ * _),←flag_sq N (-(hole w))]
  ring

def due (F:Oil N) (x z:Cover) (i j:IS)(k:Fin 3):ℂ:=
  ∑ l:IS,
    splice (tuft F (stream N) (-x) (-z) i l)
      (tuft F (stream N) (-z) 0 l j) k

def Mended (F:Oil N) := ∀ x i j k,
    tuft F (stream N) (-x) 0 i j k =
    ∑' z, if lift (wrap N z)=z then due F x z i j k else 0

lemma mends {F:Oil N}
    (h:∀ x y i j,Bud (tap F (stream N) x y i j))
    (p:∀ᶠ t:ℝ in 𝓝 0, IsIdempotentElem (F (profile (petals (stream N) t)))) :
    Mended F:=by
  intro x i j k
  rw [lattice_sum]
  let u:=tap F (stream N)
  let v:=tuft F (stream N)
  have t: Bloom
    (fun s=> ∑ w:Site N,∑ l:IS, u (-x) (-(hole w)) i l s * u (-(hole w)) 0 l j s)
    (∑ w:Site N,∑ l:IS, splice (v (-x) (-(hole w)) i l) (v (-(hole w)) 0 l j)) :=
    Bloom.sum _ fun w _=>Bloom.sum _ fun l _ =>
      (h ..).bloom.mul (h ..).bloom

  have b := t.congr (g:=u (-x) 0 i j) (by
    filter_upwards [p] with s hs
    exact (congrArg (fun P=>lint P (-x) 0 i j) (show _ * _=_ from hs).symm).trans
      (lint_mul _ _ _ _ _ _))
  change bud (u _ _ _ _) k =_
  rw [b.bud_eq]
  simp only [Finset.sum_apply,v,due]

lemma mends_limit (s:ℕ)(p:1≤s):
    ∃ n, ∀ {N:Side}, n ≤ N.val →∀ M,Mended (funde s M N):=by
  obtain ⟨a,r,e,j,k,w,t,H⟩ := funde_s s p
  obtain ⟨b,g,y,W⟩:=funde_q s p
  refine ⟨max t y,fun {N} n M=>?_⟩
  apply mends
  · exact fun x z i l=> (tuft_bloom (H M N ((le_max_left ..).trans n)) w ..).1
  filter_upwards [petals_safe (stream N) g] with u v
  exact (W M N ((le_max_right ..).trans n) _ v).isIdempotentElem
