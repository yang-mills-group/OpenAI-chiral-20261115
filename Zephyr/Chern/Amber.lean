import Zephyr.Chern.Garden
set_option autoImplicit false
noncomputable section
namespace Zephyr.Chern

open YM YM.Lattice Filter Topology YM.CF YM.CF.Tulip YM.CF.Cube YM.CF.Lat YM.CF.Tenant YM.CF.Drapes YM.CF.Branch Metric

open scoped Matrix Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
open Finset


variable {N:Side}{b B:ℝ}

structure Temper (o:Site N)(A:Angles N)(B:ℝ) : Prop where
  above : 1≤B
  grow (v:Edge (Site N)): |A v|≤ B*(1+separation v.1 o)

variable {o:Site N}{A:Angles N}
lemma Temper.more (t:Temper o A B) (g:B≤b):Temper o A b :=
  ⟨t.above.trans g,fun v=>(t.grow v).trans (by gcongr)⟩

lemma Temper.slide (t:Temper o A B) {p:Site N}{D:ℕ}(q:separation o p ≤D) :
    Temper p A (B*(1+D)) := by
  have b:=t.above
  have h:(1:ℝ)≤1+D:=by simp
  refine ⟨one_le_mul_of_one_le_of_one_le b h, fun v=>?_⟩
  refine (t.grow v).trans ?_
  rw [mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (by linarith)
  have w:= (separation_triangle v.1 p o).trans (Nat.add_le_add_left ((separation_comm _ _).trans_le q) _)
  have e : (separation v.1 o:ℝ)≤ (separation v.1 p:ℝ)+D:=by exact_mod_cast w
  nlinarith only [e, (by positivity:0≤(D:ℝ)*separation v.1 p)]

def book (i:Single N) := node i.1.1

variable {a e ρ r:ℝ}

structure Oily (a e B W:ℝ) where
  hb : 0<a
  bound : 0<W
  ρ:ℝ
  s:Sap e ρ
  q : ∀ n:ℕ,(B * (1+n))^2 / ρ^2 ≤ W * Real.exp (a/2 * n)

lemma oily (ha:0<a)(he:0<e)(B:ℝ): ∃ W,Nonempty (Oily a e B W) := by
  obtain ⟨ρ,s⟩:=sap he
  have hs:=s.pos
  let M:=1+4/a
  have m0:1≤M:=le_add_of_nonneg_right (by positivity)
  have m1: 1≤M*(a/4):=by unfold M; field_simp;linarith
  refine ⟨1+B^2*(M/ρ)^2,⟨ha,by positivity,ρ,s,fun n=>?_⟩⟩
  have h:(1:ℝ)+n ≤ M * Real.exp (a/4 * n):= by
    calc
      _ ≤ M * ((a/4 * n)+1) := by
        linarith [mul_le_mul_of_nonneg_right m1 (show (0:ℝ)≤n by positivity)]
      _ ≤ _ := mul_le_mul_of_nonneg_left (Real.add_one_le_exp _) (by linarith)
  calc
    (B * (1+n))^2 / ρ^2
      = B^2 / ρ^2 * (1+n)^2 := by ring
    _ ≤ B^2 / ρ^2 * (M * Real.exp (a/4*n))^2:=by gcongr
    _ = B^2*(M/ρ)^2 * Real.exp (a/2 * n):=by
      rw [show a/2*(n:ℝ)=a/4*n+a/4*n by ring,Real.exp_add];ring
    _ ≤ _ := by linarith [Real.exp_pos (a/2*n)]

variable {A:StemA N} {o:Site (More N)} {W:ℝ}
-- shadows?
def Pillow (o:Site (More N)) (i j : Single N) := book i=o ∨ book j=o

variable {S:Band N}{F:Oil N}{C:Toll (Single N)}{i j:Single N}
lemma hit_band (p:Piece e S C F)(v:C i j ≠0) (h:Pillow o i j) {x:Edge (Site (More N))}
    (hS:x∈leaks S): separation x.1 o < S.card := by
  obtain ⟨b,l,r⟩ := (p.expo ..).triggered v
  have m :o∈S:=h.elim (fun e=> e ▸ l) (fun e=> e ▸ r)
  exact b.lim _ (mem_filter.mp hS).2.left o m

lemma band_buds (w:Oily a e B W)(t:Temper o A B)(p:Piece e S C F)
    (h:Pillow o i j)(m:ℕ)(v:C i j≠0→m≤S.card)(k:Fin 3):
    ‖wad F A i j k‖ ≤ W*Real.exp (-(a/2)*m)*(rent a S * C i j) := by
  by_cases u:C i j=0
  · simp [wad,(kernel_free p u w.s.ready A).bud_eq,u]
  have l:= t.above
  have a1:1≤B*(1+(S.card:ℝ)):=one_le_mul_of_one_le_of_one_le l (by simp)
  have e':∀ x∈leaks S, |A x|≤B*(1+(S.card:ℝ)) := fun x hx=>
    (t.grow x).trans
      (mul_le_mul_of_nonneg_left
        (add_le_add_right (by exact_mod_cast (hit_band p u h hx).le) _)
        (zero_le_one.trans l))
  refine ((kernel_jet p w.s a1 e').2 k).trans ?_
  rw [←mul_assoc]
  apply mul_le_mul_of_nonneg_right _ (p.nonn i j)
  refine (w.q S.card).trans ?_
  rw [rent,mul_assoc,←Real.exp_add]
  apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr _) w.bound.le
  have hh:(m:ℝ)≤S.card:=by exact_mod_cast v u
  linarith [mul_le_mul_of_nonneg_left hh w.hb.le]

lemma Bough.subprice (T:Bough e a r F)(w:Oily a e B W)(t:Temper o A B)
    (h:Pillow o i j) (z:Finset (Band N)) (m:ℕ)
    (v:∀ S∈z, T.c S i j≠0→m≤S.card)
    (k:Fin 3):
    ‖∑ S∈z,wad (T.f S) A i j k‖ ≤ W*r*Real.exp (-(a/2)*m) := by
  have q:= w.bound
  refine le_trans ((norm_sum_le ..).trans (sum_le_sum
    (fun s u=> band_buds w t (T.pie s) h m (v s u) k))) ?_
  rw [←mul_sum,mul_right_comm W r]
  exact mul_le_mul_of_nonneg_left ((sum_le_sum_of_subset_of_nonneg
    (subset_univ z)
    (fun s _ _=>mul_nonneg (rent_pos a s).le ((T.pie s).nonn i j))).trans
    (T.total i j)) (by positivity)

lemma Bough.error (T:Bough e a r F)(w:Oily a e B W)(t:Temper o A B)
    (h:Pillow o i j) (z:Finset (Band N)) (m:ℕ)
    (v:∀ S, S.card<m→ S∈z)
    (k:Fin 3):
    ‖wad F A i j k - wad (T.sift z) A i j k‖ ≤ W*r*Real.exp (-(a/2)*m):=by
  simp only [wad, (T.drip_sum A i j w.s.ready).bud_eq,
    (T.sift_drip z A i j w.s.ready).bud_eq,Finset.sum_apply]
  rw [← Finset.sum_sdiff_eq_sub (subset_univ z)]
  exact T.subprice w t h _ m
    (fun S hZ _=>not_lt.mp fun u=>(mem_sdiff.mp hZ).2 (v S u)) k

lemma solo_fall (s:Solo a r F e)(w:Oily a e B W)(t:Temper o A B)
    (h:Pillow o i j) (m:ℕ)(v:m≤separation (book i) (book j))(k:Fin 3):
    ‖wad F A i j k‖ ≤ W*r*Real.exp (-(a/2)*m) := by
  obtain ⟨T⟩:=bough_exists s
  simp only [wad,(T.drip_sum A i j w.s.ready).bud_eq,Finset.sum_apply]
  apply T.subprice w t h
  intro S _ hz
  obtain ⟨c,l,r⟩:= ((T.pie S).expo ..).triggered hz
  exact v.trans (c.lim _ l _ r).le

lemma solo_price (s:Solo a r F e)(w:Oily a e B W)(t:Temper o A B)
    (h:Pillow o i j) (k:Fin 3):
    ‖wad F A i j k‖ ≤ W*r := by
  simpa only [Nat.cast_zero,mul_zero,Real.exp_zero,mul_one] using solo_fall s w t h 0
    (Nat.zero_le _) k

/-- Sharp comparison using agreement in a ball around one entry endpoint. -/
lemma solo_slit {A':StemA N}
    (s:Solo a r F e)(w:Oily a e B W)(t:Temper o A B)(t':Temper o A' B)
    (h:Pillow o i j) (m:ℕ)(agree:∀ x,separation x.1 o<m→ A x=A' x) (k:Fin 3):
    ‖wad F A i j k-wad F A' i j k‖ ≤ 2*(W*r*Real.exp (-(a/2)*m)) := by
  obtain ⟨T⟩ := bough_exists s
  let z:Finset (Band N):=univ.filter fun S=>S.card<m
  have p : wad (T.sift z) A i j k=wad (T.sift z) A' i j k := by
    simp only [wad,(T.sift_drip z A i j w.s.ready).bud_eq,
      (T.sift_drip z A' i j w.s.ready).bud_eq,Finset.sum_apply]
    refine sum_congr rfl ?_
    intro S u
    have hc: S.card<m:=(mem_filter.mp u).2
    by_cases hz:T.c S i j =0
    · rw [(kernel_free (T.pie S) hz w.s.ready A).bud_eq,
        (kernel_free (T.pie S) hz w.s.ready A').bud_eq]
    have a:∀ x∈leaks S, A x=A' x:=fun x hx=>
      agree _ ((hit_band (T.pie S) hz h hx).trans hc)
    rw [bud_congr (kernel_germ (T.pie S) w.s.ready a)]
  have v:∀ S:Band N, S.card<m→ S∈z:=fun S h=>mem_filter.mpr ⟨mem_univ _,h⟩
  have h₁:=T.error w t h z m v k
  have h₂:=T.error w t' h z m v k
  rw [two_mul]
  rw [←p] at h₂
  exact (norm_sub_le_norm_sub_add_norm_sub _ (wad (T.sift z) A i j k) _).trans
    (add_le_add h₁ ((norm_sub_rev ..).trans_le h₂))
