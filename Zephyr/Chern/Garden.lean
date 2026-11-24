import Zephyr.Chern.Petal
set_option autoImplicit false
noncomputable section
namespace Zephyr.Chern

open YM YM.Lattice Filter Topology YM.CF YM.CF.Tulip YM.CF.Cube YM.CF.Lat YM.CF.Tenant YM.CF.Drapes YM.CF.Branch Metric

open scoped Matrix Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra


structure Sap (e ρ:ℝ) : Prop where
  ready:0<e
  pos:0<ρ
  one:ρ≤1
  range(u:ℂ): ‖u‖<ρ+ρ→ ‖moor u - 1‖ < e

variable {N:Side}{e ρ:ℝ}

lemma sap (he:0<e): ∃ ρ,Sap e ρ := by
  obtain ⟨δ,p,q⟩:= Metric.continuousAt_iff.mp
    (show ContinuousAt moor 0 from moor_diff.continuous.continuousAt) e he
  let d:=min 1 (δ/2)
  have h:d≤δ/2 := min_le_right ..
  refine ⟨d,he,lt_min one_pos (half_pos p),min_le_left ..,?_⟩
  simp only [dist_eq_norm,sub_zero,moor_zero] at q
  exact fun u v=> q (v.trans_le (by linarith))

abbrev Oil (N:Side):=Chin N→Op (Single N)
abbrev StemA (N:Side):=Angles (More N)

def drip (Q:Oil N) (A:StemA N) (i j:Single N) (t:ℝ):ℂ :=
  Q (profile (petals A t)) i j

def wad (Q:Oil N) (A:StemA N) (i j:Single N) := bud (drip Q A i j)

lemma faux_open (h:Sap e ρ){A:StemA N}{B:ℝ}(hB:0<B)(a:∀ i, |A i|≤B)
    (u:ℂ)(p: ‖u‖<(ρ+ρ)/B) :
    faux A u ∈ Openc (More N) e := by
  refine ⟨1,guard0 h.ready.le,?_⟩
  rw [profile_trivial, pi_norm_lt_iff h.ready]
  intro i;rw [pi_norm_lt_iff h.ready]
  intro b
  have hh : |(if b then A i else -A i)|≤B := by cases b <;> simpa using a i
  apply h.range
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs]
  exact (mul_le_mul_of_nonneg_right hh (norm_nonneg u)).trans_lt ((lt_div_iff₀' hB).mp p)

lemma petals_open (he:0<e) (A:StemA N) :
    ∀ᶠ t in 𝓝 0, profile (petals A t)∈Openc (More N) e := by
  filter_upwards [petals_safe A he] with t ht
  exact ⟨_,ht, by rwa [sub_self,norm_zero]⟩

abbrev Piece (e:ℝ)(S:Seal (Site (More N)))(C:Toll (Single N))(F:Oil N) :=
  Suite (badge _) (bail N e) (bail N e) S C (fun x=>F x.val)

variable {S:Seal (Site (More N))}{F:Oil N}{C:Toll (Single N)}{A A':StemA N}{i j:Single N}

lemma kernel_bound (h:Piece e S C F) {x:Chin N}(p:x∈Openc _ e):
   ‖F x i j‖≤C i j := (h.expo i j).bounded ⟨x,p⟩

lemma kernel_hol (h:Piece e S C F)
    {V:Set ℂ}(hV:IsOpen V) (p:∀ u∈V, faux A u ∈ Openc _ e) (y:Chin N)
    (hy:y∈Openc _ e) :
    DifferentiableOn ℂ (fun u=> F (faux A u) i j) V := by
  classical
  let v := fun u=> if t:u∈V then
    (⟨faux A u,p u t⟩:↑(Openc (More N) e)) else ⟨y,hy⟩
  have e:∀ u∈V, (v u).val=faux A u:=fun u t=>by simp [v,t]
  have hx:= h.fuel i j V hV v ((faux_diff A).differentiableOn.congr e)
  exact hx.congr (fun u t=> congrArg (fun x=> F x i j) (e u t).symm)

lemma kernel_germ (h:Piece e S C F)(he:0<e)
    (p:∀ i∈leaks S, A i=A' i) : drip F A i j =ᶠ[𝓝 0] drip F A' i j := by
  filter_upwards [petals_open he A, petals_open he A'] with t hx hy
  set x:= profile (petals A t)
  set y:= profile (petals A' t)
  have hf :fare S x y=0 := by
    refine Finset.sum_eq_zero fun i hi=>?_
    have hv:x i=y i:=by funext b; simp_rw [x,y,profile,petals,p i hi]
    simp [hv]
  have hm:= (h.expo i j).variation ⟨x,hx⟩ ⟨y,hy⟩
  change ‖F x i j-F y i j‖≤_*(fare S x y/_) at hm
  rw [hf,zero_div,mul_zero,norm_le_zero_iff] at hm
  exact sub_eq_zero.mp hm

lemma kernel_raw (h:Piece e S C F)(s:Sap e ρ){B:ℝ}
    (hB:1≤B)(p:∀ x, |A x|≤B) :
    Bud (drip F A i j) ∧ ∀ k,
    ‖wad F A i j k‖ ≤ B^2/ρ^2 * C i j := by
  have b := zero_lt_one.trans_le hB
  have hxy(u:ℂ)(t:u∈closedBall (0:ℂ) (ρ/B)) : faux A u ∈Openc _ e :=
    faux_open s b p u ((mem_closedBall_zero_iff.mp t).trans_lt
      (div_lt_div_of_pos_right (lt_add_of_pos_right _ s.pos) b))
  have hf(u:ℂ)(t:u∈closedBall (0:ℂ) (ρ/B)):
      DifferentiableAt ℂ (fun v=> F (faux A v) i j) u :=
    (kernel_hol h isOpen_ball (fun v hv=>faux_open s b p v (mem_ball_zero_iff.mp hv))
      _ (vacancy0 _ s.ready)).differentiableAt
      (isOpen_ball.mem_nhds (mem_ball_zero_iff.mpr ((mem_closedBall_zero_iff.mp t).trans_lt
      (div_lt_div_of_pos_right (lt_add_of_pos_right _ s.pos) b))))
  have hv:DiffContOnCl ℂ (fun u=> F (faux A u) i j) (ball (0:ℂ) (ρ/B)) :=
    ⟨fun u hu=> (hf u (ball_subset_closedBall hu)).differentiableWithinAt,
     fun u hu=> (hf u (closure_ball_subset_closedBall hu)).continuousAt.continuousWithinAt⟩
  have g:=Bloom.cauchy (div_pos s.pos b) ((div_le_one b).mpr (s.one.trans hB)) hv
    (fun u hu=> kernel_bound h (hxy u hu))
  simp_rw [faux_real] at g
  refine ⟨g.1, fun k=> (g.2 k).trans_eq ?_⟩
  rw [div_pow,div_div_eq_mul_div]; ring

lemma kernel_jet (h:Piece e S C F)(s:Sap e ρ){B:ℝ}
    (hB:1≤B)(p:∀ x∈leaks S, |A x|≤B) :
    Bud (drip F A i j) ∧ ∀ k, ‖wad F A i j k‖ ≤ B^2/ρ^2*C i j := by
  let Z: StemA N:=fun x=>if x∈leaks S then A x else 0
  have hz x:|Z x|≤B:=by by_cases t:x∈leaks S; simpa [Z,t] using p x t; simp [Z,t,zero_le_one.trans hB]
  have y:drip F A i j =ᶠ[𝓝 0] drip F Z i j:= kernel_germ h s.ready fun _ hx=>(if_pos hx).symm
  obtain ⟨a,g⟩:= kernel_raw (i:=i) (j:=j) h s hB hz
  refine ⟨(a.bloom.congr y).1,?_⟩
  rw [wad, bud_congr y]; exact g

lemma kernel_free (h:Piece e S C F) (p:C i j=0)(he:0<e) (A:StemA N):
    Bloom (drip F A i j) 0 := by
  have hz : drip F A i j =ᶠ[𝓝 0] fun _=>0:=by
    filter_upwards [petals_open he A] with t ht
    exact norm_le_zero_iff.mp ((kernel_bound h ht).trans_eq p)
  rw [show (0:Three ℂ)=![0,0,0] from funext fun k=>by fin_cases k<;>rfl]
  exact (Bloom.constant _).congr hz

lemma kernel_bud (h:Piece e S C F) (he:0<e):
    Bud (drip F A i j) := by
  obtain ⟨ρ,p⟩:= sap he
  exact (kernel_raw h p (le_max_left _ _) (fun x=>le_max_of_le_right (norm_le_pi_norm A x))).1

abbrev Band (N:Side) := Seal (Site (More N))
/-- Display a Crown, with total representative of pieces reused only on Openc. -/
structure Bough (e a r:ℝ) (F:Oil N) where
  f : Band N → Oil N
  c : Band N → Toll (Single N)
  pie : ∀ S,Piece e S (c S) (f S)
  led : Ledger a c r
  shows : ∀ x∈Openc _ e, F x = ∑ S,f S x

variable {a r:ℝ}

lemma bough_exists (sf:Solo a r F e) :
    Nonempty (Bough e a r F) := by
  classical
  obtain ⟨G,C,h,q,j⟩:=sf
  let H:Band N→Oil N:= fun S x=> if hx:x∈Openc _ e then G S ⟨x,hx⟩ else 0
  have hu(S) : G S= fun x=> H S x.val:=funext fun x=> by simp [H,x.property]
  refine ⟨⟨H,C,fun S=>(by have p:=h S; rw [hu S] at p;exact p),q,fun x t=>?_⟩⟩
  calc
    _ = _ := j ⟨x,t⟩
    _ = _ := Finset.sum_congr rfl fun S _=> congrFun (hu S) ⟨x,t⟩

namespace Bough
variable (T:Bough e a r F)
def sift (s:Finset (Band N)) : Oil N:= fun x=> ∑ S∈s, T.f S x
lemma sift_drip (s:Finset (Band N)) (A:StemA N)(i j:Single N)(he:0<e):
    Bloom (drip (T.sift s) A i j) (∑ S∈s, wad (T.f S) A i j) := by
  have h:drip (T.sift s) A i j= fun u=> ∑ S∈s, drip (T.f S) A i j u:=by
    funext; simp [drip,sift, Matrix.sum_apply]
  rw [h]
  exact Bloom.sum s fun S _=> (kernel_bud (T.pie S) he).bloom

lemma drip_sum (A:StemA N)(i j:Single N)(he:0<e):
    Bloom (drip F A i j) (∑ S, wad (T.f S) A i j) := by
  apply (T.sift_drip _ _ _ _ he).congr
  filter_upwards [petals_open he A] with x hx
  exact congrArg (fun Q:Op (Single N)=>Q i j) (T.shows _ hx)

lemma total (i j:Single N): saleM a T.c i j ≤ r:=
  (Finset.single_le_sum
    (fun x (_:x∈Finset.univ)=>sale_nn (fun S=> (T.pie S).nonn) a i x)
    (Finset.mem_univ j)).trans (T.led.rows i)
end Bough

lemma solo_bud (sf:Solo a r F e) (he:0<e) : Bud (drip F A i j) :=
  let T:=(bough_exists sf).some
  (T.drip_sum _ _ _ he).1
