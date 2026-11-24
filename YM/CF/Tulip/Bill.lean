import YM.CF.Tulip.Lens
import YM.CF.Cubes.Ferry
set_option autoImplicit false
noncomputable section
namespace YM.CF.Tulip
open Function Filter Lattice Laurent Bloch Next.Free Metric Lat Finset Branch Cube Tenant SU Rush Drapes
open scoped Topology Matrix BigOperators Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {N : Side}
def markD (o y:Site N) := route (0:Cover) (lift (y-o)) 1
def hue (U:Bkg N)(o:Site N)(y:Site N) : E:= travel U o (markD o y)
def priceF (k:ℕ) (e:ℝ):=8*((4*(k:ℝ)+1)^2)*e
lemma gauge_light (o y:Site N)(i:Axis)(w:ℕ)(hw : y∈bay (terr N) o w) (hm:y+step i∈bay (terr N) o w) (hk:2*w+2<N.val) (U:Bkg N)(e)(he:0≤e)(h: Guard U e): ‖brand (gauge (hue U o) U (y,i))-1‖≤ priceF w e:=by
  have hx : separation y o≤ w:=by rw [separation_comm]; exact (bay_mem _).mp hw
  have ht : separation (y+step i) o≤ w:=by rw [separation_comm]; exact (bay_mem _).mp hm
  have HS{x:Site N}(hh:separation x o≤w): (markD o x).length≤ 4*w:=by apply route_size; exact fun i=> (by simpa using (component_le (x-o) i).trans hh)
  let A:=markD o y++[posDir i]; let B:=markD o (y+step i)
  have hp(x:Site N): stop (0:Cover) (markD o x)=lift (x-o):=route_end ..
  have hf:stop (0:Cover) A=stop (0:Cover) B:=by
    unfold A B; rw [stop_append,hp,stop,Step.vec_pos, stop, hp]; symm; apply lift_eq_iff.mpr; refine ⟨by simp; abel,fun j=>?_⟩
    have hz:= (component_le (y-o) j).trans hx; simp only [step_apply,Pi.add_apply]; split_ifs <;> omega
  have hg(x:Site N):stop o (markD o x)=x:=by -- using previous lemmas
    nth_rw 1 [← wrap_lift o]; rw [← wrap_stop_cover, ← add_zero (lift o),stop_trans]; simp only [hp,map_add,wrap_lift]; abel
  have hx': gauge (hue U o) U (y,i)= travel U o A*(travel U o B)⁻¹:=by unfold A; rw [travel_append,hg,travel,Step.pos_read,travel,mul_one]; rfl -- check
  have hv := HS hx; have hv':B.length ≤4*w:=HS ht; have he': A.length≤ 4*w+1:=by unfold A; simpa using hv
  have hh' : 4*(A.length:ℝ)^2*e+4*(B.length:ℝ)^2*e≤priceF w e:=by
    unfold priceF
    rw [show (8:ℝ)*(_)*e= 4*(4*(w:ℝ)+1)^2*e+4*(4*(w:ℝ)+1)^2*e by ring]
    have hk:(A.length:ℝ)≤4*(w:ℝ)+1:= by exact_mod_cast he'
    have ht:(B.length:ℝ)≤ 4*(w:ℝ):= by exact_mod_cast hv'
    gcongr; linarith
  rw [Prod.norm_def]; apply max_le
  · apply le_trans _ hh'; have hy:=near_hop he h.2 o A B hf; rw [hx']
    rw [Cube.cmp_g,Cube.cmp,map_one] at hy; exact hy
  apply le_trans _ hh'; have hy:=near_hop he h.1 o A B hf; rw [hx']; rw [Cube.cmp_g,Cube.cmp,map_one] at hy; exact hy
lemma branch_cost (x:Stem N)(e:ℝ)(w:ℕ)(hw:2*w+2<N.val)(d:x∈Openc N e)(o:Site N):
    ∃ g:Site N→ E, fare (bay (terr N) o w) (relayg g x) (1:Stem N)≤ (64*((w:ℝ)+1)^4)*(e+priceF w e):=by
  obtain ⟨U,h,f⟩:=d; have he:= (norm_nonneg _).trans_lt f
  let g:= hue U o
  let S:=bay (terr N) o w; have hx:= profile_g g U
  refine ⟨g,?_⟩; apply le_trans (sum_le_sum (g:=fun _=>e+priceF w e) ?_)
  · rw [sum_const,nsmul_eq_mul]; have hv:S.card*4≥(leaks S).card:= by
      calc
        _ ≤ Finset.card (S ×ˢ (Finset.univ: Finset Axis)):= card_le_card fun i hi=> mem_product.mpr ⟨(mem_filter.mp hi).2.1, mem_univ _⟩
        _ = _:=by simp [Axis]
    have hh := Tenant.reach o w
    have hp: (((leaks S).card:ℕ):ℝ)≤ S.card*4:=by exact_mod_cast hv
    exact mul_le_mul_of_nonneg_right (by change (S.card:ℝ)≤_ at hh; linarith only [hh,hp]) (by unfold priceF; positivity)
  intro j l; apply (pi_norm_le_iff_of_nonneg (by unfold priceF; positivity)).mpr; intro u
  have hh: ‖(relayg g x) j u-(relayg g (profile U)) j u‖≤e :=(le_trans (norm_le_pi_norm ((relayg g x-relayg g (profile U)) j) u) ((norm_le_pi_norm (relayg g x-relayg g (profile U)) j).trans (by rw [relayg_eq]))).trans f.le -- tune
  apply le_trans (norm_sub_le_norm_sub_add_norm_sub ((relayg g x) j u) ((relayg g (profile U)) j u) _)
  refine add_le_add hh ?_
  rcases j with ⟨y,i⟩
  have hy:= gauge_light o y i w (mem_filter.mp l).2.1 (mem_filter.mp l).2.2 hw _ _ he.le h; rw [←hx]
  cases u
  · change ‖star (brand _)-1‖≤ _; rw [show ∀ x:Twig, ‖star x-1‖=‖x-1‖ from fun x=>by rw [← norm_star (x-1),star_sub,star_one]]; exact hy
  exact hy
end YM.CF.Tulip
