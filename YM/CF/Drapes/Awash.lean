import YM.CF.Drapes.Lack
set_option autoImplicit false
noncomputable section
namespace YM.CF.Drapes
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Topology
open Finset Function Fock Filter Branch
attribute [local instance] opCStarAlgebra
lemma clips {r a c v:ℝ}(hr:0≤r)(ha:0<a)(hc:0≤c)(hv:0<v): ∃ (w:ℕ)(ρ d:ℝ), 0<ρ∧ρ<1∧0<d∧ d≤a/2∧
    let D:= Real.exp (-a/2*w)*r; let V:= (c*(((((w+w):ℕ):ℝ)+1)^4)); V*Real.exp (d*V)*(D+r*(2*ρ))+D≤v:=by
  let D(w:ℕ):=Real.exp (-a/2*w)*r; let V(w:ℕ):= c*(((((w+w):ℕ):ℝ)+1)^4)
  have hV(w):0≤ V w:=by unfold V; positivity
  let u:= Real.exp (-a/2); have hp:= Real.exp_pos (-a/2); have hh:u<1:= Real.exp_lt_one_iff.mpr (by linarith)
  have he0(w:ℕ): D w=u^w*r:=by unfold D u; rw [mul_comm (-a/2), Real.exp_nat_mul]
  have he: Summable D:=by simp_rw [show D=fun w=>u^w*r from funext he0]; exact (summable_geometric_of_lt_one hp.le hh).mul_right _
  have hg:Summable (fun i=> V i*D i):=by
    have hx: Summable (fun i:ℕ=>(i:ℝ)^4*u^i):= summable_pow_mul_geometric_of_norm_lt_one _ (by rw [Real.norm_of_nonneg hp.le]; exact hh)
    refine (((hx.mul_left (c*81*r)).add (he.mul_left c)).of_nonneg_of_le ?_ ?_ ) -- at i=0 issue
    · intro i; unfold V D; positivity
    intro i; by_cases hi:i=0
    · simp [hi,V,D]; -- edit
    have H : (1:ℝ)≤ i:=by exact_mod_cast (show 1≤ i by omega)
    calc
     _ ≤ (c*(3*(i:ℝ))^4) * D i := by unfold V; exact mul_le_mul_of_nonneg_right (by gcongr; push_cast; linarith) (by unfold D; positivity)
     _ = c*81*r*((i:ℝ)^4*u^i) := by rw [he0]; ring
     _ ≤ _ := le_add_of_nonneg_right (by unfold D; positivity)
  obtain ⟨w,h⟩:= ((show Tendsto (fun i=> V i*D i+D i) atTop (𝓝 0) by simpa using (hg.add he).tendsto_atTop_zero).eventually (gt_mem_nhds hv)).exists
  let f (d:ℝ) := V w*Real.exp (d*V w)*(D w+r*(2*d))+D w; have ht : f 0<v := by change _+_<v at h; simpa [f] using h
  obtain ⟨m, hm,hy⟩:= Metric.continuousAt_iff.mp (show Continuous f from by unfold f;fun_prop).continuousAt (v-f 0) (sub_pos.mpr ht)
  let d:=min (m/2) (min (a/2) (1/2))
  have hr':0<d:= by unfold d; simp; constructor <;> positivity -- inspect
  have hs:=min_le_right (m/2) (min (a/2) (1/2))
  have hy : |f d-f 0|< v-f 0:= hy (show dist d 0 < m from (by rw [Real.dist_eq,sub_zero,abs_of_pos hr']; exact (min_le_left ..).trans_lt (by linarith)))
  exact ⟨w,d,d,hr',lt_of_le_of_lt (hs.trans (min_le_right ..)) (by norm_num),hr',hs.trans (min_le_left ..),show f d≤v from (by linarith [(abs_lt.mp hy).2])⟩
variable {I Y D E G : Type*}[Fintype I][Fintype Y][DecidableEq I][DecidableEq Y][TopologicalSpace D][TopologicalSpace E]
variable {b: Stage Y I D G}{s t:Tag b}{b':Stage Y I E G}{s' t':Tag b'}{L:License D}{L':License E}{R: E→D}{e d a r y v c:ℝ}{A:Raw D I}
lemma Towards.smaller (p:Towards b L b' L' R e) (hA:Crown L s t a r A)(w:ℕ)(he:e≤1)(hq:0<d)(hd:d≤a/2)(h: Capacity b' c)(hc:0≤c)
  (H:s.run=s'.run)(V:t.run=t'.run)(X:D)(hz:A X=0)(hy:0≤y)
  (ha:∀ q i,∃ g:G,b.eval (bay b.F (b.home i) (w+w)) (b.drive g (R q)) X ≤ y)
  (Hk: let D:=Real.exp (-a/2*w)*r; let W:= c*(((((w+w):ℕ):ℝ)+1)^4); W*Real.exp (d*W)*(D+r*(y+|e|))+D≤v) :Crown L' s' t' d v (A ∘ R):=by
  obtain ⟨F,C,he1,hq1,hx⟩:=hA
  have hu: 0≤a:=by linarith
  have h2:=p.dusk F C he1 hq1 h hc hu X w (hx X) he H V y hy 0 (by rfl) (by simp [hz]) ha hq.le
  simp only [zero_add] at h2
  have ht:= (p.bring H V (Crown.tail (v:=w) F C he1 hq1 hx hu) he).drop hd
  have hh := (h2.plus ht).books Hk
  convert hh using 1; ext1 x; change A (R x)= lop F w _ + (_-lop F w (R x)); abel
end YM.CF.Drapes
namespace YM.CF.Drapes
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Topology
open Finset Function Fock Filter Branch
attribute [local instance] opCStarAlgebra
variable {I Y D G : Type*}[Fintype I][Fintype Y][DecidableEq I][DecidableEq Y][TopologicalSpace D]
variable {b: Stage Y I D G}{s t:Tag b}{L:License D}{a r:ℝ}{A:Raw D I}
lemma Crown.impose (h:Crown L s t a r A)(f:D→D)(hp:Continuous f) (e:∀ g d,f (b.drive g d) = b.drive g (f d))(hq:∀S x y,b.eval S (f x) (f y)=b.eval S x y)(hk:∀ g:D→ℂ,L.valid g→L.valid (fun x=> star (g (f x)))) : Crown L t s a r (fun x=> star (A (f x))) :=by
  obtain ⟨F,C,p,l,Q⟩:=h
  let M (S:Seal Y)(x:D):=star (F S (f x))
  have hl(S):Suite L t s S (fun i j=> C S j i) (M S):=by
    refine ⟨?_,fun i j=>hk _ ((p S).fuel j i)⟩
    have hT:Ticket s t S (C S) (fun x=> F S (f x)):=by
      refine ⟨fun i x=> by rw [e]; exact (p S).frame ..,fun i j=>?_⟩
      have hx := (p S).expo i j
      exact ⟨hx.positive,hx.triggered,fun x=> hx.bounded _,fun x y=> by rw [← hq]; exact hx.variation .., hx.connected.comp hp⟩
    exact hT.starT
  exact ⟨M,_,hl,l.flip,fun x=> by dsimp only [M]; rw [Q,star_sum]⟩
end YM.CF.Drapes
