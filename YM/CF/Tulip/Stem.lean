import YM.CF.Tulip.Sill
set_option autoImplicit false
set_option linter.unusedVariables false
noncomputable section
namespace YM.CF.Tulip
open Function Filter Lattice Laurent Bloch Next.Free Metric Lat Finset Branch Cube Tenant SU Rush Drapes
open scoped Topology Matrix BigOperators Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {N: Side}
def shuttle (x : Stem N)(o:Site N) (d:Step):Twig:=x (d.used o) (!d.neg)
def track (x:Stem N)(o:Site N) : Walk→Twig
  | []=>1
  | a::w=>shuttle x o a*track x (o+a.vec) w
def traceP(o:Site N)(w:Walk):= (visits o w).toFinset
lemma shuttle_g (g:Site N→E)(x:Stem N)(o:Site N)(i:Step): shuttle (relayg g x) o i=brand (g o)*shuttle x o i*star (brand (g (o+i.vec))):=by obtain ⟨a,h|h⟩:=i <;> simp [shuttle,relayg,Step.used,Step.vec,sub_eq_add_neg]
lemma track_g (g:Site N→E)(x:Stem N)(o:Site N)(w:Walk):track (relayg g x) o w=brand (g o)*track x o w*star (brand (g (stop o w))):=by
  induction w generalizing o with
  | nil=> simp [track,stop,(brand_unit (g o)).2]
  | cons a w ih=> rw [track,track,shuttle_g,ih]; simp only [stop,mul_assoc]; rw [show ∀ x: Twig, star (brand (g _))* (brand (g (o+a.vec))*x)=x from fun x=>by rw [← mul_assoc,(brand_unit ..).1,one_mul]]
lemma track_pr (U:Bkg N)(o:Site N)(w:Walk): track (profile U) o w=brand (travel U o w):=by
  induction w generalizing o with
  | nil=> simp [track,travel,brand_one]
  | cons d w ih=>rw [track,travel,ih,brand_mul]; congr 1; obtain ⟨a,h|h⟩:=d <;> simp [shuttle,profile,Step.read,brand_inv]
@[simp] lemma track_id (o:Site N)(w:Walk):track 1 o w=1:=by induction w generalizing o <;> simp_all [track,shuttle]
lemma trace_source(o:Site N)(w:Walk):o∈traceP o w:=by cases w <;> simp [traceP,visits]
lemma trace_last (o:Site N)(w:Walk):stop o w∈traceP o w:=by induction w generalizing o <;> simp_all [traceP,visits,stop]
lemma trace_k (o:Site N)(w:Walk): (traceP o w).card ≤ w.length+1:=by
  apply (List.toFinset_card_le ..).trans; induction w generalizing o with
  | nil=> simp [visits]
  | cons d w ih=> simpa [visits] using ih (o+d.vec)
lemma trace_g (o:Site N)(w:Walk): Grove (terr N) (traceP o w) :=by
  induction w generalizing o with
  | nil=> simp only [traceP,visits,List.toFinset_cons,List.toFinset_nil,insert_empty]; exact .single _
  | cons d w ih=>
    rw [traceP,visits,List.toFinset_cons]; apply Grove.join (ih (o+d.vec)) (trace_source ..); rcases d with ⟨i,h|h⟩
    · exact oneTouch ..
    rw [Branch.Field.sym]; change separation (o+ -step i) o≤1
    have he:=oneTouch (o+ -step i) i; rw [show o + -step i + step i=o by abel] at he; exact he
lemma trace_next (o:Site N)(a:Step)(w): traceP (o+a.vec) w ⊆ traceP o (a::w):=by unfold traceP; rw [visits,List.toFinset_cons]; exact subset_insert ..
lemma trace_in (o:Site N)(a:Step)(w): a.used o ∈ leaks (traceP o (a::w)):=by
  have hp := trace_source o (a::w); have hz:= trace_next o a w (trace_source (o+a.vec) w)
  apply mem_filter.mpr; refine ⟨mem_univ _,?_⟩; obtain ⟨i,h|h⟩:=a
  · exact ⟨hp,hz⟩
  simp only [Step.used,Bool.true_eq, ↓reduceIte,sub_add_cancel]; rw [sub_eq_add_neg]; exact ⟨hz,hp⟩
lemma sh_inc (o:Site N) (a:Step)(x y: Stem N)(S:Seal (Site N))(h:a.used o∈leaks S): ‖shuttle x o a-shuttle y o a‖≤ fare S x y:=by
  have hv : ‖shuttle x o a-shuttle y o a‖≤‖x (a.used o)-y (a.used o)‖:=norm_le_pi_norm (x (a.used o)-y (a.used o)) (!a.neg)
  exact le_trans hv (Finset.single_le_sum (f:=fun i:Edges N=>‖x i-y i‖) (fun i _=>norm_nonneg _) h)
lemma track_size (e:ℝ)(he:0≤e)(o:Site N)(w:Walk)(x:Stem N)(h:x∈Openc N e): ‖track x o w‖ ≤(1+e)^w.length:=by
  induction w generalizing o with
  | nil=> simp [track]
  | cons a w ih=> simp only [track]; rw [List.length_cons,pow_succ']; exact (norm_mul_le ..).trans (mul_le_mul (seasonal e x h ..) (ih _) (norm_nonneg _) (by linarith))
lemma track_vol (e:ℝ)(he:0≤e)(o:Site N)(w:Walk)(x y:Stem N)(h:x∈Openc N e)(p:y∈Openc N e):
    ‖track x o w-track y o w‖ ≤ w.length * ((1+e)^w.length * fare (traceP o w) x y):=by
  induction w generalizing o with
  | nil=> simp [track]
  | cons a w ih=>
    let S:= traceP o (a::w); let X:= shuttle x o a; let Y:=shuttle y o a; let A:=track x (o+a.vec) w; let B:=track y (o+a.vec) w
    have hx:‖X*A-Y*B‖≤ ‖X-Y‖*‖A‖+‖Y‖*‖A-B‖:=by rw [show X*A-Y*B=(X-Y)*A+Y*(A-B) by rw [sub_mul,mul_sub]; abel]; exact (norm_add_le ..).trans (add_le_add (norm_mul_le ..) (norm_mul_le ..))
    have hh:‖A-B‖≤ w.length*((1+e)^w.length*fare S x y) := (ih (o+a.vec)).trans (by gcongr; exact fare_inc (trace_next o a w) x y)
    change ‖X*A-Y*B‖≤_
    calc
      _ ≤ _:=hx
      _ ≤ fare S x y*(1+e)^w.length + (1+e)*(w.length*((1+e)^w.length*fare S x y)):=add_le_add (mul_le_mul (sh_inc o a x y _ (trace_in ..)) (track_size e he _ w x h) (norm_nonneg _) (fare_t ..)) (mul_le_mul (seasonal _ _ p ..) hh (norm_nonneg _) (by positivity))
      _ ≤ _:=by rw [List.length_cons,pow_succ,Nat.cast_add_one]; change _≤ ((w.length:ℝ)+1)* (_ * fare S x y); nlinarith only [mul_nonneg he (mul_nonneg (fare_t S x y) (show 0≤(1+e)^w.length by positivity))]
lemma track_d (o:Site N)(w:Walk): Differentiable ℂ fun x:Stem N=>track x o w:=by
  induction w generalizing o with
  | nil=> exact differentiable_const _
  | cons a w ih=> exact Differentiable.mul (a:=fun x=> shuttle x o a) (by unfold shuttle; fun_prop) (ih _)
end YM.CF.Tulip
