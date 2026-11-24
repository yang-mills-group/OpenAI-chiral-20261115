import YM.SU5.Selected.SpatialCard
import YM.SU5.Selected.PeakMotion
/-!
# CP5. Mixing criterion exploiting uniform tail Cauchy

Used with two-axis interchange. Limits in literal shifts -- not averaged. Also WOT convergence
in other coordinates chosen arbitrarily; obtain absence of *additional grade invariant states* in any axis motion.
-/
set_option autoImplicit false
set_option quotPrecheck false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.SelectionAnalysis
open Function Set Filter Metric NormedSpace
open CF.Buffered.Afterglow.Tower MeshClock Germ Vacancy ContinuousLinearMap
open scoped Topology InnerProductSpace NNReal ENNReal Classical
variable {H:Hilbert}

namespace Sunbelt
variable {a:Axis}{M:Mesh}(X:Sunbelt a (marks M) H) (S : OS.Semigroup H a)
local notation "A"=> {v:Axis // v ≠ a}
local notation "P"=> X.track
local notation "Γ" => marks M
local notation "U" k:max t:max=> (X.track.crew k).play t
local notation "Ω" x:max => X.plane x
local notation "fΛ"=> Axis → Γ
local notation "χ" v:max=> show A→Γ from fun k=> v k.val
local notation "E'" n:max=> show ℝ≥0 from Real.toNNReal (show ℝ from ((n:Γ):ℝ))
-- fold transport tools
lemma raw_price (t : List A) (u : A→ Γ) (x:H) : ‖(P).raw t u x‖≤ ‖x‖:=by
 induction t with
 | nil=> exact le_rfl
 | cons a t ih=> rw [Alliance.raw_step,ContinuousLinearMap.comp_apply]; exact (Players.pulls _ _ _).trans ih
lemma raw_reverse (t:List A) (u:A→ Γ): ((P).raw t u).adjoint=(P).raw t (-u):=by
 induction t with
 | nil=> simp_rw [Alliance.raw_nil]; exact ContinuousLinearMap.adjoint_id
 | cons i t ih=> rw [Alliance.raw_step,Alliance.raw_step,ContinuousLinearMap.adjoint_comp,ih,Players.neg_adjoint, Pi.neg_apply,Alliance.hard _ _ _ (fun j _ s=> (P).cCom ..)]

variable (e:X.heat=S.E) (ind : ∀ (k:{v:Axis//v ≠ a})(v:marks M)(t:ℝ≥0), ((X.track.crew k).play v).comp (S.E t)=(S.E t).comp ((X.track.crew k).play v))
include e
lemma plane_price (u : fΛ) (x : H) : ‖(Ω u) x‖≤ ‖x‖:= by
  unfold plane; rw [e,ContinuousLinearMap.comp_apply]; exact ((S.E _).le_opNorm _).trans ((mul_le_of_le_one_left (norm_nonneg _) (S.shrinks _)).trans (X.raw_price ..))
lemma plane_zero : X.plane 0=ContinuousLinearMap.id ℂ _:= by unfold plane; rw [e,Pi.zero_apply,show ((0:Γ):ℝ)=0 from rfl, Real.toNNReal_zero,S.eZero]; change (ContinuousLinearMap.id ℂ _).comp ((P).raw X.list 0)=_; rw [Alliance.raw_zero]; rfl

include ind
lemma plane_cross (k:A)(v:Γ)(x:fΛ) : (U k v).comp (Ω x)= (Ω x).comp (U k v):=by
  unfold plane; rw [e]; exact (Alliance.slide (S.E _) _ (U k v) (ind k v _).symm (Alliance.hard _ _ _ (fun j _ w=> (P).cCom ..) _)).symm
lemma plane_reverse (x:fΛ) : (Ω x).adjoint= Ω (Function.update (-x) a (x a)):=by
  have hr : χ (Function.update (-x) a (x a)) = -(χ x):=funext (fun i:A=> update_of_ne i.property ..)
  unfold plane; rw [Function.update_self,e,ContinuousLinearMap.adjoint_comp,S.sym, X.raw_reverse,hr,Alliance.hard _ _ _ (fun i _ t=> ind ..)]

omit ind
omit e in
/-- *all* other coordinates, time still nonnegative. No continuity implied at finite shifts. -/
def Coasts (k:{v:Axis//v≠a})(x y:H) : Prop := ∀ ε:ℝ,0<ε→ ∃ t:ℝ,
    ∀ (u:fΛ)(p q:Γ), t ≤ (p:ℝ) → t ≤ (q:ℝ) → 0 ≤ (u a:ℝ) →
      ‖inner ℂ x (X.plane (Function.update u k.val p) y) - inner ℂ x (X.plane (Function.update u k.val q) y)‖ ≤ ε
local notation "T" k:max x:max y:max u:max p:max => inner ℂ x ((Ω (Function.update u (k:A).val p)) y)

lemma solidPair {D : Set (H.space × H.space)} (g:Dense D) (k:{b:Axis//b≠a})
    (h:∀ x∈ D,X.Coasts k x.1 x.2)(x y:H): X.Coasts k x y:=by
  intro ε hp; let d : ℝ:= ‖x‖+‖y‖+1; have hd:0<d:=by unfold d; positivity
  obtain ⟨⟨u,v⟩,hu,e0⟩:= Metric.mem_closure_iff.mp (g (x,y)) (min 1 (ε/4 / d)) (by positivity)
  let e1:= ε/4/d
  rw [Prod.dist_eq,max_lt_iff] at e0; have hv: ‖v‖ ≤ ‖y‖+1:=(norm_le_norm_add_norm_sub y v).trans (by exact add_le_add (le_refl _) (le_of_lt ((show ‖y-v‖ < min 1 e1 from (dist_eq_norm y v) ▸ e0.2).trans_le (min_le_left ..))))
  have price (V:H.Op) (p:∀ x:H,‖V x‖≤‖x‖) : dist (inner ℂ x (V y)) (inner ℂ u (V v))≤ ε/4:=by
     refine le_trans (dist_triangle _ (inner ℂ x (V v)) _) ?_
     rw [dist_eq_norm,dist_eq_norm, ← inner_sub_right, ← inner_sub_left, ←map_sub]
     refine (add_le_add (norm_inner_le_norm _ _) (norm_inner_le_norm _ _)).trans ?_
     have h1: ‖x-u‖≤e1:= (show ‖x-u‖ < min 1 e1 from (dist_eq_norm x u) ▸ e0.1).le.trans (min_le_right ..)
     have h2: ‖y-v‖≤e1:= (show ‖y-v‖ < min 1 e1 from (dist_eq_norm y v) ▸ e0.2).le.trans (min_le_right ..)
     refine (add_le_add (mul_le_mul_of_nonneg_left ((p _).trans h2) (norm_nonneg _)) (mul_le_mul h1 ((p _).trans hv) (norm_nonneg _) (by unfold e1; positivity))).trans_eq ?_
     rw [show ‖x‖*e1+_=e1*d from (by unfold d; ring),show e1*d=ε/4 from div_mul_cancel₀ _ hd.ne']
  obtain ⟨t,ht⟩:=h (u,v) hu (ε/2) (by positivity) -- tune invocation needs ε/2
  refine ⟨t,fun n p q l r s=> ?_⟩
  rw [← dist_eq_norm]
  apply (dist_triangle (T k x y n p) (T k u v n p) _).trans; apply (add_le_add_right (dist_triangle (T k u v n p) (T k u v n q) _) _).trans
  let W(v:Γ):=X.plane (Function.update n k.val v)
  have h₁:=price (W p) (X.plane_price S e _)
  have h₂:=price (W q) (X.plane_price S e _); rw [dist_comm] at h₂
  have h₃:dist (T k u v n p) (T k u v n q) ≤ ε/2:= by rw [dist_eq_norm]; exact ht n p q l r s
  exact (add_le_add h₁ (add_le_add h₃ h₂)).trans_eq (by ring)
-- limit identification via grade average. No resonance remains
local notation "L" s:max => spotter M X.track s
local notation "K" k:max t:max=> ((spotter M X.track t).move k).calm
omit e in
lemma notch_rises (v:ℝ) (n:ℕ) : ∃ a:ℕ,v ≤ (notch M n a:ℝ) := by
 obtain ⟨p,hp⟩:= exists_nat_gt (v/(mill M n :ℝ≥0).val); refine ⟨p,?_⟩; change _≤(p:ℤ)*(mill M n:ℝ≥0).val; exact le_trans ((div_lt_iff₀ (show 0<(mill M n:ℝ≥0).val from mill_pos ..)).mp hp).le (le_of_eq (by push_cast; rfl))

omit e in
lemma margin (s:ℕ) (k:A)(x y:H) (ε:ℝ)(e:0<ε) (v:X.Coasts k x y): ∃ t:ℝ, ∀(u:fΛ) (p:Γ), t ≤ (p:ℝ)→0≤ (u a:ℝ) → ‖ T k x y u p - T k x ((K k s) y) u 0 ‖ ≤ ε :=by
 obtain ⟨t,ht⟩:=v ε e; refine ⟨t,fun u p l g=>?_⟩
 let R:= (L s).move k; let C:= update u k.val 0; let E := (innerSL ℂ x).comp (Ω C)
 let A₀(n:ℕ):H:= Vacancy.Average.center (fun i:Fin (n+1)=> R.wind (n+i:ℤ) y)
 have he : Tendsto (fun i:ℕ=> ‖ T k x y u p-E (A₀ i)‖) atTop (𝓝 (‖ T k x y u p-E ((K k s) y)‖)):= (Filter.Tendsto.sub (tendsto_const_nhds (x:=T k x y u p)) (E.continuous.continuousAt.tendsto.comp (R.shifted (fun i : ℕ=> i) _))).norm
 refine le_of_tendsto he ?_; obtain ⟨i,q⟩:= notch_rises (M:=M) t s; filter_upwards [eventually_ge_atTop i] with n hn
 let f(v:ℤ):= notch M s v; let A':= T k x y u p
 change ‖A'-E (Vacancy.Average.center (fun i:Fin (n+1)=> R.wind (n+i:ℤ) y))‖ ≤ ε
 rw [← Average.natural]; nth_rw 1 [← Average.constant («A»:=Fin (n+1)) A']; rw [← Average.minus]
 apply Average.norm_worth; intro j
 have hE(v:ℤ) : E (R.wind v y)= T k x y u (f v):=by rw [carries_update]; rfl
 rw [hE]; refine ht u p _ l (q.trans ?_) g; exact (bell_le M s _ _).mpr (by omega)

omit X S e in
lemma notch_infinite(s:ℕ): Tendsto (fun n:ℕ=>(notch M s n:ℝ)) atTop atTop:= tendsto_atTop_atTop.mpr (fun b:ℝ=> by
  obtain ⟨i,t⟩:= notch_rises (M:=M) b s; refine ⟨i,fun _ v=>?_⟩; exact t.trans ((bell_le M s _ _).mpr (by omega)))
-- don't include e

lemma forward_one (x y:H)(k:A)(f:ℕ→Γ)(p:Tendsto (fun i=>(f i:ℝ)) atTop atTop) (s:ℕ)(v:X.Coasts k x y) : Tendsto (fun i=> inner ℂ x ((U k (f i)) y)) atTop (𝓝 (inner ℂ x ((K k s) y))) := by
  apply Metric.tendsto_nhds.mpr; intro ε h; obtain ⟨t,ht⟩:= margin X s k x y (ε/2) (by positivity) v
  filter_upwards [p.eventually_ge_atTop t] with i u
  have hv:=ht 0 (f i) u (by change (0:ℝ) ≤ 0; exact le_rfl)
  have hx: Function.update (0:fΛ) k.val 0=(0:fΛ):=Function.update_eq_self ..
  rw [X.carries_update, hx,X.plane_zero S e,ContinuousLinearMap.comp_apply,ContinuousLinearMap.id_apply,ContinuousLinearMap.id_apply] at hv
  rw [dist_eq_norm]; exact lt_of_le_of_lt hv (by linarith)
lemma tight_at_grade (k:A)(p:∀ x y,X.Coasts k x y) (r s:ℕ): (K k r)= (K k s):=by
 ext1 x; apply ext_inner_left ℂ; intro y
 let g (i:ℕ):= notch M 0 (i:ℤ); have h(n:ℕ):= forward_one X S e y x k g (notch_infinite (M:=M) 0) n (p y x); exact tendsto_nhds_unique (h r) (h s)
lemma all_calmed (k:A)(v:∀ x y,X.Coasts k x y)(x:H)(u:Γ)(r:ℕ): (U k u) ((K k r) x)=(K k r) x:=by
 obtain ⟨s,i,rfl⟩:= notch_exists _ u; rw [tight_at_grade X S e k v r s]; exact ((L s).move _).projected ..
lemma quiet (k:A)(x:H)(r:ℕ)(p:∀ x y,X.Coasts k x y) : (K k r) x=x ↔ ∀ u:Γ,(U k u) x=x:= ⟨fun t u=> by
   conv_lhs=>rhs; rw [← t]
   rw [X.all_calmed S e k p x u r]; exact t,fun p=>(((L r).move k).calm_mem x).mpr (fun v=> p _) ⟩ -- tactic block conv indentation
include ind
lemma calm_cross (k:A)(s:ℕ)(u:fΛ) : (K k s).comp (Ω u)=(Ω u).comp (K k s):=(((L s).move k).calm_commutes (fun _=>(X.plane_cross S e ind k _ u).symm)).symm
lemma symmetric_calm(k:A)(s:ℕ)(u:fΛ)(x y:H): inner ℂ ((K k s) y) ((Ω u) x)= inner ℂ y ((Ω u) ((K k s) x)):= ((L s).stages k y _).trans (congrArg (inner ℂ y) (congrArg (fun f:H.Op=> f x) (X.calm_cross S e ind k s u)))
omit e in
lemma calm_heat (k:A)(s:ℕ)(u:ℝ≥0) : (K k s).comp (S.E u)=(S.E u).comp (K k s):=(((L s).move k).calm_commutes (fun _=>(ind k _ u).symm)).symm
lemma symmetric_mix (k:A)(x y:H)(r:ℕ)(p:∀ x y,X.Coasts k x y)(ε:ℝ)(h:0<ε): ∃ t:ℝ,∀ u:fΛ,t≤ |(u k.val:ℝ)| → 0≤(u a:ℝ) → ‖inner ℂ x ((Ω u) y) - inner ℂ x ((Ω u) ((K k r) y))‖ ≤ ε:=by
 -- leave play factor since invariant
 have ht (x y:H): ∃ t:ℝ,∀ u:fΛ,t≤ (u k.val:ℝ)→ 0≤(u a:ℝ) → ‖inner ℂ x ((Ω u) y) - inner ℂ x ((Ω u) ((K k r) y))‖ ≤ ε:=by
    obtain ⟨t,ht⟩:= margin X r k x y ε h (p x y); refine ⟨t,fun u v q=> ?_⟩; specialize ht u (u k.val) v q
    rw [Function.update_eq_self] at ht
    have he : (Ω u) ((K k r) y)= (Ω (Function.update u k.val 0)) ((K k r) y):=by

       nth_rw 1 [← Function.update_eq_self k.val u]
       rw [X.carries_update,ContinuousLinearMap.comp_apply,X.all_calmed S e k p y (u _) r]
    rw [he]; exact ht
 obtain ⟨t,htx⟩:= ht x y; obtain ⟨t',hty⟩:= ht y x; refine ⟨max t t',fun u v q=>?_⟩
 let w := update (-u) a (u a)
 by_cases hp:0 ≤ (u k.val:ℝ)
 · exact htx u ((le_max_left ..).trans (v.trans_eq (abs_of_nonneg hp))) q
 have hu: (w k.val:ℝ) = |(u k.val:ℝ)|:=by unfold w; rw [abs_of_nonpos (le_of_not_ge hp),update_of_ne k.property]; rfl
 have hx:=hty w ((le_max_right ..).trans (v.trans_eq hu.symm)) (show 0≤ (w a:ℝ) from (by unfold w; rw [update_self]; exact q))
 have hf (x y:H): inner ℂ y ((Ω w) x)= star (inner ℂ x ((Ω u) y)):=by rw [← X.plane_reverse S e ind u, ContinuousLinearMap.adjoint_inner_right]; exact (inner_conj_symm ..).symm
 rw [←symmetric_calm X S e ind k r w, hf x y,hf x ((K k r) y), ← star_sub, norm_star] at hx
 exact hx
end Sunbelt
end YM.SelectionAnalysis
#print axioms YM.SelectionAnalysis.Sunbelt.symmetric_mix
