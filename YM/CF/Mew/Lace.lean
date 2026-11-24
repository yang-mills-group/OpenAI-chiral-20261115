import YM.CF.Mew.Stream
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
namespace YM.CF.Mew
open Function Set Metric Filter Complex MeasureTheory Finset
open scoped Topology ContDiff BigOperators Matrix Classical
variable {I E F A :Type*}[Fintype I][DecidableEq I][MeasurableSpace A][NormedAddCommGroup E][NormedSpace ℂ E][CompleteSpace E][NormedAddCommGroup F][NormedSpace ℂ F][CompleteSpace F]
variable {f g u v:Key I→E}
lemma River.cong(h:River f)(p:EqOn g f (hill I)):River g:=⟨h.shore.congr p,fun i hi j k hk=> (h.slope i hi j k hk).congr_of_eventuallyEq (Eventually.mono (isOpen_ball.mem_nhds hk) (fun q hv=>p (fill_I hi _ (ball_subset_closedBall hv))))⟩
lemma twist_C (i:I)(p:EqOn f g (hill I)):EqOn (cutI f i) (cutI g i) (hill I):=fun x hx=> integral_congr_ae (ae_of_all _ fun θ=> congrArg (fun v:E=> _ • v) (p (fill_I hx _ (homeC _))))
lemma dunk_C {i j:I}(v:i≠j): EqOn (cutI (f∘ dune i) j) (cutI f j ∘ dune i) (hill I):=fun x hx=> integral_congr_ae (ae_of_all _ fun θ=>by change _ • f (update _ i 0)=_ • f (update (update _ i 0) _ _); rw [update_comm v.symm])
lemma centre(i:I): update (0:Key I) i 0=0:= update_eq_self _ _
lemma roots : (0:Key I)∈ hill I:=mem_closedBall_self zero_le_one
lemma dune_P (i:I):MapsTo (dune i) (hill I) (hill I):= fun _ hx=>fill_I hx _ (mem_closedBall_self zero_le_one)
lemma dub_V (h:River f)(hp:River g):River (fun i=>f i+g i):=⟨h.shore.add hp.shore,fun i v j k hk=> (h.slope i v j k hk).add (hp.slope i v j k hk)⟩
lemma sc_V (h:River f)(L:E→L[ℂ] F):River (L∘f):=⟨L.continuous.comp_continuousOn h.shore,fun i v j k hk=> L.differentiableAt.comp k (h.slope i v j k hk)⟩
lemma zeroR(c:E):River (fun _:Key I=>c):=⟨continuousOn_const,fun _ _ _ _ _=>differentiableAt_const _⟩
-- order-specific partials. trade no permutation assumption.
def lance (f:Key I→E) : List I→Key I→ E | []=> f | i::l=>lance (cutI f i) l
lemma laced(h:River f)(u:List I):River (lance f u):=by
 induction u generalizing f with
 | nil=> exact h
 | cons i l ih=> exact ih (h.flow i)
lemma lance_bound(h:River f)(l:List I){C:ℝ}(p:∀ i∈hill I,‖f i‖≤C): ∀ x∈hill I, ‖lance f l x‖ ≤ C:=by induction l generalizing f with|nil=>exact p|cons i l ih=> exact ih (h.flow i) (rind_x h i p)
lemma lace_C (i: List I)(p:EqOn f g (hill I)):EqOn (lance f i) (lance g i) (hill I):=by induction i generalizing f g with|nil=>exact p|cons i l ih=> exact ih (twist_C i p)
lemma lance_dune(i:I)(l:List I)(h:i∉l): EqOn (lance (f∘dune i) l) (lance f l∘ dune i) (hill I):=by induction l generalizing f with|nil=>exact fun _ _=>rfl|cons j l ih=> exact EqOn.trans (lace_C l (dunk_C (fun v:i=j => h (by simp [v])))) (ih (fun p=> h (by simp [p])))
abbrev tipI (f:Key I→E)(s:List I): E:= lance f s 0
lemma tip_V (i:I)(l:List I)(h:i∉l): tipI (f∘dune i) l=tipI f l:= (lance_dune _ _ h roots).trans (congrArg (lance _ l) (centre i))
lemma fork_T(h:River f)(p:River g)(i:I):EqOn (cutI (fun x=>f x+g x) i) (fun x=>cutI f i x+cutI g i x) (hill I):= fun _ x=>(mitt (dub_V h p) x i).deriv.symm.trans ((mitt h x i).add (mitt p x i)).deriv
lemma fork_H(h:River f)(p:River g)(i:List I):EqOn (lance (fun x=>f x+g x) i) (fun x=>lance f i x+lance g i x) (hill I):=by induction i generalizing f g with|nil=>exact fun _ _=>rfl|cons i l ih=> exact (lace_C _ (fork_T h p i)).trans (ih (h.flow i) (p.flow i))
lemma tip_A(h:River f)(p:River g)(i:List I): tipI (fun x=>f x+g x) i=tipI f i+tipI g i:=fork_H h p i roots
lemma sim_H(h:River f)(L:E→L[ℂ]F)(i:List I):EqOn (lance (L∘f) i) (fun x=>L (lance f i x)) (hill I):=by
 induction i generalizing f with
 | nil=> exact fun _ _=>rfl
 | cons j i ih=>
   have hx:EqOn (cutI (L∘ f) j) (L ∘ cutI f j) (hill I):= fun z u=>(mitt (sc_V h L) u j).deriv.symm.trans (L.hasFDerivAt.comp_hasDerivAt _ (mitt h u j)).deriv
   exact (lace_C i hx).trans (ih (h.flow j))
lemma tip_C(h:River f)(p:ℂ)(i:List I): tipI (fun x=>p • f x) i=p • tipI f i:=sim_H h (p • ContinuousLinearMap.id ℂ E) i roots
lemma tip_0(i:List I): tipI (fun _:Key I=>(0:E)) i=0:=by simpa using (tip_C (f:=fun _:Key I=>(0:E)) (zeroR _) 0 i)
lemma lanceInt(μ:Measure A)(F: Key I → A → E)(hp:∀ i:A,River (fun j=>F j i)){v:A→ℝ}(hv:Integrable v μ)(hm:∀ z∈hill I, AEStronglyMeasurable (F z) μ)(ht:∀ z∈hill I,∀ i,‖F z i‖ ≤ v i)(l:List I)(x:Key I)(hx:x∈hill I):Integrable (fun a=>lance (fun j=>F j a) l x) μ ∧ lance (fun z=>∫ i,F z i∂μ) l x= ∫ a,lance (fun j=>F j a) l x∂μ:=by
 induction l generalizing F with
 | nil=> exact ⟨hv.mono' (hm _ hx) (ae_of_all _ (ht _ hx)), rfl⟩
 | cons i l ih=>
    have he(z hz):= wind_eq μ F hp hv hm ht z hz i; let G (x:Key I)(a:A):= cutI (fun y=> F y a) i x
    obtain ⟨h,p⟩:= ih G (fun a=> (hp a).flow i) (fun j p=> (he j p).1.aestronglyMeasurable) fun j p a=> rind_x (hp a) i (fun z p=>ht z p a) j p
    exact ⟨h,(lace_C _ (show EqOn (cutI _ i) (fun x=>∫ a,G x a∂μ) (hill I) from fun z v=> (he z v).2) hx).trans p⟩ -- cannot infer f
end YM.CF.Mew
