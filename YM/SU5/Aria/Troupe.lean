import YM.SU5.Aria.Screens
/-! # Schedule cardinal independence: jitter once on *every* pose. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.Aria
open Set Function Filter Metric ContinuousLinearMap
open scoped Topology InnerProductSpace
variable {I T E:Type*}[NormedAddCommGroup E][NormedSpace ℂ E]
variable (g:I→Mist T)
namespace Casting
variable (d:I→ T)
section
variable [DecidableEq I]
-- atList recursion; use REV composition? set last first
def choice : List I→ Mist (I→ T)
| []=>.point d
| i::L=> (g i).via (fun x=>(choice L).onFn (fun k=> Function.update k i x))
lemma mean_cons (L:List I)(i:I)(f:(I→ T)→ E): (choice g d (i::L)).mean f=(g i).mean (fun x=> (choice g d L).mean (fun k=> f (Function.update k i x))):=by rw [choice,(g i).mean_via]; exact (g i).mean_congr _ ((g i).solves _ fun a=> (choice g d L).mean_onFn _ f)
lemma mean_order (L L':List I)(h:L.Perm L')(v:L.Nodup)(f:(I→ T)→ E): (choice g d L).mean f=(choice g d L').mean f:=by
 induction h generalizing f with
 | nil=> rfl
 | cons i h t=> rw [mean_cons,mean_cons]; refine (g i).mean_congr _ ((g i).solves _ fun a=>?_); exact t (List.nodup_cons.mp v).2 _
 | swap i j L=> have hu:i≠j:=Ne.symm (show j ≠ i from (by intro ht; exact (List.nodup_cons.mp v).1 (ht.symm ▸ List.Mem.head ..))); simp_rw [mean_cons]; rw [(g j).mean_comm (g i)]; congr 1; funext a; congr 1; funext b; congr 1; funext z; rw [update_comm hu] -- tune
 | trans a b i j=> exact (i v _).trans (j (a.nodup_iff.mp v) _)
lemma choice_fee (t:List I){p:I→ T→Prop}(h:∀ i∈ t,(g i).holds (p i)): (choice g d t).holds (fun b=> ∀ i∈ t,p i (b i)):=by
 induction t with
 | nil=> exact fun i t=>nomatch t
 | cons i t ih=>
   have hp:=ih fun j u=> h j (List.Mem.tail _ u)
   refine (Mist.hold_via ..).2 ((g i).promotes ?_ (h i (List.Mem.head ..))); intro x k; refine (Mist.hold_via ..).2 ((choice g d t).promotes ?_ hp); intro y z; change ∀ j ∈ (i::t), p j (Function.update y i x j)
   intro j t'; by_cases A:j=i; subst j; rw [Function.update_self]; exact k
   rw [Function.update_of_ne A]; exact z j ((List.mem_cons.mp t').resolve_left A)
private lemma mean_eval {H:Hilbert}(g:Mist T)(P:T→H.Op)(a:H): g.mean (fun i=> P i a)=g.mean P a:=by
 induction g with
 | point i=> rfl
 | midP B C i j=> rw [Mist.mean,i,j,Mist.mean]; rfl
private lemma prod_align {A:Type*}[Monoid A](P:I→T→A)(L:List I)(x y:I→T)(h:∀ i∈ L,x i=y i): (L.map (fun i=> P i (x i))).prod=(L.map (fun i=> P i (y i))).prod:=congrArg List.prod (List.map_congr_left (fun i hi=>by rw [h i hi]))
lemma mean_run {H:Hilbert}(P:I→T→ H.Op)(L:List I) (t:L.Nodup)(x:H): (choice g d L).mean (fun q=> (L.map (fun i=> P i (q i))).prod x)= (L.map (fun i=>(g i).mean (P i))).prod x:=by
 induction L with
 | nil=> rfl
 | cons i L ih=>
   obtain ⟨p,h⟩:=List.nodup_cons.mp t
   let D:= choice g d L; let B(q:I→T):=(L.map (fun i=> P i (q i))).prod x; let b:=(L.map fun i=> (g i).mean (P i)).prod x
   have hv:=ih h
   have he(q:I→T)(a:T): ((i::L).map fun k=> P k (Function.update q i a k)).prod x=P i a (B q):=by
     simp only [List.map_cons,List.prod_cons,Function.update_self]; change P i a (_)=_; unfold B; rw [prod_align P L _ q (fun j v=> Function.update_of_ne (show j ≠ i from fun w=> p (w ▸ v)) ..)]; rfl
   rw [mean_cons]; change (g i).mean (fun a=> D.mean (fun q=> ((i::L).map fun k=>P k (Function.update q i a k)).prod x))=((g i).mean (P i)) b; simp_rw [he,Mist.mean_linear' D B,show D.mean B=b from hv]; exact mean_eval ..
omit [NormedAddCommGroup E] [NormedSpace ℂ E] in
lemma costs_all {α:Filter E}(D:E→ I→Mist T)(z:E→I→T)(L:List I)(P:E→I→T→Prop)(t:∀ i∈L,∀ᶠ n in α,(D n i).holds (P n i)): ∀ᶠ n in α,(choice (D n) (z n) L).holds (fun b=>∀ i∈L,P n i (b i)):=by
 filter_upwards [(eventually_all_finset L.toFinset).mpr (fun i v=> t i (List.mem_toFinset.mp v))] with n h; exact choice_fee (D n) (z n) L fun i v=> h i (List.mem_toFinset.mpr v)
end
section analysis
open OS OS.Semigroup Metric
local notation "τ" p:max=> Real.toNNReal p
variable {i:Axis}{H:Hilbert}(S:OS.Semigroup H i)(C:H.Op)
lemma wrap_est {α β:ℝ} (U x T y:H.Op)(u:‖U‖≤1)(p:‖y‖≤1)(dx:dist x U≤ α)(dy:dist y T≤α)(h:‖C‖≤ β): dist (x.comp (C.comp y)) (U.comp (C.comp T)) ≤ α*β+β*α:=by
 rw [dist_eq_norm]; rw [dist_eq_norm] at dy dx
 rw [show x.comp (C.comp y)-U.comp (C.comp T)=(x-U)*C*y+U*(C*(y-T)) from ?_]
 apply (norm_add_le ..).trans; refine add_le_add ((norm_mul_le ..).trans ((mul_le_of_le_one_right (norm_nonneg _) p).trans ((norm_mul_le ..).trans (mul_le_mul dx h (norm_nonneg _) ((norm_nonneg _).trans dx))))) ((norm_mul_le ..).trans ((mul_le_of_le_one_left (norm_nonneg _) u).trans ((norm_mul_le ..).trans (mul_le_mul h dy (norm_nonneg _) ((norm_nonneg _).trans h)))))
 change x*(C*y)-U*(C*T)=_; noncomm_ring
lemma wrap_pay (U T:H.Op)(p:‖U‖≤1)(h:‖T‖≤1): ‖U.comp (C.comp T)‖ ≤ ‖C‖:= (opNorm_comp_le ..).trans ((mul_le_of_le_one_left (norm_nonneg _) p).trans ((opNorm_comp_le ..).trans (mul_le_of_le_one_right (norm_nonneg _) h)))
-- convergence strong product on cont part only
variable {B:Hilbert}(L:B→ₗᵢ[ℂ]H)
lemma run_tends (F:ℕ→ I→ H.Op)(T:I→B.Op)(R:I→ℝ)(l:List I)(x:B)(t:∀ i∈ l,∀ y:B,Tendsto (fun n=>F n i (L y)) atTop (𝓝 (L (T i y))))(h:∀ i∈ l,∀ n,‖F n i‖≤R i):
    Tendsto (fun n=> (l.map (F n)).prod (L x)) atTop (𝓝 (L ((l.map T).prod x))) := by
 induction l with
 | nil=>exact tendsto_const_nhds
 | cons i l ih=>
   have hw:= ih (fun j u=> t j (List.Mem.tail _ u)) (fun j u=> h j (List.Mem.tail _ u)); exact firmly (fun n=> F n i) ((norm_nonneg (F 0 i)).trans (h i (List.Mem.head ..) 0)) (Eventually.of_forall (fun n=>h i (List.Mem.head ..) n)) (t i (List.Mem.head ..) _) hw
lemma use_measured (D:Mist T)(P:T→H.Op)(x:H): D.mean (fun i=>P i x)=D.mean P x:= mean_eval ..
end analysis
end Casting
end YM.CF.Buffered.Afterglow.Tower.Aria
#print axioms YM.CF.Buffered.Afterglow.Tower.Aria.Casting.mean_run
