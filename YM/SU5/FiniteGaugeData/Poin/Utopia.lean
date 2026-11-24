import YM.SU5.FiniteGaugeData.Poin.BrightT
import Mathlib.Data.List.Sort
/-!
# Swivel to Earth. Handle *all* distinct Eu point configurations by estimating rotations.
-/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy.Seld.Poin
open Filter Function Mink Mink.General Mink.Lorentz Real Flute Set
open scoped Topology BigOperators NNReal
local notation "b"=>timeAxis
variable {n:ℕ}(x:Points n)(a:Axis)(L: List (Fin n))
-- ordering lease
abbrev Sau {α:Type*}(g:α→ℝ)(L:List α):Prop:= L.Pairwise (fun i j=>g i<g j)
abbrev ProofOrder := Sau (clockV a x) L
lemma Lynx(L M:SO): turnO L.val (turnO M.val x) = turnO (L*M).val x:=rfl
@[simp] lemma Luna: turnO 1 x=x:=rfl
lemma warm_π (Z:SO)(p:x∈conf n): turnO Z.val x∈conf n:=fun _ _ h=> p ((Function.LeftInverse.injective (f:=walk Z.val) (g:=walk Z.val⁻¹) (General.proceeds Z.val)) h) -- cast.P
lemma orderX {a:Axis}(h:Chronos («a»:=a) x): ProofOrder x a (Each n):= (pairwise_each n).imp (fun {i} {j} p=> h (show i< j from p))
where pairwise_each(n:ℕ): List.Pairwise (· < ·) (Each n):=  (List.sortedLT_finRange n).pairwise
lemma SortApp (k:Fin n→ℝ) (h:Injective k): ∃ M:List (Fin n), M.Perm (Each n)∧ Sau k M:=by
 let R(i j:Fin n):= k i ≤ k j; letI : Std.Total R:= ⟨fun i j=> le_total ..⟩; letI : IsTrans (Fin n) R:= ⟨fun _ _ _ => le_trans⟩; letI : DecidableRel R:= Classical.decRel R; let M:= (Each n).insertionSort R; have u:M.Perm (Each n):= List.perm_insertionSort ..; have he:= u.nodup_iff.mpr ( List.nodup_finRange _); refine ⟨M,u, ?_⟩; apply List.pairwise_iff_get.mpr; intro i j z; exact lt_of_le_of_ne ((List.pairwise_iff_get.mp (show M.Pairwise R from List.pairwise_insertionSort ..)) i j z) (h.ne (( List.pairwise_iff_get.mp he) i j z))
 -- combine
-- perturb.Tools.SN.
lemma stale (f: SO) : Continuous (turnO (n:=n) f.val):=by unfold turnO points; refine (PiLp.continuous_toLp _ _).comp ?_; apply continuous_pi; intro i; exact ((walk f.val).continuous.comp (by fun_prop))
lemma turn_f (s:SO)(e:Mink.Ray)(x: Points n) : Continuous fun p:ℝ=> turnO ((moveB e p)*s).val x:=by
 simp_rw [← Lynx]; let V(p:ℝ):=circleB e p; have hv:Continuous V:=by unfold V circleB; fun_prop
 refine (PiLp.continuous_toLp _ _).comp ?_; apply continuous_pi; intro i; exact (hv.clm_apply (g:=fun _=>(turnO s.val x) i) continuous_const) -- change args
lemma rsplit (x y:E4) (e:x≠y)(p:time x=time y): ∃ z:Mink.Ray,∀ᶠ t:ℝ in 𝓝[>] 0,time (walk (moveB z t).val x)≠ time (walk (moveB z t).val y):=by
 suffices h:∃ z: SpaceAxis,x z.castSucc≠ y z.castSucc by
    obtain ⟨z,h⟩:=h; let k:=Ray.fromAxis z; refine ⟨k,?_⟩; filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (gt_mem_nhds Real.pi_pos)] with t H q; change time (circleB k t x)≠time (circleB k t y); rw [ttake,ttake, p, Ray.onAxis, Ray.onAxis]; intro e; exact h (mul_left_cancel₀ (sin_pos_of_pos_of_lt_pi H q).ne' (sub_right_inj.mp e)) -- t ty
 by_contra! h; exact e (ext_by (PiLp.ext h) p)
abbrev Rain (L:SO)(p: Fin n × Fin n):Prop:= p.1≠p.2→ (clockV b (turnO L.val x) p.1)≠ clockV b (turnO L.val x) p.2
lemma RiseOrder (p:x∈conf n) (T:Finset (Fin n × Fin n)):∃ L:SO,∀ i ∈ T,Rain x L i:=by
 induction T using Finset.induction_on with
 | empty=> exact ⟨1,by simp⟩
 | insert i T e ih=>
    obtain ⟨L,h⟩:=ih; by_cases z: Rain x L i; · exact ⟨L,fun j v=>(Finset.mem_insert.mp v).elim (fun p=>p ▸ z) (h j)⟩
    unfold Rain at z; push Not at z; let X:= turnO L.val x; obtain ⟨r,m⟩:=rsplit (X i.1) (X i.2) (fun v=> z.1 (warm_π x L p v)) z.2
    let Q(t):=moveB r t*L; have ht(j:Fin n): Continuous (fun t => clockV b (turnO (Q t).val x) j):= by
       exact clock_cont.comp ((by fun_prop : Continuous (fun i:Points n=> i j)).comp (turn_f L r x))
    have hm: ∀ᶠ t:ℝ in 𝓝[>] (0:ℝ), ∀ j∈T,Rain x (Q t) j:= by
       refine (eventually_all_finset ..).mpr (fun j w=>?_)
       by_cases p:j.1=j.2; · exact Eventually.of_forall fun _ w=> False.elim (w p)
       have hq: Q 0=L:= by change moveB r 0*L=L; rw [show moveB r 0=1 from Subtype.ext (by change toll r 0=1; exact tiny r),one_mul]
       refine Eventually.mono (f:=𝓝[>] 0) (p:=fun t=> clockV b (turnO (Q t).val x) j.1 ≠ clockV b (turnO (Q t).val x) j.2) (nhdsWithin_le_nhds (isOpen_ne_fun (ht j.1) (ht j.2) |>.mem_nhds (?_))) (fun t r _=>r); change clockV b (turnO (Q 0).val x) j.1 ≠ clockV b (turnO (Q 0).val x) j.2; rw [hq]; exact h _ w p
    obtain ⟨t,hv,k⟩:= (hm.and m).exists; refine ⟨Q t, fun j w=>(Finset.mem_insert.mp w).elim (fun p=>p ▸ show Rain x (Q t) i from fun _=> k) (hv j)⟩
#print axioms rsplit
lemma CountOra (h:x∈conf n): ∃ (T:SO)(M:List (Fin n)),M.Perm (Each n) ∧ ProofOrder (turnO T.val x) timeAxis M:= by
 obtain ⟨T,t⟩:= RiseOrder x h Finset.univ; obtain ⟨y,hk,Y⟩:= SortApp (clockV b (turnO T.val x)) (fun i j p=> by_contra fun h=> t (i,j) (Finset.mem_univ _) h p); exact ⟨T,y,hk,Y⟩
lemma order_in (p:L.Perm (Each n))(h:ProofOrder x a L): x∈conf n:=by
 intro i j hz; by_contra k; have hv:(List.map (clockV a x) L).Nodup:= List.Pairwise.nodup (List.pairwise_map.mpr h); apply k; exact List.nodup_ofFn.mp (show (List.ofFn (clockV a x)).Nodup from (by rw [List.ofFn_eq_map]; exact (p.map _).nodup_iff.mp hv)) (by change x i a=x j a; rw [hz])
lemma PEye (L:List (Fin n)): IsOpen {x:Points n|ProofOrder x a L}:= by
 induction L with
 | nil=> rw [show {x:Points n|ProofOrder x a []}=Set.univ from Set.eq_univ_of_forall (fun _=>List.Pairwise.nil)]; exact isOpen_univ
 | cons i L ih=>
    let Z(j:Fin n):= {x:Points n| x i a<x j a}; rw [show {x:Points n|ProofOrder x a (i::L)}=(⋂ j∈L.toFinset, Z j)∩_ from ?_]; apply IsOpen.inter (isOpen_biInter_finset (fun i p=>isOpen_lt (by fun_prop) (by fun_prop))) ih
    ext x; simp [ProofOrder,Sau,List.pairwise_cons,Z,clockV]
#print axioms PEye
#print axioms CountOra
end YM.CF.Buffered.Afterglow.Hierarchy.Seld.Poin
