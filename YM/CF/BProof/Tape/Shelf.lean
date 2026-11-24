import YM.CF.BProof.Mark.Pairs
import YM.CF.BProof.Tape.Market
/-! Drawing and interpretation of arrays. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Tape
open Function Cube Spin Extension Metric MeasureTheory Dial Lat Tulip Tenant Branch Fock SU Lattice Angular Circle Hero Dream Filter Mark Finset Wick Stint Set
open scoped Topology Matrix Matrix.Norms.L2Operator ContDiff Classical BigOperators
attribute [local instance] opCStarAlgebra

def T (i:Bool)(x:ℝ) := if i then x else 1+x
lemma T_c (i:Bool):ContDiff ℝ ∞ (T i) := by cases i; exact contDiff_const.add contDiff_id; exact contDiff_id
lemma T'_d (i:Bool)(t:ℝ): HasDerivAt (T i) 1 t:=by cases i; exact (hasDerivAt_id t).const_add 1; exact hasDerivAt_id t
lemma T_b (i:Bool)(x:ℝ)(h:x∈walking): T i x∈TimeR:=by cases i; exact ⟨add_nonneg zero_le_one h.1,(add_le_add_right h.2 (1:ℝ)).trans (by norm_num : (1:ℝ)+1≤2)⟩; exact ⟨h.1,h.2.trans one_le_two⟩
variable (A:ℝ→Stamp)(p:Money A)
def payT (v':Bool) : Bool→ℝ→Stamp
 | true=> fun x=> deriv A (T v' x)
 | false=> fun x=> A (T v' x)
def drawQ : Thread := fun k=> ⟨fun x:Beam=> payT A k.1 k.2 x.val,by rcases k with ⟨i,b|b⟩; exact (p.2.1.continuous.comp (T_c i).continuous).comp continuous_subtype_val; exact ((p.2.1.continuous_deriv (by simp)).comp (T_c i).continuous).comp continuous_subtype_val⟩ -- tune b pattern
variable {A} {s:Side}
lemma under (v' b:Bool)(x:ℝ)(h:x∈walking)(p:Money A) : ‖payT A v' b x‖ ≤ rateH:=by cases b; exact ((p.weight _).trans_le expenses.one); exact p.2.2 _ (T_b v' _ h)
lemma deriv_pay(v:Bool)(x:ℝ)(p:Money A): HasDerivAt (payT A v false) (payT A v true x) x:= (by
    have hp:=HasDerivAt.scomp x ((p.2.1.differentiable (by simp) (T v x)).hasDerivAt) (T'_d v x); rw [one_smul] at hp; exact hp)
lemma eq_draw {A B:ℝ→Stamp}{p:Money A}{q:Money B}(h:A=B): drawQ A p=drawQ B q:= by subst B; rfl

section
variable (Q: Site (More s)→ℝ→Stamp)(p:∀ i,Money (Q i))
def drawB : Skein s rateH where
 val i:=drawQ (Q i) (p i)
 property x u t:=by change ‖payT (Q x) _ _ (visit t.val).val‖≤_; rw [walk_visit]; exact under _ _ _ t.property (p x)
lemma draw_cost (u v:Bool)(t:Beam)(x:Site (More s)) : (drawB Q p).val x (u,v) t=payT (Q x) u v t.val:=rfl
lemma folio (u v:Bool)(x:Site (More s))(t:ℝ)(h:t∈ Icc (-1:ℝ) 2): roam (drawB Q p).val (u,v) t x=payT (Q x) u v t:= by unfold roam; rw [draw_cost,visit_self h]
lemma walk_h {t:ℝ}(h:t∈walking): t∈ Icc (-1:ℝ) 2:= Icc_subset_Icc (by norm_num : (-1:ℝ)≤0) one_le_two h
lemma pretty (u:Bool)(t:ℝ)(h:t∈walking): roam (drawB Q p).val (u,false) t=fun i=> Q i (T u t):= funext fun x=> folio Q p u false x t (walk_h h)
private def pulsed : Quilt s→ₗ[ℂ] Op (Single s) where
 toFun:= pair
 map_add' x y:= (by ext i j; simp only [Matrix.add_apply,pair_local, Pi.add_apply, mul_add]; split; rfl; simp)
 map_smul' k x:=(by ext i j; simp only [Matrix.smul_apply,pair_local, Pi.smul_apply,RingHom.id_apply,smul_eq_mul]; split; ring; simp)
lemma story : Wick.Story (week (drawB Q p).val (true,false)) (week (drawB Q p).val (false,false)) (week (drawB Q p).val (true,true)) (week (drawB Q p).val (false,true)):=by
 let f:= (drawB Q p).val; let L:=pulsed (s:=s) |>.toContinuousLinearMap.restrictScalars ℝ
 have he(i:Bool)(x:ℝ)(h:x∈walking) : HasDerivAt (week f (i,false)) (week f (i,true) x) x:= by
    apply HasFDerivAt.comp_hasDerivAt _ L.hasFDerivAt; refine hasDerivAt_pi.mpr (fun j=>?_); change HasDerivAt (fun t=> roam f (i,false) t j) (roam f (i,true) x j) x; unfold f; rw [folio Q p i true j _ (walk_h h)]; apply (deriv_pay i x (p j)).congr_of_eventuallyEq (Eventually.mono (Icc_mem_nhds (by linarith [h.1] : (-1:ℝ) < x) (by linarith [h.2] : x<2)) (fun t ht=>folio Q p i false j t ht)) -- tune apply
 exact ⟨he true, he false⟩
end
section
variable {A:Type*}[MeasurableSpace A]
open TopologicalSpace
lemma feeBorel {E:Type*}[NormedAddCommGroup E][NormedSpace ℝ E][MeasurableSpace E][BorelSpace E][SecondCountableTopology E]{F:A→ℝ→E} (h:∀ a,ContDiff ℝ ∞ (F a)) (v:∀ t,Measurable fun p=> F p t)(t:ℝ):Measurable fun a=> deriv (F a) t:=by
 obtain ⟨f,hf⟩:= Filter.exists_seq_tendsto (𝓝[≠] t); let T(i:ℕ)(x:A):= slope (F x) t (f i); have hp(i): Measurable (T i):= by simp only [T,slope_def_module]; fun_prop -- tune second countability?
 exact measurable_of_tendsto_metrizable hp ((tendsto_pi_nhds).mpr fun a=> ((hasDerivAt_iff_tendsto_slope).1 (((h a).differentiable (by simp) t).hasDerivAt)).comp hf)
lemma beam_m {F:A→ C(Beam,Stamp)} (p:∀ t,Measurable fun a=> F a t): Measurable F:=by
 letI : Nonempty Beam:=⟨visit 0⟩; let f:=denseSeq Beam; let S(A:C(Beam,Stamp))(i:ℕ): Stamp:=A (f i); have he: Continuous S:= continuous_pi (fun i=> continuous_id.eval continuous_const); refine (he.measurableEmbedding ?_).measurable_comp_iff.mp (measurable_pi_lambda _ (fun i=> p (f i)))
 intro a b h; ext1 i; exact congrFun ((denseRange_denseSeq Beam).equalizer a.continuous b.continuous h) i
lemma draw_m(F:A→ℝ→Stamp)(p:∀ a,Money (F a))(v:∀ t,Measurable (fun a=>F a t)):Measurable (fun a=>drawQ (F a) (p a)):=by apply measurable_pi_lambda; rintro ⟨i,b|b⟩; apply beam_m; exact fun t=> v (T i t.val); apply beam_m; exact fun t=> feeBorel (fun x=>(p x).2.1) v (T i t.val)
lemma skein_m (F:A→ Site (More s)→ℝ→Stamp)(p:∀ a z,Money (F a z))(v:∀ t z,Measurable (fun a=> F a z t)): Measurable (fun a=> drawB (F a) (p a)):= (measurable_pi_lambda (fun (a:A)(x: Site (More s))=> drawQ (F a x) (p a x)) (fun x=> draw_m _ (fun a=>p a x) (fun t=>v t x))).subtype_mk -- tune syntax
end
end YM.CF.BProof.Tape
