import YM.CF.BProof.Grid.Fiber
import YM.CF.BProof.Borel

/-! One extension step of entity hierarchy. Selections Borel and terms read only that entity. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Grid.Fiber
open Filter Metric Lattice Function Set MeasureTheory Finset Entity TopologicalSpace
open scoped Topology NNReal ENNReal Matrix.Norms.Frobenius BigOperators Classical
variable {n : ℕ} {G : Gauge} {F : Type} [TopologicalSpace F] (X : Fiber n G F)

variable {c s : Side} (g : Ratio c s)
lemma rim_sub (p : Entity n c)(hc:4≤c.val){x}(h:Rim g p x):p.Mem g x:=by obtain ⟨i,v,b,h⟩:=h; exact ((p.mem_wall g hc _ v b).mp h).1
lemma rim_ne (p : Entity n c)(a:0<p.dim)(hc:4≤ c.val): Rim g p (p.first g) := by obtain ⟨i,hi⟩:= Finset.card_pos.mp a; refine ⟨i,hi,false,(p.mem_wall g hc _ hi false).mpr ⟨p.mem_first g,?_⟩⟩; rw [coord_first]; rfl

def grade (u : ℝ) := 1+max X.C (2*n*(u+1))
lemma grade_pos (u : ℝ) : 0<X.grade u := by unfold grade; have := X.C_one; grind
noncomputable def toll (u : ℝ) := (X.extend _ (X.grade_pos u)).choose
lemma toll_p (u : ℝ) : 0<X.toll u:= (X.extend _ (X.grade_pos u)).choose_spec.1
abbrev Birth (p : Entity n c)(d : ℝ)(U:Wire G n s)(A B:Floor F n s):=X.Fast g B U p d ∧ ∀ x,Rim g p x → A x=B x

lemma leads (p : Entity n c) (U: Wire G n s) (V:Floor F n s) (u : ℝ)(hv : 0<u)
    {m : ℝ} (h : X.Border g V U p (u/g.count.val))(hc:4≤ c.val)(hh:X.cap g.count m)(Φ:okay g U m p) :
    ∃ Y,X.Birth g p ((X.toll u+1)/g.count.val) U V Y := by
 by_cases ht:0<p.dim
 swap; · exact ⟨V,X.zeroD g V U p hc (by omega) _,fun x _=>rfl⟩
 let P:= X.grade u; let f:=p.chart g; let S:={x| p.Mem g x}; let T:={x|Rim g p x}; have hp:T⊆S:=fun _ h=>rim_sub g p hc h
 let F₀(x:Fin n→ℝ) := if h : ∃ y,y∈S∧f y=x then X.flat g V U p h.choose else V (p.first g)
 have he(x)(h:x∈S):F₀ (f x)= X.flat g V U p x:=by
   let a:∃ y,y∈S∧ f y=f x:=⟨x,h,rfl⟩
   unfold F₀; rw [dif_pos a, p.unique g hc a.choose_spec.1 h a.choose_spec.2]
 have hv(S' : Set (Cubic n s))(h:S'⊆ S) : f '' S' ⊆ Metric.closedBall 0 1:=by rintro x ⟨y,hy,rfl⟩; exact p.positions g (h hy)
 let Y:= X.flat g V U p; have hz:= (X.extend _ (X.grade_pos u)).choose_spec.2 (f '' S) (f '' T) F₀ (hv S (Subset.refl _)) (image_mono hp) ((show T.Nonempty from ⟨_,rim_ne g p ht hc⟩).image f)
 rename_i hv' -- shadow
 obtain ⟨F',h',H⟩:= hz (by rintro _ ⟨x,hx,rfl⟩ _ ⟨y,hy,rfl⟩; rw [he _ (hp hx),he _ (hp hy)]; exact X.around g V U p hv' h hc hh Φ x hx y hy)
 let W (x:Cubic n s):= X.move (p.paths G g U x)⁻¹ (F' (f x)); have hw(x): X.flat g W U p x=F' (f x):= X.cancelMove ..
 refine ⟨W, fun x i hx l=> ?_,fun x hx=>?_⟩
 · let y:=slide x i; have hE : X.costW W U x i ≤ X.cost (F' (f x)) (F' (f y))+1/g.count.val:= by
      have ht:= (abs_le.mp (X.flat_cost g W U m x i p hx l hc hh.1 Φ)).1; rw [hw,hw] at ht; change -(X.C * _) ≤ X.cost (F' (f x)) (F' (f y)) -_ at ht; linarith [hh.2]
   apply hE.trans; rw [add_div]; gcongr; refine (H _ (mem_image_of_mem _ (show x∈S from hx)) _ (mem_image_of_mem _ (show y∈S from l))).trans ?_
   rw [Entity.cost g p hc hx l]; have hp:0<(g.count.val:ℝ):=by exact_mod_cast (show 0<g.count.val from g.count.property)
   change X.toll u * _≤_; nth_rw 2 [← mul_one (X.toll u)]; rw [_root_.mul_div_assoc]; gcongr; exact X.toll_p u |>.le; exact_mod_cast Grid.near_slide x i -- tune
 unfold W; rw [← h' (mem_image_of_mem _ (show x∈ T from hx)),he _ (hp hx),flat, ← X.mul,inv_mul_cancel,X.unit]

variable [MeasurableSpace F][BorelSpace F][MetrizableSpace F] [SecondCountableTopology F][CompactSpace F] [Nonempty F]
lemma costC (G' : Fiber n G F)(x:Cubic n s) (i): Continuous fun p : Wire G n s × Floor F n s=>G'.costW p.2 p.1 x i:= by
 unfold costW; apply G'.cont_d.comp (g:=uncurry G'.cost) (f:=fun p : Wire G n s × Floor F n s=> (p.2 x,G'.move (p.1 (x,i)) (p.2 (slide x i))))
 apply Continuous.prodMk _ _; fun_prop
 exact G'.cont_a.comp (f:=fun p : Wire G n s × Floor F n s=>(p.1 (x,i),p.2 (slide x i))) (by fun_prop)

private lemma Fast_closed (p:Entity n c)(d:ℝ) : IsClosed {x: Wire G n s × Floor F n s|X.Fast g x.2 x.1 p d}:= by
 simp only [Fast,setOf_forall]; exact isClosed_iInter fun x=> isClosed_iInter fun i=> isClosed_iInter fun _=> isClosed_iInter fun _=> isClosed_le (X.costC x i) continuous_const
private lemma born_close (p:Entity n c)(d:ℝ) : IsClosed {x : (Wire G n s× Floor F n s) × Floor F n s | X.Birth g p d x.1.1 x.1.2 x.2}:=by
 simp only [Birth,setOf_and,setOf_forall]; apply IsClosed.inter ((Fast_closed X g p d).preimage (f:=fun x : (Wire G n s× Floor F n s) × Floor F n s=> (x.1.1,x.2)) (by fun_prop))
 exact isClosed_iInter fun i=> isClosed_iInter fun h=> isClosed_eq (by fun_prop) (by fun_prop)

-- general version useful for subcomplex steps
abbrev Preg := Wire G n s × Floor F n s
noncomputable def cut (p:Entity n c) (A:Preg (n:=n) (s:=s) (G:=G) (F:=F)): Preg (n:=n) (s:=s) (G:=G) (F:=F) :=
 (fun i => if Wire.Along {x|p.Mem g x} i then A.1 i else 1, fun x=> if p.Mem g x then A.2 x else Classical.arbitrary _)
lemma cut_birth (p:Entity n c) (A:Preg (n:=n) (s:=s) (G:=G) (F:=F)) (V) (d:ℝ) (hc:4≤c.val) :
    X.Birth g p d (cut g p A).1 (cut g p A).2 V ↔ X.Birth g p d A.1 A.2 V:=by
  simp only [Birth, Fast, costW, cut]
  apply and_congr
  · refine forall_congr' fun x=> forall_congr' fun i=> ?_
    apply imp_congr_right; intro h; apply imp_congr_right; intro u; rw [if_pos (show Wire.Along _ _ from ⟨h,u⟩)]
  refine forall_congr' fun x=> imp_congr_right fun h=> ?_; rw [if_pos (rim_sub g p hc h)]
lemma cut_eq (p:Entity n c) (A B:Preg (n:=n) (s:=s) (G:=G) (F:=F)) (h:Wire.Agrees G {x|p.Mem g x} A.1 B.1) (k:EqOn A.2 B.2 {x|p.Mem g x}): cut g p A = cut g p B:=by unfold cut; congr 1; ext1 x; split; rename_i f; rw [h x f]; rfl; ext1 x; split; rename_i f; rw [k f]; rfl
private lemma cut_m (p:Entity n c) : Measurable (cut (G:=G) (F:=F) g p):= by
 unfold cut; apply Measurable.prodMk
 · refine measurable_pi_lambda _ fun i=>?_ ; split_ifs <;> fun_prop
 refine measurable_pi_lambda _ fun i=>?_ ; split_ifs <;> fun_prop

lemma sally (p:Entity n c) (d:ℝ) : ∃ t : Preg (n:=n) (s:=s) (G:=G) (F:=F) → Floor F n s,Measurable t ∧ ∀ U,(∃ V,X.Birth g p d U.1 U.2 V)→ X.Birth g p d U.1 U.2 (t U) := by
 let A:=Preg (n:=n) (s:=s) (G:=G) (F:=F); let S:={x : A × Floor F n s| X.Birth g p d x.1.1 x.1.2 x.2}; let T:=Prod.fst '' S
 have ht:=born_close X g p d
 have hh : IsClosed T:=isClosedMap_fst_of_compactSpace S ht
 obtain ⟨F₀,hF,H⟩:= closed_choice (X:=↥T) ((fun x : ↥T × Floor F n s=> (x.1.val,x.2)) ⁻¹' S) (ht.preimage (by fun_prop)) (by rintro ⟨x,y,u,rfl⟩; exact ⟨y.2,u⟩)
 refine ⟨fun x=> if h:x∈T then F₀ ⟨x,h⟩ else Classical.arbitrary _, Measurable.dite hF measurable_const hh.measurableSet, fun x v=>?_⟩
 obtain ⟨y,hv⟩:=v; have ht:x∈T:=⟨(x,y),hv,rfl⟩; simp only [dif_pos ht]; exact H ⟨x,ht⟩

def fill (p:Entity n c) (d:ℝ) := (X.sally g p d).choose ∘ cut g p
lemma fill_m (p:Entity n c) (d:ℝ) : Measurable (X.fill g p d):=(sally X g p d).choose_spec.1.comp (cut_m ..)
lemma fill_p (p:Entity n c) (d:ℝ) (u:Preg (n:=n) (s:=s) (G:=G) (F:=F)) (hc:4≤c.val) (h:∃ V,X.Birth g p d u.1 u.2 V) : X.Birth g p d u.1 u.2 (X.fill g p d u):=(cut_birth X g p u _ d hc).mp ((X.sally g p d).choose_spec.2 _ (let ⟨_,a⟩:=h;⟨_,(cut_birth X g p u _ d hc).mpr a⟩))
end YM.CF.BProof.Grid.Fiber
