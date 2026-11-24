import GaugeFieldConstruction.EarthY
/- Incidence Majorant -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Fock.Wosk
open Pastry Function Set Metric MeasureTheory NormedSpace Filter Finset
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Classical
attribute [local instance] opCStarAlgebra
open Roots Mew Roots.GJ
variable {I J O V B W G:Type}[LinearOrder I][Fintype I][DecidableEq J][LinearOrder G][Fintype G]
lemma lea_p (L:List O)(X Y: O→ℝ)(p:∀i∈L,X i≤Y i):Lee L X≤Lee L Y:=by induction L with|nil=>rfl| cons i L h=> rw [consA,consA]; exact add_le_add (p i (List.mem_cons_self)) (h (fun i t=>p i (List.mem_cons_of_mem _ t)))
lemma lea_n (L:List O)(X:O→ℝ)(p:∀i∈L, 0≤X i): 0 ≤ Lee L X:=by
 induction L with|nil=>exact le_rfl|cons i L ih=> rw [consA]; exact add_nonneg (p i (List.mem_cons_self)) (ih (fun i t=>p i (List.mem_cons_of_mem _ t)))
lemma lea_z (L:List O):Lee L (fun _=>(0:ℝ))=0:=by induction L with|nil=>rfl|cons i L ih=> rw [consA,ih]; simp
lemma lea_plus (L:List O)(X Y: O→ℝ): Lee L (X+Y)=Lee L X+Lee L Y:=by induction L with|nil=> change (0:ℝ)=0+0; ring|cons i L ih=>rw [consA,consA _ X,consA _ Y,ih]; change X i+Y i+_= _; ring
lemma lea_pair (L:List O)(X Y: O→ℝ): Lee L (fun i=>X i+Y i)=Lee L X+ Lee L Y:=lea_plus ..
lemma lea_scale (L:List O)(X:O→ℝ)(t:ℝ): Lee L (fun i=>t*X i)=t*Lee L X:=by induction L with|nil=> change 0=t*0; ring|cons i L h=>rw [consA,consA _ X,h,mul_add]
lemma lea_sum {J:Type}[Fintype J](L:List O)(F:O→J→ℝ): (∑ i,Lee L fun j=>F j i)=Lee L (fun j=>∑ i,F j i):=by induction L with|nil=> simp [Lee]| cons i L h=>simp_rw [consA,sum_add_distrib,h]
lemma lea_sub (S L:List O)(w:S.Sublist L)(X:O→ℝ)(h:∀i∈L,0≤ X i):Lee S X ≤ Lee L X:=by
 induction w with
 | slnil=>exact le_rfl
 | cons i _ ih=>rw [consA]; exact (ih (fun i t=>h i (List.mem_cons_of_mem _ t))).trans (le_add_of_nonneg_left (h i (List.mem_cons_self)))
 | cons_cons i _ ih=>rw [consA,consA]; exact add_le_add_right (ih (fun i t=>h i (List.mem_cons_of_mem _ t))) _
variable (a b h r:ℝ)(g:Lem I J V B)(f:Lem I J W B)
abbrev weightV :ℝ:= Real.exp (a*g.seat.card) * b^g.keys.length * g.won
abbrev bil (w:J):ℝ:= if w ∈ g.seat then weightV a b g else 0
abbrev Lite (x:Option (G×G)):ℝ:= x.elim 1 (fun _=> h^2)
def wageL (g:Lem I J (Option (G×G)) B):=Lite h g.val * weightV a b g
def costL (g:Lem I J (Option (G×G)) B)(y:J):= Lite h g.val * bil a b g y
lemma WP_v (v:0≤ b)(p:0≤g.won):0≤weightV a b g:=mul_nonneg (by positivity) p -- tune
lemma WP_p (v:0≤ b)(p:0≤g.won)(y:J):0≤ bil a b g y:=by unfold bil; split; exact WP_v _ b g v p; exact le_rfl
lemma WP_d (y:J)(v:0≤ b)(p:0≤g.won): bil a b g y≤weightV a b g:=by unfold bil; split; exact le_rfl; exact WP_v _ _ _ v p
lemma WP_pair (p:0≤a)(v:0≤b)(t:0≤r)(g0:0≤g.won)(f0:0≤f.won)(i:O): weightV a b (joint g f r i)≤ r* (weightV a b g) * (weightV a b f):=by
 let X:= Real.exp (a*g.seat.card); let Y:=Real.exp (a*f.seat.card); let g1:= g.keys.length; let f1:=f.keys.length
 unfold weightV; dsimp only [joint]; rw [List.length_append,pow_add]
 have hx: Real.exp (a* (g.seat∪ f.seat).card) ≤ X*Y:=by
    unfold X Y; rw [←Real.exp_add]; refine Real.exp_monotone ?_; rw [←mul_add]; apply mul_le_mul_of_nonneg_left _ p; exact_mod_cast Finset.card_union_le g.seat f.seat
 exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hx (by positivity)) (by positivity)).trans_eq (by unfold X Y; ring)
lemma WP_union (p:0≤a)(v:0≤b)(t:0≤r)(g0:0≤g.won)(f0:0≤f.won)(i:O)(x:J): bil a b (joint g f r i) x ≤r*bil a b g x*weightV a b f + r*weightV a b g* bil a b f x:=by
 have hr:∀(i:J),0≤r*weightV a b g * bil a b f i:= fun i=>mul_nonneg (mul_nonneg t (WP_v _ b _ v g0)) (WP_p _ _ f v f0 i)
 have hz:∀(i:J),0≤r*bil a b g i*weightV a b f:= fun i=>mul_nonneg (mul_nonneg t (WP_p _ _ g v g0 i)) (WP_v _ b _ v f0)
 dsimp only [bil,joint]; split
 · next hu=>
    cases Finset.mem_union.mp hu with
    | inl w=> rw [if_pos w]; exact (WP_pair _ _ r g f p v t g0 f0 i).trans (le_add_of_nonneg_right (hr x))
    | inr w=> rw [if_pos w]; exact (WP_pair _ _ r g f p v t g0 f0 i).trans (le_add_of_nonneg_left (hz x))
 · exact add_nonneg (hz x) (hr x)

variable (ι:G→J)(W:G→G→Toil I J B)(c d:ℝ)
def OpenB (S:List (Lem I J V B)):Prop:= ∀ i∈S,0 ≤ i.won
lemma OpenB.mute {S L:List (Lem I J V B)}(s:S.Sublist L)(h:OpenB L):OpenB S:=fun i t=> h i (s.subset t)
lemma OpenB.append {S L:List (Lem I J V B)}(u:OpenB S)(v:OpenB L):OpenB (S++L):=fun i t=> (List.mem_append.mp t).elim (u i) (v i)
def privH (i:G)(y:J):ℝ:= ∑ j:G,Lee (W i j) fun v=>bil a b v y
structure FumedH : Prop where
  fee0 :∀ i j,OpenB (W i j)
  card0:∀ i j, ∀ v∈ W i j, ι i∈ v.seat ∧ ι j∈ v.seat
  σ0:∀ i, ∑ j:G,Lee (W i j) (fun v=>weightV a b v)≤ c
  σ1:∀ j,∑ i:G,Lee (W i j) (fun v=>weightV a b v)≤ c
  pc0:∀ y:J,∑ i,privH a b W i y≤ d
#check FumedH
abbrev puffQ (g:Lem I J (Option (G×G)) B):Prop:= ∀ i j,g.val=some (i,j) → ι i∈ g.seat ∧ ι j∈g.seat
def Puffion (K:Book0 I J G B):Prop:= OpenB K ∧∀ i∈ K,puffQ ι i
def MajorZ (K:Book0 I J G B)(s:ℝ):Prop:=∀ x:J, Lee K (fun e=>costL a b h e x) ≤ s
variable {C:ℝ}
lemma costsE (x:Option (G×G)):0 ≤ Lite h x:=by cases x with|none=>exact zero_le_one|some x=>exact sq_nonneg _
lemma cursorE (t:1≤ h)(x:Option (G×G)):1 ≤ Lite h x:=by cases x with|none=> exact le_rfl|some x=>change 1≤ h^2; exact one_le_pow₀ t
lemma costsZ (e:Lem I J (Option (G×G)) B)(v:0≤ b)(w:0≤ e.won)(x:J):0≤costL a b h e x:= mul_nonneg (costsE ..) (WP_p a b _ v w x)
abbrev hype (Q:Book0 I J G B)(x:J):= Lee Q (fun e=>bil a b e x)
lemma MajorZ.lower {Q:Book0 I J G B}(h0:1≤ h)(v:0≤b)(p:OpenB Q)(q:MajorZ a b h Q C)(x:J): hype a b Q x ≤ C:= (lea_p Q _ _ (fun i hu=> le_mul_of_one_le_left (WP_p a b _ v (p i hu) x) (cursorE h h0 i.val))).trans (q x)
lemma priv_w (v:0≤ b)(Z:FumedH a b ι W c d)(i:G)(x:J):0≤ privH a b W i x:=sum_nonneg fun j _=>lea_n (W i j) _ (fun q h=>WP_p a b _ v (Z.fee0 i j q h) x)
lemma raw_w (v:0≤ b)(Z:FumedH a b ι W c d)(i j:G):Lee (W i j) (fun v=>weightV a b v) ≤ c:=(single_le_sum (f:=fun j=> Lee (W i j) (fun v=>weightV a b v)) (fun j _=>lea_n _ _ (fun q h=> WP_v a _ _ v (Z.fee0 i j q h))) (mem_univ _)).trans (Z.σ0 i)
end YM.CF.Fock.Wosk
end
