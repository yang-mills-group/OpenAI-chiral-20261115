import YM.CF.Vp929.Contour.Jars
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 800000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Py.Rate
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator ComplexConjugate
open Forge Rill Hive Fock Stilo Palot Scion
open Cube Lat Tenant Tulip
open Pastry Hake Levier Urn Peaks Fock Laic Branch Drapes
open Rush Scroll Paige Vault Phase Acorn Spire
attribute [local instance] opCStarAlgebra
open Vow Salt
open Ione Beau Haro Cascade
open scoped Mew
open Mew
variable {X Y:Type*}{n:Side}{P:BudgetPoint}{h v w:ℝ}{F:RegBudget n}{K:ForceBudget n}{t:Cusp n}
open Pressure
open Ascent Wray Jet Larch
variable {c:Book X}{d:Book Y}{g:Looks X}{g':Looks Y}
lemma Display.grow {H:Submodule ℝ (X→ℝ)} (p:Display H c)(x:X){u v}(t:c x u)(v':u≤v):c x v:=by obtain ⟨L,h,z,e⟩:= p.exists_T; exact (e _ ⟨_,t⟩ v).2 fun l h=> ((e _ ⟨_,t⟩ u).1 t l h).trans v'
section
variable [Sub X] [Sub Y]
lemma Portfolio.tip (F:X→Y) (h:∀ x a,c x a→ d (F x) a)(g₁:∀ S f,g S f→ g' S (fun z=> (F (f z).1,F (f z).2))) (p:∀ x y,F (x-y)=F x-F y) (T:Portfolio d g'): Display (accounts c g) (fun x=> d (F x)):= by
 refine Portfolio.engage F p (fun x q=>?_ ) ?_ T; · obtain ⟨u,v⟩:=q; exact ⟨u,h x u v⟩
 rintro S f ⟨t,q,b,e⟩; exact ⟨t, g₁ S f q, b, fun z h'=> ⟨h _ _ (e _ h').1, h _ _ (e _ h').2⟩⟩
lemma Portfolio.redeem (F:X→Y)(h:∀ x a,c x a→ d (F x) a)(g₁:∀ S f,g S f→ g' S (fun z=> (F (f z).1,F (f z).2))) (p:∀ x y,F (x-y)=F x-F y){t:Y→ℝ}(e:t∈accounts d g'):t ∘ F∈accounts c g:= by
 apply Portfolio.permit t e F p
 · rintro x ⟨a,t⟩; exact ⟨_,h _ a t⟩
 rintro S f ⟨t,q,b,e⟩; exact ⟨t,g₁ S f q,b,fun z h'=> ⟨h _ _ (e _ h').1, h _ _ (e _ h').2⟩⟩
end
open Push.AbsoluteSums Trees
abbrev DuesQ(Q:Sweep n→Prop)(P:BudgetPoint)(h:ℝ): Book (RegBudget n):=fun x=> IncX Q x P h
abbrev DarkQ(Q:Sweep n→Prop)(P:BudgetPoint)(h:ℝ): Book (ForceBudget n):=fun x=> Dark Q x P h
abbrev MonoQ (P:BudgetPoint)(h a:ℝ): Book (Pax n):=fun v b=>∃ x:Aura n→ℝ,(∀ i, Medal P i.val ∅ (v i) h (x i)) ∧ ∀ o:Seat n, tallB x P.B a o≤ b
abbrev Packed (P:BudgetPoint)(h a:ℝ): Book (Cusp n):=fun K b=>∃ x:Aura n→ℝ, Anuk K x P h ∧ ∀ o:Seat n, tallB x P.B a o≤b
abbrev Marked (P:BudgetPoint)(h a:ℝ): Book (Cusp n):=fun K b=> ∃ x:blazeK n,(∀ i:Aura n,∀ D∈ fullD i, Medal P i.val D (K i D) h (x i D)) ∧ ∀ o:Seat n, tallB (Vow.hymn x) P.B a o≤ b
abbrev Census [NormedAddCommGroup Y][NormedSpace ℂ Y]{i:Type*} : Looks (X→i→ Y):= fun S f=>∀ x,S|> fun S'=>Glimpses S' (fun z=> ((f z).1 x,(f z).2 x))
abbrev Query (D: Aura n → Set (Support (More n))): Looks (Cusp n):= fun S f=>∀ (i:Aura n)(v), v∈ D i→ Glimpses S fun z=> ((f z).1 i v,(f z).2 i v)
abbrev markedQ : Looks (Cusp n):=Query fun i=> fullD i
variable (u:1≤h) {a:ℝ}(ha:0≤a) {Q:Sweep n→ Prop}
private lemma singleWeight {i:Type*}[Fintype i]{x o:i→ℝ}(c:ℝ)(j:i)(h:∀ i,0≤x i)(hx:∀ i,0≤o i)(p:1≤o j)(t:∑ i,o i*x i ≤ c):x j ≤ c:= (le_mul_of_one_le_left (h j) p).trans ((single_le_sum (f:=fun i=> o i*x i) (fun i _=>mul_nonneg (hx i) (h i)) (mem_univ j)).trans t)
-- uniform pass costs for every piece
include u
local notation "D'"=> Finset (Dwell n)
open Display
private abbrev ask_why (P:BudgetPoint)(x:Seat n)(i:Scree.Hub n):= if x=i.val.1 then currency P.B P.supportExponent i.val.2 else 0
omit u
private lemma ask_nn (P:BudgetPoint)(x:Seat n)(i:Scree.Hub n):0≤ask_why P x i:=by unfold ask_why; split; exact (Real.exp_pos _).le; exact le_rfl
private lemma ask_sum (P:BudgetPoint)(V:Scree.Hub n→ℝ)(x:Seat n): ∑ i,ask_why P x i*V i = ∑ i:Scree.Hub n,if x=i.val.1 then P.mass i.val.2 (V i) else 0:=by refine sum_congr rfl (fun i _=>?_ ); unfold ask_why; split; exact rfl; exact zero_mul _
include u
lemma ask_piece (V:RegBudget n)(t:DuesQ Q P h V v)(i:Scree.Hub n) : PressB P i (V i) h v:=by
 obtain ⟨F,h,t⟩:= t.weight; apply Display.grow (registerPass i u) _ (h i); refine singleWeight _ i (fun j=> (registerPass j u).coin _ _ (h j)) (ask_nn P (i.val.1)) ?_ ((ask_sum P F i.val.1).trans_le (t _)); rw [ask_why,if_pos rfl]; exact Real.one_le_exp (mul_nonneg P.exponent_pos.le (by positivity))
lemma ask_Team : Portfolio (DuesQ Q P h) Census:= by
 let H(i:Scree.Hub n):= Portfolio.tip (fun V:RegBudget n=> V i) (c:=DuesQ Q P h) (fun x u' y=> ask_piece u x y i) (g:= Census) (fun _ _ h=> h i) (fun _ _=>rfl) (registerPass i u)
 refine (Display.drug H (ask_why P) (ask_nn _)).hull _ ?_
 rintro X ⟨u,t⟩ b; constructor; · rintro ⟨⟨v,h,p⟩,v'⟩; exact ⟨v,h,fun o=> (ask_sum P v o).trans_le (p o)⟩
 rintro ⟨w,v,p⟩; exact ⟨⟨w,v,fun o=>(ask_sum P w o).symm.trans_le (p o)⟩, t.face⟩

private abbrev darkest_why (P:BudgetPoint)(x:Seat n)(i:Force n):= if x∈i.val.1.val.2 then currency P.B P.supportExponent i.val.1.val.2 else 0
omit u
private lemma darkest_nn (P:BudgetPoint)(x:Seat n)(i:Force n):0≤darkest_why P x i:=by unfold darkest_why; split; exact (Real.exp_pos _).le; exact le_rfl
private lemma darkest_sum (P:BudgetPoint)(V:Force n→ℝ)(x:Seat n): ∑ i,darkest_why P x i*V i = ∑ i:Force n,if x∈i.val.1.val.2 then P.mass i.val.1.val.2 (V i) else 0:=by refine sum_congr rfl (fun i _=>?_ ); unfold darkest_why; split; exact rfl; exact zero_mul _
include u
lemma darkest_piece (V:ForceBudget n)(t:DarkQ Q P h V v)(i:Force n) : ForceB P i (V i) h v:=by
 obtain ⟨F,h,t⟩:= t.weight; apply Display.grow (registerForce i u) _ (h i); refine singleWeight _ i (fun j=> (registerForce j u).coin _ _ (h j)) (darkest_nn P (i.val.1.val.1)) ?_ ((darkest_sum P F i.val.1.val.1).trans_le (t _)); rw [darkest_why,if_pos i.val.1.prop]; exact Real.one_le_exp (mul_nonneg P.exponent_pos.le (by positivity))
lemma darkest_Team : Portfolio (DarkQ Q P h) Census:= by
 let H(i:Force n):= Portfolio.tip (fun V:ForceBudget n=> V i) (c:=DarkQ Q P h) (fun x u' y=> darkest_piece u x y i) (g:= Census) (fun _ _ h=> h i) (fun _ _=>rfl) (registerForce i u)
 refine (Display.drug H (darkest_why P) (darkest_nn _)).hull _ ?_
 rintro X ⟨u,t⟩ b; constructor; · rintro ⟨⟨v,h,p⟩,v'⟩; exact ⟨v,h,fun o=> (darkest_sum P v o).trans_le (p o)⟩
 rintro ⟨w,v,p⟩; exact ⟨⟨w,v,fun o=>(darkest_sum P w o).symm.trans_le (p o)⟩, t.face⟩
omit u
private abbrev chance (i: Seat n)(A:Aura n)(p:BudgetPoint)(a:ℝ):ℝ:= if i∈ A.val then currency p.B a A.val else 0
private lemma chance_nn (i:Seat n)(A:Aura n) : 0≤ chance i A P a:=by unfold chance; split; exact (Real.exp_pos _).le; exact le_rfl
private lemma tot_ch (i:Seat n)(A:Aura n→ℝ) : ∑ x,chance i x P a*A x= tallB A P.B a i:=by unfold tallB; rw [sum_filter]; refine sum_congr rfl fun x _=>?_ ; unfold chance; split; exact mul_comm ..; exact zero_mul _
lemma soleCash {A:Aura n→ℝ}(ha:0≤a)(i:Aura n)(g:∀ i,0≤ A i)(u:∀ i:Seat n, tallB A P.B a i≤v):A i ≤ v:=by obtain ⟨j,j'⟩:= i.prop; exact singleWeight _ i g (fun x=>chance_nn j x) (by unfold chance; rw [if_pos j']; exact Real.one_le_exp (mul_nonneg ha (by positivity))) ((tot_ch j A).trans_le (u _))
include u ha
lemma MonoQ.part {A:Pax n}(p:MonoQ P h a A v)(i:Aura n): Medal P i.val ∅ (A i) h v:=by obtain ⟨x,t,v⟩:=p; exact (t i).big (soleCash ha i (fun i=> (t i).wage (zero_le_one.trans u)) v)
lemma MonoQ.Team : Portfolio (MonoQ (n:=n) P h a) Census:=by
 let H(i:Aura n):= Portfolio.tip (fun V:Pax n=> V i) (c:= MonoQ P h a) (fun _ _ p=> p.part u ha i) (g:= Census) (fun _ _ h=> h i) (fun _ _=>rfl) (registerPrize i.val ∅ u)
 refine (Display.drug H (fun i x=>chance i x P a) (fun _ _=>chance_nn ..)).hull _ ?_
 intro X u b; exact ⟨fun ⟨y,w,v⟩=> ⟨y,w,fun x=> (tot_ch x y).trans_le (v x)⟩, fun ⟨y,w,v⟩=> ⟨y,w,fun x=> (tot_ch x y).symm.trans_le (v x)⟩⟩
lemma Packed.part {A:Cusp n}(p:Packed P h a A v)(i:Aura n)(D:Support (More n))(x:D∈fullD i): Medal P i.val D (A i D) h v:= by obtain ⟨x',t,v⟩:=p; exact (t.2 _ _ (mem_filter.mp x).2.1 (mem_filter.mp x).2.2).big (soleCash ha i t.1 v)
lemma Marked.part {A:Cusp n}(p:Marked P h a A v)(i:Aura n)(D:Support (More n))(x:D∈fullD i): Medal P i.val D (A i D) h v:= by obtain ⟨x',t,v⟩:=p; apply (t i D x).big; let T (i j) (h:j∈ fullD i):0≤ x' i j:= (t i j h).wage (zero_le_one.trans u); exact (single_le_sum (T i) x).trans (soleCash ha i (fun i=> sum_nonneg (T i)) v)
lemma Packed.team : Portfolio (Packed (n:=n) P h a) markedQ:=by
 let H(i:Aura n)(D:Support (More n))(x:D∈ fullD i):= Portfolio.tip (fun V:Cusp n=> V i D) (c:=Packed P h a) (fun _ _ p=> p.part u ha i D x) (g:=markedQ) (fun _ _ h=> h i D x) (fun _ _=>rfl) (registerPrize i.val D u)
 refine (Display.drug (fun i=> Display.sup fun x:↥(fullD i)=> H i x.val x.prop) (fun i x=>chance i x P a) (fun _ _=>chance_nn ..)).hull _ ?_
 intro X u b; exact ⟨fun ⟨y,w,v⟩=> ⟨y,fun i=>⟨w.1 i,fun t=> w.2 _ _ (mem_filter.mp t.prop).2.1 (mem_filter.mp t.prop).2.2⟩,fun x=> (tot_ch x y).trans_le (v x)⟩, fun ⟨y,w,v⟩=> ⟨y,⟨fun i=> (w i).1,fun i B p q=>(w i).2 ⟨B,mem_filter.mpr ⟨mem_univ _,p,q⟩⟩⟩,fun x=> (tot_ch x y).symm.trans_le (v x)⟩⟩
lemma Marked.team : Portfolio (Marked (n:=n) P h a) markedQ:=by
 let H(i:Aura n)(D:Support (More n))(x:D∈ fullD i):= Portfolio.tip (fun V:Cusp n=> V i D) (c:=Marked P h a) (fun _ _ p=> p.part u ha i D x) (g:=markedQ) (fun _ _ h=> h i D x) (fun _ _=>rfl) (registerPrize i.val D u)
 let A:= (i:Aura n) × ↥(fullD i); let V (x:Aura n→Support (More n)→ℝ)(z:A):= x z.1 z.2.val
 refine (Display.drug (fun x:A=>H x.1 x.2.val x.2.prop) (fun i x=>chance i x.1 P a) (fun _ _=>chance_nn ..)).hull _ ?_
 intro X u b
 have hm (q:A→ℝ)(x:Aura n→ Support (More n)→ℝ)(hx:V x=q)(i:Seat n): ∑ j:A,chance i j.1 P a*q j=tallB (Vow.hymn x) P.B a i:=by
    rw [←tot_ch (P:=P),←hx,Fintype.sum_sigma]; refine sum_congr rfl fun j _=>?_ ; unfold Vow.hymn; rw [mul_sum]; exact (fullD j).sum_coe_sort fun D=> chance i j P a * x j D
 refine ⟨fun ⟨x,p,v⟩=>⟨V x,fun i=> p i.1 i.2.val i.2.prop,fun i=> (hm _ _ rfl i).trans_le (v i)⟩,fun ⟨y,p,v⟩=>?_ ⟩
 let q (i:Aura n)(x:Support (More n)):= if u:x∈fullD i then y ⟨i, ⟨x,u⟩⟩ else 0
 have he: V q=y:= funext fun ⟨i,x,h⟩=> dif_pos h; exact ⟨q, fun i x h=> by unfold q; rw [dif_pos h]; exact p ⟨i,x,h⟩, fun o=> (hm _ q he o).symm.trans_le (v o)⟩
end YM.CF.Py.Rate
